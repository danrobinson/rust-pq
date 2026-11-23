"""Symbolically execute the normal path of the linked width-specialized H_msg driver."""

from image import require, sign_extend


def target(image, suffix, family):
    return image.function(suffix, family)[0]


def verify(image, width, length):
    pc, words = image.function(
        f"5h_msgKj{width:x}_EB6_".encode(), b"6slhdsa5shake4hash"
    )
    absorb = target(image, b"6Sponge6absorb", b"6slhdsa8shake256")
    finish = target(image, b"6Sponge6finish", b"6slhdsa8shake256")
    shim = target(image, b"35___rust_no_alloc_shim_is_unstable_v2", b"___rustc")
    alloc = target(image, b"19___rust_alloc_zeroed", b"___rustc")
    # Distinct names represent arbitrary caller regions. Symbolic words in the sponge
    # after each absorb stand for the full post-state of that particular call.
    gp = {r: ("saved", r) for r in range(19, 31)}
    gp.update(
        {
            0: ("params", 0),
            1: ("r", 0),
            2: ("seed", 0),
            3: ("root", 0),
            4: ("msg", 0),
            5: "message length",
            8: ("result", 0),
            31: ("stack", 0),
        }
    )
    v, mem = {}, {("params", 8): length}
    nabs = finished = allocations = shims = 0

    def address(base, delta, write=False):
        region, offset = gp[base]
        offset += delta
        if region == "stack":
            require(
                gp[31][1] <= offset <= -8 and offset % 8 == 0,
                "stack access outside frame",
            )
        else:
            require(
                (region == "result" and write and offset in (0, 8, 16))
                or (region == "params" and not write and offset == 8),
                "unexpected access",
            )
        return region, offset

    i = 0
    steps = 0
    while 0 <= i < len(words):
        steps += 1
        require(steps <= len(words), "unexpected loop in H_msg")
        w = words[i]
        d, n, second = w & 31, w >> 5 & 31, w >> 10 & 31
        i += 1
        if w & 0xFFC00000 in (0x91000000, 0xD1000000):
            require(d != 18, "platform register")
            region, off = gp[n]
            require(region == "stack", "unexpected pointer arithmetic")
            delta = (w >> 10 & 4095) * (-1 if w >> 30 & 1 else 1)
            gp[d] = region, off + delta
            if d == 31:
                require(
                    -496 <= off + delta <= 0 and (off + delta) % 16 == 0,
                    "invalid stack frame",
                )
        elif w & 0xFFE0FFE0 == 0xAA0003E0:
            require(d not in (18, 31) and w >> 16 & 31 != 31, "reserved MOV register")
            gp[d] = gp[w >> 16 & 31]
        elif w & 0xFFE00000 == 0x52800000:
            require(d not in (18, 31), "reserved MOV destination")
            gp[d] = w >> 5 & 0xFFFF
        elif w == 0x6F00E400:
            v[0] = (0, 0)
        elif w & 0xFFC00000 in (
            0xA9000000,
            0xA9400000,
            0xAD000000,
            0xAD400000,
            0x3D800000,
            0x3DC00000,
            0xF9000000,
            0xF9400000,
        ):
            pair = (w >> 24) in (0xA9, 0xAD)
            vector = (w >> 24) in (0xAD, 0x3D)
            load = bool(w & (1 << 22))
            size = 16 if vector else 8
            base = (sign_extend(w >> 15 & 127, 7) if pair else w >> 10 & 4095) * size
            require(not pair or d != second or not load, "overlapping pair destination")
            for j, reg in enumerate((d, second) if pair else (d,)):
                require(vector or reg not in (18, 31), "unsupported general register")
                require(
                    not (vector and load and 8 <= reg <= 15),
                    "callee-saved SIMD clobber",
                )
                require(
                    not (load and pair and not vector and reg == n),
                    "changing pair base",
                )
                keys = [
                    address(n, base + size * j + k, not load) for k in range(0, size, 8)
                ]
                if load:
                    if vector:
                        v[reg] = tuple(mem[k] for k in keys)
                    else:
                        gp[reg] = mem[keys[0]]
                else:
                    for k, val in zip(
                        keys,
                        v[reg] if vector else (gp[reg],),
                    ):
                        mem[k] = val
        elif w & 0x7F000000 == 0x36000000:  # TBZ Xt,#bit,target
            bit = ((w >> 31) << 5) | (w >> 19 & 31)
            if gp[d] & (1 << bit) == 0:
                i = i - 1 + sign_extend(w >> 5 & 0x3FFF, 14)
        elif w & 0xFF000000 == 0xB4000000:
            # A region pointer is non-null under the input/allocator contract.
            if gp[d] == 0:
                i = i - 1 + sign_extend(w >> 5 & 0x7FFFF, 19)
        elif w & 0xFC000000 == 0x14000000:
            i = i - 1 + sign_extend(w & 0x3FFFFFF, 26)
        elif w & 0xFC000000 == 0x94000000:
            dest = pc + 4 * (i - 1 + sign_extend(w & 0x3FFFFFF, 26))
            result = None
            if dest in (absorb, finish):
                region, _ = gp[0]
                require(region == "stack", "sponge argument outside stack")
                keys = [address(0, k * 8, dest == absorb) for k in range(26)]
                require(
                    [mem[k] for k in keys]
                    == [("absorbed", nabs, k) if nabs else 0 for k in range(26)],
                    "wrong sponge data or cursor",
                )
                if dest == absorb:
                    require(
                        nabs < 4
                        and gp[1] == (("r", "seed", "root", "msg")[nabs], 0)
                        and gp[2] == (width, width, width, "message length")[nabs],
                        "wrong absorption",
                    )
                    nabs += 1
                    for k, key in enumerate(keys):
                        mem[key] = ("absorbed", nabs, k)
                else:
                    require(
                        nabs == 4
                        and allocations == 1
                        and gp[1] == ("out", 0)
                        and gp[2] == length,
                        "wrong finish buffer or size",
                    )
                    for key in keys:
                        del mem[key]
                    finished += 1
            elif dest == shim:
                shims += 1
            elif dest == alloc:
                require(
                    gp[0] == length and gp[1] == 1 and shims == 1,
                    "incorrect allocation",
                )
                allocations += 1
                result = ("out", 0)
            else:
                raise ValueError(f"unexpected H_msg call {dest:#x}")
            gp = {r: x for r, x in gp.items() if 19 <= r <= 29 or r == 31}
            gp[30] = ("link", i)
            if result is not None:
                gp[0] = result
            v.clear()
        elif w == 0xD65F03C0:
            require(
                (nabs, finished, shims, allocations) == (4, 1, 1, 1)
                and gp[31] == ("stack", 0)
                and all(gp[r] == ("saved", r) for r in range(19, 31)),
                "wrong H_msg return",
            )
            require(
                [mem["result", k] for k in (0, 8, 16)] == [length, ("out", 0), length],
                "incorrect result pointer, capacity or length",
            )
            return pc, len(words) * 4
        else:
            raise ValueError(f"unsupported H_msg instruction {w:08x}")
    raise ValueError("escaped H_msg")
