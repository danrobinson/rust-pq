"""Symbolically execute the ABI wrapper. Track every 64-bit word and both lanes of ST2."""

from image import require, sign_extend


def verify(image, callee):
    pc, words = image.function(b"parallel6single")
    sp = ("stack", 0)
    gp = {r: ("saved", r) for r in range(19, 31)}
    gp[0] = ("state", 0)
    vector = {}
    memory = {("state", 8 * i): ("input", i) for i in range(25)}
    calls = 0

    def offset(ptr, delta):
        region, n = ptr
        require(region in ("state", "stack"), "arithmetic on a data value")
        return region, n + delta

    def address(r, displacement=0):
        return offset(sp if r == 31 else gp[r], displacement)

    def access(ptr):
        region, off = ptr
        floor, ceiling = (0, 200) if region == "state" else (sp[1], 0)
        require(off % 8 == 0 and floor <= off <= ceiling - 8, "out-of-bounds access")
        return ptr

    for i, w in enumerate(words):
        d, n = w & 31, w >> 5 & 31
        if w & 0xFFC00000 in (
            0x91000000,
            0xD1000000,
        ):  # ADD/SUB immediate, including MOV sp
            delta = (w >> 10 & 4095) * (-1 if w >> 30 & 1 else 1)
            val = address(n, delta)
            if d == 31:
                require(
                    val[0] == "stack" and -448 <= val[1] <= 0 and val[1] % 16 == 0,
                    "invalid SP",
                )
                sp = val
            else:
                require(d != 18, "write to Apple platform register")
                gp[d] = val
        elif w & 0xFFE0FFE0 == 0xAA0003E0:  # MOV Xd,Xm
            require(d not in (18, 31), "reserved MOV destination")
            gp[d] = gp[w >> 16 & 31]
        elif w & 0xFFE0FC00 == 0x4EA01C00 and n == w >> 16 & 31:
            require(d not in range(8, 16), "write to callee-saved SIMD register")
            vector[d] = vector[n]
        elif w & 0xFFC00000 == 0xAD400000:  # LDP Q
            require(d != w >> 10 & 31, "overlapping SIMD pair load")
            ptr = address(n, 16 * sign_extend(w >> 15 & 127, 7))
            for j, reg in enumerate((d, w >> 10 & 31)):
                require(reg not in range(8, 16), "write to callee-saved SIMD register")
                vector[reg] = tuple(
                    memory[access(offset(ptr, 16 * j + 8 * k))] for k in range(2)
                )
        elif w & 0xFFFFFC00 in (0x4C008C00, 0x4C9F8C00):  # ST2 {Vd.2D,V(d+1).2D}
            ptr = address(n)
            for k in range(2):
                for j in range(2):
                    memory[access(offset(ptr, 16 * k + 8 * j))] = vector[(d + j) % 32][
                        k
                    ]
            if w & 0x00800000:
                require(n != 31, "unexpected post-indexed stack store")
                gp[n] = offset(ptr, 32)
        elif w & 0xFFC00000 in (0xA9000000, 0xA9400000, 0xF9400000, 0xF9000000):
            pair = w >> 24 == 0xA9
            if pair and w & 0x00400000:
                require(d != w >> 10 & 31, "overlapping integer pair load")
            ptr = address(
                n, 8 * (sign_extend(w >> 15 & 127, 7) if pair else w >> 10 & 4095)
            )
            for j, reg in enumerate((d, w >> 10 & 31) if pair else (d,)):
                require(reg not in (18, 31), "reserved register not in wrapper subset")
                key = access(offset(ptr, 8 * j))
                if w & 0x00400000:
                    gp[reg] = memory[key]
                else:
                    memory[key] = gp[reg]
        elif w & 0xFC000000 == 0x94000000:  # BL imm26
            require(
                pc + 4 * i + 4 * sign_extend(w & 0x3FFFFFF, 26) == callee
                and calls == 0,
                "wrong callee",
            )
            ptr = gp[0]
            require(ptr == sp and sp == ("stack", -448), "wrong permutation argument")
            for j in range(25):
                for lane in range(2):
                    key = access(offset(ptr, 16 * j + 8 * lane))
                    require(
                        memory[key] == ("input", j),
                        "incomplete or incorrect permutation input",
                    )
                    memory[key] = ("permuted", j)
            # Only ABI-preserved registers can be used by the caller after return.
            gp = {r: v for r, v in gp.items() if 19 <= r <= 29}
            gp[30] = ("link", pc + 4 * i + 4)
            vector.clear()
            calls += 1
        elif w == 0xD65F03C0:
            require(i == len(words) - 1, "early return")
        else:
            raise ValueError(f"unexpected wrapper instruction {w:08x}")
    require(
        words[-1] == 0xD65F03C0 and calls == 1 and sp == ("stack", 0),
        "incomplete wrapper",
    )
    require(
        all(gp.get(r) == ("saved", r) for r in range(19, 31)),
        "ABI registers not restored",
    )
    require(
        all(memory["state", 8 * i] == ("permuted", i) for i in range(25)),
        "wrong output projection",
    )
