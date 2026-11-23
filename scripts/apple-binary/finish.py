"""Lift the linked Sponge::finish on valid cursors and single-rate-block outputs."""

from image import require, sign_extend


def verify(image):
    pc, words = image.function(b"6Sponge6finish", b"6slhdsa8shake256")
    single, _ = image.function(b"parallel6single")
    # 48-byte aligned frame, saving x22:x21, x20:x19 and fp:lr.
    prologue = [0xA9BD57F6, 0xA9014FF4, 0xA9027BFD, 0x910083FD]
    epilogue = [0xA9427BFD, 0xA9414FF4, 0xA8C357F6, 0xD65F03C0]
    require(words[:4] == prologue, "finish frame setup")
    after_call = set()
    # Lanes are arbitrary independent words. Track their exact XOR masks. Keeping
    # the 25 masks in one array also handles both padding bits in the same lane.
    for cursor in range(136):
        g = {0: "sponge", 1: "out", 2: "length"}
        masks = [0] * 25
        i = 4
        cmp = None
        for _ in words:
            require(0 <= i < len(words), "finish prefix out of bounds")
            w = words[i]
            i += 1
            if w == 0xAA0003F5:
                g[21] = g[0]
            elif w == 0xF9406408:
                require(g[0] == "sponge", "wrong cursor base")
                g[8] = cursor
            elif w == 0xD343FD00:
                g[0] = g[8] >> 3
            elif w == 0xF1031D1F:
                cmp = (g[8], 199)
            elif w & 0xFF00001F == 0x54000008:
                require(cmp is not None, "undefined prefix flags")
                if cmp[0] > cmp[1]:
                    i = i - 1 + sign_extend(w >> 5 & 0x7FFFF, 19)
            elif w == 0xAA0203F3:
                g[19] = g[2]
            elif w == 0xAA0103F4:
                g[20] = g[1]
            elif w == 0xD37D0908:
                g[8] = (g[8] & 7) << 3
            elif w & 0xFFE0001F == 0x52800009:
                g[9] = w >> 5 & 0xFFFF
            elif w == 0x9AC82128:
                g[8] = (g[9] << (g[8] % 64)) % 2**64
            elif w == 0xF8607AA9:
                require(g[21] == "sponge" and 0 <= g[0] < 25, "incorrect lane read")
                g[9] = g[0], masks[g[0]]
            elif w == 0xCA080128:
                g[8] = (g[9][0], g[9][1] ^ g[8])
            elif w == 0xF8207AA8:
                require(g[21] == "sponge" and g[8][0] == g[0], "wrong lane store")
                masks[g[0]] = g[8][1]
            elif w == 0xF94042A8:
                require(g[21] == "sponge", "wrong final pad base")
                g[8] = 16, masks[16]
            elif w == 0xD2410108:
                g[8] = g[8][0], g[8][1] ^ (1 << 63)
            elif w == 0xF90042A8:
                require(g[21] == "sponge" and g[8][0] == 16, "wrong final pad store")
                masks[16] = g[8][1]
            elif w == 0xAA1503E0:
                g[0] = g[21]
            elif w & 0xFC000000 == 0x94000000:
                require(
                    pc + 4 * (i - 1 + sign_extend(w & 0x3FFFFFF, 26)) == single
                    and g[0] == g[21] == "sponge"
                    and g[19] == "length"
                    and g[20] == "out",
                    "wrong finish permutation call or retained registers",
                )
                expected = [0] * 25
                expected[cursor // 8] ^= 31 << (8 * (cursor % 8))
                expected[16] ^= 1 << 63
                require(masks == expected, "wrong SHAKE domain or final pad")
                after_call.add(i)
                break
            else:
                raise ValueError(f"unsupported finish prefix {w:08x}")
        else:
            raise ValueError("finish did not permute")
    require(len(after_call) == 1, "unexpected post-permutation continuation")
    # This phase begins with completely unconstrained post-permutation lane values
    # and no usable caller-saved registers or flags from before the call.
    for length in range(137):
        (i,) = after_call
        g = {19: length, 20: ("out", 0), 21: "sponge"}
        output = []
        cmp = None
        for _ in range(16 * (length + 1)):
            require(0 <= i < len(words), "finish output out of bounds")
            w = words[i]
            i += 1
            if w & 0xFF00001F == 0xB4000013:
                if g[19] == 0:
                    i = i - 1 + sign_extend(w >> 5 & 0x7FFFF, 19)
            elif w == 0xD2800008:
                g[8] = 0
            elif w & 0xFC000000 == 0x14000000:
                i = i - 1 + sign_extend(w & 0x3FFFFFF, 26)
            elif w in (0xF102211F, 0xF103211F):
                cmp = (g[8], w >> 10 & 4095)
            elif w & 0xFF00001F in (0x54000000, 0x54000003):
                require(cmp is not None, "undefined output flags")
                if cmp[0] == cmp[1] if w & 15 == 0 else cmp[0] < cmp[1]:
                    i = i - 1 + sign_extend(w >> 5 & 0x7FFFF, 19)
            elif w == 0xD343FD00:
                g[0] = g[8] >> 3
            elif w == 0xF8607AA9:
                require(g[21] == "sponge" and 0 <= g[0] < 25, "incorrect output lane")
                g[9] = ("lane", g[0])
            elif w == 0xD37D090A:
                g[10] = (g[8] & 7) << 3
            elif w == 0x9ACA2529:
                require(g[9][0] == "lane", "incorrect byte shift")
                g[9] = ("shifted", g[9][1], g[10] % 64)
            elif w == 0x38001689:
                require(
                    g[20] == ("out", len(output))
                    and len(output) < length
                    and g[9][0] == "shifted",
                    "out-of-range or incorrect byte store",
                )
                output.append(g[9][1:])
                g[20] = ("out", len(output))
            elif w == 0x91000508:
                g[8] += 1
            elif w == 0xF1000673:
                cmp = g[19], 1
                g[19] = (g[19] - 1) % 2**64
            elif words[i - 1 : i + 3] == epilogue:
                require(
                    output == [(j // 8, 8 * (j % 8)) for j in range(length)],
                    "incorrect finish byte sequence",
                )
                break
            else:
                raise ValueError(f"unsupported finish output {w:08x}")
        else:
            raise ValueError("finish output did not return")
    return pc, len(words) * 4
