"""Read a thin arm64 Mach-O executable. Resolve code by both nlist and LC_FUNCTION_STARTS."""

import struct


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sign_extend(value, bits):
    return value - (1 << bits) if value >> (bits - 1) else value


class Image:
    def __init__(self, data):
        self.data = data
        magic, cpu, _, filetype, count, size, _, _ = struct.unpack_from("<8I", data)
        require(
            (magic, cpu, filetype) == (0xFEEDFACF, 0x100000C, 2),
            "expected a thin arm64 executable",
        )
        self.sections = {}
        self.symbols = []
        symtab = starts_table = None
        pos = 32
        for _ in range(count):
            cmd, length = struct.unpack_from("<II", data, pos)
            require(
                length >= 8 and pos + length <= 32 + size <= len(data),
                "bad load command",
            )
            if cmd == 0x19:
                require(length >= 72, "short segment command")
                seg, va, _, fileoff, filesize, _, prot, n, _ = struct.unpack_from(
                    "<16s4Q4I", data, pos + 8
                )
                require(72 + 80 * n <= length, "truncated section table")
                seg = seg.rstrip(b"\0")
                if seg == b"__TEXT":
                    require(
                        prot == 5 and fileoff == 0 and filesize <= len(data),
                        "unexpected text segment",
                    )
                    require(not hasattr(self, "base"), "duplicate text segment")
                    self.base = va
                    for i in range(n):
                        off = pos + 72 + 80 * i
                        sec, owner, addr, sz, offset = struct.unpack_from(
                            "<16s16sQQI", data, off
                        )
                        require(
                            owner.rstrip(b"\0") == seg
                            and addr - va == offset
                            and offset + sz <= filesize,
                            "unexpected section layout",
                        )
                        require(
                            sec.rstrip(b"\0") not in self.sections, "duplicate section"
                        )
                        self.sections[sec.rstrip(b"\0")] = (addr, sz, offset)
            elif cmd == 2:
                require(length >= 24 and symtab is None, "invalid symbol table command")
                symtab = struct.unpack_from("<4I", data, pos + 8)
            elif cmd == 0x26:
                require(
                    length >= 16 and starts_table is None,
                    "invalid function-start command",
                )
                starts_table = struct.unpack_from("<II", data, pos + 8)
            pos += length
        require(
            symtab and starts_table and hasattr(self, "base"), "missing Mach-O metadata"
        )
        symoff, nsyms, stroff, strsize = symtab
        start, nbytes = starts_table
        require(symoff + 16 * nsyms <= len(data), "truncated symbol table")
        require(
            pos == 32 + size
            and stroff + strsize <= len(data)
            and start + nbytes <= len(data),
            "bad linkedit",
        )
        strings = data[stroff : stroff + strsize]
        for i in range(nsyms):
            name, typ, _, _, addr = struct.unpack_from("<IBBHQ", data, symoff + 16 * i)
            if typ & 0xEE == 0x0E:
                require(
                    name < len(strings) and strings.find(b"\0", name) >= 0,
                    "bad symbol name",
                )
                self.symbols.append((strings[name : strings.index(b"\0", name)], addr))
        self.starts = []
        address = self.base
        delta = shift = 0
        encoded = data[start : start + nbytes]
        for i, byte in enumerate(encoded):
            delta |= (byte & 127) << shift
            if byte & 128:
                shift += 7
                require(shift < 64, "oversized function offset")
            elif not delta:
                require(not any(encoded[i:]), "invalid function-start terminator")
                break
            else:
                address += delta
                self.starts.append(address)
                delta = shift = 0
        else:
            raise ValueError("missing function-start terminator")

    def read(self, section, address, count):
        base, size, offset = self.sections[section]
        require(
            base <= address and address + count <= base + size,
            "address outside required section",
        )
        off = offset + address - base
        return self.data[off : off + count]

    def function(self, suffix, family=b"6slhdsa8shake2568parallel"):
        matches = [
            addr
            for name, addr in self.symbols
            if family in name and name.endswith(suffix)
        ]
        require(len(matches) == 1, f"missing or ambiguous {suffix!r}")
        (address,) = matches
        end = self.starts[self.starts.index(address) + 1]
        raw = self.read(b"__text", address, end - address)
        return address, [word for (word,) in struct.iter_unpack("<I", raw)]
