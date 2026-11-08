#!/usr/bin/env python3
import argparse
import re
import struct
import sys

MACHINES = {"x86_64": 0x8664, "arm64": 0xAA64}
MACHINE_NAMES = {0x8664: "x86_64", 0xAA64: "arm64", 0x14C: "x86", 0x1C4: "arm"}

IMAGE_FILE_DLL = 0x2000
PE32_PLUS_MAGIC = 0x20B

ALLOWED_IMPORTS = [
    re.compile(r"^kernel32\.dll$", re.I),
    re.compile(r"^ucrtbase\.dll$", re.I),
    re.compile(r"^api-ms-win-crt-[a-z0-9-]+-l\d+-\d+-\d+\.dll$", re.I),
]

EXPECTED_MIN_JNI = {
    "minisat.dll": 6,
    "glucose.dll": 6,
    "lingeling.dll": 6,
    "minisatprover.dll": 7,
}


def c_string(data, off):
    if off < 0 or off >= len(data):
        raise ValueError("string offset outside the file")
    end = data.find(b"\0", off)
    if end < 0:
        raise ValueError("unterminated string")
    return data[off:end].decode("latin-1")


class Image:
    def __init__(self, data):
        self.data = data
        if len(data) < 0x40 or data[:2] != b"MZ":
            raise ValueError("not a Windows executable (no MZ header)")
        pe = struct.unpack_from("<I", data, 0x3C)[0]
        if pe + 24 > len(data) or data[pe:pe + 4] != b"PE\0\0":
            raise ValueError("missing PE signature")
        (self.machine, nsec, _ts, _symptr, _nsym, optsize, self.characteristics) = struct.unpack_from(
            "<HHIIIHH", data, pe + 4
        )
        opt = pe + 24
        if opt + optsize > len(data) or nsec > 96:
            raise ValueError("implausible PE headers")
        self.magic = struct.unpack_from("<H", data, opt)[0]
        if self.magic != PE32_PLUS_MAGIC:
            raise ValueError("not a PE32+ (64-bit) image")
        dirs_off = opt + 112
        ndirs = struct.unpack_from("<I", data, opt + 108)[0]
        if ndirs > 16 or dirs_off + 8 * ndirs > opt + optsize:
            raise ValueError("implausible data directory table")
        self.dirs = [struct.unpack_from("<II", data, dirs_off + 8 * i) for i in range(ndirs)]
        self.sections = []
        sec = opt + optsize
        for i in range(nsec):
            if sec + 40 * (i + 1) > len(data):
                raise ValueError("section table extends past the end of the file")
            _name, vsize, va, rsize, rptr = struct.unpack_from("<8sIIII", data, sec + 40 * i)
            self.sections.append((va, max(vsize, rsize), rptr, rsize))

    def offset(self, rva):
        for va, size, ptr, rsize in self.sections:
            if va <= rva < va + size:
                off = rva - va + ptr
                if off >= len(self.data):
                    raise ValueError("RVA maps outside the file")
                return off
        raise ValueError("RVA 0x%x is not inside any section" % rva)

    def imports(self):
        if len(self.dirs) < 2 or self.dirs[1][0] == 0:
            return []
        out = []
        p = self.offset(self.dirs[1][0])
        for _ in range(512):
            if p + 20 > len(self.data):
                raise ValueError("import table extends past the end of the file")
            _oft, _ts, _fwd, name, _ft = struct.unpack_from("<IIIII", self.data, p)
            if name == 0:
                return out
            out.append(c_string(self.data, self.offset(name)))
            p += 20
        raise ValueError("implausibly many imported libraries")

    def delay_imports(self):
        if len(self.dirs) < 14 or self.dirs[13][0] == 0:
            return []
        out = []
        p = self.offset(self.dirs[13][0])
        for _ in range(512):
            if p + 32 > len(self.data):
                raise ValueError("delay-import table extends past the end of the file")
            _attrs, name = struct.unpack_from("<II", self.data, p)
            if name == 0:
                return out
            out.append(c_string(self.data, self.offset(name)))
            p += 32
        raise ValueError("implausibly many delay-imported libraries")

    def exports(self):
        if len(self.dirs) < 1 or self.dirs[0][0] == 0:
            return []
        p = self.offset(self.dirs[0][0])
        if p + 40 > len(self.data):
            raise ValueError("export table extends past the end of the file")
        nnames = struct.unpack_from("<I", self.data, p + 24)[0]
        names_rva = struct.unpack_from("<I", self.data, p + 32)[0]
        if nnames > 100000:
            raise ValueError("implausible number of exports")
        base = self.offset(names_rva)
        if base + 4 * nnames > len(self.data):
            raise ValueError("export name table extends past the end of the file")
        return [c_string(self.data, self.offset(struct.unpack_from("<I", self.data, base + 4 * i)[0])) for i in range(nnames)]


def check(path, arch):
    try:
        return _check(path, arch)
    except (ValueError, OSError, struct.error, IndexError, OverflowError, MemoryError) as e:
        return ["cannot parse as a well-formed Windows DLL: %s" % e], []


def _check(path, arch):
    with open(path, "rb") as f:
        data = f.read()
    img = Image(data)
    problems = []
    got = MACHINE_NAMES.get(img.machine, "machine 0x%x" % img.machine)
    if img.machine != MACHINES[arch]:
        problems.append("built for %s, expected %s" % (got, arch))
    if not img.characteristics & IMAGE_FILE_DLL:
        problems.append("not a DLL")

    imports = img.imports()
    delayed = img.delay_imports()
    for lib in imports + delayed:
        if not any(p.match(lib) for p in ALLOWED_IMPORTS):
            problems.append("depends on %s (only kernel32 and the Universal C Runtime are allowed)" % lib)

    exports = img.exports()
    jni = [e for e in exports if e.startswith("Java_")]
    base = path.replace("\\", "/").split("/")[-1].lower()
    if not jni:
        problems.append("exports no JNI symbols (Java_*)")
    else:
        expected = EXPECTED_MIN_JNI.get(base)
        if expected is not None and len(jni) < expected:
            problems.append("exports %d JNI symbols but %s is expected to export at least %d" % (len(jni), base, expected))

    summary = "%s: imports=%s jni-exports=%d" % (got, " ".join(imports + delayed) or "none", len(jni))
    return problems, [summary]


def main(argv):
    ap = argparse.ArgumentParser(description="Check a Windows JNI solver library.")
    ap.add_argument("--arch", required=True, choices=sorted(MACHINES))
    ap.add_argument("libs", nargs="+")
    args = ap.parse_args(argv)
    failed = 0
    for lib in args.libs:
        problems, summaries = check(lib, args.arch)
        print("%-4s %s" % ("FAIL" if problems else "ok", lib))
        for line in summaries:
            print("       " + line)
        for p in problems:
            print("       PROBLEM: %s" % p)
        if problems:
            failed += 1
    if failed:
        print("%d of %d libraries FAILED" % (failed, len(args.libs)))
        return 1
    print("all %d libraries passed" % len(args.libs))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
