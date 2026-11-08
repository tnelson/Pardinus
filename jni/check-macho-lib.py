#!/usr/bin/env python3
import argparse
import re
import struct
import sys

CPU_NAMES = {0x01000007: "x86_64", 0x0100000C: "arm64", 7: "i386", 12: "arm"}

MH_MAGIC_64 = 0xFEEDFACF
FAT_MAGIC = 0xCAFEBABE
FAT_MAGIC_64 = 0xCAFEBABF
MH_DYLIB = 6

LC_SYMTAB = 0x2
LC_LOAD_DYLIB = 0xC
LC_ID_DYLIB = 0xD
LC_LAZY_LOAD_DYLIB = 0x20
LC_VERSION_MIN_MACOSX = 0x24
LC_CODE_SIGNATURE = 0x1D
LC_BUILD_VERSION = 0x32
LC_LOAD_WEAK_DYLIB = 0x80000018
LC_RPATH = 0x8000001C
LC_REEXPORT_DYLIB = 0x8000001F

DEPENDENCY_COMMANDS = (LC_LOAD_DYLIB, LC_LAZY_LOAD_DYLIB, LC_LOAD_WEAK_DYLIB, LC_REEXPORT_DYLIB)
PLATFORM_MACOS = 1
N_EXT = 0x01
N_TYPE_MASK = 0x0E
N_SECT = 0x0E

ALLOWED_DEPENDENCIES = {
    "/usr/lib/libSystem.B.dylib",
    "/usr/lib/libc++.1.dylib",
    "/usr/lib/libc++abi.dylib",
}

EXPECTED_MIN_JNI = {
    "libminisat.dylib": 6,
    "libglucose.dylib": 6,
    "liblingeling.dylib": 6,
    "libminisatprover.dylib": 7,
}


def parse_version(text):
    parts = [int(p) for p in text.split(".")]
    while len(parts) < 3:
        parts.append(0)
    return tuple(parts[:3])


def decode_version(v):
    return (v >> 16, (v >> 8) & 0xFF, v & 0xFF)


def format_version(t):
    return ".".join(str(x) for x in t)


def c_string(data, start, end):
    return data[start:end].split(b"\0")[0].decode("utf-8", "replace")


def split_slices(data):
    if len(data) < 8:
        raise ValueError("file too short")
    be_magic = struct.unpack_from(">I", data, 0)[0]
    if be_magic in (FAT_MAGIC, FAT_MAGIC_64):
        count = struct.unpack_from(">I", data, 4)[0]
        if count > 16:
            raise ValueError("implausible number of architectures in fat header: %d" % count)
        out = []
        for i in range(count):
            if be_magic == FAT_MAGIC:
                cpu, _sub, off, size, _align = struct.unpack_from(">IIIII", data, 8 + 20 * i)
            else:
                cpu, _sub, off, size, _align, _res = struct.unpack_from(">IIQQII", data, 8 + 32 * i)
            if off + size > len(data):
                raise ValueError("fat slice extends past the end of the file")
            out.append((CPU_NAMES.get(cpu, "cpu0x%x" % cpu), data[off:off + size]))
        return out
    le_magic = struct.unpack_from("<I", data, 0)[0]
    if le_magic == MH_MAGIC_64:
        cpu = struct.unpack_from("<I", data, 4)[0]
        return [(CPU_NAMES.get(cpu, "cpu0x%x" % cpu), data)]
    raise ValueError("not a 64-bit Mach-O or universal binary")


def analyze_slice(s):
    magic, cpu, _sub, filetype, ncmds, sizeofcmds, _flags, _res = struct.unpack_from("<IiiIIIII", s, 0)
    if magic != MH_MAGIC_64:
        raise ValueError("slice is not a 64-bit Mach-O")
    if ncmds > 4096 or 32 + sizeofcmds > len(s):
        raise ValueError("implausible load command table")
    info = {
        "filetype": filetype,
        "install_name": None,
        "dependencies": [],
        "rpaths": [],
        "minos": None,
        "platform": None,
        "has_signature": False,
        "jni_exports": 0,
    }
    symtab = None
    off = 32
    for _ in range(ncmds):
        cmd, size = struct.unpack_from("<II", s, off)
        if size < 8 or off + size > len(s):
            raise ValueError("malformed load command")
        if cmd == LC_ID_DYLIB:
            name_off = struct.unpack_from("<I", s, off + 8)[0]
            info["install_name"] = c_string(s, off + name_off, off + size)
        elif cmd in DEPENDENCY_COMMANDS:
            name_off = struct.unpack_from("<I", s, off + 8)[0]
            info["dependencies"].append(c_string(s, off + name_off, off + size))
        elif cmd == LC_RPATH:
            name_off = struct.unpack_from("<I", s, off + 8)[0]
            info["rpaths"].append(c_string(s, off + name_off, off + size))
        elif cmd == LC_BUILD_VERSION:
            platform, minos, _sdk, _ntools = struct.unpack_from("<IIII", s, off + 8)
            info["platform"] = platform
            info["minos"] = decode_version(minos)
        elif cmd == LC_VERSION_MIN_MACOSX:
            minos, _sdk = struct.unpack_from("<II", s, off + 8)
            info["platform"] = PLATFORM_MACOS
            info["minos"] = decode_version(minos)
        elif cmd == LC_CODE_SIGNATURE:
            info["has_signature"] = True
        elif cmd == LC_SYMTAB:
            symtab = struct.unpack_from("<IIII", s, off + 8)
        off += size

    if symtab is not None:
        symoff, nsyms, stroff, strsize = symtab
        if nsyms > 10_000_000 or symoff + 16 * nsyms > len(s) or stroff + strsize > len(s):
            raise ValueError("symbol table extends past the end of the slice")
        count = 0
        for i in range(nsyms):
            n_strx, n_type, _n_sect, _n_desc, _n_value = struct.unpack_from("<IBBHQ", s, symoff + 16 * i)
            if (n_type & N_EXT) and (n_type & N_TYPE_MASK) == N_SECT and n_strx < strsize:
                name = c_string(s, stroff + n_strx, stroff + strsize)
                if name.startswith("_Java_"):
                    count += 1
        info["jni_exports"] = count
    return info


def check(path, required_archs, max_min_os):
    try:
        return _check(path, required_archs, max_min_os)
    except (ValueError, OSError, struct.error, IndexError, OverflowError, MemoryError) as e:
        return ["cannot parse as a well-formed Mach-O file: %s" % e], []


def _check(path, required_archs, max_min_os):
    with open(path, "rb") as f:
        data = f.read()
    problems = []
    summaries = []
    slices = split_slices(data)
    present = [name for name, _ in slices]

    for arch in required_archs:
        if arch not in present:
            problems.append("missing the %s slice (has: %s)" % (arch, ", ".join(present) or "none"))

    base = path.replace("\\", "/").split("/")[-1]
    for arch, s in slices:
        info = analyze_slice(s)
        prefix = "[%s] " % arch
        summaries.append(
            "%s: minos=%s deps=%s jni-exports=%d signed=%s"
            % (
                arch,
                format_version(info["minos"]) if info["minos"] else "none",
                " ".join(info["dependencies"]) or "none",
                info["jni_exports"],
                "yes" if info["has_signature"] else "no",
            )
        )
        if info["filetype"] != MH_DYLIB:
            problems.append(prefix + "not a dynamic library (Mach-O file type %d, expected MH_DYLIB)" % info["filetype"])
        name = info["install_name"]
        if name is None:
            problems.append(prefix + "has no install name")
        elif not name.startswith("@"):
            problems.append(prefix + "install name %s is an absolute path from the build machine" % name)
        for dep in info["dependencies"]:
            if dep not in ALLOWED_DEPENDENCIES:
                problems.append(prefix + "depends on %s (only system libraries are allowed)" % dep)
        if info["rpaths"]:
            problems.append(prefix + "has an RPATH (%s)" % ", ".join(info["rpaths"]))
        if info["minos"] is None:
            problems.append(prefix + "records no minimum macOS version")
        elif info["platform"] != PLATFORM_MACOS:
            problems.append(prefix + "built for platform %s, not macOS" % info["platform"])
        elif info["minos"] > max_min_os:
            problems.append(
                prefix + "requires macOS %s, newer than the allowed %s"
                % (format_version(info["minos"]), format_version(max_min_os))
            )
        if arch == "arm64" and not info["has_signature"]:
            problems.append(prefix + "has no code signature (arm64 macOS refuses to load unsigned libraries)")
        if info["jni_exports"] == 0:
            problems.append(prefix + "exports no JNI symbols (_Java_*)")
        else:
            expected = EXPECTED_MIN_JNI.get(base)
            if expected is not None and info["jni_exports"] < expected:
                problems.append(
                    prefix + "exports %d JNI symbols but %s is expected to export at least %d"
                    % (info["jni_exports"], base, expected)
                )
    return problems, summaries


def main(argv):
    ap = argparse.ArgumentParser(description="Check a macOS JNI solver library.")
    ap.add_argument("--archs", default="x86_64,arm64", help="slices that must be present, comma separated")
    ap.add_argument("--max-min-os", default="12.0", help="highest minimum macOS version a slice may require")
    ap.add_argument("libs", nargs="+")
    args = ap.parse_args(argv)
    required = [a for a in args.archs.split(",") if a]
    max_min_os = parse_version(args.max_min_os)

    failed = 0
    for lib in args.libs:
        problems, summaries = check(lib, required, max_min_os)
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
