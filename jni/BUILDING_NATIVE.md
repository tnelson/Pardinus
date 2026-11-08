# Building native solvers 

This was written from the perspective of _Forge_; other applications may need to apply minor changes.

Note that the MacOS instructions will work only from a Mac.**

## Setup  

* In order to run these commands, you'll need Docker running. 
* For portability reasons, check that the `jni/*/wscript` files contain the static-link flags
  (run from the root of the Pardinus repository):

```bash
# Each solver wscript should show a LINKFLAGS line (4 lines)
grep -h "LINKFLAGS = " jni/{glucose,lingeling,minisat,minisatp}/wscript
```

## Linux

Builds `libminisat`, `libminisatprover`, `libglucose` and `liblingeling` via Docker.


### Build and test

```bash
cd jni
./build-linux.sh --arch aarch64
```

This will build and output the solvers into `output/linux-aarch64/`. 

Next, compile the Java classes that will test the new solvers, and then run those tests:

```bash
mvn -q -f ../pom.xml compile
./test-linux.sh --arch aarch64 --classpath ../target/classes
```

If the test reports a missing class, add dependency jars with more `--classpath` options.

### Choosing a Linux architecture

Controlled by the `--arch` flag. This is still Linux only. 

| `--arch`  | For | 
|---|---|---|
| `aarch64` | 64-bit ARM Linux: ARM servers, or Linux in Docker or a VM on an Apple Silicon Mac | 
| `x86_64`  | 64-bit Intel/AMD Linux: most PCs and servers |

`--arch all` builds both. 

### Output and Installing

To use the libraries in another project, without manually copying them: add `--install-to DIR` to the build command.

### Other options

```bash
# Preview the docker commands to be run.
./build-linux.sh --arch aarch64 --dry-run
```

```bash
# Open a shell in the container for debugging.
./build-linux.sh --arch aarch64 --shell
```

```bash
# Rebuild the image to update various Linux packages.
./build-linux.sh --arch aarch64 --rebuild-image
```

Note that running deletes *all* previously-built native solvers. 

## Building for macOS

Builds `libminisat.dylib`, `libminisatprover.dylib`, `libglucose.dylib` and `liblingeling.dylib`
as universal binaries for both arm64 and x85_64. 

Make sure you have the Xcode command line tools (`xcode-select --install`) and a full JDK installed.

```bash
cd jni
./build-macos.sh
```

The output goes to `output/macos/`. Next, compile the Java test classes and run the tests on your Mac:

```bash
mvn -q -f ../pom.xml compile
./test-macos.sh --classpath ../target/classes
```

By default, this only tests the part of the universal binary for _your Mac's CPU_. To test the alternative, run either `--arch x86_64` or `--arch arm64`.

## Building for Windows

Builds `minisat.dll`, `minisatprover.dll`, `glucose.dll` and `lingeling.dll` for 64-bit Windows,
for both Intel/AMD (`x86_64`) and ARM (`arm64`). 

```bash
cd jni
./build-windows.sh
```

Output goes to `output/windows-x86_64/` and `output/windows-arm64/`.

## Known gaps

- The 32-bit `linux-x86` libraries still link `libstdc++` dynamically.
- 32-bit Windows (`windows-x86`) is not built by these scripts. 
