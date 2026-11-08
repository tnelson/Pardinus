# Building native solvers for Linux

Builds `libminisat`, `libminisatprover`, `libglucose` and `liblingeling` via Docker.
Only Linux binaries are covered here. 

## Setup 

* In order to run these commands, you'll need Docker running. 
* For portability reasons, check that the `jni/*/wscript` files contain the static-link flags
  (run from the root of the Pardinus repository):

```bash
# Each solver wscript should show a LINKFLAGS line (4 lines)
grep -h "LINKFLAGS = " jni/{glucose,lingeling,minisat,minisatp}/wscript
```

## Build and test

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

## Choosing a Linux architecture

Controlled by the `--arch` flag. This is still Linux only. 

| `--arch`  | For | 
|---|---|---|
| `aarch64` | 64-bit ARM Linux: ARM servers, or Linux in Docker or a VM on an Apple Silicon Mac | 
| `x86_64`  | 64-bit Intel/AMD Linux: most PCs and servers |

`--arch all` builds both. 

## Output and Installing

To use the libraries in another project, without manually copying them: add `--install-to DIR` to the build command.

## Other options

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

## Known gaps

- The 32-bit `linux-x86` libraries still link `libstdc++` dynamically.
