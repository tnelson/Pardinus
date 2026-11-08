#!/usr/bin/env bash

set -euo pipefail

: "${ARCH:?ARCH is required}" "${CLASSPATH_IN:?CLASSPATH_IN is required}"
GLIBC_MAX="${GLIBC_MAX:-2.31}"

[ "$(uname -m)" = "$ARCH" ] || { echo "container CPU is $(uname -m), expected $ARCH"; exit 1; }
command -v javac >/dev/null 2>&1 && command -v python3 >/dev/null 2>&1 \
  || { echo "this container lacks javac or python3; it must be the builder image"; exit 1; }
ls /libs/*.so >/dev/null 2>&1 || { echo "no .so files in the libraries directory"; exit 1; }

echo "=== platform: $(uname -m), $(java -version 2>&1 | head -n1) ==="
echo ""
echo "=== static checks (check-native-lib.py, glibc <= $GLIBC_MAX) ==="
python3 /work/check-native-lib.py --arch "$ARCH" --max-glibc "$GLIBC_MAX" /libs/*.so

echo ""
echo "=== JVM solve tests (kodkod SATFactory) ==="
mkdir -p /tmp/nst
cp /work/NativeSolverTest.java /tmp/nst/
cd /tmp/nst
javac -cp "$CLASSPATH_IN" NativeSolverTest.java
java -Djava.library.path=/libs -cp "$CLASSPATH_IN:." NativeSolverTest

echo ""
echo "=== ALL CHECKS PASSED ==="
