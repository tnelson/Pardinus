#!/usr/bin/env bash

set -euo pipefail

WORK="${WORK:-/work}"
OUT="${OUT:-/output}"
BUILD="${BUILD:-/tmp/build}"
LOGS="${LOGS:-/tmp/logs}"
SCRIPT_DIR="$WORK"
LOCK="$WORK/sources.lock"
JDK_HEADERS_URL="https://raw.githubusercontent.com/openjdk/jdk17u/jdk-17.0.13-ga/src/java.base"

. "$WORK/lib-common.sh"

triple_for() {
  case "$1" in
    x86_64) echo x86_64-w64-mingw32 ;;
    arm64) echo aarch64-w64-mingw32 ;;
    *) die "unknown TARGET '$1' (use x86_64 or arm64)" ;;
  esac
}

lib_name_for() {
  case "$1" in
    minisat) echo minisat ;;
    minisatp) echo minisatprover ;;
    glucose) echo glucose ;;
    lingeling) echo lingeling ;;
    *) die "unknown solver '$1'" ;;
  esac
}

check_tools() {
  local t missing=""
  for t in "$TRIPLE-clang" "$TRIPLE-clang++" git patch tar unzip curl python3; do
    command -v "$t" >/dev/null 2>&1 || missing="$missing $t"
  done
  [ -z "$missing" ] || die "missing tools in this image:$missing (run build-windows.sh, which builds docker/Dockerfile.windows)"
}

fetch_jni_headers() {
  local dir="$BUILD/jni-include" want have
  mkdir -p "$dir"
  curl -fsSL --retry 3 -o "$dir/jni.h" "$JDK_HEADERS_URL/share/native/include/jni.h"
  curl -fsSL --retry 3 -o "$dir/jni_md.h" "$JDK_HEADERS_URL/windows/native/include/jni_md.h"
  want="$(lock_value jdk-jni-h sha256)"
  have="$(sha256_of_file "$dir/jni.h")"
  [ "$have" = "$want" ] || die "jni.h has sha256 $have but sources.lock pins $want"
  want="$(lock_value jdk-jni-md-windows sha256)"
  have="$(sha256_of_file "$dir/jni_md.h")"
  [ "$have" = "$want" ] || die "jni_md.h has sha256 $have but sources.lock pins $want"
  JNI_INCLUDE="$dir"
}

prepare_sources() {
  local solver="$1" dir="$2"
  rm -rf "$dir"
  cp -R "$WORK/$solver" "$dir"
  rm -rf "$dir/build" "$dir"/.lock-waf* "$dir"/.waf3-*
  case "$solver" in
    minisat)
      rm -rf "$dir/minisat"
      run_logged "$solver-clone" git clone -q https://github.com/stp/minisat.git "$dir/minisat"
      verify_sources "$solver" "$BUILD"
      ;;
    minisatp)
      rm -rf "$dir/minisatp"
      run_logged "$solver-clone" git clone -q https://github.com/emina/minisatp.git "$dir/minisatp"
      verify_sources "$solver" "$BUILD"
      ;;
    glucose)
      rm -rf "$dir/glucose-syrup" "$dir/glucose-syrup.tgz"
      run_logged "$solver-fetch" wget http://www.labri.fr/perso/lsimon/downloads/softwares/glucose-syrup.tgz --directory-prefix "$dir"
      verify_sources "$solver" "$BUILD"
      tar -xzf "$dir/glucose-syrup.tgz" -C "$dir"
      patch -s -p0 -d "$dir/glucose-syrup/core" -i "$dir/Solver.patch"
      ;;
    lingeling)
      rm -rf "$dir/code"
      run_logged "$solver-fetch" wget http://fmv.jku.at/lingeling/lingeling-ayv-86bf266-140429.zip --directory-prefix "$dir"
      verify_sources "$solver" "$BUILD"
      unzip -q "$dir/lingeling-ayv-86bf266-140429.zip" 'code/*' -d "$dir"
      ;;
  esac
}

compile_solver() {
  local solver="$1" dir="$2" lib="$3"
  local common=(-shared -static -O3 -w -I"$WORK/windows/compat" -I"$JNI_INCLUDE" -Wl,--no-insert-timestamp)
  local cxx=(-std=gnu++11 -D__STDC_LIMIT_MACROS -D__STDC_FORMAT_MACROS)
  cd "$dir"
  case "$solver" in
    minisat)
      run_logged "$solver-build" "$TRIPLE-clang++" "${common[@]}" "${cxx[@]}" -I. -I./minisat -o "$lib.dll" \
        kodkod_engine_satlab_MiniSat.cpp org_alloytools_solvers_natv_minisat_MiniSat.cpp \
        minisat/minisat/utils/Options.cc minisat/minisat/utils/System.cc minisat/minisat/core/Solver.cc
      ;;
    minisatp)
      run_logged "$solver-build" "$TRIPLE-clang++" "${common[@]}" "${cxx[@]}" -DMINGW -ffloat-store -I. -I./minisatp -o "$lib.dll" \
        kodkod_engine_satlab_MiniSatProver.cpp minisatp/Solver.C minisatp/Proof.C minisatp/File.C
      ;;
    glucose)
      run_logged "$solver-build" "$TRIPLE-clang++" "${common[@]}" "${cxx[@]}" -include sys/time.h -I. -I./glucose-syrup -o "$lib.dll" \
        kodkod_engine_satlab_Glucose.cpp \
        glucose-syrup/utils/Options.cc glucose-syrup/utils/System.cc glucose-syrup/core/Solver.cc
      ;;
    lingeling)
      run_logged "$solver-build" "$TRIPLE-clang" "${common[@]}" -include lingeling-compat.h \
        -DNDBLSCR -DNLGLOG -DNDEBUG -DNCHKSOL -DNLGLPICOSAT -DNLGLDRUPLIG -DNLGLYALSAT -I. -o "$lib.dll" \
        kodkod_engine_satlab_Lingeling.c code/lglib.c
      ;;
  esac
  [ -f "$lib.dll" ] || die "$solver: the compiler produced no $lib.dll"
}

build_solver() {
  local solver="$1" lib dir
  lib="$(lib_name_for "$solver")"
  dir="$BUILD/$solver"
  echo ""
  echo "=== $solver ($TARGET) ==="
  prepare_sources "$solver" "$dir"
  compile_solver "$solver" "$dir" "$lib"
  cp "$dir/$lib.dll" "$OUT/"
  python3 -I "$WORK/check-pe-lib.py" --arch "$TARGET" "$OUT/$lib.dll" \
    || die "$solver: portability check failed"
  cd "$BUILD"
}

write_manifest() {
  local m="$OUT/MANIFEST.txt" f
  {
    echo "native solver libraries for windows-$TARGET"
    echo "built (UTC):      $(date -u +%Y-%m-%dT%H:%M:%SZ)"
    echo "pardinus commit:  ${PARDINUS_COMMIT:-unknown} (tracked files: ${PARDINUS_TREE:-unknown})"
    echo "base image:       ${BASE_IMAGE:-unknown}"
    echo "builder image:    ${BUILDER_IMAGE:-unknown}"
    echo "build OS:         $(. /etc/os-release 2>/dev/null && echo "$PRETTY_NAME"), $(uname -m)"
    echo "target:           $TRIPLE (static, Universal C Runtime)"
    echo "compiler:         $("$TRIPLE-clang++" --version | head -n1)"
    echo "verifier sha256:  $(sha256_of_file "$WORK/check-pe-lib.py")"
    echo ""
    echo "pinned sources (sources.lock):"
    grep -v -e '^#' -e '^$' "$LOCK" | sed 's/^/  /'
    echo ""
    echo "libraries (sha256, bytes, name):"
    for f in "$OUT"/*.dll; do
      echo "  $(sha256_of_file "$f")  $(wc -c < "$f" | tr -d ' ')  $(basename "$f")"
    done
  } > "$m"
}

main() {
  : "${TARGET:?TARGET is required}" "${SOLVERS:?SOLVERS is required}"
  TRIPLE="$(triple_for "$TARGET")"
  check_tools

  mkdir -p "$BUILD" "$OUT"
  rm -f "$OUT"/*.dll "$OUT/MANIFEST.txt"
  fetch_jni_headers
  install_wget_shim "$BUILD/shim"
  export PATH="$BUILD/shim:$PATH"
  export PARDINUS_JNI_DIR="$WORK"

  local solver
  for solver in $SOLVERS; do
    build_solver "$solver"
  done

  write_manifest
  [ -n "${HOST_UID:-}" ] && chown -R "$HOST_UID:${HOST_GID:-$HOST_UID}" "$OUT" || true

  echo ""
  echo "=== all builds complete: windows-$TARGET ==="
  ls -l "$OUT"
}

if [ "${BASH_SOURCE[0]}" = "$0" ]; then
  main "$@"
fi
