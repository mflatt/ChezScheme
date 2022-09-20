#!/bin/bash
set -e -o pipefail
export ZUO_JOBS="$(getconf _NPROCESSORS_ONLN)"
./configure -m="$TARGET_MACHINE"
make
case "$TARGET_MACHINE" in
  *a6nt)
    curl -Ls https://github.com/burgerrg/win-iconv/releases/download/v0.0.9/iconv-x64.dll > "$TARGET_MACHINE"/bin/"$TARGET_MACHINE"/iconv.dll
    ;;
  *i3nt)
    curl -Ls https://github.com/burgerrg/win-iconv/releases/download/v0.0.9/iconv-x86.dll > "$TARGET_MACHINE"/bin/"$TARGET_MACHINE"/iconv.dll
    ;;
esac
