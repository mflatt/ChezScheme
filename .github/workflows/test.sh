#!/bin/bash
export ZUO_JOBS="$(getconf _NPROCESSORS_ONLN)"
if test "$TOOLCHAIN" = vs ; then
    cmd.exe /c "build.bat $TARGET_MACHINE /test-some"
else
    make test-some
fi
