#!/bin/bash
export ZUO_JOBS="$(getconf _NPROCESSORS_ONLN)"
if test -n "$USE_MSVC" ; then
    ./build.bat $TARGET_MACHINE "/test-some"
else
    make test-some
fi
