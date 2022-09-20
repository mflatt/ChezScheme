#!/bin/bash
export ZUO_JOBS="$(getconf _NPROCESSORS_ONLN)"
make test-some
