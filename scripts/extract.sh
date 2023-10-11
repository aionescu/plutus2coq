#!/usr/bin/env bash
set -euo pipefail

ROOT=$(git rev-parse --show-toplevel)

coqc \
  -R $ROOT/hs-to-coq/base "" \
  -R $ROOT/coq-output "" \
  $1
