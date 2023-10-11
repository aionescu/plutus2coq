#!/usr/bin/env bash
set -euo pipefail

SRC_DIR=$1
PRAGMA="{-# LANGUAGE $2 #-}"
TMP=$(mktemp plutus2coq-XXXXXXXXXX.hs)

for module in $(find $SRC_DIR -type f -name "*.hs"); do
  if [ "$(head -n 1 $module)" = "$PRAGMA" ]; then
    echo "ALREADY PATCHED: $module"
  else
    echo "Patching module: $module"
    echo "$PRAGMA" | cat - $module >$TMP && cp $TMP $module
  fi
done

rm -f $TMP
