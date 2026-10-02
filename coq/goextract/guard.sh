#!/usr/bin/env bash
# Refuse coinductive types and cofixpoints in what gogen translates (see
# GuardCoind.v). Usage, from coq/: bash goextract/guard.sh <file.v>
# The file must print an OCaml Recursive Extraction; the guard fails if it
# contains Lazy (OCaml extraction's marker for coinductive types and
# cofixpoints) or does not compile.
set -uo pipefail
f="$1"
out="$(coqc -Q . NC "$f" 2>&1)" || { echo "guard: $f does not compile"; echo "$out" | tail -20; exit 1; }
if echo "$out" | grep -qE '\bLazy\b|\blazy\b'; then
  echo "guard: $f extracts a coinductive type or a cofixpoint, which gogen does not support:"
  echo "$out" | grep -nE '\bLazy\b|\blazy\b' | head -10
  exit 1
fi
echo "guard: no coinductive type or cofixpoint in $f"
