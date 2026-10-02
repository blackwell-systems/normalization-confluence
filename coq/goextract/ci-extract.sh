#!/usr/bin/env bash
# Extract the Go oracle's JSON (and, with --ocaml, build the OCaml checkers the
# differential tests compare against) inside the given prover image. Usage, from
# the repository root:
#   bash coq/goextract/ci-extract.sh <image> [--ocaml]
# Like extraction/ci-build.sh, it runs at the fixed path /work/coq. Outputs land
# in coq/goextract/*.json (and coq/extraction/checker, astchecker).
set -euo pipefail
image="$1"
ocaml="${2:-}"
root="$(cd "$(dirname "$0")/../.." && pwd)"
# The images run as a non-root user; let it write into the bind mount.
chmod -R a+rwX "$root/coq"
docker run --rm --platform linux/amd64 -e OCAML="$ocaml" -v "$root:/work" -w /work/coq "$image" bash -euo pipefail -c '
  eval "$(opam env 2>/dev/null)" || true
  if ! command -v coqc >/dev/null 2>&1; then
    mkdir -p "$HOME/.local/bin"
    printf "#!/bin/sh\nexec %s compile \"\$@\"\n" "$(command -v rocq)" > "$HOME/.local/bin/coqc"
    chmod +x "$HOME/.local/bin/coqc"
    export PATH="$HOME/.local/bin:$PATH"
  fi
  coqc --version
  make Trace.vo TableCheck.vo TableFast.vo Checker.vo AstChecker.vo
  rm -f goextract/*.json
  make -C goextract json
  if [ "$OCAML" = --ocaml ]; then
    make -C extraction clean >/dev/null
    make -C extraction checker astchecker
  fi
'
