#!/usr/bin/env bash
# Build the proofs, extract and compile the two checkers, and run their tests,
# inside the given (digest-pinned) Rocq image. Usage, from the repo root:
#   bash coq/extraction/ci-build.sh rocq/rocq-prover:9.3@sha256:...
# The build runs at the fixed path /work/coq so the outputs do not depend on where
# the repository is checked out. Outputs land in coq/extraction/.
set -euo pipefail
image="$1"
root="$(cd "$(dirname "$0")/../.." && pwd)"
# The image runs as a non-root user; let it write into the bind mount.
chmod -R a+rwX "$root/coq"
docker run --rm --platform linux/amd64 -v "$root:/work" -w /work/coq "$image" bash -euo pipefail -c '
  eval "$(opam env 2>/dev/null)" || true
  if ! command -v coqc >/dev/null 2>&1; then
    mkdir -p "$HOME/.local/bin"
    printf "#!/bin/sh\nexec %s compile \"\$@\"\n" "$(command -v rocq)" > "$HOME/.local/bin/coqc"
    chmod +x "$HOME/.local/bin/coqc"
    export PATH="$HOME/.local/bin:$PATH"
  fi
  coqc --version
  ocamlfind ocamlopt -version
  make clean >/dev/null
  make
  cd extraction
  make clean >/dev/null
  make
  make test
'
