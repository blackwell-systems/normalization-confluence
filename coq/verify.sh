#!/usr/bin/env bash
# Build the mechanized proof and gate on it being axiom-free. Exits non-zero if any
# proof fails to compile OR if any key theorem depends on an axiom / admitted lemma.
# Run locally (needs coqc on PATH) or in CI; also the human one-command check.
set -euo pipefail
cd "$(dirname "$0")"

echo "== compiling =="
make clean >/dev/null 2>&1 || true
make

echo "== axiom-free gate (Print Assumptions) =="
cat > _audit.v <<'EOF'
Require Import NC.Newman NC.Governance NC.Defensibility NC.Gsm NC.Federation.
Print Assumptions governance_confluent.
Print Assumptions governance_unique_normal_forms.
Print Assumptions example_confluent.
Print Assumptions disjoint_events_commute.
Print Assumptions repair_terminates.
Print Assumptions kleene_lfp.
Print Assumptions lfp_unique.
EOF
OUT=$(coqc -Q . NC _audit.v 2>/dev/null || true)
rm -f _audit.v _audit.vo .*.aux _audit.glob
echo "$OUT"

if echo "$OUT" | grep -qiE 'Axioms:|^Axiom|admit'; then
  echo "FAIL: an axiom or admitted lemma was detected"
  exit 1
fi
N=$(echo "$OUT" | grep -c 'Closed under the global context' || true)
if [ "$N" -lt 7 ]; then
  echo "FAIL: expected 7 axiom-free results, got $N"
  exit 1
fi
echo "PASS: all $N theorems are Closed under the global context (no axioms, no admits)"
