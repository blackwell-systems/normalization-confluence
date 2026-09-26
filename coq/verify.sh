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
Require Import NC.Newman NC.Governance NC.Defensibility NC.Gsm NC.Federation NC.Chaotic NC.Checker NC.AstChecker NC.CRDT NC.Categorical.
Print Assumptions governance_confluent.
Print Assumptions governance_unique_normal_forms.
Print Assumptions example_confluent.
Print Assumptions disjoint_events_commute.
Print Assumptions repair_terminates.
Print Assumptions kleene_lfp.
Print Assumptions lfp_unique.
Print Assumptions chaotic_reaches_lfp.
Print Assumptions chaotic_limit_unique.
Print Assumptions checked_converges.
Print Assumptions check_sound_commute.
Print Assumptions check_sound_converges.
Print Assumptions compensationFree_step_no_repair.
Print Assumptions cmrdt_SEC.
Print Assumptions cmrdt_governed_SEC.
Print Assumptions cvrdt_SEC.
Print Assumptions witness_converges.
Print Assumptions witness_not_cmrdt.
Print Assumptions witness_leaves_valid_space.
Print Assumptions image_iff_fixed.
Print Assumptions retract_into_fixed.
Print Assumptions clamp3_retracts_into.
Print Assumptions consistent_iff_equalizer.
EOF
OUT=$(coqc -Q . NC _audit.v 2>/dev/null || true)
rm -f _audit.v _audit.vo .*.aux _audit.glob
echo "$OUT"

if echo "$OUT" | grep -qiE 'Axioms:|^Axiom|admit'; then
  echo "FAIL: an axiom or admitted lemma was detected"
  exit 1
fi
N=$(echo "$OUT" | grep -c 'Closed under the global context' || true)
if [ "$N" -lt 23 ]; then
  echo "FAIL: expected 23 axiom-free results, got $N"
  exit 1
fi
echo "PASS: all $N theorems are Closed under the global context (no axioms, no admits)"
