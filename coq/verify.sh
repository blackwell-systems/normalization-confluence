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
Require Import NC.Newman NC.Governance NC.Defensibility NC.Gsm NC.Federation NC.Chaotic NC.Checker NC.Trace NC.TableCheck NC.TableFast NC.TableFn NC.AstChecker NC.CRDT NC.Categorical NC.Cohomology NC.CohomologyMin NC.CohomologyGraph NC.FederationOrder.
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
Print Assumptions check_no_overflow.
Print Assumptions check_binary_writes_exact.
Print Assumptions run_tequiv.
Print Assumptions perm_tequiv_total.
Print Assumptions tget_of_list.
Print Assumptions check_tables_nf_valid.
Print Assumptions check_tables_step_valid.
Print Assumptions check_tables_commute.
Print Assumptions check_tables_converges.
Print Assumptions check_tables_converges_all.
Print Assumptions check_tables_pairs_in_range.
Print Assumptions vlook_of_listV.
Print Assumptions bget_chunk.
Print Assumptions check_fast_eq.
Print Assumptions check_fast_converges.
Print Assumptions check_fn_converges.
Print Assumptions check_tables_fn.
Print Assumptions check_fast_fn.
Print Assumptions stepG_valid_eq.
Print Assumptions checkBuild_normalize_valid.
Print Assumptions checkBuild_wfc_terminates.
Print Assumptions checkBuild_wfc_potential.
Print Assumptions checkBuild_step_valid.
Print Assumptions checkBuild_commute.
Print Assumptions checkBuild_converges.
Print Assumptions checkBuild_converges_all.
Print Assumptions checkBuild_no_overflow.
Print Assumptions checkBuild_binary_writes_exact.
Print Assumptions checkBuild_pairs_in_range.
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
Print Assumptions rhoF_retraction.
Print Assumptions rhoF_image_iff_L2.
Print Assumptions updates_commute.
Print Assumptions rhoFold_retraction.
Print Assumptions rhoFold_image_iff_consistent.
Print Assumptions rhoFold_compositional.
Print Assumptions gluing_order_dependent.
Print Assumptions fixed_point_iff_trivial_holonomy.
Print Assumptions flip_no_section.
Print Assumptions identity_holonomy_has_section.
Print Assumptions simultaneous_section_iff.
Print Assumptions S3Sep.a_inv.
Print Assumptions S3Sep.del_e1_nontrivial.
Print Assumptions S3Sep.a_even.
Print Assumptions S3Sep.b_odd.
Print Assumptions sectionb_iff.
Print Assumptions sign_hom.
Print Assumptions section_G_implies_ab.
Print Assumptions min_G_lower.
Print Assumptions min_G_attained.
Print Assumptions min_ab_lower.
Print Assumptions min_ab_attained.
Print Assumptions theta_separation.
Print Assumptions section_iff_coboundary.
Print Assumptions sat_iff_trivial_holonomy.
Print Assumptions tree_has_section.
Print Assumptions tree_unique.
Print Assumptions cycle_basis_criterion.
Print Assumptions keep_balanced_suffices.
Print Assumptions unbalanced_blocks.
Print Assumptions tri_identity_has_section.
Print Assumptions tri_flip_no_section.
Print Assumptions gauge_fix.
Print Assumptions gauge_fixed_holonomy.
Print Assumptions tree_gauge.
Print Assumptions tree_const.
Print Assumptions H1_classification.
Print Assumptions tree_vertex_count.
Print Assumptions betti_number.
Print Assumptions tri_flip_not_cohomologous_to_identity.
Print Assumptions step_comm.
Print Assumptions bubble.
Print Assumptions order_independent.
Print Assumptions ex_orders_agree.
EOF
OUT=$(coqc -Q . NC _audit.v 2>/dev/null || true)
rm -f _audit.v _audit.vo .*.aux _audit.glob
echo "$OUT"

if echo "$OUT" | grep -qiE 'Axioms:|^Axiom|admit'; then
  echo "FAIL: an axiom or admitted lemma was detected"
  exit 1
fi
N=$(echo "$OUT" | grep -c 'Closed under the global context' || true)
if [ "$N" -lt 96 ]; then
  echo "FAIL: expected 96 axiom-free results, got $N"
  exit 1
fi
echo "PASS: all $N theorems are Closed under the global context (no axioms, no admits)"
