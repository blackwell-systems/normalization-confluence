# Changelog

This file records notable changes to the papers and the mechanized proof in this repository.

The format follows [Keep a Changelog](https://keepachangelog.com/en/1.1.0/). The repository has no version tags, so entries are grouped by date (merge date for pull requests, commit date for earlier history, both as recorded in the git history, UTC-7). Theorem counts refer to the minimum enforced by the axiom-free gate in `coq/verify.sh`.

## [Unreleased]

### Added
- `coq/CausalReplay.v`: convergence under causal delivery, where only concurrent events need to commute (#19).
  - `causal_convergence`: if governed steps commute on concurrent pairs, any two causally consistent delivery orders reach the same state.
  - `causal_cmrdt_SEC`: op-based CRDTs (concurrent operations commute, causal delivery) converge, as an instance.
  - `compensation_free_exact`: a compensation-free system meets the causal condition if and only if it is an op-based CRDT.
  - `witness_causal_not_cmrdt`: strictness under causal delivery.
  - `witness_beyond_all_pairs`: a system that converges under causal delivery although not every operation pair commutes, so the all-pairs theorem does not cover it.
  - `causal_tequiv`: causally consistent orders are trace-equivalent under concurrency, connecting causal delivery to `run_tequiv` in `Trace.v`.
- `coq/GovernanceCausal.v`: `causal_governance_confluent`, the rewrite-system Convergence Theorem with compensation interleaving, with CC1 required only for distinct co-enabled events; witness `cw_confluent` / `cw_violates_all_pairs_cc1` satisfies the weakened hypothesis while violating the original (#19).
- `coq/README.md`: section for the causal modules (#19).

### Changed
- Axiom-free gate raised from 112 to 125 theorems, checked on Coq 8.18, Coq 8.20 and Rocq 9.3 (#19).
- `SUBSUMPTION.md`: op-based CRDTs are now proven to be exactly the compensation-free fragment under causal delivery, with a new section on causal delivery (#19).
- `README.md` updated to match (#19).

### Fixed
- `LANDSCAPE.md`: corrected the placement of I-confluence. Its replay-convergent part is exactly the op-based CRDTs; non-commuting I-confluent systems converge by merge, outside the replay model (#19).

## 2026-10-04

### Added
- `LANDSCAPE.md`: "Related work for the cohomological layer" section (graph fundamental groups, gain-graph and signed-graph balance, cohomology of global-section obstructions, topology in distributed computing, cycle consistency and group synchronization, applied sheaf theory, related formalizations) (#17).

### Changed
- `CATEGORICAL-STRUCTURE.md` 10 and 10.1: related-work pointer, open items updated to match `coq/CohomologyGraph.v`, and contribution wording that credits the graph topology and balance criterion as classical (#17).

## 2026-10-03

### Added
- `coq/AstTables.v`: `checkBuildT`, the rules oracle through step tables, which evaluates the rules once per state and event. `checkBuildT_eq` proves it equal to `checkBuild` for every machine and declaration; supporting results include `scan_cells_fn`, `boxT_eq`, `enc_box`, `box_enc`, `tables_fn_eq` and `cells_ok`. `astchecker` and the generated Go `rulecheck` run it. Gate raised from 96 to 104 theorems (#14).
- `astdiff` differential test tool comparing the rules oracles (#14).
- `coq/AstCompact.v`: `checkBuildC`, the rules oracle in compact memory, which enumerates the valuation box on the fly (`foldB`) and holds only packed tables. `checkBuildC_eq` proves it equal to `checkBuild` unconditionally. Memory guard in `tests/run.sh` for 2^20-state machines in 256 MiB. Gate raised from 104 to 112 theorems (#15).

### Fixed
- Rules front ends (OCaml `astchecker`, Go `rulecheck`) refuse a machine whose product of domains exceeds 2^24 states, instead of enumerating it; `goextract/tests/run.sh` now requires matching stderr between the OCaml and Go front ends for every input error (#16).

## 2026-10-02

### Added
- Rules oracle aligned with gsm's signed arithmetic: `evalE` returns `Z`, with new theorems `check_no_overflow` and `check_binary_writes_exact`. Extraction regression tests (`make test`); CI builds the extracted checkers on every matrix job, and `oracles.yml` publishes digest-pinned binaries with `SHA256SUMS`. Gate raised from 67 to 69 theorems (#5).
- Table and rules oracles that decide the property checked by gsm's `Build` (#6):
  - `coq/Trace.v`: `tequiv`, `run_tequiv`, `perm_tequiv_total`.
  - `coq/TableCheck.v`: `check_tables` with `check_tables_nf_valid`, `check_tables_step_valid`, `check_tables_commute`, `check_tables_converges`, `check_tables_converges_all`, `check_tables_pairs_in_range`.
  - `AstChecker.v`: `checkBuild` with `checkBuild_wfc_terminates`, `checkBuild_wfc_potential`, `checkBuild_normalize_valid`, `checkBuild_step_valid`, `checkBuild_commute`, `checkBuild_converges`, `checkBuild_converges_all`, `checkBuild_no_overflow`, `checkBuild_binary_writes_exact`, `checkBuild_pairs_in_range`, `stepG_valid_eq`.
  - Tables format 2 and an optional pairs file for `astchecker`; the rules format is unchanged.
  - Gate raised from 69 to 89 theorems.
- `coq/TableFast.v`: `check_fast`, proven equal to `check_tables` (`check_fast_eq`), with `check_fast_converges`. Gate raised from 89 to 92 theorems (#8).
- `coq/TableFn.v`: `check_fn`, the table oracle over accessor functions, with `check_fn_converges`, `check_tables_fn` and `check_fast_fn`. The `checker` front end holds entries in arrays and calls `check_fn`. Gate raised from 93 to 96 theorems (#13).
- `goextract`: generates the verified checkers as Go from Rocq's JSON extraction (`gogen`), with `cmd/tablecheck` and `cmd/rulecheck` front ends, a prim check against Rocq definitions, and CI (`goextract.yml`) requiring byte-identical output in the pinned Rocq 9.3 image and zero differential disagreements against the OCaml checkers (#10).

### Changed
- `check_fast` reads each step target's column once per state using per-state cells and a 16-ary trie, keeping its name, signature and theorems; `vlook_of_listV` and `bget_chunk` replace `wlook_of_list16` in the gate (92 to 93 theorems) (#12).

### Fixed
- `AstChecker.v` evaluated rules over `nat`, so `Sub` truncated at 0 where gsm uses signed integers, and a `Bool` write stored a different value than gsm for negative results; both front ends now reject malformed and out-of-range input (#5).
- Extracted table oracle no longer overflows the stack on 2^20-state tables (#8).
- Rules oracle no longer overflows the stack on gsm-sized machines: `fuelOf` and `setClamped` use the mapped `Init.Nat.mul` and `Init.Nat.min`, `natZ` replaces `Z.of_nat` (`natZ_eq`), and `box` uses tail loops (`box_in`). A test guard rejects extracted calls to unary `nat` arithmetic (#11).

## 2026-10-01

### Added
- CI verifies the proof on Rocq 9.3 alongside Coq 8.18 and 8.20 (#1).
- `coq/CohomologyMin.v`: the S_3 theta-graph minimum-coordination counts (`min_G_lower`, `min_G_attained`, `min_ab_lower`, `min_ab_attained`, `sign_hom`, `section_G_implies_ab`, `theta_separation`) (#2).
- `coq/CohomologyGraph.v`: the completion on an arbitrary group-labeled graph (`section_iff_coboundary`, `tree_has_section`, `tree_unique`, `cycle_basis_criterion`, `keep_balanced_suffices`, `unbalanced_blocks`). Gate raised from 38 to 55 theorems (#2).
- `LYAPUNOV-EXTENSION.md`: forward-looking research note on continuous-state analogues (nothing in it is proven) (#3).
- `coq/FederationOrder.v`: `order_independent`, order-independence for arbitrary acyclic federations without assuming connectivity of linear extensions (#4).
- `coq/CohomologyGraph.v`: H^1 as a quotient and its rank (`gauge_fix`, `gauge_fixed_holonomy`, `H1_classification`, `tree_vertex_count`, `betti_number`, `tri_flip_not_cohomologous_to_identity`). Gate raised from 55 to 67 theorems (#4).

### Changed
- The categorical paper cites the new mechanized lemmas (#2, #4).

## 2026-09-25

### Added
- `coq/Categorical.v`: the categorical core (Lemma 0, the consistent set as an equalizer, Theorem 1 for a general acyclic federation, Theorem 2 compositionality).
- `coq/Cohomology.v`: the cohomological layer, single-cycle case, and the non-abelian minimal-coordination crux.
- Draft companion paper, "The Categorical Structure of Federated Convergence: Limits, Sheaves, and Minimal Coordination" (`categorical_structure_of_federated_convergence.tex`), with `COMPANION-OUTLINE.md`.
- Minimal-coordination results in `CATEGORICAL-STRUCTURE.md`, including the characterization of minimum coordination as Group Feedback Edge Set.
- Gate raised from 19 to 38 theorems over the day.

### Changed
- `LANDSCAPE.md`: positioning against CALM, Indigo/IPA, rewriting logic and self-stabilization.
- Prior-art citations added to all three papers.

### Fixed
- Corrected an abelian-polynomial complexity claim in the minimal-coordination analysis.
- Fixed an O(n log n) total-cost typo and renamed resolver `R_j` to `Gamma_j` in the papers.

## 2026-09-24

### Added
- Coq/Rocq mechanization in `coq/`: `Newman.v` and `Governance.v` (machine-checked confluence), `Defensibility.v` (non-vacuity and discrimination checks), `Gsm.v` (soundness of gsm's WFC and CC certification), `Federation.v` (monotone-cycles federated convergence core), `Chaotic.v` (chaotic, asynchronous iteration convergence), `Checker.v` (verified convergence checker with extraction), `AstChecker.v` (AST-level verified oracle), and `CRDT.v` (CRDTs as the compensation-free fragment).
- Axiom-free CI gate (`coq/verify.sh`, `.github/workflows/verify.yml`) on Coq 8.18 and 8.20, starting at 7 theorems and raised to 19 over the day.
- `REGIMES.md`, `LANDSCAPE.md`, `SUBSUMPTION.md` and `CATEGORICAL-STRUCTURE.md`.

### Changed
- Both papers reference the mechanization.

## 2026-09-23

### Added
- Federated paper: multi-source networks via resolution operators, the Monotone Cycles theorem (convergence beyond acyclicity), the Compositionality theorem (sub-federations as effective registries), and a federated-repair regime table.
- Infinite-domain results, split across both papers.

### Changed
- First paper forward-references the federated results.

## 2026-02-17 to 2026-02-20

### Added
- Initial publication of "Normalization Confluence for Registry-Governed Stream Processing" (`normalization_confluence_2026.tex` and PDF), with a Zenodo DOI (10.5281/zenodo.18671870).
- "Normalization Confluence in Federated Registry Networks" (`normalization_confluence_in_federated_registry_networks.tex` and PDF), cited by its Zenodo concept DOI (10.5281/zenodo.18677400).
- Makefile and script to compile the papers in a Docker container.

### Changed
- README restructured as a research-area overview; paper layout and typography refinements.
