# Stream processors

Detailed results for the stream modules: the base paper's Stream Convergence theorem and the exact
condition for stream agreement. Each module's one-line summary is in the [module
index](../README.md#modules-by-regime); the status of each question in this regime is in
[REGIME-AUDIT.md](../../REGIME-AUDIT.md#5-stream-processors), section 5.

## Stream processors and Stream Convergence (`Stream.v`)

The base paper's headline theorem (Thm. "Stream Convergence", `thm:convergence`) is about stream
processors that receive events over time, not about one rewrite system. `Stream.v` formalizes
Def. "Stream Processor" (`def:processor`) on top of the causal GRS with the well-founded WFC of
`GovernanceWF.v`, so every result is domain-independent, and proves the stream-level results
axiom-free. `rho*` is taken as in `Governance.v` (specified by `rho_star_reach`).

- Model: `prstep` is the processor discipline inside the GRS (compensate while invalid; apply an
  enabled event only from a valid state); every `prstep` is a GRS step and a `prstep` normal form is
  a GRS normal form (`prstep_cstep`, `nf_prstep_cstep`). A `processor` has received sets
  `recv : nat -> list Event` and configurations `conf : nat -> State * list Event`, with
  `psi p t = fst (conf p t)`. `is_processor` asks for duplicate-free received sets drawn from the
  stream, growth by appending, eventual delivery, and the paper's "the computation on `E_P(t)` is a
  reduction sequence from `(sigma0, E_P(t))`". `settled p t` says the processor has finished
  processing `E_P(t)`; `fair p` says it keeps reducing while nothing new arrives.
  `incremental_computes`: a processor that carries its configuration across arrivals is a
  processor.
- (a) `stream_validity`, `comp_phase_terminates`, `comp_phase_done_valid`,
  `settled_empty_buffer` (with a progress hypothesis the finished configuration has an empty
  buffer). (b) `stream_order_independence` (finished reductions from the same received set end in
  the same state) and `stream_orders_agree` (any two feasible application orders, each followed by
  `rho*`, agree). (c) `stream_agreement` (also across different times) and
  `base_thm_convergence_c`. Bundled: `stream_convergence` (any well-founded potential) and
  `base_thm_convergence` (the paper's `Phi : Sigma -> nat`).
- `base_rem_set_function` (`rem:set-function`): `F(E)` exists and depends only on the set `E`.
- `base_cor_quiescent`, `base_cor_quiescent_nat` (`cor:quiescent`): on a finite stream two fair
  processors eventually hold the same valid state forever. The proof derives "eventually settled"
  from termination and fairness.
- `base_cor_infinite`, `base_cor_infinite_quiescent` (`cor:infinite` at stream level).
- Corrections. Part (c) as written (no "settled" qualifier) is false:
  `base_thm_convergence_c_counterexample` (two fair processors with the same received set, one
  of which has not yet applied it). The closing sentence of the theorem ("disagreements are
  transient ... restoring agreement") and `rem:infinite-streams` are false for infinite streams:
  `base_thm_convergence_transient_counterexample` (one processor a tick behind the other on an
  infinite stream; both settled at every time, they disagree at every time).
- Non-vacuity: the `Z` withdrawal registry with two processors that receive withdrawals 1 and 2 in
  different orders and at different times (`zw_stream_registry`, `zw_processors`,
  `zw_stream_agree`, `zw_stream_quiescent`, `zw_stream_quiescent_nat`,
  `zw_stream_convergence_nat`, `zw_incremental`); the counter registry of the counterexamples
  meets every registry hypothesis (`ct_registry`).

## The exact condition for stream agreement (`StreamExact.v`)

`Stream.v` proves stream agreement from sufficient conditions (WFC, CC1 on co-enabled pairs, CC2 at
every state). `StreamExact.v` lifts the exact condition to stream processors. `StreamAgree s0`: for
every stream, any two processors from `s0`, settled at times `t1`, `t2` with the same received set,
have the same state. The processor discipline `prstep` compensates before it applies, so the exact
condition is the joinability condition of `prstep` itself, not the rewrite-system condition.

- `PJC c0`: at every configuration `(sigma, B)` reachable from `c0` by `prstep` with `sigma` valid,
  for distinct enabled `e1, e2` in `B`, the successors `(apply e1 sigma, B - e1)` and
  `(apply e2 sigma, B - e2)` are `prstep`-joinable (no compensation critical pair: `prstep` is
  deterministic at invalid states). `pjc_exact`: `CR prstep c0 <-> PJC c0`.
- `stream_agree_set_function` (no qualifier): `StreamAgree s0` iff for every duplicate-free `E`
  all finished reductions from `(s0, E)` end in the same state. `pjc_stream_agreement`
  (sufficiency, no qualifier): `(forall E, NoDup E -> PJC (s0, E)) -> StreamAgree s0`.
- `stream_exact` (headline): with `Progress` (at a valid state a non-empty buffer has an enabled
  event: the causal closure of received sets, the hypothesis of `settled_empty_buffer`),
  `StreamAgree s0 <-> forall E, NoDup E -> PJC (s0, E)`. Uses WFC (any well-founded potential),
  decidability of `valid` and `enabled`, and `enabled_perm`, all hypotheses of `Stream.v`.
- `stream_diverge`: the converse made concrete. A `PJC` failure at a configuration reachable from
  `(s0, E)` gives two processors that both receive `E`, both settle, and disagree.
- `cc_pjc`, `stream_agreement_recovered`: under `Stream.v`'s hypotheses `PJC` holds everywhere, so
  `stream_agreement` is a corollary of the exact theorem. `jc_pjc`, `jc_stream_agreement`: the
  rewrite-system condition `JC` of `jc_exact` at every `(s0, E)` implies `PJC` and stream agreement.
- Free delivery with canonical repair (`gov e s = rho*(apply e s)`, `grun` the governed run of a
  word): `PCC s0` says the governed steps of `e1, e2` commute at `grun (rho* s0) w` for every
  duplicate-free `w ++ [e1; e2]` (CC1 at the states a processor reaches; no CC2).
  `stream_exact_free`: `StreamAgree s0 <-> PCC s0`; `stream_diverge_free` turns a `PCC` failure
  into two disagreeing processors on the set `w ++ [e1; e2]`; `stream_exact_free_pjc` is the
  general theorem on this model. Supporting: `pcc_pjc`, `fx_two_runs`, `fx_repair`,
  `fx_inv_reach`, `fx_inv_valid`, `sx_un_cr`.
- Counterexamples. `jc_not_necessary`: CC2 fails at `s0` itself, so `JC (s0, [e])` and the
  condition of `cc_exact_from` fail, yet every two processors from `s0` agree (a processor never
  applies at an invalid state): the natural iff with the rewrite-system condition is false.
  `progress_needed`: without `Progress`, `PJC` is not necessary (two events, each enabled only
  while the other is buffered; finished buffers differ, finished states agree).
  `jc_fail_disagree`: a free registry whose steps do not commute; `JC`, `PJC`, `PCC` and
  `StreamAgree` fail and two concrete processors with the same received set settle in different
  states.
- Non-vacuity: `zw_stream_exact` (the `Z` withdrawal registry meets `Progress`, `PJC` everywhere and
  `PCC` from every start; the agreement of `zp1` and `zp2` at time 2 is rederived through
  `stream_exact_free`), `zw_stream_exact_iff`, `zw_jc_stream_agreement` (the `JC` route with the
  nat potential); every counterexample registry discharges the hypotheses of the section it
  instantiates.

## At-least-once delivery for stream processors (`StreamAtLeastOnce.v`)

`StreamExact.v` requires duplicate-free received lists (`is_processor` asks `NoDup (recv p t)`).
Under at-least-once delivery a processor may receive an event more than once; every copy enters the
buffer and is applied. `StreamAtLeastOnce.v` drops the `NoDup` requirement and closes audit gap
15 (b).

- Delivery classes. `is_processor_d D` is `is_processor` with `NoDup (recv p t)` replaced by
  `D (recv p t)`; `StreamAgreeD D s0` is agreement of settled `D`-processors with the same received
  SET. `procd_nodup_iff`, `stream_agree_nodup_iff`: the class `NoDup` is `StreamExact`'s.
  `StreamAgreeA s0` (every list allowed) is at-least-once agreement: lists with the same events
  are compared whatever the multiplicities. `stream_agree_d_set_function`: agreement iff, for
  every two `D`-lists with the same events, the finished reductions from `s0` end in the same state.
- Any enabledness, under `Progress`: `stream_alo_exact`,
  `StreamAgreeA s0 <-> (forall E, PJC (s0, E)) /\ DupAbsorb s0`, with `PJC` at every received list
  (duplicates allowed) and `DupAbsorb s0`: for `a` in `E`, some finished reduction from
  `(s0, a :: E)` ends where some finished reduction from `(s0, E)` ends. This reduces agreement to
  one redelivered copy at a time (`sa_reduce`); it is not a local condition. The two conjuncts are
  independent (`ct_general`, `ow_general`). `stream_exact_recovered`: the duplicate-free class
  gives `stream_exact` back through the same set-function form (duplicate-free lists with the same
  events are permutations).
- Free delivery (canonical repair `rho*`, valid and reached by compensation): every finished
  reduction from `(s0, E)` is the governed run of a reordering of `E` from `rho* s0` (`sf_final`),
  so `StreamAgreeA s0` is `ALOConv` of the governed step from `rho* s0` (`stream_alo_aloconv`).
  `stream_alo_exact_free`: `StreamAgreeA s0 <-> PCC s0 /\ forall a, PIdem s0 a`, where
  `PIdem s0 a` is idempotence of `a` at every state `grun (rho* s0) u` with `u ++ [a]`
  duplicate-free (where a processor first applies `a`); through `AtLeastOnceExact.alo_exact`.
  `stream_alo_free_split`: `StreamAgreeA s0 <-> StreamAgree s0 /\ forall a, PIdem s0 a`, so the
  at-least-once condition is `stream_exact_free`'s plus reachable idempotence.
- Counterexamples. `ct_alo_fails` (the counter): `PCC`, exactly-once agreement and `PJC` at every
  list hold; `PIdem`, `DupAbsorb` and `StreamAgreeA` fail, and processors receiving `[0]` and
  `[0; 0]` settle at 1 and 2. So `stream_exact`'s condition does not give at-least-once agreement,
  and the idempotence clause is needed. `ow_alo_fails` (the overwrite register): every event is
  idempotent at every state and `DupAbsorb` holds, yet `PCC`, `PJC` and `StreamAgreeA` fail.
- Non-vacuity: `mx_alo_holds` (the max-register: `PCC` and `PIdem` from every start; processors
  receiving `[1; 2; 1]` and `[2; 1]` settle at the same state).
