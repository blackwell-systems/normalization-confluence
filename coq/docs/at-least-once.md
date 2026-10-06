# At-least-once delivery

Detailed results for the at-least-once modules: when a duplicate is absorbed, and the exact
conditions, free and causal. Each module's one-line summary is in the [module
index](../README.md#modules-by-regime); the status of each question in this regime is in
[REGIME-AUDIT.md](../../REGIME-AUDIT.md#3-at-least-once-delivery), section 3.

## At-least-once delivery (`AtLeastOnce.v`)

The convergence results on the other pages assume each replica sees each event exactly once. Transports usually promise
at-least-once delivery, so an event can be redelivered, possibly much later. `AtLeastOnce.v` makes
exactly-once a checked property: it proves when a duplicate is absorbed and gives a divergence
witness when it is not. A delivery is a list of events with duplicates; its exactly-once projection
`dedup` keeps the first delivery of each event. The governed step (apply, then repair to a normal
form) ranges over an invariant domain `D` it preserves. Axiom-free:

- `alo_absorbed`: the general, local form. A delivery reaches the same state as its exactly-once
  projection when every redelivered event is idempotent (`step a (step a s) = step a s` on `D`) and
  commutes with each event delivered between the redelivery and the previous copy.
- `alo_commuting_exactly_once`, `alo_commuting_converges`: the all-orders case. If all delivered
  events commute and every duplicated event is idempotent, an at-least-once delivery reaches the
  same state as every exactly-once delivery of the same events in any order, and any two
  at-least-once deliveries of the same events agree. Built on `Trace.v`'s `run_tequiv`.
- `causal_alo_exactly_once`, `causal_alo_converges`: the causal case. Only concurrent events need to
  commute (as in `causal_convergence`), happens-before is irreflexive, and redelivery is itself
  causally consistent (`causal_alo`: no copy of a cause is delivered after any copy of its effect).
  Then every duplicate is absorbed and the run equals every causally consistent exactly-once run.
  `causal_alo_absorbs` and `causal_alo_dedup_causal` are the two steps; the order argument reuses
  `causal_tequiv` and `run_tequiv`.
- `non_idempotent_diverges`: for any event whose governed step is not idempotent at some state,
  delivering it twice from that state diverges from delivering it once. `inc_not_idempotent` /
  `inc_duplicate_diverges` instantiate it with a counter increment clamped to a cap: from `0`,
  duplicate delivery ends at `2`, exactly-once at `1`.
- `late_duplicate_diverges`: the naive causal statement (idempotent duplicates are absorbed whenever
  the first deliveries are causal) is false. On `CausalReplay.v`'s flag machine, `Add` and `Remove`
  are idempotent and every concurrent pair commutes, yet redelivering `Add` after its causal
  successor `Remove` leaves the flag set, while exactly-once delivery clears it. That delivery is not
  `causal_alo`, which is why the causal theorem requires it.
- `mx_alo_converges` (a max-register clamped to a cap, all-orders case) and
  `fl_causal_alo_converges` (a flag with add and causally later remove next to a clamped
  max-register; `fl_not_all_commute` shows the all-orders theorem does not apply): non-vacuity
  instances discharging every hypothesis.

In short, deduplication is needed only for an event whose governed step is not idempotent, or whose
redelivered copy can overtake an event it does not commute with. The first always diverges at a
witness state (`non_idempotent_diverges`); the second can (`late_duplicate_diverges`).

## At-least-once delivery, exact (`AtLeastOnceExact.v`)

`AtLeastOnce.v` gives sufficient conditions only (global idempotence and commutation on `D`, or the
local `absorbs` condition) and a divergence witness with no reachability qualifier.
`AtLeastOnceExact.v` states the necessary and sufficient conditions at a fixed start state `s0`, for
the events in a set `Ev`. A causal form is proved first (happens-before `hb`, irreflexive); the free
form is its instance with `hb` empty. Axiom-free:

- `causal_alo_exact`, `causal_alo_exact_idem`: every causally consistent at-least-once delivery
  (`causal_alo`) over `Ev` reaches the state of every causally consistent exactly-once order of the
  same events from `s0` (`CALOConv s0`) iff `CCRon s0` (GovernanceConverse's `CCR` restricted to
  `Ev`; `ccr_on_true_iff` is the link) and, for every event `a`, either of the equivalent
  conditions: `AbsorbAt s0 a` (a redelivery of `a` is a no-op after every causal exactly-once run
  from `s0` containing `a` and no causal successor of `a`), or `IdemAt s0 a` (`step a` is idempotent
  at every state `run u s0` with `u ++ [a]` causally consistent). Under `CCR`, absorption past the
  events delivered in between is automatic (`idem_absorb`); `absorb_idem` is the other direction.
- `alo_exact`, `alo_exact_absorb`: the free form. Every at-least-once delivery over `Ev` reaches the
  state of every exactly-once delivery of the same events (`ALOConv s0`) iff exactly-once runs
  commute at reachable states (`CommReach s0`) and every event is idempotent at every reachable
  state where it is first delivered (`IdemReach`), equivalently absorbed after every reachable
  exactly-once run containing it (`AbsorbReach`). `alo_idem_reachable`: `ALOConv s0` forces
  idempotence at every state reachable by any at-least-once delivery, the run-level converse of
  `non_idempotent_diverges`.
- Per event: `safe_at_exact`, `safe_free_exact` (`a` needs no deduplication, i.e. no delivery whose
  only duplicates are copies of `a` diverges from its exactly-once projection, iff `AbsorbAt` /
  `AbsorbReach`), `needs_dedup_exact`, `needs_dedup_witness`, `alo_safe`, and under `CCR` /
  `CommReach` the idempotence forms `safe_at_iff_idem`, `safe_free_iff_idem`.
- gsm's `Report.NotIdempotent` (`NotIdempotent valid a`: some valid state where a second application
  changes the state): `notidem_needs_dedup`, `causal_notidem_needs_dedup` (a witness at a reachable
  state means `a` needs deduplication); `gsm_unlisted_safe`, `causal_gsm_unlisted_safe` (when
  exactly-once delivery converges from `s0` and every reachable state is valid, an unlisted event
  needs no deduplication). Exactly: under `CommReach`, needing deduplication is non-idempotence at a
  reachable state where the event is first delivered; `NotIdempotent` quantifies over valid states
  instead of reachable ones. These placements are for free and causal delivery. For a registry that
  declares `Independent` pairs, exactly-once delivery covers only trace-equivalent orders, and no
  theorem places `NotIdempotent` there (REGIME-AUDIT.md gap 15 (a)).
- Recovered: `old_free_implies` / `alo_commuting_recovered` and `old_causal_implies` /
  `causal_alo_recovered` derive the exact conditions from the hypotheses of
  `alo_commuting_exactly_once` and `causal_alo_exactly_once`.
- Counterexamples: `inc_alo_fails` (capped increment: `CommReach` holds, `IdemReach` fails, the
  event needs deduplication); `fw_alo_fails` (first-writer-wins register: every event idempotent at
  every state and every duplicate absorbed at every reachable run, yet `ALOConv` fails, so the
  commutation clause is needed); `flag_idem_needs_dedup` (flag `Add`/`Remove`: idempotent
  everywhere, so `IdemReach` holds and gsm lists neither, yet `Add` needs deduplication under free
  delivery: idempotence alone is not enough without absorption past the intervening `Remove`);
  `jmp_unreachable` (not idempotent at an unreachable state, so gsm lists it and
  `non_idempotent_diverges` fires there, yet every delivery from `0` converges: global idempotence is
  not necessary); `causal_absorb_qualifier` (under causal delivery, absorption at every causal run
  containing `a` is not necessary: `Add` is not absorbed after `[Add; Remove]`, but that redelivery
  is not causally consistent).
- Non-vacuity: `mx_alo_exact` (max-register, all orders), `fl_causal_alo_exact` (causal flag with a
  max-register), `n_causal_alo_exact` (GovernanceConverse's `n_step`: `CCR` holds from `0` but
  `cc_concurrent` fails, so `causal_alo_exactly_once` does not apply, yet every causally consistent
  at-least-once delivery converges from `0`).
