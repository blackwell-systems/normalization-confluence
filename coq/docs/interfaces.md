# Interfaces between the layers (`LayerInterfaces.v`)

The framework has three layers, each with a merged experiment: A, the execution algebra
(`PresentedExecution.v`); B, the constraint algebra (`TransportCSP.v`, `TransportCSPHard.v`); C,
settlement dynamics as fair recurrence (`CanonicalRecurrence.v`). See
[THEORY.md](../../docs/THEORY.md#interfaces-between-the-layers). `LayerInterfaces.v` tests the
objection

> A, B and C are three unrelated classical theories stapled together

by attacking three interface hypotheses. A, B and C are used as they are; nothing in them was
changed to make an interface fit. Axiom-free, in the `coq/verify.sh` gate. No REGIME-AUDIT status
changes.

## The elementary shape, stated first

For `N : X -> X` and a predicate `P` of the states considered:

- `DescendsOn P N e`: for every `x` with `P x`, `N (e (N x)) = N (e x)`;
- `RespectsOn P N e`: `e` respects the kernel of `N` on `P` (`N x = N y` gives `N (e x) = N (e y)`);
- `FactorsOn P N e`: `N o e` factors through `N` on `P` (some `g` has `N (e x) = g (N x)`);
- `CommutesOn P N e`: strict commutation, `N (e x) = e (N x)` on `P`.

`descends_iff_respects` and `descends_iff_factors`: when `P` is closed under `N` and `N` is
idempotent on `P`, the first three are equivalent. `commutes_descends`: strict commutation implies
descent. `descends_word`: if every map of a word descends and keeps `P`, the word descends.

This is the textbook condition for an operation to be compatible with an equivalence relation (a
congruence, so the operation passes to the quotient; Burris and Sankappanavar, *A Course in
Universal Algebra*, Springer GTM 78, 1981, Chapter II, §5, "Congruences and Quotient Algebras").
Nothing in Part 1 is claimed as new. "Descends along `N`" is used in the sense the repository
already uses for state descent and history descent (`CanonicalExecution.v`): factors through the
quotient. No Grothendieck or sheaf descent is involved. The content below is not the shape; it
is, for each layer, which `N`, which `P`, and the fact that the condition is exact there.

## Hypothesis A-C: Newman as the bridge

**Result: held for termination, failed for fair settlement, with the exact replacement found.**

The bridge (any relation `R`, start `c0`; `Reach` and `PeaksJoin` from `CanonicalExecution.v`):

- `newman_bridge`: `SN R c0` and decidable normality at reachable configurations (`NFDec`) give
  `PeaksJoin R c0 <-> CR R c0` and `CR R c0 <-> UNF R c0`, where `UNF` is uniqueness of normal forms
  below every reachable configuration. Local joinability, confluence and unique normal forms
  coincide. The first equivalence is `peak_exact` (Newman 1942, localized); the second is where
  `NFDec` is used, to find a normal form below every reachable configuration constructively.
- `cr_peaks`, `cr_unf`: the converse directions (confluence gives local joinability and unique
  normal forms) need no termination.

Layer C's reduction. For a C system (labels `js`, update `u`), `LStep x y` is a moving step: some
label of `js` sends `x` to `y <> x`. `nf_iff_stable`: its normal forms are exactly the settled
states (`Stable`, fixed by every label), so "unique normal forms" and C2's singleton fixed points
talk about the same states.

Can C's fair eventual behavior (C2, every fair run eventually stays settled) replace `SN`?

- **No, in general.** `four_point_fair_not_confluent`, on the standard four-point system
  `ka <- kb <-> kc -> kd` (the textbook counterexample to Newman without termination; for example
  Klop, "Term rewriting systems from Church-Rosser to Knuth-Bendix and beyond," ICALP 1990, LNCS
  443, 350-369, Figure 3), in C's form: label 0 sends `kb` to `ka`
  and `kc` to `kd`, label 1 swaps `kb` and `kc`. Every peak joins (`k_lc`), every fair run settles
  (C2, `k_fair_settles`: a fair run names 0, and label 0 sends every state to a settled one), the
  run under label 1 alone is an infinite reduction and is not fair, `SN` fails, and both confluence
  and unique normal forms fail: `ka` and `kd` are distinct normal forms below `kb`. No canonical
  target settles for `N` the identity.
- **The exact condition.** `fair_starves`: under C2, every reachable moving loop *starves* a label:
  some label of `js` that the loop never names moves every state of the loop (a reduction enabled
  at every step and hidden forever; in fairness terms, the loop is not weakly fair, or just). The
  proof inserts, before each step of the loop, every label that is idle at the current state; this
  changes no state, and if every label were named or idle somewhere the result would be a fair
  lasso with an unsettled loop state, refuting C2 (`bad_lasso_refutes`). No finiteness is used.
- `sn_iff_no_loop` (finite state type): `SN LStep s0` iff no moving loop is reachable from `s0`
  (pigeonhole on chains of length `|X|`).
- `fair_sn_exact` (finite): under C2, `SN LStep s0 <-> ~ StarvedLoop s0`.
- `fair_newman` (finite): under C2 and no reachable starved loop, local joinability, confluence and
  unique normal forms coincide.

So fair settlement replaces termination exactly when reductions cannot be hidden forever. In the
four-point system the loop `kb, kc` starves label 0, which moves both loop states.

The condition is exact for termination, not for confluence: `drop_starved_confluent` (the drop
network of `CanonicalRecurrence.v`: label 0 swaps `fa` and `fb`, label 1 drops every value to `fz`)
has a starved loop, C2, no `SN`, and is confluent, because every state reaches the only normal form
`fz`. Non-vacuity of `fair_newman`: `or_fair_newman` (two flags raised by two labels; C2, no starved
loop, every peak joins, and the theorem yields confluence and unique normal forms).

`cc_exact` (`GovernanceConverse.v`) is this bridge's instance for the single registry: under WFC
(termination of repair, which supplies `SN`), unique normal forms iff CC1 (every reachable peak of
two events joins) and CC2. Its CC2 conjunct is not a peak: it is the transition-level descent of
Part 2 below (`state_descent_iff_cc2`, `cc2_is_descends`). Under the fair reading, WFC's role is
played by C2 plus the absence of a starved loop; no instance of the governance model was rebuilt
that way here.

## Hypothesis B-C: fixed points are B-solutions

**Result: held, with one leak on the canonical side.**

A store `Sh` with `get` and `set` on a vertex list `vs`, with the two lens laws
`get v (set v d s) = d` and `set v (get v s) s = s`.

- Reading A. The edge repair `U_(a,b,f)(s) = s[b := f (s_a)]` (`erep`). `erep_fixed_iff`: it fixes
  `s` iff `f (s_a) = s_b`. `edge_fixed_iff_section`: `s` is fixed by every edge repair of `G` (it
  is `Stable` for the dynamics `eU G`, label `j` repairing the `j`-th edge) iff `s` is a section of
  `G`; `edge_fixed_iff_csp`: iff `s` solves `csp_of G []` (through `section_solution`, the bridge of
  `section_iff_csp`). `edge_fixed_exists_iff_csp`: existence of a fixed store iff the CSP is
  satisfiable, when every assignment on `vs` is realized by a store.
- Reading B. The resolver repair `U_j(s) = s[j := F_j(s)]` (`SignedResolver.rupd`).
  `rupd_fixed_iff`: fixed by every `U_j` iff `F_j s = s_j` for every `j`. `rupd_fixed_iff_csp`:
  when `F_j` reads its in-neighbors through a merge `g_j`, fixed iff a section of the merge network
  (`hsection`) iff a solution of its CSP (`hsection_iff_csp`).

In C's vocabulary (any dynamics `u`, labels `js` nonempty):

- `no_solution_no_settlement`: no B-solution gives no raw settlement from any start (the fair
  schedule `js` forever never reaches a settled state).
- `singleton_iff_solution`: at a reachable state `x`, there is a fair lasso at `x` whose every
  loop state is `x` iff `x` is a B-solution. C2's singleton fair recurrent classes are exactly the
  reachable B-solutions.
- `canon_needs_solutions`: canonical settlement at `c` (C1) puts every reachable B-solution in the
  fiber of `c`. `settled_canon_exact`: under C2 this is exact,
  `CanonSettles s0 c <-> every reachable B-solution x has N x = c`.
- `ghost_refutes`: a ghost, a reachable B-solution whose canonical image is not the designated `c`,
  refutes C1.
- `multistable`: two reachable B-solutions with different canonical images refute C1 for every
  target.

Instances:

| Instance | B side | C side | Theorem |
|---|---|---|---|
| flip2, as a reading-A network on a one-vertex store: two self-loops at 0, the swap and the drop of `fa` | unique section `fz` | fair lasso `fa -0-> fb -1-> fb -0-> fa`, no settlement | `flip2_unique_solution_livelock` (its dynamics is `fu2 tt` label by label) |
| negation cycle `x0 := not x1, x1 := x0`, as a reading-B merge network | no solution | no fair run settles from any start | `negation_no_solution` |
| copy-back cycle from `(0, 1)` | two solutions reached | every canonical target fails | `copyback_multistable` |
| copy-back cycle from `(1, 1)` | the solution `(1, 1)`, not `slfp = (0, 0)` | C2 holds, C1 fails: a ghost | `copyback_ghost_solution` |

So a unique B-solution does not give C-settlement (flip2), and the converse statements in the
hypothesis hold as stated. The connection to the existing cycle statements: `sections_are_fixed_points`
and `reaches_fixed_iff_section` (`CohomologyGeneral.v`) are about fixed points of the *loop
composite* on one fiber of a cycle; the statements here are about fixed points of the *repair
dynamics* on the whole store, for any network. Both identify sections with fixed points; they are
different maps, and neither is derived from the other here.

**Leak.** "No B-solution implies no settlement" holds for raw settlement (C2) only.
`no_solution_canon_settles`: the oscillation of `semantic_oscillation` has no settled state and
no raw settlement, and still settles canonically at `true`. Canonical settlement is a statement
about fibers, not about solutions.

## Hypothesis A-B: naturality, strict and canonicalized

**Result: (1) held with the exact converse and two counterexamples; (2) held.**

(1) Strict. A per-vertex family `e_v` is natural for `G` (`NatSq`) when `f (e_a x) = e_b (f x)` on
every edge `(a, b, f)` and every `x`. This is a natural transformation from the diagram the network
defines (the functor from the free category on the graph that sends each edge to its map) to
itself (Mac Lane, *Categories for the Working Mathematician*, Springer GTM 5, 1971: natural
transformations in I.4, free categories on graphs in II.7); naturality on the generating edges
suffices, and nothing beyond that reading is used.

- `natural_maps_sections`: a natural family maps sections to sections componentwise.
- `preserves_exact`: for one fixed network, a family preserves sections iff each square commutes
  on the values sections take (`f (e_a (s a)) = e_b (f (s a))` for every section `s`).
- `natural_converse_fails`: the naive converse fails for a fixed network. On `bool`, edges
  `0 -> 1` (identity) and `2 -> 0` (constant false): `e_0` constant false and `e_1 = id` preserve
  every section (every section has `s 0 = false`), and the square of `0 -> 1` fails at `true`.
- `square_necessary`, `natural_iff_edgewise`: the squares are necessary under the quantification
  "each edge as a network of its own", for edges that are not self-loops: on a network without
  self-loops, `NatSq G e` iff `e` preserves the sections of every one-edge subnetwork.
- `selfloop_square_not_necessary`: the self-loop exception is real; a self-loop by negation has no
  section, so every family preserves its sections, including one whose square fails.
- `uniform_natural_is_unary_pol`: the uniform case `e_v = p` is exactly a unary polymorphism of the
  edge relations (`pol_iff_commute` with `k = 1`); `section_closure` is its many-section form.

(2) Canonicalized, in `FederationEvents.v`. `Candidate` is strict commutation
`f (reg e) z (sig e b) = sig e (f (reg e) z b)`; `XU` and `C1` are
`f z (sig e (f z b)) = f z (sig e b)`, that is `N o sig o N = N o sig` with `N = f (reg e) z`
(idempotent on valid states by `c_absorb`, closing them by `c_m1`).

- `candidate_is_commutes`, `candidate_implies_xu`: Candidate is `CommutesOn`, and under `Common`
  it implies XU (`commutes_descends`).
- `xu_is_descends`, `xu_iff_respects`: XU is `DescendsOn` the valid states, equivalently `sig e`
  respects the kernel of the repair there: `sig e` passes to the quotient of the valid states by
  `f (reg e) z`.
- `c1_is_descends`, `c1_iff_respects`: C1 is the same on the consistent states (valid, and fixed by
  some image); they are closed under the repair, so the same equivalence applies.
- `strict_not_necessary`: on the supply federation XU holds, Candidate fails, and every reordering
  of events converges (`supply_instance`, `supply_converges`). Strict naturality is unnecessarily
  strong.

## Does one descent definition unify the uses of `N`?

**At the transition level, yes.** One definition, `DescendsOn P N e`, with:

| Use | `N` | `P` | Instance lemma |
|---|---|---|---|
| A's state descent S | the canonicalizer | every state | `state_descent_is_descends`, `state_descent_respects_recovered` |
| CC2 (all-events form) | `rho_star` from WFC | every state | `cc2_is_descends` |
| XU | `f (reg e) z` | valid states | `xu_is_descends`, `xu_iff_respects` |
| C1 | `f (reg e) z` | consistent states | `c1_is_descends`, `c1_iff_respects` |
| Candidate (strict) | `f (reg e) z` | valid states | `candidate_is_commutes` (`CommutesOn`, which implies descent) |

**Across scales it is a hierarchy, and C's use of `N` is of a different kind.**

- Local (one transition): `N o e o N = N o e`.
- Finite histories: history descent, `h ~ k` gives `N (run h) = N (run k)`.
  `history_from_descent` and `path_history_from_descent` (the second is `state_side_transfer`
  read through `DescendsOn`): descent of every event makes history descent of the raw runs read
  after `N` the same question as history descent of the governed runs from `N s0`. The levels are
  independent: `descent_not_history` (with `N` the identity every map descends, and two
  non-commuting events separate a reordering) and `history_not_descent` (one event, so every
  reordering is trivial, and the event does not respect `N`'s kernel). The substantive
  independence witnesses are the existing `copy_xu_esh` (S fails alone) and `fm_conv_esh` (H fails
  alone) in `CanonicalInstances.v`.
- Infinite histories (C): `N` is an observation `X -> C`, and `CanonSettles s0 c` says the
  trajectory `N (x_t)` is eventually constant at `c` along every fair run. It reads `N` only through
  the fiber of `c` (`canon_settles_fiber`). The link to the transition level:
  `trajectory_quotient` and `canon_settles_quotient_invariant`: if every step respects the kernel
  of `N` (`ObsRespects`), the `N`-trajectory, and so canonical settlement, depends only on the
  `N`-image of the dynamics and of the start (the trajectory is a trajectory of the quotient
  dynamics). `trajectory_needs_descent`: without descent two dynamics agreeing after `N` at every
  state can differ in canonical settlement, and canonical settlement can hold for a dynamics that
  does not respect `N`.

So C does not use `N` as a descent condition: transition-level descent neither implies C-settlement
(the four-point system with `N` the identity) nor is implied by it (`trajectory_needs_descent`).
What descent gives C is a reduction: under it, C on `X` is fair settlement of the quotient dynamics.

## Statement review

- Every hypothesis set has a non-vacuity instance: `strict_not_necessary` (descent, federation),
  `or_fair_newman` (`fair_newman`), the four B-C instances, `natural_converse_fails` (which also
  exhibits a section).
- Qualifiers in the statements: `NFDec` in `newman_bridge`; a finite state type in
  `sn_iff_no_loop`, `fair_sn_exact`, `fair_newman` (`fair_starves` needs none); `js <> []` in the
  B-C settlement theorems; the lens laws and `TargetsIn` / `EndsIn` / `Realize` in the store
  theorems; no self-loops in `natural_iff_edgewise`; `Common` in `candidate_implies_xu` and the
  federation descent equivalences.
- What is not claimed: nothing here is new mathematics in isolation. Newman's lemma (Newman, "On
  theories with a combinatorial definition of 'equivalence'," *Ann. of Math.* 43(2), 1942,
  223-243; Huet, "Confluent reductions: abstract properties and applications to term rewriting
  systems," *J. ACM* 27(4), 1980, 797-821, for the proof by noetherian induction), the four-point
  counterexample (Klop, ICALP 1990, cited above), compatibility of operations with an equivalence,
  and naturality are classical. Weak fairness as the condition that a continuously enabled
  transition is eventually taken is standard: Lehmann, Pnueli and Stavi ("Impartiality, justice
  and fairness: the ethics of concurrent termination," ICALP 1981, LNCS 115, 264-277), where it is
  called justice; Francez (*Fairness*, Springer, 1986), a book-length treatment of fairness notions
  and fair termination. The content is the exact form each takes at this development's interfaces.

## Leaks

1. **A-C:** fair settlement does not replace termination in Newman's lemma
   (`four_point_fair_not_confluent`); it does exactly when no reachable loop starves a label
   (`fair_sn_exact`). That exactness needs a finite state type, and it characterizes termination,
   not confluence (`drop_starved_confluent`).
2. **B-C:** no B-solution refutes raw settlement only; canonical settlement can still hold
   (`no_solution_canon_settles`).
3. **A-B strict:** the commuting squares are not necessary for a fixed network
   (`natural_converse_fails`); they are necessary edge by edge, and not for self-loops
   (`selfloop_square_not_necessary`).
4. **Unification:** one descent definition covers the transition-level uses (S, CC2, XU, C1, and
   Candidate as its strict form). C's use of `N` is trajectory-level; it is linked to descent by a
   quotient-invariance theorem, not an instance of it.
