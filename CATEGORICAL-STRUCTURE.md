# Categorical structure

Status: **proven at paper level in `Set` / finite posets; not yet mechanized.** The convergence
facts this builds on (Newman, WFC/CC, federation M1, resolver R1/R2, monotone convergence,
compositional collapse) are the papers' results and are in part in the Coq development. What this
note adds is a categorical account of the federation layer that turns compositionality from a
per-topology argument into a corollary of one structural fact. The main results (a federation's
normal forms are a limit, and the federated normalizer is the retraction onto it) are proven here,
self-contained except for two standard external results (Knaster-Tarski, and connectivity of the
linear extensions of a finite poset). Everything lives in `Set` and finite posets, so once the
objects are set up the arguments are elementary. The hypotheses M1/R2/monotonicity are exactly what
gsm certifies at build time, so read each theorem as "for any federation gsm accepts."

This is a theory-layer artifact only: nothing here is proposed for the gsm API, which stays plain
and structure-free by design.

## 1. The object: the normalizer as an idempotent monad

Fix the semantics side (state spaces), not the syntax side (see the duality note in §8).

A **registry** is `R = (V_R, {dom(v)}, ρ_R)` with raw state space `D_R = ∏_{v∈V_R} dom(v)` and a
**normalizer** `ρ_R : D_R → D_R` that is total (termination) and idempotent, `ρ_R∘ρ_R = ρ_R`
(confluence plus termination give unique normal forms). Write `Φ_R := im(ρ_R)`.

So `ρ_R` is an idempotent endomap: on discrete `Set` a retraction onto `Φ_R`, and in the ordered
(monotone) regime a closure operator, i.e. a genuine idempotent monad whose algebras are the closed
elements. "The normal forms are a limit" is then a consequence, since fixed points of an idempotent
map are an equalizer.

**Lemma 0 (a single registry is an equalizer).** `Φ_R = Fix(ρ_R) = eq(id_{D_R}, ρ_R)`, a limit in
`Set`.
*Proof.* Idempotence gives `im(ρ_R) = Fix(ρ_R)`: if `s = ρ_R(x)` then `ρ_R(s) = ρ_R(x) = s`;
conversely fixed points lie in the image. And `Fix(ρ_R) = {s : id(s) = ρ_R(s)} = eq(id, ρ_R)`.
Equalizers are limits. ∎

## 2. Federation

A **federation** `F` is a finite directed graph on registries `R_1, …, R_n`. A target `B` with
sources `src(B) = {A_1, …, A_k}` (`k ≥ 1`) carries shared variables `sh(B) ⊆ V_B` and a
**resolver** `Res_B : ∏_j Φ_{A_j} → S_B`, where `S_B := ∏_{v∈sh(B)} dom(v)` (for `k = 1` this is the
single-source `Map`). A registry with no incoming edge is a **root**. Let `D_F := ∏_i D_{R_i}`.

Build-time hypotheses gsm certifies:

- **(R1)** `Res_B` is a function of its sources' normal forms alone.
- **(R2 / M1)** `Res_B` writes only `sh(B)`, and for any source normal forms, overwriting `sh(B)` of
  a `B`-normal-form with `Res_B(...)` yields a state on which `ρ_{R_B}` leaves `sh(B)` unchanged and
  returns to `Φ_{R_B}`. Local repair restores validity by touching only non-shared variables; the
  authority over `sh(B)` belongs to the sources.

**Consistent states (candidate limit).**

```
L_F := { (s_1,…,s_n) ∈ ∏_i Φ_{R_i} : for every target B,  s_B↾sh(B) = Res_B((s_{A_j})_j) }.
```

**Proposition 1 (`L_F` is a finite limit).** `L_F = eq(g, h)` for `g, h : ∏_i Φ_{R_i} ⇉ ∏_B S_B`
given by `g(s) = (s_B↾sh(B))_B` and `h(s) = (Res_B((s_{A_j})_j))_B`. Each `Φ_{R_i}` is a limit
(Lemma 0), and `L_F` is an equalizer of a product, so `L_F` is a finite limit in `Set`. ∎

**The federated normalizer (acyclic case).** Fix a topological order (roots first). Process
registries in that order; for registry `i`: (1) overwrite `i`'s shared component with `Res_i`
applied to its already-finalized sources; (2) set the `i`-component to `ρ_{R_i}` of the result.
Call this `ρ_F^π` for the order `π`.

## 3. Core theorem (acyclic)

**Lemma A (soundness).** `im(ρ_F^π) ⊆ L_F`.
*Proof.* Let `t = ρ_F^π(s)`. Each component was set as `t_i = ρ_{R_i}(…) ∈ Φ_{R_i}`, so every
component is a normal form. For a target `B`, its sources precede it and are final when `B` is
processed, so step (1) writes `Res_B((t_{A_j})_j)` into `sh(B)`, and by **(R2/M1)** the subsequent
`ρ_{R_B}` leaves `sh(B)` unchanged. Hence `t_B↾sh(B) = Res_B((t_{A_j})_j)`, so `t ∈ L_F`. ∎

**Lemma B (completeness: consistent states are fixed).** For `s ∈ L_F`, `ρ_F^π(s) = s`.
*Proof.* Induct along `π`. A root `i` has `s_i ∈ Φ_{R_i}` and no sources, so step (1) is vacuous and
`ρ_{R_i}(s_i) = s_i` by idempotence: unchanged. For a target `B`, by the induction hypothesis its
sources are unchanged, still `(s_{A_j})_j`; step (1) writes `Res_B((s_{A_j})_j)`, which by `s ∈ L_F`
equals the `s_B↾sh(B)` already present (a no-op); then `ρ_{R_B}(s_B) = s_B` since `s_B ∈ Φ_{R_B}`. By
induction `ρ_F^π(s) = s`. This uses only the definition of `L_F`, not R2/M1. ∎

**Corollary (idempotence and image).** `ρ_F^π` is idempotent and `im(ρ_F^π) = L_F = Fix(ρ_F^π)`.
*Proof.* By Lemma A, `ρ_F^π(s) ∈ L_F`; by Lemma B, `ρ_F^π` fixes `L_F`; so
`ρ_F^π(ρ_F^π(s)) = ρ_F^π(s)`. Image `⊆ L_F` is Lemma A; `⊇` because each `t ∈ L_F` satisfies
`t = ρ_F^π(t)`. ∎

**Lemma C (order-independence).** `ρ_F^π = ρ_F^{π'}` for any two topological orders.
*Proof.* Linear extensions of a finite poset are connected under transpositions of adjacent
incomparable elements (classical), so it suffices to show swapping two consecutive incomparable
registries `i, j` (no directed path either way) leaves the output unchanged. Both follow all their
ancestors, so the prefix before them is identical in either order and their sources are finalized
identically. Processing `i` reads only `i`'s ancestors and writes only `i`'s component; processing
`j` reads only `j`'s ancestors (not including `i`, by incomparability) and writes only `j`'s
component. Disjoint reads-versus-writes commute, so the tuple after both is identical and the suffix
proceeds identically. ∎

Write `ρ_F` for the common value.

**Theorem 1 (federation retraction, acyclic).** `ρ_F : D_F → D_F` is a well-defined,
order-independent, idempotent retraction with `im(ρ_F) = L_F`, the finite limit of Proposition 1.
Equivalently, the federated normal forms are exactly a limit and `ρ_F` is the retraction onto it.
*Proof.* Combine Lemma C (well-defined, order-free), the Corollary (idempotent, image `= L_F`), and
Proposition 1. ∎

This is self-contained: no appeal to the paper's §8. The only certified inputs are R1/R2/M1, which
is the purpose of gsm's `Build`.

## 4. Monotone cycles

Drop acyclicity; require `D_F` a finite lattice (componentwise order) with every `ρ_{R_i}` and
`Res_B` monotone. Let `T : D_F → D_F` do all overwrites-then-local-normalize simultaneously; `T` is
monotone. Consistent states are `L_F = Fix(T) = eq(id, T)`, again a limit.

**Theorem 1' (reflective localization, monotone cyclic).** `T` has a least fixed point `μT`
(Knaster-Tarski), reached from `⊥` by Kleene iteration, terminating on a finite lattice. Then `ρ_F`
(iterate `T` to the fixed point) is monotone, inflationary, and idempotent: a closure operator, i.e.
a genuine idempotent monad on the poset `D_F` whose algebras are exactly `L_F`. So `L_F ↪ D_F` is
reflective with reflector `ρ_F`, and any fair chaotic iteration converges to the same `μT` (standard
for monotone operators on a complete lattice). ∎

A non-monotone cycle (for instance a negation cycle) admits no closure operator, hence no reflector,
which is exactly why gsm rejects it. The categorical obstruction and the operational rejection
coincide.

## 5. Compositionality (the payoff)

Let `G` be a sub-federation on registries `J = {R_i}` with effective registry `E = (L_G, ρ_G)` by
Theorem 1. Embed `G` into `F`: `E` becomes one node connected by outer morphisms to registries
`K = {R_k}`. **Embed discipline** (gsm-enforced): outer morphisms read `G` only through `E`'s
declared interface variables and write only into their own targets; no morphism reaches inside `G`
except into that interface.

**Theorem 2 (compositionality).** The flat federation `F_flat` (all of `J ∪ K`, all morphisms) and
the two-level `F_emb` (`E` as one node plus the outer morphisms) have the same consistent set and
the same normalizer: `L_flat ≅ L_emb` and `ρ_{F_flat} = ρ_{F_emb}` under that bijection.
*Proof.* **(constraints factor)** A tuple `(s_i)_{i∈J∪K}` lies in `L_flat` iff (a) all `G`-internal
constraints hold and (b) all outer constraints hold. By definition (a) says `(s_i)_{i∈J} ∈ L_G`. By
the Embed discipline the outer constraints reference `J` only through `E`'s interface, so (b) is
exactly the outer-constraint condition of `F_emb`. Hence projection restricts to a bijection
`L_flat ≅ L_emb`: the flat limit factors as the outer limit taken over the node `L_G`. This is
"limits compose" made concrete. **(normalizers agree)** Because outer morphisms have `E`'s interface
as source, every `R_i (i∈J)` precedes every dependent `R_k`, and `G` is sealed, so `F_flat` has a
topological order listing all of `J` first (in a `G`-internal order) then `K`. Along it the `F_flat`
computation is literally "run `ρ_G` on the `J`-part, then propagate outward," which is the `F_emb`
computation. By Lemma C, `ρ_{F_flat}` equals its value along that order, so
`ρ_{F_flat} = ρ_{F_emb}`. For a cycle crossing the boundary, use the monotone regime: both sides
compute the least fixed point of the same `T` by the factorization, and least fixed points are
unique. ∎

So compositionality is a theorem, and its proof exposes its exact hypothesis: the Embed sealing plus
either acyclicity or monotonicity across the boundary. That is precisely what gsm checks.

### 5.1 Assume-guarantee refinement (input and output ports)

Theorem 2 assumed `E` is only a *source* to the outside: outer morphisms read `G` through its
interface and write only their own targets. If an outer morphism instead *writes* into `G`'s
interface, both the "run `G` first" ordering and the transfer of `G`'s certificate fail, because the
written variable was certified under `G`'s own control, not an external one. The fix is the standard
assume-guarantee (rely-guarantee) contract, and it is what makes boundary-only reuse sound in both
directions.

Split `E`'s interface into **output ports** `out(E)` (externally readable, `G`-controlled) and
**input ports** `in(E)` (externally writable, free parameters inside `G`). For an input valuation
`p ∈ P := ∏_{v∈in(E)} dom(v)`, let `G[p]` be `G` with its input ports pinned to `p`: an ordinary
sub-federation with consistent set `L_{G[p]}` and normalizer `ρ_{G[p]}` (Theorem 1 / 1').

**Parametric certificate.** The certificate certifies `G[p]` convergent for *every* valid `p ∈ P` (a
`∀p` verdict: WFC/CC/M1/R2/monotonicity for each pinned input). gsm's exhaustive build-time
verification already ranges over reachable states, so it produces this; the certificate records the
port split, the parametric verdict, and the subsystem digest.

**Theorem 2' (assume-guarantee compositionality).** With the port split and a parametric certificate
for `G`, boundary-only `Embed` is sound: `L_flat ≅ L_emb` and `ρ_{F_flat} = ρ_{F_emb}`, and no
re-enumeration of `G`'s internals is needed. The **seam check** is: (i) outer morphisms touch `G`
only at declared ports; (ii) R2 holds at every input port that gains an external source (so the
external write is validity-preserving for the receiving `G`-component and the induced `p` is a valid
input valuation); (iii) the composed graph is acyclic or monotone across the boundary.
*Proof.* **(factor)** A composed state `(s_J, s_K) ∈ L_flat` iff (a) `s_J ∈ L_{G[p]}` for the input
valuation `p` the outer resolvers write into `in(E)`, (b) `p` is exactly that resolved value, and (c)
the outer constraints on `out(E)` hold. By seam (ii), `p` is a valid input valuation, so the
parametric certificate gives `L_{G[p]}` well-defined (Theorem 1) without inspecting `G`'s internals.
By seam (i) the outside reaches `G` only through ports, so (a) depends on the outside only through
`p` and (c) depends on `G` only through `out(E)`: the constraints separate, giving
`L_flat ≅ L_emb` with `E`'s node-state `= (in = p, out = out-values of s_J)`. **(normalizers agree)**
In the acyclic-across-boundary case there is a topological order: external sources of `in(E)`, then
`G`-internal running `ρ_{G[p]}`, then external consumers of `out(E)`. Along it the flat computation
is "resolve `p`, run `ρ_{G[p]}`, propagate `out(E)` outward," which is `F_emb` with `E`'s normalizer
`ρ_{G[·]}` evaluated at `p`. Lemma C gives `ρ_{F_flat}` equal to its value along that order, hence
`= ρ_{F_emb}`. For a cross-boundary cycle the monotone regime applies: `ρ_{G[·]}` is monotone in `p`
(all of `G`'s maps are monotone there), both sides compute the least fixed point of the same combined
`T`, unique by Knaster-Tarski. ∎

Taking `in(E) = ∅` makes `P` a point and recovers Theorem 2, which it therefore subsumes. This is the
exact soundness condition for reusing a cached certificate without re-verifying a subsystem's
internals: declare ports, certify parametrically over inputs, and check only the seam.

## 6. The resolver boundary (precise)

Theorems 1 and 2 used that `Res_B` is a function (R1) writing only shared variables and
validity-preserving (R2). They did **not** use any universal property of `Res_B`. So the two claims
often conflated are orthogonal:

- **"Federated normal forms are a limit"** holds for every accepted federation (trees, DAGs with any
  R1/R2 resolver, monotone cycles): it is just `Fix` of a closure.
- **"The merge `Res_B` is a categorical meet (a product of the source constraints)"** is strictly
  finer, true only for most-restrictive / AND. Priority and OR are R1/R2 functions that give a valid
  closure (so the limit and compositionality hold) but are chosen sections, not universal arrows.

Universality of the *merge* is therefore independent of the state space being a *limit*.
State-based CRDTs are the compensation-free special case of the monotone regime (join-semilattice
objects, monotone maps), consistent with `CRDT.v` / `SUBSUMPTION.md`.

## 7. Duality note (why "gluing is a colimit" is not a contradiction)

Gluing systems along a shared interface is a colimit (pushout) on the **syntax side**: combining two
constraint theories that share a sub-theory is a pushout in the category of presentations. The
picture above is on the **semantics side** (state spaces / models), where the same gluing is the
dual **limit** (fiber product of models agreeing on the shared part). The two are linked by the
contravariant models functor (a Stone-type / Sat-Mod duality). gsm's "limits compose" is the
semantics reading, followed throughout.

## 8. Bridge to event-sourced execution: state as a fold, order-independence as commutativity

This connects the convergence condition to any event-sourced execution log (a system that rebuilds
state by replaying a recorded sequence of events).

Events act on normal forms: each event `e` gives `α_e := ρ_R ∘ apply_e : Φ_R → Φ_R`, and
`e ↦ α_e` extends uniquely to a monoid homomorphism `α : E* → End(Φ_R)` from the free monoid on
events (this is the fold / replay).

**Lemma (order-independence is commutativity).** `α` factors through the free commutative monoid
`ℕ^E` iff the `α_e` pairwise commute, and gsm's **CC** is exactly that hypothesis.
*Proof.* `ℕ^E` is `E*` modulo the congruence generated by `ef = fe`, so by its universal property a
monoid map out of `E*` descends to `ℕ^E` iff it identifies `ef` with `fe`, i.e.
`α_e∘α_f = α_f∘α_e`. Order-independent replay is exactly "sequences with the same multiset act
equally," i.e. this descent. CC (local confluence of the per-event repairs, on normal forms) states
`ρ(apply_e(apply_f(x))) = ρ(apply_f(apply_e(x)))` on `Φ_R`, which is `α_e∘α_f = α_f∘α_e`. ∎

So order-independent replay is CC read through the universal property of the free commutative monoid:
an event-sourced log is a fold over the free monoid, and CC is precisely when it descends to the
commutative monoid.

## 9. Scope

Self-contained here: Lemma 0, Proposition 1, Lemmas A/B/C, Theorems 1, 1', 2, 2' (the
assume-guarantee refinement, which is the soundness condition for boundary-only certificate reuse),
the resolver remark, and the bridge lemma. External standard results used: Knaster-Tarski and fair-iteration convergence
for the monotone-cyclic case (Theorem 1'), and connectivity of the linear extensions of a finite
poset (Lemma C). Everything lives in `Set` and finite posets, so no deep limit-commutation in an
exotic category is invoked; the categorical framing is explanatory and boundary-finding, and the
analytic weight is the convergence facts, elementary here once the objects are set up. Not yet
mechanized: a Coq rendering would need a category-theory library and is low priority next to the
existing convergence development it would reuse.

## 10. Sheaf structure of compositional verification

**The presheaf.** Over a system's variable set, take a region to be a variable subset `U`, the
subsystem on `U` to be the rules whose footprint lies in `U`, and the section `F(U)` to be that
subsystem's normalizer `ρ_U` with its convergence verdict. Restriction `F(U) → F(U')` for `U' ⊆ U`
restricts the normalizer. The sheaf question: do local certificates that agree on overlaps glue to a
global one, checkable from the overlap alone?

**Gluing is not naive (counterexample).** Two subsystems `A`, `B` sharing a variable `s` can each be
confluent yet glue to a non-confluent union. Let `s ∈ {0,1,2}`; `A` has invariant `s ≠ 1` with
repair `s := 0`; `B` has invariant `s ≠ 1` with repair `s := 2`. Each is confluent, and both have
valid set `{0,2}`, so they agree on which values of `s` are valid. But in the union, from `s = 1` the
result is `0` (A first) or `2` (B first): order-dependent, non-confluent. Agreement on valid values
is not enough.

**The precise gluing condition.** The obstruction is that `A` and `B` disagree as normalizers on the
shared state (`A: 1↦0`, `B: 1↦2`). So the correct "agree on the overlap" is: the two certificates'
restrictions to the shared variables are **equal as normalizers** (same normal-form map on shared
states). Then the shared variable has one unambiguous normal form, the union is confluent, and the
sections glue, the global normalizer running each private part plus the agreed map on the overlap.
This is checkable on the overlap alone (compare the two normalizers over the shared subspace), never
the joint product. So convergence certificates form a **sheaf** on the site whose overlaps satisfy
this agreement.

**Two regimes force agreement, and they are gsm's regimes.**

- *Single-writer overlap*: only one subsystem writes `s` (the other reads it). The writer's
  normalizer is the only one on `s`, so agreement is automatic. This is the authority / M1
  discipline.
- *Monotone overlap*: both write `s`, but monotonically. The combined repair is a monotone operator
  with a unique least fixed point (Knaster-Tarski), so the normalizers agree on the glued result.
  This is the `AllowMonotoneCycles` regime.

**The federation already realizes this.** In a federation, distinct components do not literally share
a variable; a shared writable variable is a *multi-source target*, and the resolver merges its
sources. The resolver's hypotheses are exactly the sheaf gluing condition: R1 (source-determinacy)
makes the merged normal form single-valued (confluence on the overlap), and R2 (validity
preservation) makes it land in the agreed valid set. So **R1 + R2 is the "agree as normalizers on
the overlap" axiom, and gsm's resolver verification is the sheaf gluing check.** The design is
validated, not extended by a new primitive: the machinery that composes overlapping subsystems
soundly is already present.

**Cycles and the obstruction.** For two subsystems the condition is a single equality (or
monotone-compatibility) check, so nothing subtle survives. The interesting case is a cycle of three
or more subsystems, `A` overlapping `B`, `B` overlapping `C`, `C` overlapping `A`, where each
pairwise overlap agrees yet no global section exists. This is the classic local-consistency,
global-impossibility phenomenon, measured by the first Cech cohomology `H^1` of the presheaf over
the nerve of the overlap cover.

Worked concretely, the obstruction is the **loop composite**. Take a triangle where `A` and `B`
share `x`, `B` and `C` share `y`, `C` and `A` share `z`, the cycle's morphisms fixing each next
shared component from the previous normal form. A global section is a shared assignment fixed all the
way around, so the shared value must be a fixed point of `g = m_CA ∘ m_BC ∘ m_AB` on the shared
subspace. **A global convergent section exists iff `g` has a fixed point reachable by iteration**,
and the witness for its absence is `g` itself.

This is a Cech `H^1` class in the honest sense exactly when the identifications are invertible: then
`g` is the holonomy around the loop, `H^1` has coefficients in the automorphism group of the shared
fiber, and a non-identity `g` is a non-trivial class. Minimal example: shared values in `{0,1}`, two
edges the identity and one negation, so `g =` flip, which has no fixed point (it orbits `0↦1↦0`), so
no consistent global assignment exists and the witness points at the negation edge. When the
morphisms are non-invertible (a repair that collapses values), `g` is a monoid element, not a group
element, so the honest statement is the fixed-point condition, not group cohomology: `g` may still
have a fixed point (`g(0)=1, g(1)=1, g(2)=1` fixes `1`, so it glues) or none (`g(0)=1, g(1)=0,
g(2)=0` orbits with no fixed point, so it does not). Either way the witness is `g`, computed by
composing the cycle's morphisms over the shared subspace, bounded by that subspace rather than the
product.

This lines up exactly with gsm's cycle story. An acyclic overlap graph has no loop, so `H^1` is
trivial and gluing always succeeds (the tree / DAG theorems). A monotone cycle collapses the
obstruction: the least fixed point is the unique global section, so the cohomology vanishes in the
monotone regime (Monotone Convergence Despite Cycles). A non-monotone cycle is precisely where a
non-trivial `H^1` can appear: the negation counterexample is the minimal such cocycle, a loop of
shared constraints with no consistent global normal form. So the cohomology is not decoration; it is
the invariant separating the convergent regimes (acyclic, monotone) from the divergent one
(non-monotone cycles), and its non-vanishing is the obstruction gsm rejects.

**The concrete payoff.** Two things follow. First, the sheaf result explains why R1/R2 and the
monotone-cycle condition are the right hypotheses: they are the gluing axiom and the vanishing of the
obstruction, not separately motivated checks. Second, it points at one genuinely new capability, an
**obstruction diagnostic**: when a cyclic federation fails to converge, computing the `H^1` witness
identifies the specific cycle of morphisms and shared constraints that blocks composition, rather
than reporting a generic rejection. For federating N independently-governed policies, that answers
"can these compose" and, when they cannot, "where is the conflict." Worked over a three-subsystem
cycle (above), the witness is the loop composite `g` on the shared subspace: computable (compose the
cycle's morphisms, test for a reachable fixed point, bounded by the shared subspace) and legible (it
names the cycle and exhibits the orbit or the missing fixed point).

**Status.** The two-subsystem gluing condition, its counterexample, and the two sufficient regimes
are established here and coincide with gsm's verified regimes; the identification of R1/R2 with the
gluing axiom validates the existing federation design. The obstruction for cycles is the loop
composite's failure to have a reachable fixed point, computable over the shared subspace and
genuinely Cech `H^1` in the invertible case; turning it into a Build-time diagnostic (report the
obstructing cycle and its composite) is a concrete, low-risk next feature.

## 11. Further directions (stubs)

- **Higher-dimensional rewriting (Squier's theorem, polygraphs).** WFC + CC is convergent rewriting;
  Squier's theorem upgrades "unique normal forms" to a coherent presentation (all reduction paths
  equal up to higher cells) and connects convergence to homological finiteness of the monoid. This
  is the rigorous form of "the order of steps cannot change the result." Paper depth, low
  engineering payoff.

## Ranking of payoff-over-risk

1. **Federation-as-limit (§1-6)**: proven at paper level here; buys free compositionality (Theorem
   2) for the whole accepted class, with the merge-universality boundary made precise.
2. **Free-monoid / commutative-quotient bridge (§8)**: proven; connects convergence to event-sourced
   replay in one lemma.
3. **Sheaf structure (§10)**: worked (first pass). Certificates form a sheaf on the
   single-writer-or-monotone site, and gsm's R1/R2 resolvers already realize the gluing, so the
   existing federation design is validated rather than extended. The open, high-value piece is the
   cohomological obstruction diagnostic for non-monotone cycles.
4. **Squier / higher-dimensional rewriting (§11)**: reframes confluence as coherence; strong for the
   single-registry paper's credibility.
