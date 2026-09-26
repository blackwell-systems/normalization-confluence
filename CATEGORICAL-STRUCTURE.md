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

This is a Cech `H^1` class in the strict sense exactly when the identifications are invertible: then
`g` is the holonomy around the loop, `H^1` has coefficients in the automorphism group of the shared
fiber, and a non-identity `g` is a non-trivial class. Minimal example: shared values in `{0,1}`, two
edges the identity and one negation, so `g =` flip, which has no fixed point (it orbits `0↦1↦0`), so
no consistent global assignment exists and the witness points at the negation edge. When the
morphisms are non-invertible (a repair that collapses values), `g` is a monoid element, not a group
element, so the correct statement is the fixed-point condition, not group cohomology: `g` may still
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
genuinely Cech `H^1` in the invertible case; the practical loop-composite diagnostic is implemented
in gsm as `Federation.DiagnoseCycle` (it names the offending cycle and reports whether the loop
repair settles or orbits from a representative seed). What remains open is the cohomology-proper
classification, computing the `H^1` class itself in the invertible case and its non-abelian
analogue in general, rather than the reachable-fixed-point test.

### 10.1 The completion: `H^0`, `H^1`, and the two routes to convergence

Assemble the sheaf on the nerve `N` of the cover by subsystems: a vertex per subsystem, an edge per
non-empty overlap, a triangle per triple overlap. Write the shared fiber on an overlap as `S` (a
finite set) and, in the invertible fragment, the identification across edge `(i,j)` as a bijection
`g_ij` in a group `G ≤ Sym(S)`, with the cocycle condition `g_ik = g_jk · g_ij` on triangles.

**`H^0` is the convergent states.** A global section assigns each subsystem `i` a shared value `s_i`
with `g_ij · s_i = s_j` on every overlap: exactly a consistent global normal form. So `H^0(N, F)` is
the consistent set `L` of section 2, the federation's convergent states, and "converges
compositionally" is "`H^0` is non-empty."

**`H^1` is the obstruction (invertible fragment).** The 0-cochains are gauges (`h_i ∈ G` per vertex,
a relabeling of subsystem `i`'s shared normal form); the coboundary is `(dh)_ij = h_j · h_i^{-1}`;
the 1-cocycles `Z^1` are the transition families satisfying the triangle condition; `H^1` is `Z^1`
modulo the gauge equivalence `g'_ij = h_j · g_ij · h_i^{-1}`, with the trivial class the coboundaries.

**Theorem (completion, invertible fragment).** When the shared fiber is a `G`-torsor, a global
section exists iff the transition cocycle `{g_ij}` is trivial in `H^1` (a coboundary).
*Proof.* Fix a base `c ∈ S`; freeness and transitivity make `g ↦ g · c` a bijection `G → S`, so each
`s_i = h_i · c` for a unique `h_i ∈ G`. (Coboundary implies section) if `g_ij = h_j · h_i^{-1}`, set
`s_i = h_i · c`; then `g_ij · s_i = h_j · h_i^{-1} · h_i · c = h_j · c = s_j`, a global section.
(Section implies coboundary) a section `{s_i}` with `g_ij · s_i = s_j` gives `g_ij · h_i = h_j`, so
`g_ij = h_j · h_i^{-1} = (dh)_ij`. ∎

**`H^1` is holonomy, and its generators are a cycle basis.** Fix a spanning tree of `N` and gauge the
tree transitions to the identity; the cocycle is then determined by its values on the non-tree edges,
one per independent cycle, and each value is the holonomy around that cycle, the loop composite `g`
the diagnostic computes. So `H^1` (as a pointed set) is the holonomies of a cycle basis modulo
simultaneous conjugation, its rank is the first Betti number of the nerve (the number of independent
cycles), and it is trivial iff every loop composite is the identity. That is exactly the diagnostic's
condition, and the cycle basis is the minimal obstruction basis: fixing the holonomy on each
generator makes `H^0` non-empty.

**Two routes to `H^0` non-empty, which is gsm's dichotomy.** The obstruction vanishes in two
independent ways:

- *Trivial holonomy.* An acyclic nerve has no independent cycles (Betti number 0, `H^1` trivial), and
  more generally trivial loop composites give a coboundary. This is the acyclic / tree route.
- *Monotone fibers.* When `S` carries a lattice order and the transitions are monotone (not
  invertible, so outside the torsor picture), Knaster-Tarski gives a least fixed point of the loop
  composite, so `H^0` is non-empty regardless of holonomy. This is the monotone route.

These are exactly gsm's "two independent routes to confluence" (acyclic structure and monotonicity),
now identified categorically: the first kills the cohomological obstruction, the second sidesteps it
via order.

**General (non-invertible) case.** When transitions are non-invertible the fiber is not a torsor and
the transitions are not group elements, so classical Cech `H^1` does not apply. There the obstruction
is `H^0` directly (section 2): a global section exists iff the loop composite has a reachable fixed
point (section 10), a monoid/dynamical condition rather than group cohomology. The invertible
fragment is where the completion is a clean cohomological iff; the general case reduces to the
fixed-point condition already established.

**What the completion delivers.** `H^0 =` the convergent states; `H^1 =` the holonomy obstruction,
with an explicit cycle-basis of generators (the minimal set of loops to fix) and a Betti-number rank;
the vanishing of `H^1` and the monotone least-fixed-point are the two categorical routes to
convergence, recovering gsm's stated dichotomy as one picture. Proven here for the invertible/torsor
fragment; open beyond it is the non-abelian obstruction and mechanization.

### 10.2 Minimal coordination: eventual versus strong consistency

NC's convergence is strong eventual consistency (SEC): replicas consuming the same events reach the
same valid state regardless of order. CC is the order-independence SEC names, the monotone regime is
exactly the CRDT / join-semilattice case (machine-checked in `CRDT.v`), and the well-founded regime
(WFC + CC with compensation) is a strictly broader coordination-free class than CRDTs. So the
convergence question is the coordination question: a coordination-free (eventually consistent)
convergent implementation exists exactly when `H^0` is non-empty, and the obstruction to it is the
`H^1` class of the completion. This is the CALM boundary (monotone implies coordination-free) and
Bailis's I-confluence, made decidable and, by 10.1, classified (see also `LANDSCAPE.md`).

The classification buys more than a yes/no, because `H^1` is generated by the holonomies of a cycle
basis of the nerve (first-Betti-number many loops), and those loops are the minimal set that must be
coordinated:

**Proposition (minimal coordination).** In the invertible fragment, a federation admits a
coordination-free strongly-eventually-consistent convergent implementation iff `H^1 = 0`. When
`H^1 ≠ 0`, imposing a coordination boundary (a total order or single writer on the shared variable)
along a cycle basis trivializes the obstruction, yielding a convergent implementation that is
strongly consistent only on those loops and coordination-free everywhere else. A cycle basis
(first-Betti-number many loops) suffices, and it is minimal when `H^1` is free, since fewer than a
generating set leaves a non-trivial class.
*Proof sketch.* Coordinating a loop forces its shared variable to a single agreed value, which is
the single-writer overlap of section 10, so that loop's transition becomes a coboundary and its
holonomy generator dies. Killing a generating set of `H^1` leaves the trivial class, so `H^0`
becomes non-empty by the completion theorem, while off the coordinated loops the transitions are
unchanged and stay coordination-free. Minimality is the minimal-generating-set count of `H^1`. ∎

So a federation decomposes into a coordination-free majority (eventual consistency) and a minimal
coordinated core (strong consistency), the core being a cycle basis of the obstruction rather than
the whole network. For a distributed deployment this reads: put consensus only on the obstructing
cycles, run everything else coordination-free, and pay the availability cost of coordination on a
minimal set. It refines CALM and I-confluence from a global yes/no coordination verdict into a
localized, minimal mixed-consistency partition.

Boundary: this locates where coordination is needed for convergence, assuming the delivery layer
gives each replica the same event set (NC is the convergence layer, not the transport). It is clean
in the invertible fragment; the general non-invertible case reduces to the loop-composite
fixed-point condition of section 10, where coordinating a loop still means forcing its shared
variable to an agreed value, but the minimal-basis count is not a cohomological rank.

### 10.3 Non-abelian minimal coordination (posed, with partial results)

The clean minimality of 10.2 is the abelian shadow of a non-abelian problem. This section poses the
general problem precisely and records what is provable now versus what is open.

**Setup.** The nerve `N` is a finite connected graph (a vertex per subsystem, an edge per overlap;
per component in general). Gauge a spanning tree `T` to the identity. The overlap identifications are
then a **holonomy representation** `ρ : π_1(N) → G`, where `G ≤ Sym(S)` is the shared fiber's
symmetry group, generally NON-abelian for `|S| ≥ 3`. `π_1(N)` is free of rank `b = |E| − |V| + 1`
(the first Betti number), with one generator per non-tree edge; `ρ` sends each generator to that
edge's loop composite (holonomy). "Coordinate an edge" means impose single-writer on its shared
variable, which drops that edge's holonomy constraint (equivalently, deletes the edge from the
constraint graph, since the coordinated value is fixed by consensus, not by the morphism).

**Section criterion.** After gauging `T` to the identity, a global section assigns every vertex the
same base value, so the constraint of each non-tree edge `i` is exactly `g_i = e` (its holonomy is
trivial). Hence:

- **A global section exists iff `ρ` is trivial**, i.e. every non-tree-edge holonomy is `e`. This is
  mechanized for the independent-loop (bouquet) case as `simultaneous_section_iff` in
  `coq/Cohomology.v`, axiom-free and with no use of commutativity, so it holds for non-abelian `G`.

**The minimal-coordination problem.** Minimize the number of edges to coordinate so the residual
constraint graph admits a section (its holonomy representation is trivial). Provable bounds:

- *Sufficiency (any `G`).* Coordinating a cycle basis (`b` non-tree edges) leaves a tree, which has
  no loops, so a section exists. Thus the minimum is `≤ b`.
- *Fixed-tree refinement (any `G`).* For a fixed spanning tree `T`, coordinating exactly the non-tree
  edges with non-trivial holonomy is necessary and sufficient: necessity is the forward direction of
  the section criterion (an uncoordinated edge with `g_i ≠ e` blocks any section), sufficiency is the
  backward direction (the residual holonomies are all `e`). So restricted to non-tree-edge
  coordination, the minimum for `T` is exactly `#{i : g_i ≠ e}`, which is `≤ b`.

**The minimum is a hitting set.** Coordinating an edge deletes its constraint, so a global section
exists after coordinating a set `F` iff every cycle of the residual graph `N \ F` has trivial
holonomy. Equivalently `F` must MEET every cycle whose holonomy is non-trivial. So the minimal
coordination is the **minimum edge set hitting all non-trivial-holonomy cycles**. The diagnostic
(section 10) identifies exactly that family: each non-trivial cycle is a loop whose composite has no
reachable fixed point. This is the correct general characterization; the fixed-tree count above is
one hitting set (hit each non-trivial fundamental cycle at its own non-tree edge), hence an upper
bound, not necessarily the minimum, since a shared edge can hit several cycles at once.

**Tractable regimes (polynomial).**

- *Edge-disjoint obstruction (any `G`).* If the non-trivial cycles are pairwise edge-disjoint, one
  deleted edge per cycle is both forced and sufficient, so the minimum is exactly the number of
  obstructing cycles, for abelian or non-abelian `G` alike. This is the independent-loop case
  mechanized as `simultaneous_section_iff`, and it gives an algorithm: run the diagnostic on a cycle
  basis and coordinate the orbiting cycles. It covers the common topology where subsystems'
  shared-variable cycles do not overlap.
- *Abelian image (polynomial).* When the holonomies commute, `ρ` factors through the cycle space as a
  linear map to an abelian group, the non-trivial cycles are the complement of its kernel, and the
  minimum hitting set is a matroid rank: the rank of the image of `ρ`, computable by elimination over
  the cycle space. This is basis-independent and recovers the Betti-type count of 10.2.

**Resolved: the non-abelian minimum is never below the abelian count, and can be strictly above.**
The direction question settles cleanly, against the naive intuition that non-commutativity buys
savings. A global section after deleting `F` requires `π_1(N\F) ⊆ ker ρ`. Since a holonomy that is
trivial in `G` is trivial in the abelianization, `ker ρ ⊆ ker(\mathrm{ab} ∘ ρ)`, so every `F`
feasible for the `G`-problem is feasible for the abelianized one, and the minimum only grows:

> **`min_G ≥ min_{G^{ab}}`.** The abelian count is a LOWER bound on the true coordination, never an
> over-count. Non-commutativity adds obstruction (commutator-valued cycles the abelianization cannot
> see); it never removes it.

*A separating instance (`S_3`), so the inequality is strict.* Take the theta graph: two vertices,
three parallel edges `e_1, e_2, e_3`, first Betti number `2`. Gauge `e_1` to the identity and set the
two generator holonomies to `a = (0\,1\,2)` and `b = (0\,1)` in `S_3`. Every single-edge deletion
leaves a residual cycle with holonomy in `{a, b, a^{-1}b}`, all `≠ e`, so no section survives one
deletion; deleting `e_2` and `e_3` leaves a tree. Hence the true minimum is `2`. But `S_3^{ab} = Z/2`
via the sign, and `a = (0\,1\,2)` is even, so its abelian image is `0`: the abelianized holonomies are
`(0, 1)`, rank `1`, and deleting `e_3` alone makes the residual abelian-trivial, so `min_{G^{ab}} = 1`.
Thus `1 = min_{G^{ab}} < min_G = 2`. The gap is exactly the 3-cycle loop, a genuine convergence
obstruction that the parity invariant declares fine.

*Consequence (a soundness warning).* Sizing coordination by any abelianized holonomy (the sign, or
any homomorphism to an abelian group) is UNSOUND: it under-provisions, declaring coordination-free
some cyclic federations that cannot in fact converge without coordinating an even-permutation
(commutator-subgroup) relabeling loop. The full non-abelian hitting set is required for correctness;
the abelian regime above is a genuine special case (commuting holonomies), not an approximation to
lean on in general.

**A deployable algorithm now (correct, polynomial, `≤ b`).** Pick any spanning tree, run the
diagnostic on each fundamental cycle, and coordinate the ones that orbit. This always yields a valid
coordination (every residual fundamental cycle is trivial, so a section exists), it is polynomial,
and its size is at most `b`. It is exactly minimal in the edge-disjoint regime (each obstructing cycle
needs its own hit). It is NOT in general optimal: in the abelian dependent case the matroid rank can
be below the fundamental-cycle count (coordinate a maximal independent set instead, still
polynomial), and in the non-abelian shared-edge case the exact minimum is the open hitting-set
problem. So the accept-with-coordination capability is deployable today with a correct, bounded core;
what stays open is only its optimality tightening, whose complexity (NP-hardness, approximation
relative to `b`) is the remaining question. This `S_3` computation is established here at the paper
level; mechanizing the finite verification is a bounded follow-up.

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
   existing federation design is validated rather than extended. The completion (10.1) pins `H^0` as
   the convergent states and `H^1` as the holonomy obstruction, and yields the minimal-coordination
   result (10.2): the obstruction is exactly the eventual-versus-strong-consistency boundary, and a
   cycle basis is the minimal set that must be coordinated. The practical loop-composite diagnostic is
   implemented in gsm (`Federation.DiagnoseCycle`); the cohomology-proper `H^1` classification is open.
4. **Squier / higher-dimensional rewriting (§11)**: reframes confluence as coherence; strong for the
   single-registry paper's credibility.
