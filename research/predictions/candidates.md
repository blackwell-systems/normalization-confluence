# Prediction candidates against the frozen framework

Step 1 of the protocol in [README.md](README.md). Three candidates, each derived from the frozen
kernels, each about a question whose answer was not found in the repository or in the literature
checked. No proof, search or enumeration that would decide any of them was run. One is to be chosen
and copied unchanged to `P1.md` by the repository owner; this file does not choose.

Kernel names below are read from the frozen files (hashes in [frozen.sha256](frozen.sha256)):
`TransportCSP.v` (`pol_gamma_iff`, `chain_pol`, `ac_exact`), `TransportCSPHard.v` (`pol_dfam_iff`,
`pol_superfamily_proj`, `dfam_minimal`, `semilattice_pol`), `DistributedCycles.v` (`q1_unique_iff`,
`dist_ring_livelock`), `CanonicalRecurrence.v` (`C2`, `C2_loops`, `C1_refutes`,
`bad_lasso_refutes`, `lasso_classification`), `LayerInterfaces.v` (`singleton_iff_solution`,
`no_solution_no_settlement`, `settled_canon_exact`, `ghost_refutes`, `multistable`,
`flip2_unique_solution_livelock`).

Two of the three are about systems outside the repository (routing protocols, two-sided matching
markets). Candidate A is about the repository's own open question on monotone transports
([paper-argument.md](../paper-argument.md), Part 4, item 4), in a stronger form than the one
recorded there.

## Candidate A. Monotone transports off the chain have only projections

**Claim (formal).** Let `P` be a finite poset with at least three elements, `Mon(P)` the set of all
order-preserving maps `P -> P`, and `Gamma_P := gamma Mon(P) P` the template of `TransportCSP.v`
with the graph of every monotone map and every pin. If `P` is not a chain, then for every arity
`k`, every `k`-ary polymorphism of `Gamma_P` is a projection:
`pol k p Gamma_P -> exists i, i < k /\ forall xs, length xs = k -> p xs = nth i xs _`.

**Plain sentence.** On any finite poset of three or more elements that is not a chain, the only
operations that commute with every monotone map are the projections.

**Derivation from the kernels.**
- `pol_gamma_iff`: a polymorphism of `gamma F cs` is exactly an operation commuting with every map
  of `F` and fixing every pin. So the claim is a statement about the centralizer of `Mon(P)`.
- `pol_dfam_iff` and `pol_superfamily_proj`: on the diamond, any family containing the six maps of
  `dfam` (read flag 1, read flag 2, their AND, their OR, the two constants) has only projections,
  at every arity. `dfam_minimal`: each of the six is needed.
- `chain_pol` and `semilattice_pol`: where the family commutes with a join or meet (every chain;
  join-homomorphisms on any lattice), non-projection polymorphisms exist.
- The step the kernels suggest but do not take. What the six maps of `dfam` do is read two
  independent up-set memberships into a two-element chain and combine them by AND and OR. On any
  poset with a comparable pair `lo < hi`, the indicator map of an up-set `U` (`x |-> hi` if
  `x in U`, else `lo`) is monotone. A polymorphism commuting with all of them acts on up-set
  membership through one Boolean function. Two up-sets in general position then force that function
  to be a bounded lattice homomorphism, which means a coordinate. This is the argument of
  `pol_dfam_iff` with up-sets in place of flags. It does not apply as stated when `P` has no
  comparable pair (antichains), or no two up-sets with all four membership regions nonempty (for
  example a chain plus an isolated point, or crowns). The prediction is that no non-chain poset
  escapes: the projection-only clone of `pol_dfam_iff` is the general behavior off the chain.
- The two-element antichain is excluded by the size bound: every map of it is monotone, and the
  majority and minority operations commute with all of them.

**Why it is not known.**
- In the repository: LANDSCAPE.md ("Monotone transports off the chain") proves the hardness
  boundary only for posets that retract onto a three-element non-chain, or are bounded. It states
  no clone result beyond the diamond. The search in `research/predicted-hard-cell` tests for
  Siggers, majority and Mal'tsev polymorphisms only, not for projection-only clones.
- Literature read for this file or recorded in LANDSCAPE.md:
  - Larose and Zádori 2006 (SysPol for finite algebras; lattices; no Taylor term commutes with a
    majority operation).
  - Broniek 2006 (complexity of SysPol for every unary algebra on at most three elements; it
    classifies complexity, not the clone).
  - Mayr 2023.
  - Machida and Rosenberg: the 2003 survey (the monoid of all unary maps on three or more elements
    has the least clone as centralizer), "Monoids whose centralizer is the least clone" (2004, a
    sufficient condition), and the classification of centralizing monoids on a three-element set.
  - The poset-polymorphism line (Larose and Zádori 1997, 2003, 2004; Szabó and Zádori 2001), which
    concerns a different template, the order relation itself.
  - A web search for centralizers of monoids of order-preserving maps found no statement for the
    monoid `Mon(P)` of an arbitrary finite poset.
  - None of these states the claim, and none gives the clone even at size four.

**Pass.** A proof, axiom-free and with the kernels unchanged, that for every finite non-chain poset
with at least three elements every polymorphism of `Gamma_P` of every arity is a projection.

**Fail.** One finite non-chain poset `P` with at least three elements and one explicit
non-projection operation commuting with every monotone map of `P` and idempotent. Its commutation
must be mechanized, or checked by exhaustive computation and then mechanized.

**What a refutation looks like.** A small poset, likely disconnected or with few comparabilities,
for example `1 + 2`, `1 + 1 + 2` or a crown. On it, some binary or ternary operation behaves like
a projection inside each component but chooses its argument by where the arguments lie, and still
commutes with every monotone map, constants and component-merging maps included. Such an operation
may still have no Taylor identities. The hardness boundary would then survive while the clone claim
fails. That outcome scores FAIL for this claim as committed.

**How it could fail.** The diamond argument rests on two independent up-sets and a comparable pair.
On posets without them the monotone monoid is smaller, and its centralizer can only be larger. The
argument for the full transformation monoid (Machida and Rosenberg) covers antichains of three or
more elements, but nothing found covers the mixed cases.

**Probability that it holds.** About 0.6.

**Size of the test.**
- Refutation side: an exhaustive search over posets up to five or six elements for binary and
  ternary non-projection idempotent operations commuting with `Mon(P)`. This is finite and small;
  a hit then needs about 200 lines to mechanize.
- Proof side: a case split (up-sets in general position, retraction onto a smaller non-chain,
  antichains, and the remaining cases) over all finite posets. That is a few hundred to about 1500
  lines of Coq, depending on how much of the clone argument of `TransportCSPHard.v` generalizes.

## Candidate B. Routing: one stable routing in every failure scenario gives settlement

**Model.** Distributed Bellman-Ford (distance-vector, no path attribute) over a finite routing
algebra, in layer C's execution model:
- Route values: a finite set `S`, totally ordered by preference (smaller is better), with an
  invalid route `inf` that is the worst and a trivial route `0` held by the destination.
- Policies: a finite set of edge policies `f : S -> S` with `f inf = inf`. Policies need not be
  isotone (monotone in the preference order) and need not be increasing: this is the policy-rich
  setting of Daggitt, Gurney and Griffin.
- Network: a finite digraph `G` on nodes `V`, a destination `d`, and a policy `f_uv` on each arc
  `uv` (`u` may route through `v`).
- State: `r : V -> S` with `r d = 0`. Updating node `u` (a label) sets
  `r u := min ({f_uv (r v) | uv in G} ∪ {inf})`.
- Runs: one label per step (`prs`), fair schedules (every node named infinitely often,
  `DistributedCycles.Fair`), from any state (stale starts included).
- The settled states (fixed by every label) are the stable routings, the solutions of the routing
  equations.
- `H(G)`: for every destination `d` and every spanning subgraph `G'` of `G` (arcs removed: the
  failure scenarios), the equations of `(G', d)` have exactly one solution.

**Claim (formal).** For every finite algebra and every network `G`: if `H(G)`, then for every
destination, every state `r0` and every fair schedule, the run is eventually constant at the unique
solution. Equivalently, by `C2`, no network obtained from `G` by removing arcs has a bad fair lasso
for raw settlement. The converse holds by `multistable` and `no_solution_no_settlement`. So the
claim makes `H(G)` the exact condition for absolute convergence in every failure scenario.

**Plain sentence.** A policy-rich distance-vector network that has exactly one stable routing in
every failure scenario converges from every state under every fair one-node-at-a-time schedule, even
when its policies are not monotone.

**Derivation from the kernels.**
- `q1_unique_iff` (DistributedCycles.v): for a repair that is monotone with the step laws, every
  fair schedule from every start settles at the least fixed point iff the repair has exactly one
  fixed point. With isotone policies the update above is monotone, so the claim for one network is
  a short instantiation there. That case does not count and is not the prediction.
- `flip2_unique_solution_livelock`: without monotonicity, a unique B-solution does not give
  settlement. `singleton_iff_solution` and `C2_loops`: settlement fails exactly through a fair
  loop that is not a singleton fixed point, and the singleton classes are the B-solutions.
- `lasso_classification` sorts every long-run failure met into four classes:
  - no solution (the negation cycle; `no_solution_no_settlement`);
  - a unique solution with a livelock (flip2);
  - a settled state in the wrong fiber (the ghost; `ghost_refutes`);
  - several solutions (`multistable`).
- The step the kernels suggest but do not take. `H(G)` excludes the no-solution, ghost and multistable classes
  in every failure scenario. The prediction is that for routing systems the flip2 class does not
  occur alone: a bad fair lasso in DBF always leaves a trace in the B-layer of some failure
  scenario. The sketch: the arcs a loop's routes actually use span a scenario with no solution or a
  second one. So hereditary B-uniqueness replaces the monotonicity hypothesis of `q1_unique_iff`.
  Outside routing the kernels say this replacement is false (flip2), which is why the claim can
  fail.

**Why it is not known.** Read or searched for this file:
- Griffin, Shepherd and Wilfong 2002, "The stable paths problem and interdomain routing" (no
  dispute wheel gives a unique solution and safety; path-vector with message queues, from empty
  routes).
- Sobrinho 2005, "An algebraic theory of dynamic network routing" (monotonicity is exact for
  convergence over all networks, path-vector).
- Cittadini, Di Battista, Rimondini and Vissicchio, "Wheel + Ring = Reel" (ICNP 2009, ToN 2011):
  safety under every route filtering is characterized by the absence of a dispute reel, and several
  stable states make a network unsafe under filtering. That is the SPP model, path-vector, with
  filters rather than arc removal, and the necessary direction only for multistability.
- Daggitt, Gurney and Griffin, SIGCOMM 2018, and Daggitt and Griffin, IEEE/ACM ToN 2023: strictly
  increasing algebras converge absolutely, with a unique solution, under the Üresin and Dubois
  asynchronous model with delays. That condition is sufficient; the claim here goes beyond it.
- Santos and Sobrinho, "Internet routing: characterization via an algebraic property of cycles and
  a polynomial-time algorithm" (ACM, 2026). Centripetalism characterizes the existence of unique
  stable routings for all destinations and failure scenarios, which is `H(G)`. Only the abstract
  was read: the full text returned HTTP 403.
- Jaggard, Ramachandran and Wright 2009 on communication models (searched, not read).

None found states that `H(G)` gives convergence of the dynamics from stale states under fair
sequential activation. **The main literature risk:** the full text of Santos and Sobrinho 2026 may
prove protocol convergence under centripetalism, and Cittadini et al. may contain the path-vector
analogue. Both must be read before this candidate is chosen. If either settles the claim in this
model, drop it.

**Pass.** A proof of the claim for every finite algebra and network, axiom-free, through `C2` or
`C1_closed` (the target fiber is a singleton fixed point, closed under the steps).

**Fail.** One finite algebra, network and destination with `H(G)` verified, and one bad fair lasso
for raw settlement. It must be mechanized; the refutation then follows by `bad_lasso_refutes`, with
no finiteness needed.

**What a refutation looks like.** A three- or four-node network with a non-isotone policy (a
preference that depends on a route attribute a neighbor can toggle). Two nodes' best choices
alternate through each other's current routes under a fair schedule. Yet every arc-deleted scenario
still has exactly one stable routing: the flip2 pattern realized by min-of-policies updates.

**How it could fail.** Non-isotone policies are exactly what breaks `q1_unique_iff`'s monotone
sandwich argument. `H(G)` is a statement about fixed points of subnetworks, while a livelock is a
statement about trajectories, and the kernels connect the two only under monotonicity or through
the four failure classes listed above.

**Probability that it holds.** About 0.5.

**Size of the test.**
- Refutation side: a search over small networks (three or four nodes, `|S|` at most four, a few
  policies), checking `H(G)` by enumerating solutions of every subnetwork and searching for fair
  lassos. Finite, minutes to hours. A hit needs about 150 lines to mechanize.
- Proof side: a general argument over all networks (for example induction on the arcs a fair loop
  uses), medium to large, 800 lines or more of Coq.

## Candidate C. A unique stable matching does not stop fair blocking-pair dynamics

**Model.** The marriage market with `n` men and `n` women and complete strict preferences:
- State: a matching (partial allowed).
- Labels: the `n^2` pairs `(m, w)`.
- Update: `u_(m,w) mu` matches `m` with `w` if `(m, w)` blocks `mu`, meaning each is single or
  prefers the other to the current partner. Their former partners become single. Otherwise the
  update leaves `mu` unchanged. Updates are deterministic.
- Fair schedule: every pair named infinitely often, naming a non-blocking pair being a no-op step,
  as in `DistributedCycles.Fair`.
- With complete lists, the states fixed by every label are exactly the stable matchings.

**Claim (formal).** There are `n <= 4`, preferences with exactly one stable matching `mu*`, and a
start matching `mu0` such that `BadLasso Stable mu0` holds. That is, a pair-word `p` reaches a
matching `mu`, and a nonempty pair-word `q` that names every one of the `n^2` pairs returns `mu` to
itself, with some loop state unstable. Hence fair settlement fails from `mu0`
(`bad_lasso_refutes`), although the B-solution is unique.

**Plain sentence.** In the classical stable marriage market, a unique stable matching does not
prevent blocking-pair dynamics from cycling forever, even when every pair gets infinitely many
chances to block, and this already happens with at most four men and four women.

**Derivation from the kernels.**
- `flip2_unique_solution_livelock`: a unique B-solution does not give fair settlement.
  `q1_unique_iff`: it does when the repair is monotone with the step laws.
- `singleton_iff_solution` and `C2_loops`: the singleton fair recurrent classes are the B-solutions,
  here the stable matchings, and settlement fails exactly through a non-singleton fair loop.
- The step the kernels suggest but do not take. The pair update is not monotone in any order that
  makes `mu*` an extremal fixed point: one agent trades up, a former partner drops to single. So the
  system sits with flip2, not with `q1_unique_iff`, and the kernels predict the flip2 failure here.
- What the kernels do not settle is fairness. A pair that blocks at every state of a cycle must be
  resolved on the loop, and the pairs of `mu*` are natural candidates for that. So fairness over all
  `n^2` pairs may force every cycle to escape to `mu*` once the stable matching is unique. Candidate
  B predicts the opposite outcome (uniqueness suffices) for a different class with the same kernel
  pair; together the two test whether the kernels discriminate.

**Why it is not known.** Read or searched:
- Knuth 1976 (blocking-pair resolution can cycle).
- Roth and Vande Vate 1990 (from every matching some path of blocking-pair resolutions reaches a
  stable matching; random resolution converges with probability one).
- Abeledo and Rothblum 1995 (paths to marriage stability).
- Diamantoudi, Miyagawa and Xue 2004 (roommates).
- Kojima and Ünver 2008 (many-to-many).
- Ackermann, Goldberg, Mirrokni, Röglin and Vöcking 2011 (uncoordinated two-sided markets,
  exponential convergence times).
- "Improved paths to stability for the stable marriage problem" (2020) and "Fragile stable
  matchings" (2024), from the search results; titles and abstracts only.

The cycles in this literature are under an adversary that picks which blocking pair to resolve. No
statement was found that combines fairness over all pairs with a unique stable matching. **The
literature risk:** a known cycling example, Knuth's in particular, may already have a unique stable
matching and admit a pair-fair cycle. Check the full text of Knuth 1976 and Ackermann et al. before
choosing.

**Pass.** An explicit instance with `n <= 4`, its unique stable matching and a bad fair lasso, all
mechanized (uniqueness and the lasso by computation; the refutation of settlement by
`bad_lasso_refutes`).

**Fail.** An exhaustive check, up to the symmetries of relabeling men, women and the sides, showing
that for every `n <= 4` and every preference profile with exactly one stable matching there is no
bad fair lasso from any start. The check is to be run by a program reviewed independently, with
`n <= 3` also decided in Coq (state space small: matchings of 3 by 3).

**What a refutation looks like.** The search finds pair-fair cycles only in profiles with several
stable matchings. Every profile with a unique stable matching settles under every pair-fair
schedule, because some pair of `mu*` blocks throughout each candidate cycle and fairness forces it
to be resolved.

**How it could fail.** The fairness requirement over all `n^2` pairs is much stronger than the
adversarial choice used in the cycling literature. Uniqueness of the stable matching puts structure
on preferences (the man-optimal and woman-optimal matchings coincide) that may make some `mu*` pair
block along every cycle.

**Probability that it holds.** About 0.6 for `n <= 4`.

**Size of the test.**
- Refutation side: `n = 3` is small (46,656 profiles, 34 matchings, 9 labels). `n = 4` needs
  symmetry reduction (on the order of 10^8 profiles after reduction, 209 matchings, 16 labels):
  hours of computation.
- Proof side: one instance, about 200 lines to mechanize.

## Considered and dropped

Recorded so the choice can see what was ruled out and why.

- **Compaction: deduplication with bounded retention under at-least-once delivery** (the
  COVERAGE.md candidate axis).
  - A time-based retention under asynchrony is no deduplication, so it is `alo_exact`.
  - A count-based window of `k` events has an exact condition of the expected shape, with a short
    argument: exactly-once convergence plus absorption of a duplicate at every delivered set of at
    least `k + 1` events.
  - Its causal variant gives the same, because duplicates of earlier events can refill the window.
  - Too sure to be a test (above 0.9).
- **Confluence under fair settlement** (the open end of `fair_sn_exact`). Under `C2` and joinable
  reachable peaks, confluence holds iff every state in a non-trivial strongly connected component
  has a unique normal form. A short induction over the component order gives this, so it is too
  sure.
- **BGP under one-node polling with a unique solution and a livelock.** Likely settled by the
  NAUGHTY GADGET line (Griffin, Shepherd and Wilfong 2002; Fabrikant and Papadimitriou 2008).
  Candidate B asks the hereditary form instead.
- **Population protocols under pairwise fairness, and Boolean networks with no negative cycle.**
  Fair livelocks appear in the smallest cases (a positive 3-cycle rotating one token), a known
  phenomenon. Too easy, and close to known results.

## Recommendation

**Candidate B is preferred, if the two full-text checks clear it.** It is about an outside protocol
class that people deploy, it is uncertain (0.5), and it tests what the framework adds rather than
what it restates. Its derivation is the framework's own distinction between the monotone kernel
`q1_unique_iff` and the flip2 failure, used to say which side of that line a policy-rich routing
system falls on. A pass would make hereditary B-uniqueness an exact replacement for monotonicity in
a class where convergence matters. A fail would be a flip2 instance in routing that the B-layer of
every failure scenario cannot see. The checks are the full texts of Santos and Sobrinho 2026 and
Cittadini et al. 2011.

**Candidate C is the fallback if either check finds the claim.** It is outside the repository,
crisp, cheap to test in both directions, and derived from the same kernel pair. With B it forms a
contrasting pair, so choosing C still tests whether the kernels place a system on the correct side
of the monotone line.

**Candidate A is the most mathematical and the least outside.** Choose it only if a test inside the
repository's own layer B is wanted.
