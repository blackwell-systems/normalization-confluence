# The continuous extension: WFC as Lyapunov, CC as contraction

**Status: research note, forward-looking.** Nothing on this page is proven or mechanized. The
published results (the two papers, the `coq/` development) are about *discrete* governed state.
This note states what the discrete conditions become in a *continuous* state space, which
continuous systems inherit the collapse and which provably cannot, and what would have to be
established to turn the mapping into theorems. It is a map of a direction, not a claim of arrival.
Read it as the companion to [REGIMES.md](REGIMES.md) for the setting the papers do **not** cover.

## Why this note exists

Normalization confluence proves that a discrete governed system collapses: whatever order events
and repairs arrive in, every processor lands on the same valid normal form. The recurring question
is whether that survives when the state space is continuous instead of discrete: a numeric
controller, a physical or chemical system, an optimizer, a flow rather than a rewrite. The short
answer is that the *collapse* has a precise continuous analogue, but it is a **new theorem in a
different branch of mathematics**, not a corollary of the discrete results, and it is strictly
harder to establish. This note pins down exactly what the analogue is so that a continuous claim
can be scoped precisely rather than asserted by analogy.

## The one-sentence idea

The two discrete conditions have two *different* continuous analogues, and you need **both** to
keep the collapse:

```
  discrete (proven, this work)              continuous (this note, unproven)
  --------------------------------          ------------------------------------
  WFC   well-founded compensation    -->     Lyapunov function
        (a measure strictly                  (a potential V >= 0 that strictly
         decreases; repair terminates)        decreases along the flow)

  CC    compensation commutativity   -->     contraction / incremental stability
        (local confluence; the normal        (any two trajectories converge to
         form is UNIQUE and order-             each other; the attractor is
         independent, via Newman)             UNIQUE and initial-condition-
                                              independent)
```

A Lyapunov function alone is only the WFC half wearing a continuous costume. It certifies that the
system *settles*, and says nothing about *where*. The property that makes normalization confluence
worth having, order-independent convergence to a **unique** state, is the CC half, and its
continuous carrier is contraction, not Lyapunov. Confusing the two is the single most common way a
continuous "it converges" claim overreaches.

## The correspondence, term by term

| Discrete result (proven) | Continuous analogue (unproven) | What carries over | What changes |
|---|---|---|---|
| **WFC**: well-founded measure `Phi` strictly decreases on invalid states | **Lyapunov function** `V >= 0`, `dV/dt < 0` off the equilibrium set | "the system settles" | finite termination becomes *asymptotic* convergence: you approach the limit, you may never reach it in finite time |
| **CC**: local confluence of event/repair steps | **Contraction**: a metric `M(x) > 0` with `M_dot + M Df + Df^T M < 0` uniformly (Lohmiller-Slotine); or incremental stability (Sontag δISS) | uniqueness and order/initial-condition independence of the limit | must hold on a convex, forward-invariant region; it does not follow from a *local* condition the way CC does under termination |
| **Newman's Lemma**: termination + local confluence => global confluence | *(no clean analogue)* | | this is the cheap step discretely and it has **no** free continuous counterpart: contraction is inherently a uniform/global condition, so "local contraction everywhere" does not glue to global contraction for free |
| **Unique normal form** (`cor:unique-nf`) | **Unique attractor** reached from any initial condition | the shape of the guarantee | reachability weakens from exact to asymptotic |
| **Idempotent retraction onto the valid set (a limit)** (categorical view, Lemma 0 / `image_iff_fixed`) | **Deformation retraction onto a single attractor** | the "retract onto the fixed points" picture | the retraction is a flow, not an idempotent map; idempotence becomes stationarity |
| **Monotone-cycles regime** (`thm:monotone-cycles`): lattice-monotone repair, least fixed point by Kleene/chaotic iteration | **Monotone (cooperative) dynamical systems** (Hirsch-Smith) | order-preserving flow, generic convergence to equilibrium | Hirsch gives convergence for *almost every* bounded trajectory to *some* equilibrium, weaker than a unique least fixed point reached by every order |

## The sweet spot: where the collapse genuinely generalizes

There is one class where both halves hold at once and the continuous collapse is real:

> **Gradient flow of a strongly (or geodesically) convex potential.**
> Take `x_dot = -grad f(x)`. Then `V = f` is a Lyapunov function (`dV/dt = -|grad f|^2 <= 0`), and
> if `f` is `mu`-strongly convex the Jacobian `-Hess f <= -mu I` makes the flow **contracting** in
> the Euclidean metric. The result: a unique minimizer, reached exponentially fast, independent of
> where you start. That is the continuous unique-normal-form.

This is the real ceiling of "my collapse works in the continuous case": convex-potential gradient
systems, and their Riemannian (geodesically convex) generalization. State it that way and it holds.

## The boundary: where it provably does not, and why that helps

The same picture that gives the sweet spot draws the wall, and the wall is the useful part.

> **Non-convex, multi-basin systems do not collapse.** A potential with many local minima has many
> basins of attraction, hence many attractors. The Lyapunov half still holds (the energy decreases,
> the system settles into *a* minimum), so the claim that holds is convergence to *an* equilibrium.
> The contraction half fails (trajectories from nearby states fall into different basins), so you
> **cannot** claim a unique, order-independent limit. Which basin you reach depends on initial
> condition, noise, and effectively on order.

This is the exact continuous mirror of the discrete failure mode. Discretely, when CC fails you get
divergence or multiple normal forms (`prop:cycle-necessary`, the negation morphism `phi(x)=1-x`).
Continuously, when contraction fails you get multiple attractors. In both settings it is
**uniqueness**, not mere convergence, that is lost.

The practical consequence for any continuous claim (for example a protein-folding or physics-scale
target): a folding energy landscape is a funnel with many metastable minima. That is a multi-basin,
non-convex system *by construction*. A Lyapunov argument there rigorously buys stability and
convergence-to-a-basin, and nothing more. It does not license the order-independent unique-collapse
guarantee, because the property that guarantee rests on (contraction) is false for that landscape.
So this extension does not soften the discrete/continuous boundary the papers respect; it makes it
sharper, by naming precisely what continuous convergence is available (to an equilibrium set) and
what is not (a unique normal form), and giving the reason in the system's own terms.

## What you give up crossing over

| Property (discrete) | Continuous |
|---|---|
| **Finite reachability**: the normal form is reached in finitely many steps | **Asymptotic**: the attractor is approached, generally not reached in finite time |
| **Build-time decidability**: WFC/CC checked by finite enumeration | **Undecidable in general**: Lyapunov / contraction certificates come from sum-of-squares (SOS/SDP) programming for polynomial fields, degree-bounded and semi-algorithmic, not a build-time pass |
| **Axiom-free discrete mechanization** (`coq/`, extracted table/rules oracles) | **Real-analysis mechanization**: needs Coquelicot / Lean mathlib / Isabelle-HOL analysis; the extraction-and-enumeration oracle story does not transfer |

## What would have to be proven

Turning this note into results, in rough order of tractability:

1. **The correspondence as definitions and a bridge theorem.** State the continuous governed system
   (state manifold, invariant set, repair vector field), define its Lyapunov and contraction
   conditions, and prove: Lyapunov + contraction on a forward-invariant convex region implies a
   unique attractor reached independent of initial condition. Mostly assembling known pieces
   (Lyapunov/LaSalle + Lohmiller-Slotine) into the paper's vocabulary. This is the note's core claim
   made rigorous.
2. **The convex-gradient sweet spot as a clean corollary**, including the geodesically convex
   Riemannian case, with the exponential rate.
3. **A federated/interconnection analogue.** The discrete federated story localizes coordination to
   a cycle basis (`thm:monotone-cycles`, the categorical `H^1`). The continuous analogue is *network
   contraction*: when do contracting subsystems compose into a globally contracting one? This is
   small-gain / diagonal-stability territory (Slotine, Sontag). Whether the "coordinate a cycle
   basis" result has a continuous echo in feedback-gain conditions is genuinely open and is the most
   interesting question here.
4. **Mechanization**, if wanted, in an analysis-capable assistant. Heavy, and it forfeits the
   extracted-oracle discipline that makes the discrete development distinctive, so it is the last
   thing to attempt and only for the sweet-spot fragment.

## Continuation: the safety-filter target, and why it is nearly in reach

Roadmap item 3 (does the federated minimal-coordination result have a continuous echo) is the
highest-value question here, and it mostly resolves once you notice that the *obstruction* half
already exists in control theory under a different name.

### The continuous obstruction already exists: small-gain = Hurwitz interconnection

Networked-systems control already answers "when does a network of coupled contracting subsystems
converge to a single trajectory." State the precise condition, since the clean per-cycle form is
only one special case of it.

Give each subsystem a per-node contraction rate `c_i > 0` (a matrix-measure bound
`mu(J_ii) <= -c_i`) and each coupling a Lipschitz gain `l_ij` (`j -> i`). Assemble the
**interconnection matrix** `Gamma` with diagonal `-c_i` and off-diagonal `l_ij`. This matrix is
**Metzler** (nonnegative off-diagonal), and:

> the interconnection is strongly contracting (a **unique** trajectory that every solution converges
> to, exponentially, from any initial condition) **iff `Gamma` is Hurwitz**, equivalently `-Gamma`
> is a nonsingular **M-matrix** / diagonally stable, equivalently the spectral radius of the
> nonnegative loop-gain part is `< 1`.

(Russo-di Bernardo-Sontag 2013; Aminzare-Sontag 2014; the clean modern statement in Davydov-Bullo
2024, which says outright that "the Hurwitz assumption on the Metzler matrix is equivalent to a
small gain theorem.") The ISS version is the **cyclic small-gain theorem** (Dashkovskiy-Ruffer-Wirth
2007/2010; Liu-Hill-Jiang 2011): its condition is the operator inequality `Gamma_mu !>= id`, which
becomes the literal **per-cycle** statement "the composition of gains around every cycle is `< id`"
only in the **maximization** formulation (DRW Thm 8.14); for the summation formulation and for
linear gains the sharp condition is the spectral/M-matrix one above, not a bare product-around-each-
cycle. The per-cycle reading is the correct *intuition* and is exact in the max case; the general
statement is Hurwitz-Metzler.

With that precision, the correspondence is:

```
  discrete (this work)                     continuous (contraction / small-gain, known)
  ------------------------------------     ------------------------------------------
  loop composite (holonomy) g around  <->  loop gain around a coupling cycle
  a morphism cycle                          (product of the l_ij)
  cycle converges iff g is trivial /   <->  no destabilizing cycle: Gamma Hurwitz / M-matrix
  has a fixed point                         (per-cycle "loop gain < 1" exact in the max form)
  both localize the obstruction to the cycles of a directed graph
```

So the direction previously called "least certain" is not open: the continuous per-cycle obstruction
is a theorem control theory already holds. You inherit the obstruction half; you do not reprove it.
What you contribute sits on top of it.

### What is actually missing there, and is yours to add

The Hurwitz / small-gain test is a **yes/no test**. It does not answer: if the network fails it,
what is the *minimal* set of couplings to cut or nodes to damp to make it pass. That is the analogue
of the discrete minimal-coordination result, and it is the piece control theory does not have. The
conjecture to prove, stated with the structure the literature actually gives it:

> **Conjecture (continuous minimal coordination).** For `N` repair controllers, each contracting in
> a metric `M_i`, coupled on a directed graph with gains `l_ij`, call the interconnection *stable*
> when `Gamma` is Hurwitz. Then:
> (a) the composed system has a unique attractor reached from any initial condition (contraction /
>     incremental stability), robust to communication delays (Wang-Slotine 2006) and, in the
>     discrete/forward-Euler setting, to asynchronous updates, **iff `Gamma` is Hurwitz** (this is
>     network contraction = cyclic small-gain, inherited);
> (b) the minimal coordination that restores it, using **edge cuts only** (decouple a pair, i.e. pin
>     a shared variable to one writer), is a minimum-weight **subset feedback arc set** over the
>     destabilizing cycles (plain FAS if every cycle is bad): NP-hard, `O(log n log log n)`-
>     approximable, FPT in the number of cuts. Allowing **node-damping** (raise one `c_i`, which
>     helps every cycle through that node) makes it a **mixed vertex+arc feedback set**; with a
>     **continuous** damping magnitude it leaves pure combinatorics for a **mixed-integer geometric
>     program** (log-gains add around a cycle, margins subtract). All of this sits on top of an inner
>     **metric-selection SDP/SOS** layer (Aylward-Parrilo-Slotine 2008) that chooses the `M_i` and
>     thereby the effective `c_i`, `l_ij`; jointly it is a bilevel continuous-combinatorial problem
>     with no discrete analogue.

Part (a) is assembly and citation. Part (b), and characterizing the metric layer, is the new theorem
and the useful one: control has the diagnosis (Hurwitz test), not the minimal repair.

### The abelian-shadow caveat

Two things separate the discrete result from its continuous image, and both make the discrete one
richer.

First, **the group structure dissolves.** Discretely, the minimal coordination is exactly a **group
feedback arc set**: each cycle carries a holonomy in a group, a cycle is "bad" when that holonomy is
non-trivial (non-balanced), and you delete the fewest edges to make every residual cycle balanced.
That is a genuine, named problem (for `Z_2` it is odd-cycle transversal / edge bipartization, the
complement of Max-Cut). Continuously, the "bad cycle" test is not a group-balance condition at all;
it is a real-valued **magnitude inequality** (loop gain `< 1`). A magnitude threshold has no group
label to balance, so the faithful continuous models are subset-FAS and the mixed-integer geometric
program above, and *group* feedback set is only an analogy there, not an exact reduction.

Second, and downstream of the first, **scalars commute.** The sharpest discrete result, that
non-commutative holonomy *raises* the coordination floor above the abelianized count (the `S_3`
theta-graph, minimum 2 vs sign-count 1, categorical paper Section 9), has no continuous counterpart:
a product of gains is abelian. So the continuous safety-filter version corresponds to your
abelianized lower bound and is strictly the easier theory. The discrete result stays the richer one,
both because it keeps the group labeling and because that labeling can be non-abelian.

## Worked example: two robots whose collision-avoidance filters deadlock

The smallest system that exhibits the whole story. Two-robot deadlock is a well-studied failure mode
(Grover-Liu-Sycara, IJRR 2023; the general CBF-QP result of Reis-Aguiar-Tabuada, Automatica 2024;
the reciprocal-avoidance "dance" of RVO/ORCA, van den Berg et al.), which is why it is the right
test. One caveat stated up front, because it is the load-bearing correction from checking this
against the literature: the established mechanism is **not** a gain blow-up. It is a spurious
*stable* equilibrium created by symmetry, and the safe control goes to **zero** there, not to
infinity. The contraction / cyclic-cut reading below is consistent with that mechanism but is, as
far as a targeted search of the CBF-deadlock and velocity-obstacle literature found, **not stated
anywhere**: casting this deadlock as a small-gain / contraction failure on a coupling cycle is this
note's own synthesis, an opportunity to establish, not a restatement of a known result.

### Setup

Two robots `A`, `B` with states `x_A, x_B` in the plane, single-integrator motion `x_dot = u`.
Each has a nominal goal-tracking controller `u_nom = k (goal - x)`, contracting at rate `k` toward
its goal. Each runs a control-barrier-function safety filter enforcing a minimum separation:

```
  h(x_A, x_B) = || x_A - x_B ||^2 - D^2 >= 0      (stay at least D apart)
```

The filter is a QP that minimally edits `u_nom` to keep `h_dot >= -alpha h`. The point: `A`'s safe
input depends on `x_B`, and `B`'s on `x_A`.

### The coupling graph, and the cycle

Draw an edge `j -> i` when `j`'s state enters `i`'s filter. `A` responds to `B` and `B` responds to
`A`, so:

```
        A  <-------->  B          two directed edges A->B and B->A
                                   => exactly one cycle: the 2-cycle A<->B
```

- **Per-node contraction.** Away from the safety constraint each robot just tracks its goal, a
  contraction at rate `k` (the nominal gain).
- **The coupling is the active safety constraint.** When the separation constraint is active, each
  robot's *safe* input depends on the other's position: the QP subtracts a multiple of the
  constraint gradient from the nominal input. That mutual dependence, not any single gain value, is
  the edge. Grover-Liu-Sycara's activation lemma makes the reciprocity exact: if `A`'s constraint
  with `B` is active, `B`'s with `A` is active too. Both edges switch on together, so the coupling
  is a genuine 2-cycle exactly when it matters.

### The obstruction, read off the cycle

The correct mechanism, then the cycle reading of it.

**What actually happens (established).** At a symmetric head-on configuration the QP reaches a
**force-equilibrium on the safety boundary**: the nominal pull toward the goal is exactly cancelled
by the constraint-gradient repulsion (this is the KKT stationarity of the QP), so the safe input is
`u* = 0` while the robot is not at its goal. That zero-control point is a **spurious, asymptotically
stable equilibrium** of the closed loop, and it exists because of the geometric **symmetry** of the
two constraints, not because of any parameter tie (Grover-Liu-Sycara prove gain heterogeneity alone
does not remove it; Reis-Aguiar-Tabuada prove the general CBF-QP introduces such boundary equilibria
and give conditions for their asymptotic stability). ORCA reports the same as velocities converging
to zero in dense symmetric encounters.

**The cycle reading (this note's synthesis).** A globally contracting interconnection has exactly
**one** equilibrium and every trajectory converges to it. So a *second* asymptotically stable
equilibrium is direct evidence that the composed safe dynamics is **not** globally contracting near
that configuration: its interconnection matrix `Gamma` has lost Hurwitzness on the `A<->B` cycle.
That is the bridge:

```
  far apart:            constraint inactive, no coupling edge, each robot contracts to its goal
                        => Gamma Hurwitz, unique attractor = the goals. Clean pass.

  symmetric contact:    both constraints active, the A<->B cycle switches on, and a second stable
                        equilibrium appears on h = 0 => Gamma NOT Hurwitz on that cycle
                        => contraction lost => the goal is no longer the unique attractor. Deadlock.
```

Which outcome you land in (the stall, or the ORCA side-to-side dance) then depends on tie-break and
schedule, and that dependence *is* the continuous face of CC failure: the same shape as the discrete
negation morphism `phi(x) = 1 - x` giving a shared value no order-independent normal form
(`prop:cycle-necessary`). The reframing localizes the known deadlock to the `A<->B` cycle from the
graph alone. It does not claim to have discovered the deadlock; it claims the cycle/contraction lens
sees it, which the literature's equilibrium analysis does not currently connect to small-gain.

### The minimal coordination

The graph has one destabilizing cycle, so the minimum subset feedback arc set is **one edge**.
Cutting an edge means removing one direction of mutual dependence: make `A` ignore `B` in its filter
(give `A` priority, it holds its nominal path) while `B` keeps responding to `A` and does all the
yielding. The remaining graph is `A -> B` only:

```
        A  -------->  B           no cycle: a cascade, A drives, B avoids
```

A cascade of contracting systems is contracting (`Gamma` is triangular, hence Hurwitz, with no
cycle to destabilize it), so the composed system now has a unique attractor: `A` reaches its goal,
`B` reaches its goal by a detour, and the result no longer depends on tie-break or schedule.
Deadlock resolved by the smallest possible intervention, one arbitration.

This matches what the literature finds *rigorously* resolves deadlock, and matches it in the sharp
way. Symmetry-breaking by priority / right-of-way is the standard fix (BRVO, Sadat-Vaughan 2012;
Grover-Liu-Sycara's structured maneuver), and Grover-Liu-Sycara show specifically that heterogeneous
*gains* do not suffice: the break must be **structural**. Cutting an edge is exactly a structural
break, not a parameter retune, so the framework prescribes the kind of fix the literature says is
the one that works.

And this is the exact continuous image of the discrete authority argument: **coordinating an edge =
pinning the shared variable to a single writer.** Here the shared variable is "which robot yields /
which side to pass," `A` is the authority that fixes it, and turning the cyclic mutual dependence
into an acyclic cascade is the continuous form of "acyclic federations converge because the source's
normal form deterministically fixes the target's shared component" (`thm:fed-convergence`).

### Where the abelian shadow bites (three robots)

Push to three robots in a symmetric priority cycle: `A` yields to `B` yields to `C` yields to `A`
(rock-paper-scissors). Discretely, a non-abelian holonomy around such a cycle can force coordinating
**two** of the three edges (the `S_3` phenomenon of Section 9). Continuously, the destabilizing
condition is one scalar loop gain over the 3-cycle, so cutting **any one** of the three edges breaks
it: minimum subset feedback arc set is 1. The continuous fix is cheaper than the discrete
non-abelian minimum, which is the abelian-shadow caveat made concrete: a scalar loop gain cannot
encode the order-of-relabeling obstruction that a discrete group holonomy can.

### What this example establishes

Nothing is proven here, and the deadlock itself is established by other means (a symmetric spurious
equilibrium, not this note's cycle argument). What the example shows is that the contraction / cut
lens *re-derives the same conclusions from the coupling graph alone*: it (1) flags that the filters
deadlock (loss of Hurwitzness on the cycle, equivalent to the second stable equilibrium the
literature proves), (2) names the conflicting cycle, (3) returns the minimal coordination (one
structural cut), which coincides with the priority fix the literature finds rigorously works, and
(4) recovers the discrete authority argument as continuous priority assignment. The novel content is
the lens, not the deadlock: no CBF-deadlock paper found connects this to small-gain or contraction.
The three-robot remark then shows precisely where the continuous theory is the easier, abelian one.

## References for the continuation

Verified against the primary sources; the continuation's claims are grounded in these.

*Contraction and network contraction.* W. Lohmiller, J.-J. Slotine, "On contraction analysis for
non-linear systems," Automatica 34(6), 1998. G. Russo, M. di Bernardo, E. D. Sontag, "A contraction
approach to the hierarchical analysis and design of networked systems," IEEE TAC 58(5), 2013.
Z. Aminzare, E. D. Sontag, "Synchronization of diffusively-connected nonlinear systems," IEEE TNSE
1(2), 2014. A. Davydov, F. Bullo, "Perspectives on Contractivity in Control, Optimization, and
Learning," arXiv:2404.11707, 2024 (states Hurwitz-Metzler = small-gain). W. Wang, J.-J. Slotine,
"Contraction analysis of time-delayed communications and group cooperation," IEEE TAC 51(4), 2006
(delay robustness).

*Cyclic small-gain.* S. Dashkovskiy, B. Ruffer, F. Wirth, "An ISS small gain theorem for general
networks," MCSS 19(2), 2007, and "Small gain theorems for large scale systems and construction of
ISS Lyapunov functions," SIAM J. Control Optim. 48(6), 2010 (per-cycle form exact in the max
formulation, Thm 8.14; general case is the operator / spectral-radius condition). T. Liu, D. Hill,
Z.-P. Jiang, "Lyapunov formulation of ISS cyclic-small-gain in continuous-time dynamical networks,"
Automatica 47(9), 2011.

*CBF deadlock (the corrected mechanism).* J. Grover, C. Liu, K. Sycara, "The Before, During, and
After of Multi-Robot Deadlock," IJRR 42(6), 2023 (deadlock = force-equilibrium on the safe-set
boundary; symmetry causes it; gain heterogeneity does not remove it), and "Why Does Symmetry Cause
Deadlocks?" IFAC-PapersOnLine 53(2), 2020. M. F. Reis, A. P. Aguiar, P. Tabuada, "Control Barrier
Function Based Quadratic Programs Introduce Undesirable Asymptotically Stable Equilibria," IEEE
CDC 2020 / Automatica 159, 2024. J. van den Berg, S. Guy, M. Lin, D. Manocha, "Reciprocal n-Body
Collision Avoidance" (ORCA), ISRR 2009. S. Sadat, R. Vaughan, "BRVO: Biased Reciprocal Velocity
Obstacles Break Symmetry," CRV 2012 (priority as the symmetry-breaking fix).

*Minimal coordination as a graph problem.* Even, Naor, Schieber, Sudan, "Approximating Minimum
Feedback Sets and Multicuts in Directed Graphs," Algorithmica 20(2), 1998 (subset feedback arc set;
O(log n log log n) approximation). Chen, Liu, Lu, O'Sullivan, Razgon, "A Fixed-Parameter Algorithm
for the Directed Feedback Vertex Set Problem," JACM 55(5), 2008 (FPT). Cygan, Pilipczuk, Pilipczuk,
"On Group Feedback Vertex Set Parameterized by the Size of the Cutset," Algorithmica, 2016 (group
feedback set; `Z_2` = odd-cycle transversal / edge bipartization). Aylward, Parrilo, Slotine,
"Stability and Robustness Analysis of Nonlinear Systems via Contraction Metrics and SOS
Programming," Automatica, 2008 (metric selection as SDP/SOS).

## Where this sits

- Proven, discrete: the two papers and [`coq/`](../coq); the map of regimes is [REGIMES.md](REGIMES.md).
- This note: the continuous *direction*, none of it established.
- The discrete/continuous boundary is a first-class scoping tool, not a limitation to paper over:
  the collapse is a discrete phenomenon, extends cleanly only to convex-potential continuous flows,
  and provably fails on the multi-basin systems that most physical "it converges" claims actually
  involve.
