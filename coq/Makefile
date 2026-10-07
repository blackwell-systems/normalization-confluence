# Build the mechanized confluence proof. Requires coqc (Rocq/Coq >= 8.18; tested on Rocq 9.3).
all: Newman.vo Governance.vo Defensibility.vo Gsm.vo Federation.vo Chaotic.vo Checker.vo Trace.vo TableCheck.vo TableFast.vo TableFn.vo AstChecker.vo AstTables.vo AstCompact.vo CRDT.vo Categorical.vo Cohomology.vo CohomologyMin.vo CohomologyGraph.vo FederationOrder.vo CausalReplay.vo GovernanceCausal.vo FederationEvents.vo GovernanceWF.vo ChaoticACC.vo FederationEventsCycles.vo FederationEventsConverse.vo GovernanceConverse.vo

Newman.vo: Newman.v
	coqc -Q . NC Newman.v

Governance.vo: Governance.v Newman.vo
	coqc -Q . NC Governance.v

Defensibility.vo: Defensibility.v Governance.vo
	coqc -Q . NC Defensibility.v

Gsm.vo: Gsm.v Newman.vo
	coqc -Q . NC Gsm.v

Federation.vo: Federation.v
	coqc -Q . NC Federation.v

Chaotic.vo: Chaotic.v Newman.vo
	coqc -Q . NC Chaotic.v

Checker.vo: Checker.v
	coqc -Q . NC Checker.v

Trace.vo: Trace.v
	coqc -Q . NC Trace.v

TableCheck.vo: TableCheck.v Trace.vo
	coqc -Q . NC TableCheck.v

TableFast.vo: TableFast.v TableCheck.vo Trace.vo
	coqc -Q . NC TableFast.v

TableFn.vo: TableFn.v TableFast.vo TableCheck.vo Trace.vo
	coqc -Q . NC TableFn.v

AstChecker.vo: AstChecker.v Checker.vo Trace.vo TableCheck.vo
	coqc -Q . NC AstChecker.v

AstTables.vo: AstTables.v AstChecker.vo TableFn.vo TableFast.vo TableCheck.vo Trace.vo
	coqc -Q . NC AstTables.v

AstCompact.vo: AstCompact.v AstTables.vo AstChecker.vo TableFn.vo TableFast.vo TableCheck.vo Trace.vo
	coqc -Q . NC AstCompact.v

CRDT.vo: CRDT.v Checker.vo
	coqc -Q . NC CRDT.v

Categorical.vo: Categorical.v
	coqc -Q . NC Categorical.v

Cohomology.vo: Cohomology.v
	coqc -Q . NC Cohomology.v

CohomologyMin.vo: CohomologyMin.v Cohomology.vo
	coqc -Q . NC CohomologyMin.v

CohomologyGraph.vo: CohomologyGraph.v
	coqc -Q . NC CohomologyGraph.v

FederationOrder.vo: FederationOrder.v
	coqc -Q . NC FederationOrder.v

CausalReplay.vo: CausalReplay.v Trace.vo
	coqc -Q . NC CausalReplay.v

GovernanceCausal.vo: GovernanceCausal.v Newman.vo
	coqc -Q . NC GovernanceCausal.v

FederationEvents.vo: FederationEvents.v Trace.vo
	coqc -Q . NC FederationEvents.v

GovernanceWF.vo: GovernanceWF.v Newman.vo Governance.vo GovernanceCausal.vo
	coqc -Q . NC GovernanceWF.v

ChaoticACC.vo: ChaoticACC.v Newman.vo Federation.vo Chaotic.vo
	coqc -Q . NC ChaoticACC.v

FederationEventsCycles.vo: FederationEventsCycles.v Trace.vo Federation.vo
	coqc -Q . NC FederationEventsCycles.v

FederationEventsConverse.vo: FederationEventsConverse.v FederationEvents.vo Trace.vo
	coqc -Q . NC FederationEventsConverse.v

GovernanceConverse.vo: GovernanceConverse.v Newman.vo Governance.vo Trace.vo CausalReplay.vo
	coqc -Q . NC GovernanceConverse.v

# Print the assumption base of the main results (expect: "Closed under the global context").
check: all
	@printf 'Require Import NC.Newman NC.Governance NC.Defensibility.\nPrint Assumptions governance_confluent.\nPrint Assumptions example_confluent.\n' > _check.v
	@coqc -Q . NC _check.v 2>/dev/null | grep -v '^$$'
	@rm -f _check.v _check.vo .*.aux

clean:
	rm -f *.vo *.vok *.vos *.glob .*.aux _check.v

# At-least-once delivery (AtLeastOnce.v).
all: AtLeastOnce.vo

AtLeastOnce.vo: AtLeastOnce.v Trace.vo CausalReplay.vo
	coqc -Q . NC AtLeastOnce.v

# Coordinated cycles (CoordinatedCycles.v).
all: CoordinatedCycles.vo

CoordinatedCycles.vo: CoordinatedCycles.v CohomologyGraph.vo FederationOrder.vo FederationEvents.vo
	coqc -Q . NC CoordinatedCycles.v

# Verification calculus for CC (Calculus.v).
all: Calculus.vo

Calculus.vo: Calculus.v
	coqc -Q . NC Calculus.v

# Monotone federation (MonotoneFederation.v, WP6).
all: MonotoneFederation.vo

MonotoneFederation.vo: MonotoneFederation.v Newman.vo Federation.vo Chaotic.vo ChaoticACC.vo Trace.vo FederationEventsCycles.vo
	coqc -Q . NC MonotoneFederation.v

# General-map cohomology (CohomologyGeneral.v).
all: CohomologyGeneral.vo

CohomologyGeneral.vo: CohomologyGeneral.v Cohomology.vo CohomologyGraph.vo CoordinatedCycles.vo FederationOrder.vo
	coqc -Q . NC CohomologyGeneral.v

# Stream processors and the Stream Convergence Theorem (Stream.v).
all: Stream.vo

Stream.vo: Stream.v Newman.vo GovernanceCausal.vo GovernanceWF.vo
	coqc -Q . NC Stream.v

# The papers' concrete examples (PaperInstances.v).
all: PaperInstances.vo

PaperInstances.vo: PaperInstances.v Newman.vo Governance.vo GovernanceConverse.vo FederationEvents.vo Trace.vo
	coqc -Q . NC PaperInstances.v

# rho* constructed from WFC and the base facts on it (RhoStar.v, WP1).
all: RhoStar.vo

RhoStar.vo: RhoStar.v Newman.vo Governance.vo GovernanceCausal.vo GovernanceWF.vo GovernanceConverse.vo Categorical.vo
	coqc -Q . NC RhoStar.v

# Categorical bridge (CategoricalBridge.v).
all: CategoricalBridge.vo

CategoricalBridge.vo: CategoricalBridge.v Categorical.vo FederationOrder.vo
	coqc -Q . NC CategoricalBridge.v

# Event order on monotone cycles, checked per event (FederationEventsCyclesCheck.v).
all: FederationEventsCyclesCheck.vo

FederationEventsCyclesCheck.vo: FederationEventsCyclesCheck.v FederationEventsCycles.vo Federation.vo Trace.vo
	coqc -Q . NC FederationEventsCyclesCheck.v

# The federated GRS and the federated theorems in corrected form (FederationGRS.v).
all: FederationGRS.vo

FederationGRS.vo: FederationGRS.v Newman.vo Governance.vo Trace.vo FederationEvents.vo FederationEventsConverse.vo GovernanceConverse.vo
	coqc -Q . NC FederationGRS.v

# Compositional collapse: sub-federations as effective registries (Collapse.v).
all: Collapse.vo

Collapse.vo: Collapse.v Newman.vo Governance.vo Trace.vo FederationEvents.vo FederationEventsConverse.vo GovernanceConverse.vo FederationGRS.vo
	coqc -Q . NC Collapse.v

# Per-edge C1 composes on multi-edge targets (FederationEventsCyclesMulti.v).
all: FederationEventsCyclesMulti.vo

FederationEventsCyclesMulti.vo: FederationEventsCyclesMulti.v FederationEventsCyclesCheck.vo FederationEventsCycles.vo Federation.vo Trace.vo
	coqc -Q . NC FederationEventsCyclesMulti.v

# Monotone cycles: exact validity and exact reachability of the lfp (MonotoneExact.v).
all: MonotoneExact.vo

MonotoneExact.vo: MonotoneExact.v Newman.vo Federation.vo Chaotic.vo ChaoticACC.vo FederationEventsCycles.vo MonotoneFederation.vo
	coqc -Q . NC MonotoneExact.v

# The exact condition for stream agreement (StreamExact.v).
all: StreamExact.vo

StreamExact.vo: StreamExact.v Newman.vo Governance.vo GovernanceCausal.vo GovernanceWF.vo GovernanceConverse.vo Stream.vo
	coqc -Q . NC StreamExact.v

# The exact converses over any well-founded order (GovernanceWFConverse.v).
all: GovernanceWFConverse.vo

GovernanceWFConverse.vo: GovernanceWFConverse.v Newman.vo Governance.vo GovernanceWF.vo GovernanceConverse.vo RhoStar.vo
	coqc -Q . NC GovernanceWFConverse.v

# Rootless propagation on invertible cycles (RootlessCycles.v).
all: RootlessCycles.vo

RootlessCycles.vo: RootlessCycles.v CohomologyGraph.vo CoordinatedCycles.vo FederationOrder.vo Cohomology.vo
	coqc -Q . NC RootlessCycles.v

# Exact event-order condition under the coordination plan (CoordinatedExact.v).
all: CoordinatedExact.vo

CoordinatedExact.vo: CoordinatedExact.v Trace.vo CohomologyGraph.vo FederationOrder.vo FederationEvents.vo FederationEventsConverse.vo CoordinatedCycles.vo
	coqc -Q . NC CoordinatedExact.v

# The exact condition for at-least-once delivery, free and causal (AtLeastOnceExact.v).
all: AtLeastOnceExact.vo

AtLeastOnceExact.vo: AtLeastOnceExact.v Trace.vo CausalReplay.vo AtLeastOnce.vo GovernanceConverse.vo
	coqc -Q . NC AtLeastOnceExact.v

# The root-set criterion for lossy networks without a spanning root (RootSet.v).
all: RootSet.vo

RootSet.vo: RootSet.v CohomologyGraph.vo CohomologyGeneral.vo
	coqc -Q . NC RootSet.v

# State-based CRDT merges as an instance of the exact theorems (CvRDTExact.v).
all: CvRDTExact.vo

CvRDTExact.vo: CvRDTExact.v Newman.vo Trace.vo Governance.vo GovernanceConverse.vo GovernanceWFConverse.vo Checker.vo CRDT.vo CausalReplay.vo AtLeastOnce.vo AtLeastOnceExact.vo
	coqc -Q . NC CvRDTExact.v

# The 3-SAT reduction for lossy networks: correctness, parsimony and size (LossyHardness.v).
all: LossyHardness.vo

LossyHardness.vo: LossyHardness.v CohomologyGraph.vo CohomologyGeneral.vo RootSet.vo
	coqc -Q . NC LossyHardness.v

# The exact event-order condition under root-set coordination (RootSetEvents.v).
all: RootSetEvents.vo

RootSetEvents.vo: RootSetEvents.v CohomologyGraph.vo CohomologyGeneral.vo Trace.vo FederationOrder.vo FederationEvents.vo FederationEventsConverse.vo CoordinatedCycles.vo CoordinatedExact.vo RootSet.vo
	coqc -Q . NC RootSetEvents.v

# Exact confluence when compensation may disable a buffered event (EnabledAfterComp.v).
all: EnabledAfterComp.vo

EnabledAfterComp.vo: EnabledAfterComp.v Newman.vo Governance.vo GovernanceConverse.vo GovernanceWFConverse.vo
	coqc -Q . NC EnabledAfterComp.v

# The exact condition for the distributed model with propagation steps (DistributedExact.v).
all: DistributedExact.vo

DistributedExact.vo: DistributedExact.v Trace.vo FederationEvents.vo FederationEventsConverse.vo FederationGRS.vo
	coqc -Q . NC DistributedExact.v

# The distributed propagation model on monotone cycles (DistributedCycles.v).
all: DistributedCycles.vo

DistributedCycles.vo: DistributedCycles.v Trace.vo Federation.vo FederationEventsCycles.vo FederationEventsCyclesCheck.vo
	coqc -Q . NC DistributedCycles.v

# The no-reset distributed model on monotone cycles, exactly (DistributedCyclesExact.v).
all: DistributedCyclesExact.vo

DistributedCyclesExact.vo: DistributedCyclesExact.v Trace.vo Federation.vo FederationEventsCycles.vo FederationEventsCyclesCheck.vo DistributedCycles.vo
	coqc -Q . NC DistributedCyclesExact.v

# The CRDT boundary theorem and the sharpened strictness witness (CRDTBoundary.v).
all: CRDTBoundary.vo

CRDTBoundary.vo: CRDTBoundary.v Trace.vo CRDT.vo CausalReplay.vo GovernanceConverse.vo CvRDTExact.vo
	coqc -Q . NC CRDTBoundary.v

# The positive sheaf assembly over sub-federation covers (SheafGluing.v).
all: SheafGluing.vo

SheafGluing.vo: SheafGluing.v Categorical.vo FederationOrder.vo CategoricalBridge.vo Cohomology.vo FederationEvents.vo Collapse.vo
	coqc -Q . NC SheafGluing.v

# Minimum coordination tied to the authority-root plan model; the Max-Cut reduction (CoordinationMinimum.v).
all: CoordinationMinimum.vo

CoordinationMinimum.vo: CoordinationMinimum.v CohomologyGraph.vo CoordinatedCycles.vo CohomologyGeneral.vo
	coqc -Q . NC CoordinationMinimum.v

# H^1 of the nerve as a 2-complex: triangle relations, classification and Z/2 count (CohomologyNerve.v).
all: CohomologyNerve.vo

CohomologyNerve.vo: CohomologyNerve.v CohomologyGraph.vo
	coqc -Q . NC CohomologyNerve.v

# Minimum coordination for lossy networks: characterization, decision, hardness (LossyMinimum.v).
all: LossyMinimum.vo

LossyMinimum.vo: LossyMinimum.v CohomologyGraph.vo CohomologyGeneral.vo RootSet.vo LossyHardness.vo
	coqc -Q . NC LossyMinimum.v

# Experimental (validation in progress): the canonical-execution meta-theory and its six
# validation criteria (CanonicalExecution.v, CanonicalInstances.v).
all: CanonicalExecution.vo CanonicalInstances.vo

CanonicalExecution.vo: CanonicalExecution.v Newman.vo GovernanceConverse.vo GovernanceWFConverse.vo RhoStar.vo
	coqc -Q . NC CanonicalExecution.v

CanonicalInstances.vo: CanonicalInstances.v CanonicalExecution.vo Newman.vo Trace.vo CausalReplay.vo Governance.vo GovernanceConverse.vo GovernanceWFConverse.vo EnabledAfterComp.vo AtLeastOnce.vo AtLeastOnceExact.vo GovernanceCausal.vo Stream.vo StreamExact.vo FederationEvents.vo FederationEventsConverse.vo Federation.vo FederationEventsCycles.vo FederationEventsCyclesCheck.vo DistributedExact.vo DistributedCycles.vo DistributedCyclesExact.vo
	coqc -Q . NC CanonicalInstances.v

# Experimental (validation in progress): the P layer of the canonical-execution experiment,
# interaction locality as a factorization through a composition boundary (CanonicalLocality.v).
all: CanonicalLocality.vo

CanonicalLocality.vo: CanonicalLocality.v CanonicalExecution.vo CanonicalInstances.vo Trace.vo FederationEvents.vo FederationEventsConverse.vo FederationEventsCycles.vo FederationEventsCyclesCheck.vo SheafGluing.vo
	coqc -Q . NC CanonicalLocality.v

# Signed cycles: the invertible-versus-lossy separation on walks, Harary balance at Z/2
# (SignedCycles.v), and the signed-cycle to E bridge for resolver networks (SignedResolver.v).
all: SignedCycles.vo SignedResolver.vo

SignedCycles.vo: SignedCycles.v CohomologyGraph.vo CohomologyGeneral.vo RootSet.vo LossyMinimum.vo
	coqc -Q . NC SignedCycles.v

SignedResolver.vo: SignedResolver.v CohomologyGraph.vo CohomologyGeneral.vo SignedCycles.vo FederationEventsCycles.vo DistributedCycles.vo DistributedCyclesExact.vo CanonicalExecution.vo
	coqc -Q . NC SignedResolver.v

# Local (state-dependent) interaction graphs of Boolean resolver networks: local fidelity
# (Remy, Ruet and Thieffry), local settlement (Richard 2011, Theorems 3 and 4; Shih and Dong),
# and their counterexamples (LocalSigned.v).
all: LocalSigned.vo

LocalSigned.vo: LocalSigned.v CohomologyGraph.vo SignedCycles.vo DistributedCycles.vo CanonicalExecution.vo SignedResolver.vo
	coqc -Q . NC LocalSigned.v

# Convergence among quiescent interleavings alone on monotone cycles without resets: the exact
# condition with the propagation dynamics' own canonical state (DistributedConvergenceExact.v).
all: DistributedConvergenceExact.vo

DistributedConvergenceExact.vo: DistributedConvergenceExact.v Trace.vo Federation.vo FederationEventsCycles.vo FederationEventsCyclesCheck.vo DistributedCycles.vo DistributedCyclesExact.vo
	coqc -Q . NC DistributedConvergenceExact.v

# Rootless propagation on arbitrary finite invertible networks: the reachable set, existence from
# every start, uniqueness, and the unique normal form, exactly (RootlessNetworks.v).
all: RootlessNetworks.vo

RootlessNetworks.vo: RootlessNetworks.v CohomologyGraph.vo RootlessCycles.vo
	coqc -Q . NC RootlessNetworks.v

# Fair asynchronous settlement under local conditions (gap 3): the synchronous orbit theorem
# (Shih and Ho 1999, Theorem 3.1, with (A) needed only on the orbit), token monotonicity, the
# single-token lemma, and fair settlement from acyclicity (LocalFairSettlement.v).
all: LocalFairSettlement.vo

LocalFairSettlement.vo: LocalFairSettlement.v DistributedCycles.vo CanonicalExecution.vo SignedResolver.vo LocalSigned.vo
	coqc -Q . NC LocalFairSettlement.v

# No closed asynchronous run with two unstable vertices under no local cycle plus out-degree at
# most one, hence fair settlement from at most two tokens (gap 3 progress, LocalTwoToken.v).
all: LocalTwoToken.vo

LocalTwoToken.vo: LocalTwoToken.v DistributedCycles.vo CanonicalExecution.vo SignedResolver.vo LocalSigned.vo LocalFairSettlement.vo
	coqc -Q . NC LocalTwoToken.v

# The imbalance law: under out-degree at most one, at most half of the tokens are bad relative to
# a fixed point (b <= g, for every number of tokens; gap 3 progress, LocalTokenBalance.v).
all: LocalTokenBalance.vo

LocalTokenBalance.vo: LocalTokenBalance.v DistributedCycles.vo CanonicalExecution.vo SignedResolver.vo LocalSigned.vo LocalFairSettlement.vo LocalTwoToken.vo
	coqc -Q . NC LocalTokenBalance.v

# At-least-once delivery under declared independence I: the exact condition, the per-event form,
# unordered retries, and gsm's NotIdempotent under I (gap 15 (a), AtLeastOnceDeclared.v).
all: AtLeastOnceDeclared.vo

AtLeastOnceDeclared.vo: AtLeastOnceDeclared.v Trace.vo CausalReplay.vo AtLeastOnce.vo AtLeastOnceExact.vo GovernanceConverse.vo
	coqc -Q . NC AtLeastOnceDeclared.v

# Propagation over channels that deliver projections late, reordered or duplicated: plain and
# versioned merge, the exact condition over channels, convergence at drain, the two-level
# emulation, and the counterexamples (gap 21, ProjectionChannels.v).
all: ProjectionChannels.vo

ProjectionChannels.vo: ProjectionChannels.v Trace.vo FederationEvents.vo FederationEventsConverse.vo FederationGRS.vo DistributedExact.vo
	coqc -Q . NC ProjectionChannels.v

# At-least-once delivery for stream processors: delivery classes of received lists, the exact
# condition for any enabledness and the local one under free delivery (gap 15 (b),
# StreamAtLeastOnce.v).
all: StreamAtLeastOnce.vo

StreamAtLeastOnce.vo: StreamAtLeastOnce.v Newman.vo GovernanceCausal.vo GovernanceWF.vo Stream.vo StreamExact.vo Trace.vo AtLeastOnce.vo AtLeastOnceExact.vo GovernanceConverse.vo
	coqc -Q . NC StreamAtLeastOnce.v

# Buffered guards in acyclic federations: JC' for any enabledness, and the local exact condition
# for events that wait under the federal guard (gap 15 (d), FederatedGuards.v).
all: FederatedGuards.vo

FederatedGuards.vo: FederatedGuards.v Newman.vo Governance.vo GovernanceConverse.vo EnabledAfterComp.vo FederationEvents.vo FederationEventsConverse.vo FederationGRS.vo
	coqc -Q . NC FederatedGuards.v

# Causal and at-least-once event delivery in the distributed model: the exact condition for any
# delivery class, and the causal, free and causal at-least-once instances (gap 15 (c),
# DistributedDelivery.v).
all: DistributedDelivery.vo

DistributedDelivery.vo: DistributedDelivery.v Trace.vo CausalReplay.vo AtLeastOnce.vo AtLeastOnceExact.vo FederationEvents.vo FederationEventsConverse.vo DistributedExact.vo GovernanceConverse.vo
	coqc -Q . NC DistributedDelivery.v

# Robert's theorem for fair asynchronous schedules on acyclic networks: the distributed
# propagation model, events, the resolver model and the Boolean global-graph form (gap 16 (d),
# RobertFair.v).
all: RobertFair.vo

RobertFair.vo: RobertFair.v Trace.vo FederationEvents.vo FederationEventsConverse.vo FederationGRS.vo FederationOrder.vo DistributedExact.vo DistributedCycles.vo DistributedCyclesExact.vo CanonicalExecution.vo SignedResolver.vo LocalSigned.vo LocalFairSettlement.vo
	coqc -Q . NC RobertFair.v

# Reconfiguration inside a run: a switch from configuration A to configuration B with events in
# flight; the barrier and live exact conditions, the classification behind gsm's CheckMigration,
# and federation topology changes under FedMachine semantics (gap 20, Reconfiguration.v).
all: Reconfiguration.vo

Reconfiguration.vo: Reconfiguration.v Newman.vo Governance.vo GovernanceConverse.vo Trace.vo FederationEvents.vo FederationEventsConverse.vo
	coqc -Q . NC Reconfiguration.v

# Symmetry reduction for keyed collections: independent, identically governed items; each
# convergence condition holds for any number of items iff at a cutoff of one item (two for CC1
# alone) (roadmap item 8, step 1, SymmetryCutoff.v).
all: SymmetryCutoff.vo

SymmetryCutoff.vo: SymmetryCutoff.v Newman.vo Governance.vo GovernanceConverse.vo Trace.vo AtLeastOnce.vo AtLeastOnceExact.vo
	coqc -Q . NC SymmetryCutoff.v

# Abstraction for checking: rules that compare values and declared constants are decided over a
# finite set of representatives (one per order type), and linear rules through generated
# formulas whose validity is exact for each condition (roadmap item 8, step 2, AbstractionCutoff.v).
all: AbstractionCutoff.vo

AbstractionCutoff.vo: AbstractionCutoff.v Newman.vo Governance.vo GovernanceConverse.vo SymmetryCutoff.vo
	coqc -Q . NC AbstractionCutoff.v

# The gsm instantiation of abstraction: CC1 at the valid states and idempotence transfer from the
# representatives to every integer, the repair-first registry stays in the fragment, and gsm's
# runtime converges from every integer state (roadmap item 8, step 2, AbstractionGsm.v).
all: AbstractionGsm.vo

AbstractionGsm.vo: AbstractionGsm.v Newman.vo Governance.vo SymmetryCutoff.vo AbstractionCutoff.vo Trace.vo
	coqc -Q . NC AbstractionGsm.v

# Compositional checking by default: each footprint component is checked on its own subspace; WFC
# and gsm's guarantee (CC1 on valid states) hold for the registry iff for every component, with
# reads in the footprint and repair inside its component (roadmap item 8, step 3,
# CompositionalCheck.v).
all: CompositionalCheck.vo

CompositionalCheck.vo: CompositionalCheck.v AstChecker.vo Checker.vo Trace.vo TableCheck.vo
	coqc -Q . NC CompositionalCheck.v

# The barrier's A part without injectivity: A converges modulo the migration iff every pair of
# the closure of adjacent swaps under common continuations has equal images, decided on finite
# instances, so the barrier outcome is exact (gap 20 residue (c), ReconfigurationClosure.v).
all: ReconfigurationClosure.vo

ReconfigurationClosure.vo: ReconfigurationClosure.v Newman.vo GovernanceConverse.vo Trace.vo Reconfiguration.vo
	coqc -Q . NC ReconfigurationClosure.v

# Difference constraints with saturating writes: CC1, repair within K steps, idempotence and gsm's
# runtime guarantee over the declared ranges iff over the states within n(W + 1) of an anchor, W the
# guard constants plus the chained offsets (roadmap item 8 step 2, DifferenceAbstraction.v).
all: DifferenceAbstraction.vo

DifferenceAbstraction.vo: DifferenceAbstraction.v Newman.vo Governance.vo SymmetryCutoff.vo AbstractionCutoff.vo Trace.vo
	coqc -Q . NC DifferenceAbstraction.v

# Events with equal governed steps are checked once: a check over any list of parameter
# assignments that covers the representative ones returns the full check's boolean; with gsm's
# range test conjoined to the guard, every out-of-range assignment is repair alone, so gsm's list
# (in-range assignments plus one out-of-range) decides CC1 and idempotence over Z (EventCollapse.v).
all: EventCollapse.vo

EventCollapse.vo: EventCollapse.v Newman.vo Governance.vo SymmetryCutoff.vo AbstractionCutoff.vo Trace.vo AbstractionGsm.vo
	coqc -Q . NC EventCollapse.v

# Composition beyond acyclic collapse: the exact interface theorem for blocks of any engines, its
# interleaving conjunct, the cyclic monotone J by Bekic's principle (gap 5), and collapse in the
# distributed model (gap 19, CompositionBlocks.v).
all: CompositionBlocks.vo

CompositionBlocks.vo: CompositionBlocks.v Trace.vo Federation.vo FederationEvents.vo FederationEventsConverse.vo FederationGRS.vo DistributedExact.vo Collapse.vo FederationEventsCycles.vo DistributedCycles.vo CohomologyGraph.vo RootlessCycles.vo RootlessNetworks.vo
	coqc -Q . NC CompositionBlocks.v

# Difference constraints for events with integer parameters: parameters as read-only coordinates of
# the joint state, exact parameters (x := x - p, reserved + q <= stock) read as their values and
# paid in the threshold; CC1, idempotence, repair and gsm's runtime guarantee over the joint
# representatives (roadmap item 8, DifferenceParams.v).
all: DifferenceParams.vo

DifferenceParams.vo: DifferenceParams.v Newman.vo Governance.vo SymmetryCutoff.vo AbstractionCutoff.vo Trace.vo DifferenceAbstraction.vo
	coqc -Q . NC DifferenceParams.v
# Reconfiguration under a delivery class: declared independence, causal and at-least-once delivery
# across the switch, live and at a barrier, decided on finite instances (gap 20 residue (b),
# ReconfigurationDelivery.v).
all: ReconfigurationDelivery.vo

ReconfigurationDelivery.vo: ReconfigurationDelivery.v Newman.vo Trace.vo CausalReplay.vo AtLeastOnce.vo AtLeastOnceExact.vo AtLeastOnceDeclared.vo GovernanceConverse.vo Reconfiguration.vo ReconfigurationClosure.vo DistributedDelivery.vo
	coqc -Q . NC ReconfigurationDelivery.v
# Versioned projection channels beyond two-level networks: on nested networks (every single-source
# network among them) every channel state is a current-value state, so dist_exact's condition is
# exact; a four-registry network outside the class where it fails (gap 21 residue (a),
# ProjectionChains.v).
all: ProjectionChains.vo

ProjectionChains.vo: ProjectionChains.v Trace.vo FederationEvents.vo FederationEventsConverse.vo FederationGRS.vo DistributedExact.vo ProjectionChannels.vo
	coqc -Q . NC ProjectionChains.v
# Layer A of the regime map, the execution algebra: a presented admissible path system (whiskered
# generator squares); P2 (invariance iff the continuation closure agrees) and P1 (generators suffice
# locally when the semantics respects the future); six existing exact theorems recovered
# (PresentedExecution.v).
all: PresentedExecution.vo

PresentedExecution.vo: PresentedExecution.v Newman.vo Trace.vo CanonicalExecution.vo CausalReplay.vo GovernanceConverse.vo ReconfigurationClosure.vo CanonicalInstances.vo AtLeastOnce.vo AtLeastOnceExact.vo AtLeastOnceDeclared.vo Reconfiguration.vo
	coqc -Q . NC PresentedExecution.v


# Static consistency as a CSP: sections of a transport network are the solutions of a CSP instance
# over Gamma_F, Pol(Gamma_F) is the centralizer of F, the reduction's 26-map family, and arc
# consistency deciding monotone transports on finite chains (TransportCSP.v).
all: TransportCSP.vo

TransportCSP.vo: TransportCSP.v CohomologyGraph.vo CohomologyGeneral.vo RootSet.vo LossyHardness.vo
	coqc -Q . NC TransportCSP.v

# gsm's migration check under a delivery class, its two own-argument steps: the declared closure
# search pruned to one orientation per declared pair (exact for a symmetric relation, and for any
# relation once symmetrized), and at-least-once delivery with repeated submissions (gsm's checks at
# every reachable state are the exact conditions; ReconfigurationGsm.v).
all: ReconfigurationGsm.vo

ReconfigurationGsm.vo: ReconfigurationGsm.v Newman.vo Trace.vo AtLeastOnce.vo AtLeastOnceExact.vo Reconfiguration.vo ReconfigurationClosure.vo ReconfigurationDelivery.vo
	coqc -Q . NC ReconfigurationGsm.v

# The predicted hard cell: monotone transports on the diamond (six maps reading one flag, the AND
# or the OR of two flags, or a constant) are NP-complete by a 3-SAT reduction, and every
# polymorphism of their template is a projection (TransportCSPHard.v).
all: TransportCSPHard.vo

TransportCSPHard.vo: TransportCSPHard.v CohomologyGraph.vo CohomologyGeneral.vo RootSet.vo LossyHardness.vo TransportCSP.vo
	coqc -Q . NC TransportCSPHard.v

# Layer C, settlement dynamics as fair recurrence: on a finite state type, every fair schedule
# settles in a canonical fiber iff no fair lasso has a loop state outside it (CanonicalRecurrence.v).
all: CanonicalRecurrence.vo

CanonicalRecurrence.vo: CanonicalRecurrence.v Newman.vo DistributedCycles.vo Chaotic.vo CohomologyGraph.vo SignedCycles.vo CanonicalExecution.vo DistributedCyclesExact.vo SignedResolver.vo
	coqc -Q . NC CanonicalRecurrence.v
