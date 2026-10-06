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
