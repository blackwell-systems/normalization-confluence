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

# The 3-SAT reduction for lossy networks: correctness, parsimony and size (LossyHardness.v).
all: LossyHardness.vo

LossyHardness.vo: LossyHardness.v CohomologyGraph.vo CohomologyGeneral.vo RootSet.vo
	coqc -Q . NC LossyHardness.v
