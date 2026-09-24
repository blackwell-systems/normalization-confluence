# Build the mechanized confluence proof. Requires coqc (Rocq/Coq >= 8.18; tested on Rocq 9.3).
all: Newman.vo Governance.vo Defensibility.vo Gsm.vo Federation.vo Chaotic.vo Checker.vo AstChecker.vo CRDT.vo

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

AstChecker.vo: AstChecker.v Checker.vo
	coqc -Q . NC AstChecker.v

CRDT.vo: CRDT.v Checker.vo
	coqc -Q . NC CRDT.v

# Print the assumption base of the main results (expect: "Closed under the global context").
check: all
	@printf 'Require Import NC.Newman NC.Governance NC.Defensibility.\nPrint Assumptions governance_confluent.\nPrint Assumptions example_confluent.\n' > _check.v
	@coqc -Q . NC _check.v 2>/dev/null | grep -v '^$$'
	@rm -f _check.v _check.vo .*.aux

clean:
	rm -f *.vo *.vok *.vos *.glob .*.aux _check.v
