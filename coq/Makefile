# Build the mechanized confluence proof. Requires coqc (Rocq/Coq >= 8.18; tested on Rocq 9.3).
all: Newman.vo Governance.vo

Newman.vo: Newman.v
	coqc -Q . NC Newman.v

Governance.vo: Governance.v Newman.vo
	coqc -Q . NC Governance.v

# Print the assumption base of the main theorems (expect: "Closed under the global context").
check: Governance.vo
	@printf 'Require Import NC.Newman NC.Governance.\nPrint Assumptions governance_confluent.\nPrint Assumptions governance_unique_normal_forms.\n' > _check.v
	@coqc -Q . NC _check.v 2>/dev/null | grep -v '^$$'
	@rm -f _check.v _check.vo .*.aux

clean:
	rm -f *.vo *.vok *.vos *.glob .*.aux _check.v
