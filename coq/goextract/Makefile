# Generate the Go oracle from the Rocq extraction, and test it.
#   json  -- extract oracle_core.json and the prim-check pair (needs coqc)
#   gen   -- regenerate the committed Go from the committed JSON (needs go)
#   test  -- go vet and go test, then the regression and stress cases; with
#            OCAML=../extraction also the differential tests against the OCaml
#            checkers (build them first with make -C ../extraction)
GO ?= go
# The unary nat recursions gogen accepts, with the reason for each. UNARY=any
# accepts every one: only for a prover other than the pinned reference, whose
# standard library extracts differently (the provers CI job).
ALLOW = -allow-unary-file allow-unary.txt
ifeq ($(UNARY),any)
ALLOW = -allow-unary '*'
endif
COQC ?= coqc
OCAML ?=

.PHONY: all guard json gen build test clean

all: gen build

# The proof's own Makefile knows the dependencies (each .vo on its .v and on
# the modules it requires), so always ask it: a stale .vo is rebuilt, never
# reused.
.PHONY: proof
proof:
	$(MAKE) -C .. Trace.vo TableCheck.vo TableFast.vo TableFn.vo Checker.vo AstChecker.vo

ExtrGo.vo: ExtrGo.v
	cd .. && $(COQC) -Q . NC goextract/ExtrGo.v

PrimRef.vo: PrimRef.v
	cd .. && $(COQC) -Q . NC goextract/PrimRef.v

oracle_core.json: ExtractGo.v ExtrGo.vo proof
	cd .. && $(COQC) -Q . NC goextract/ExtractGo.v

primref_mapped.json: ExtractPrimMapped.v ExtrGo.vo PrimRef.vo
	cd .. && $(COQC) -Q . NC goextract/ExtractPrimMapped.v

primref_plain.json: ExtractPrimPlain.v PrimRef.vo
	cd .. && $(COQC) -Q . NC goextract/ExtractPrimPlain.v

Fixture.vo: Fixture.v
	cd .. && $(COQC) -Q . NC goextract/Fixture.v

fixture.json: ExtractFixture.v ExtrGo.vo Fixture.vo
	cd .. && $(COQC) -Q . NC goextract/ExtractFixture.v

# guard.sh refuses coinductive types and cofixpoints in everything gogen
# translates (GuardCoind.v); its self-test must refuse tests/coind/Coind.v.
guard: proof PrimRef.vo Fixture.vo Semantics.vo
	cd .. && bash goextract/guard.sh goextract/GuardCoind.v
	cd .. && ! bash goextract/guard.sh goextract/tests/coind/Coind.v >/dev/null

Semantics.vo: Semantics.v
	cd .. && $(COQC) -Q . NC goextract/Semantics.v

semantics.json: ExtractSemantics.v ExtrGo.vo Semantics.vo
	cd .. && $(COQC) -Q . NC goextract/ExtractSemantics.v

# Rocq's own values for Semantics.v, which semantics/semantics_test.go compares
# the generated Go with.
semantics/compute.out: SemanticsCompute.v Semantics.vo
	cd .. && $(COQC) -Q . NC goextract/SemanticsCompute.v 2>/dev/null > goextract/semantics/compute.out

json: guard oracle_core.json primref_mapped.json primref_plain.json fixture.json semantics.json semantics/compute.out

gen:
	$(GO) run ./gogen -pkg oracle $(ALLOW) -o oracle/oracle_gen.go oracle_core.json
	$(GO) run ./gogen -pkg mapped $(ALLOW) -o primcheck/mapped/primref_gen.go primref_mapped.json
	$(GO) run ./gogen -pkg plain $(ALLOW) -o primcheck/plain/primref_gen.go primref_plain.json
	$(GO) run ./gogen -pkg fixture $(ALLOW) -o fixture/fixture_gen.go fixture.json
	$(GO) run ./gogen -pkg semantics $(ALLOW) -o semantics/semantics_gen.go semantics.json

build:
	$(GO) build -o bin/tablecheck ./cmd/tablecheck
	$(GO) build -o bin/rulecheck ./cmd/rulecheck

test: build
	$(GO) vet ./...
	$(GO) test ./...
	bash tests/run.sh $(OCAML)

clean:
	rm -rf bin *.vo *.vok *.vos *.glob .*.aux
