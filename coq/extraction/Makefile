# Build the verified convergence checker: extract from Coq, compile with OCaml.
CHECKER = checker

all: $(CHECKER)

../Checker.vo: ../Checker.v
	cd .. && coqc -Q . NC Checker.v

checker_core.ml: Extract.v ../Checker.vo
	cd .. && coqc -Q . NC extraction/Extract.v

$(CHECKER): checker_core.ml main.ml
	ocamlfind ocamlopt checker_core.mli checker_core.ml main.ml -o $(CHECKER)

# Show it accepts a commuting machine and rejects a non-commuting one.
demo: $(CHECKER)
	@printf '4 2\n0 1 2 3\n0 1 2 3\n' > good.tables
	@printf '3 2\n1 1 1\n2 2 2\n' > bad.tables
	@echo "commuting:";     ./$(CHECKER) good.tables
	@echo "non-commuting:"; ./$(CHECKER) bad.tables || echo "(correctly rejected)"

clean:
	rm -f checker_core.ml checker_core.mli *.cmi *.cmx *.cmo *.o $(CHECKER) good.tables bad.tables
