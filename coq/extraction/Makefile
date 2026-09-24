# Build the verified convergence checkers: extract from Coq, compile with OCaml.
#   checker    -- table oracle: certifies a machine's emitted step tables converge.
#   astchecker -- rules oracle: certifies a combinator machine from its AST itself.
CHECKER = checker
ASTCHECKER = astchecker

all: $(CHECKER) $(ASTCHECKER)

../Checker.vo: ../Checker.v
	cd .. && coqc -Q . NC Checker.v

../AstChecker.vo: ../AstChecker.v ../Checker.vo
	cd .. && coqc -Q . NC AstChecker.v

# Both checkers extract from one Extract.v into the shared checker_core module.
checker_core.ml: Extract.v ../Checker.vo ../AstChecker.vo
	cd .. && coqc -Q . NC extraction/Extract.v

$(CHECKER): checker_core.ml main.ml
	ocamlfind ocamlopt checker_core.mli checker_core.ml main.ml -o $(CHECKER)

$(ASTCHECKER): checker_core.ml ast_main.ml
	ocamlfind ocamlopt checker_core.mli checker_core.ml ast_main.ml -o $(ASTCHECKER)

# Show the table oracle accepts a commuting machine and rejects a non-commuting one.
demo: $(CHECKER)
	@printf '4 2\n0 1 2 3\n0 1 2 3\n' > good.tables
	@printf '3 2\n1 1 1\n2 2 2\n' > bad.tables
	@echo "commuting:";     ./$(CHECKER) good.tables
	@echo "non-commuting:"; ./$(CHECKER) bad.tables || echo "(correctly rejected)"

# Show the rules oracle certifying a combinator machine straight from its AST: a is
# capped at 3 by compensation; inc_a, inc_b, raise_flag all commute on valid states.
astdemo: $(ASTCHECKER)
	@printf '(doms 6 6 2)\n(inv (le (var 0) (lit 3)) (do (set 0 (lit 3))))\n(ev (do (set 0 (add (var 0) (lit 1)))))\n(ev (do (set 1 (add (var 1) (lit 1)))))\n(ev (do (set 2 (lit 1))))\n' > good.machine
	@printf '(doms 6 6)\n(inv (le (var 0) (lit 3)) (do (set 0 (lit 3))))\n(ev (do (set 0 (add (var 0) (lit 1))) (set 1 (add (var 1) (lit 1)))))\n(ev (do (set 1 (lit 0))))\n' > bad.machine
	@echo "convergent rules:";     ./$(ASTCHECKER) good.machine
	@echo "non-convergent rules:"; ./$(ASTCHECKER) bad.machine || echo "(correctly rejected)"

clean:
	rm -f checker_core.ml checker_core.mli *.cmi *.cmx *.cmo *.o $(CHECKER) $(ASTCHECKER) \
		good.tables bad.tables good.machine bad.machine
