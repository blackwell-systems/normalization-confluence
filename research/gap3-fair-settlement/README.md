# Gap 3: fair settlement under local acyclicity plus out-degree at most one

Computational evidence, **not mechanized and not proved**. It is recorded here so that the search
can be reproduced. Nothing in this directory is in the axiom-free gate.

**Question.** A Boolean network may have no cycle in any local interaction graph G(x) (condition
(A), `NoLocalCycle` in `coq/LocalSigned.v`) and out-degree at most 1 in every G(x) (condition (B),
`OutDeg1`, which is non-expansiveness by `outdeg_nonexpansive`). Does every fair asynchronous
schedule then settle?

**Finding.** For n = 3, 4, 5 and 6, no network satisfying (A) and (B) has any cycle in its
asynchronous state graph. So every schedule, fair or not, reaches the unique fixed point from
every start.
- **How it was checked:** exhaustive SAT search at every n, plus brute force over all 2^24
  networks at n = 3.
- **Cross-checks:** two independent encodings and three solvers agree. Dropping (B), or relaxing
  (A) to "no self-loops", makes the solver find cycles at once, and each one is replayed by an
  independent checker (`verify.py`).
- **n = 7:** running at the time of writing.
- **General case:** open. The conjectured key lemma F2 is in `REPORT.md`, section 5.
- **Literature:** not found in the literature searched. Shih and Ho 1999 (Adv. Appl. Math.
  22(1):60-102) could not be read and may already cover this; see `REPORT.md`, section 3.

**Files.**

| File | Contents |
|---|---|
| `enc.py` | SAT encodings |
| `run.py`, `run_sym.py`, `run_strong.py` | search drivers |
| `z3check.py` | second encoding |
| `brute3.c` | n = 3 brute force |
| `verify.py` | plain checker |
| `localized.py` | (A) only on the cycle states |
| `f2_sat.py` | the F2 lemma |
| `n6s_*.log` | n = 6 solver logs |

**Reproduce.**
```
python3 -m venv .venv && .venv/bin/pip install python-sat z3-solver
.venv/bin/python run_strong.py 6 sym,tok,alldir cadical195
cc -O2 -o brute3 brute3.c && ./brute3
```
