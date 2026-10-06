# Gap 3: fair settlement under local acyclicity plus out-degree at most one

Computational evidence for the general case, **not mechanized and not proved**. It is recorded here
so that the search can be reproduced. Nothing in this directory is in the axiom-free gate.

**Mechanized since (#92, `coq/LocalFairSettlement.v`, every n).** Part of the question is now
proved in Coq:
- **Synchronous form:** (B), with (A) at one state of a synchronous periodic orbit, makes the orbit
  a fixed point (`sync_orbit_fixed`). So under (A) and (B) every synchronous orbit reaches the
  unique fixed point (`sync_simple`, the conclusion of Shih and Ho 1999, Theorem 3.1).
- **Single-token lemma:** localized and with no fixed point used (`one_token_closed`), with token
  monotonicity (`ucnt_mono`). Hence every fair schedule from a start with at most one unstable
  vertex settles (`one_token_fair_settlement`).
- **Acyclicity gives fair settlement:** the report's step 4 (`fair_settlement_of_acyclic`).
- **Boundary instances:** `outdeg_needed`, `no_neg_not_enough`, `no_pos_not_enough`, and
  `shih_ho_instance`.

**Mechanized since (#93, `coq/LocalTwoToken.v`, every n): two tokens.** Under (A) and (B), no
closed asynchronous run from a state with at most two unstable vertices changes the state
(`two_token_closed`), so every fair schedule from such a start settles
(`two_token_fair_settlement`). The proof is not F2: with one token on each side of the fixed point
the token agreeing with it never points into the disagreement set (`head_arc`), and a closed run
rearranges into a synchronous orbit (`swap_TH`, `W_main`). The SAT decision for exactly two tokens
(n = 3 to 7), the invariants mined on the way and the ones that fail are in [K2.md](K2.md).

Still open: closed asynchronous runs with three or more unstable vertices at every state. For
three tokens a token agreeing with the fixed point can pass to one that disagrees (K2.md), so the
two-token argument does not apply as it stands. The three-token case is decided UNSAT by SAT for
n = 3 to 7; [K3.md](K3.md) records the decision, transition
statistics over 31,490 sampled moves, the proved structural lemmas (at most half the tokens are
bad; near-rigidity at one bad token; the critical pairs are exactly "same token" and "follow"),
every candidate order tried and how it fails, and the obstruction: normalizing a closed run into
synchronous rounds needs a per-token rate balance that is not proved. Gap 3 stays open.

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
- **General case:** open. The conjectured key lemma F2 is in `REPORT.md`, section 5. It is proved
  for one token, as the isometry argument inside `sync_orbit_fixed`, and open for two or more.
- **Literature:** not found in the literature searched. Shih and Ho 1999 (Adv. Appl. Math.
  22(1):60-102) has since been read in full and treats synchronous iteration only (its Theorem 3.1
  is the synchronous form above). `REPORT.md`, section 3, is kept as written at the time.

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
| `K2.md` | the two-token case: SAT decision, mined invariants, the proof in `LocalTwoToken.v` |
| `run_k2.py`, `k2_n7_*.log` | SAT search for closed runs with exactly two tokens, n = 7 logs |
| `sample.py`, `sample_rich.py` | samplers of (A)+(B) networks (random, or with a forced long two-token walk) |
| `mine.py`, `mine2.py` | candidate invariants on count-preserving two-token moves |
| `fals_good.py` | SAT test of "a bad token passes to a good receiver" |
| `checkproof.py` | the two-token proof steps on sampled instances |
| `K3.md` | the three-token case: SAT decision, transition statistics, candidate orders, the obstruction |
| `run_k3.py`, `k3_n3to6.log`, `k3_n7_cadical195_*.log` | SAT search for closed runs with exactly k tokens (k = 3 by default) |
| `fals_f12.py`, `check3.py`, `commute3.py` | the structural lemmas of K3.md, section 2 (SAT and samples) |
| `sample3.py`, `stats3.py`, `mine3.py`, `mine3_all.log` | three-token walk sampler, transition statistics, candidate orders |
| `episode.py`, `episodes.log` | SAT falsification of episode orders |
| `game.py`, `gamepot.py`, `gamelp.py`, `gamelong.py`, `gamecyc.py`, `realize.py`, `core.py`, `game_*.log` | the forest-plus-token relaxation, its n = 6 cycle, and why no network realizes it |
| `avar.py`, `signvar.py`, `localB.py`, `noconst.py`, `boxes.py` | which parts of (A) and (B) the claim uses; the box iteration |

**Reproduce.**
```
python3 -m venv .venv && .venv/bin/pip install python-sat z3-solver
.venv/bin/python run_strong.py 6 sym,tok,alldir cadical195
cc -O2 -o brute3 brute3.c && ./brute3
```
