# Gap 3 (LossyNetworks P2): fair settlement under no local cycle plus out-degree at most one

Date: 2026-10-05. Scripts and n = 6 logs are in this directory; the original working names were `search/` (scripts) and `lit/` (preprints, not included).

## 1. Summary

**Setting.** The definitions are those of `coq/LocalSigned.v`:
- `larc x j i` holds exactly when `f_i(flip j x) <> f_i(x)`.
- Cycles are elementary, and a self-loop counts as a cycle of length 1.
- (A) is `NoLocalCycle js`.
- (B) is `OutDeg1 js`. This is the hypothesis of `richard_t3` (Richard 2011, Theorem 3), and it is equivalent to Hamming non-expansiveness by `outdeg_nonexpansive`.
- `Fair` follows `DistributedCycles.Fair`.
- `Settles` means the state is eventually constant.

**Main result.** For n = 3, 4, 5 and 6, no network satisfying (A) and (B) has a cycle in its asynchronous state graph. The search is exhaustive: SAT at every n, plus brute force at n = 3. An acyclic state graph means every run, fair or not, makes only finitely many changes. So for n up to 6, every fair schedule settles at the unique fixed point, from every start. Largest n fully decided: 6. The n = 7 runs were left undecided.

**The sketch.** Steps 1 and 2 are verified. Step 3 is corrected: a state-graph cycle does not by itself give a fair non-settling run. Step 4 is therefore sufficient but not equivalent. The stronger statement, acyclicity, still holds up to n = 6.

**Single-token lemma (proved).** Assume (B), no self-loops, and that a fixed point exists. Then no state-graph cycle has exactly one unstable vertex at each of its states.

**Localization.** Keep (B) and "no self-loops" at every state, but require (A) only at the states the cycle visits. No cycle exists at n = 3, 4 or 5. With (B) dropped, a cycle appears at n = 4. A proof may therefore need (A) only on the cycle.

**Conjectured key lemma, F2.** Take a network with (B) and no self-loops, a simple state-graph cycle, and U the set of vertices it flips. Then at every state x of the cycle, every u in U has an out-arc into U in G(x).
- Under F2, G(x) restricted to U is a functional graph. A functional graph has a cycle, which contradicts (A).
- F2 is exhaustively verified by SAT at n = 3 and n = 4, and holds on 52,382 sampled cycles at n = 4.
- At n = 5 the check timed out at 900 s and is undecided.

**Literature.** Neither the question nor the reduced acyclicity question was found in the literature searched.

## 2. The sketch, step by step

1. **Verified.** Firing an unstable v makes v stable, because there is no self-loop. For w <> v, w changes status exactly when v -> w is an arc of G(x), and (B) allows at most one such w. So the unstable count never increases: each move changes it by -1, 0 or -2. Only "no self-loops" is used from (A).
2. **Verified.** The count is eventually constant. Each real move then passes a token v -> w along an arc that lies in both G(x) and G(flip v x).
3. **Corrected.** A fair non-settling run always gives a state-graph cycle. The converse fails: a token can stay parked at an unstable vertex that never fires on the cycle, and fairness forces it to fire.
   - At n = 3 with (B) only, 12,431 networks have a cycle, but only 7,547 have a fair non-settling run.
   - The exact characterization used in the search: a strongly connected set C of states with an internal edge that covers every vertex. Covering means w is stable somewhere in C, or w fires inside C.
4. **Corrected to "sufficient".** Acyclicity implies fair settlement, but not conversely. The search ran both targets.

**Single-token lemma proof.** With exactly one unstable vertex, the asynchronous move is the synchronous step F. By `outdeg_nonexpansive`, d(F(x), p) <= d(x, p), where p is the fixed point given by `shih_dong_E`. So the distance is non-increasing around the cycle, hence constant on it. But each move changes it by exactly 1. Contradiction.

**Both signs of (A) are needed.**
- (B) plus no local negative cycle: the positive 3-ring has fair non-settling runs.
- (B) plus no local positive cycle: state-graph cycles exist at n = 3 to 5.

## 3. Literature (Crossref-verified)

**Read in full:**
- **Richard 2011.** Discrete Appl. Math. 159(11):1085-1093, doi:10.1016/j.dam.2011.01.010. Theorems 3 and 4 are `richard_t3` and `richard_t4`. It credits Shih and Ho 1999 (pp. 75-88) with: (A) plus out-degree at most 1 implies a fixed point. Nothing on the asynchronous state graph.
- **Richard 2019 survey.** J. Theor. Biol. 463:67-76, doi:10.1016/j.jtbi.2018.11.028. Under Shih-Dong alone, Robert's acyclicity is lost (4-component example). Nothing on (A) combined with non-expansiveness.
- **Richard 2015.** Theoret. Comput. Sci. 583:1-26, doi:10.1016/j.tcs.2015.03.038. Section 6 defines strong asynchronous convergence; Section 7 leaves its forbidden-subnetwork characterization open.
- **Ruet 2017.** Discrete Appl. Math. 221:1-17, doi:10.1016/j.dam.2017.01.001. Nothing on transient asynchronous cycles under (A) and (B).

**Read as metadata or abstract only:**
- Ruet, Math. Struct. Comput. Sci. 26(4) (2016) 702-718.
- Melliti, Regnault, Richard and Sené, LNCS 8155:124-138 (2013). Covers global graphs with no negative cycle, not local conditions.
- Tonello, Farcot and Chaouiya, SIAM J. Appl. Dyn. Syst. 18(1) (2019) 68-79.
- Shih and Dong, Adv. Appl. Math. 34(1) (2005) 30-46.
- Richard, Adv. Appl. Math. 41(4) (2008) 620-627.

**Unread (access blocked):** Shih and Ho, "Solution of the Boolean Markus-Yamabe problem", Adv. Appl. Math. 22(1) (1999) 60-102, doi:10.1006/aama.1998.0622. Its abstract poses global asymptotic stability under Hamming-distance and Jacobian-spectrum conditions. It may already answer this question if its result covers asynchronous updates.

## 4. Search method and results

**Solvers.** CaDiCaL 1.9.5, Glucose 4 and MapleChrono via python-sat, plus z3.

**Encodings (`search/enc.py`).**
- Truth-table variables, with arc variables a(x, j, i) = F[i][x] xor F[i][flip j x].
- (A): every elementary cycle is forbidden at every state.
- (B): pairwise at-most-one constraints on each vertex's out-arcs.
- "Cycle" target: a nonempty successor-closed set of states.
- "Fair" target: the exact characterization from Section 2.

**Sound strengthenings.**
- `sym`: translation and permutation symmetry breaking.
- `tok`: every move passes a token (step 1).
- `alldir`: every vertex flips. This is minimality via subcube restriction.
- `k2`: every cycle state has at least 2 unstable vertices (single-token lemma).

**Independent checks.** `verify.py` (a plain-Python checker), `brute3.c` (all 2^24 networks at n = 3) and `z3check.py` (a second encoding).

**Cross-checks, all passed:**
- **n = 3 counts:** brute force and SAT agree. 680 networks satisfy (A); 224 satisfy (A) and (B).
- **Pinned to `sd_F`:** the fair target is SAT under (A) and UNSAT with (B) added.
- **(B) dropped:** a counterexample is found and verified at n = 4 and n = 5.
- **(A) relaxed:** the strengthened encodings still find cycles at n = 4, 5 and 6.

| n | Query under (A)+(B) | Result | Time |
|---|---|---|---|
| 3 | brute force, cycle and fair | none | 1.3 s |
| 4 | cycle / fair (exact) | UNSAT / UNSAT | 0.16 s / 5.0 s |
| 4 | z3 closed walks, lengths 2-16 | UNSAT | ~120 s |
| 5 | cycle, plain / sym | UNSAT / UNSAT | 168 s / 4.1 s |
| 6 | sym+tok+alldir, CaDiCaL / Glucose | UNSAT / UNSAT | 41.4 s / 66.2 s |
| 6 | sym+tok+alldir+k2 | UNSAT | 28.4 s |

**Supporting results.**
- **Localization:** UNSAT at n = 3 to 5; SAT at n = 4 once (B) is dropped.
- **F2:** holds at n = 3 and 4; timed out at n = 5.
- **Ruled out:** four candidate potentials fail at n = 4.

**n = 7:** `run_strong.py 7 sym,tok,alldir`, with and without `k2`, was running at the time of writing.

## 5. Proof idea

1. **Minimal counterexample.** In a minimal counterexample every vertex flips, the token count is constant with k >= 2, and every move passes a token.
2. **F2 finishes it,** even with (A) required only at x. The obstacle is persistence: the arc a vertex needs can be destroyed by other firings. The proof therefore has to be global along the cycle, probably by induction on cycle length or on the number of tokens.
3. **Alternatives:** Shih-Dong subcube induction, or Richard's opposition lemmas (`opp_false`).
4. **Difficulty:** medium-hard.

## 6. Next step and Coq size estimates

1. **Read Shih and Ho 1999 through a library.** Cite it if it covers asynchronous updates.
2. **Otherwise, prove F2.** Do not state the general claim before it is proved.
3. **Coq size estimates:**

| Piece | Lines |
|---|---|
| Single-token lemma | ~80-150 |
| Fair settlement from acyclicity | ~150-250 |
| F2 and the main theorem (compare `richard_t3`, ~750) | ~600-1,200 |
| Instance certificates by `vm_compute` for n <= 4 | ~50-100 each |

The n = 5 and 6 SAT results would need a verified certificate checker to replay in Coq.
