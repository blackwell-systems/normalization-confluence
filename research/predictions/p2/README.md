# The P2 search

Programs used to test [P2.md](../P2.md): does some marriage market with `n <= 4` and exactly one
stable matching have a bad fair lasso of the blocking-pair dynamics? The answer found is yes, at
`n = 3`; the instance is mechanized in [coq/StableMatchingP2.v](../../../coq/StableMatchingP2.v).

## Method

States are all partial matchings (34 for `n = 3`, 209 for `n = 4`), labels the `n^2` pairs, and
the update is the one committed in P2.md. The state graph has an edge `s -> u_j s` for every pair
`j` that blocks at `s`.

A bad fair lasso exists from some start exactly when some strongly connected component `S` with
at least one edge has, for every pair `j`, a state of `S` where `j` does not block (a no-op step
there) or an edge labeled `j` with both ends in `S`. Stable matchings are sinks, so such an `S`
holds only unstable matchings; the condition is monotone in `S`, so no refinement below an SCC is
needed. Every matching is a possible start. The argument is written out in `p2ref.py`.

## Files

| File | What it does |
|---|---|
| `p2ref.py` | Reference checker in plain Python: the model, Tarjan's SCCs, the fair-SCC test, a lasso builder. `python3 p2ref.py` checks the two published instances. |
| `p2ref_n3.py` | The reference checker on all `n = 3` profiles, no symmetry reduction (about 15 s). |
| `p2ref_strong.py` | Strong-fairness counts for `n = 3` (a robustness check beyond the committed claim). |
| `p2search.c` | The exhaustive search in C with symmetry reduction, for `n <= 4`. |
| `test_p2.py` | Sanity tests (about 30 s). |

## Symmetry reduction

The men's profile runs over one representative of each orbit under relabeling men and relabeling
women (`n!^2` group elements); the women's profile runs over all `n!^n` profiles. Every profile is
equivalent to an enumerated one. The count of profiles of the whole space with an invariant
property is the sum over representatives `r` of `|orbit(r)|` times the number of women's profiles
`wp` with the property for `(r, wp)`. The program prints these full-space counts ("weighted") and
the number of profiles actually analysed ("checked"). The side swap is not used.

## Rerun

```
cc -O2 -o p2search p2search.c
./p2search 3                                   # instant
for i in 0 1 2 3 4 5 6 7; do ./p2search 4 $i 8 > shard$i.out & done; wait   # minutes
python3 test_p2.py ./p2search
python3 p2ref.py
```

## Sanity tests (`test_p2.py`)

- The best-response cycle printed by Ackermann et al. (2011, Thm 3) is a blocking-pair cycle in
  this model; the cyclic 3-by-3 market has its three known stable matchings.
- For every `n = 3` profile, "exactly one stable matching" agrees with "the man-optimal and the
  woman-optimal matchings (Gale-Shapley) coincide".
- The C program and the Python reference give the same full-space counts for `n = 2` and `n = 3`,
  and the same answers on 400 random `n = 4` profiles.
- The P2 instance: one stable matching, and the loop word returns through unstable matchings.

## Results

See the Outcome section of [P2.md](../P2.md).
