#!/usr/bin/env python3
"""Merge the shard outputs of p2search. Usage: python3 merge_shards.py shard*.out"""
import collections
import sys

c, reps, cpu = collections.Counter(), 0, 0.0
for f in sys.argv[1:]:
    for line in open(f):
        t = line.split()
        if t and t[0] == "n":
            reps, cpu = int(t[5]), cpu + float(t[7])
        if t and t[0] == "k":
            for i in range(2, len(t), 2):
                c[(int(t[1]), t[i])] += int(t[i + 1])
total = sum(v for (k, f), v in c.items() if f == "weighted")
print(f"representatives {reps}, cpu seconds {cpu:.0f}")
print(f"profiles (full space) {total}; analysed {sum(v for (k, f), v in c.items() if f == 'checked')}")
print("stable  analysed  profiles  with_cycle  with_fair_cycle  (profiles = full-space counts)")
for k in sorted({k for k, _ in c}):
    print(k, c[(k, "checked")], c[(k, "weighted")], c[(k, "cyc_weighted")], c[(k, "fair_weighted")])
