#!/usr/bin/env python3
"""Recompute the numbers the engineer's guide (docs/site/guide/index.html) shows.

Run from anywhere: python3 docs/site/guide/check_examples.py

1. The shelf (cap 5, stock 4, events "add 3" and "remove 1"): every step the interactive demo shows,
   in both modes, for both orders.
2. The account example of section 4, which is AtomicRepair.v's atomic_not_descent with
   0 = good standing, 1 = suspended, 2 = over the limit: every atomic run from good standing ends in
   good standing, while with a background reconciler the same two events in the same order end in
   two different states.
"""
import itertools
import sys

errors = []


def expect(what, got, want):
    if got != want:
        errors.append(f"{what}: got {got!r}, the guide says {want!r}")


# 1. The shelf. --------------------------------------------------------------------------------
CAP, START = 5, 4
RAW = {"add 3": lambda x: x + 3, "remove 1": lambda x: max(x - 1, 0)}


def cap(x):
    return min(x, CAP)


def fix_on_write(order):
    """Fix up after every event: (raw value, value after fix-up) per step."""
    s, steps = START, []
    for e in order:
        raw = RAW[e](s)
        s = cap(raw)
        steps.append((raw, s))
    return steps


def cap_on_read(order):
    """Store raw counts, cap when reading: (stored value, value read) per step."""
    s, steps = START, []
    for e in order:
        s = {"add 3": s + 3, "remove 1": s - 1}[e]  # stored counts are not clamped
        steps.append((s, cap(s)))
    return steps


A, B = ["add 3", "remove 1"], ["remove 1", "add 3"]
expect("fix on write, add first", fix_on_write(A), [(7, 5), (4, 4)])
expect("fix on write, remove first", fix_on_write(B), [(3, 3), (6, 5)])
expect("cap on read, add first", cap_on_read(A), [(7, 5), (6, 5)])
expect("cap on read, remove first", cap_on_read(B), [(3, 3), (6, 5)])
# State descent fails at the raw 7 for "remove 1": fix(e(fix 7)) = 4, fix(e 7) = 5.
expect("fix(remove(fix 7))", cap(RAW["remove 1"](cap(7))), 4)
expect("fix(remove 7)", cap(RAW["remove 1"](7)), 5)
# Raw counts commute: every order of any multiset of these events stores the same count.
for n in range(1, 6):
    for bag in itertools.combinations_with_replacement(["add 3", "remove 1"], n):
        ends = set()
        for order in itertools.permutations(bag):
            ends.add(cap_on_read(list(order))[-1][1])
        expect(f"cap on read agrees for {bag}", len(ends), 1)

# 2. The account (atomic_not_descent). ---------------------------------------------------------
OK, SUSPENDED, OVER = "good standing", "suspended", "over the limit"
VALID = {OK, SUSPENDED}
EVENTS = {
    "charge": lambda s: OVER,                         # XF: every state goes to 2
    "review": lambda s: SUSPENDED if s == OVER else OK,  # XE: 0, 1 go to 0; 2 goes to 1
}


def fix_step(s):
    return OK  # x_rho: one repair step sends the invalid state to 0


def fix(s):
    while s not in VALID:
        s = fix_step(s)
    return s


# The Coq system, for comparison: x_apply, x_rho, x_valid.
COQ = {0: OK, 1: SUSPENDED, 2: OVER}
for n, s in COQ.items():
    expect(f"charge at {n}", EVENTS["charge"](s), COQ[2])
    expect(f"review at {n}", EVENTS["review"](s), COQ[{2: 1}.get(n, 0)])


def atomic_results(start, buffer):
    out = set()
    for order in itertools.permutations(buffer):
        s = start
        for e in order:
            s = fix(EVENTS[e](s))
        out.add(s)
    return out


def interleaved_results(start, buffer):
    """Every normal form when events may fire before the fix-up runs (free delivery)."""
    out, seen, todo = set(), set(), [(start, tuple(buffer))]
    while todo:
        s, buf = todo.pop()
        if (s, buf) in seen:
            continue
        seen.add((s, buf))
        moves = []
        for i, e in enumerate(buf):
            moves.append((EVENTS[e](s), buf[:i] + buf[i + 1:]))
        if s not in VALID:
            moves.append((fix_step(s), buf))
        if not moves:
            out.add(s)
        todo.extend(moves)
    return out


for n in range(0, 5):
    for bag in itertools.combinations_with_replacement(sorted(EVENTS), n):
        expect(f"atomic runs of {bag}", atomic_results(OK, bag), {OK})
expect("background reconciler, charge then review", interleaved_results(OK, ["charge", "review"]), {OK, SUSPENDED})
# Same order, different timing: (charge, fix-up, review) and (charge, review).
expect("charge, fix-up, review", EVENTS["review"](fix(EVENTS["charge"](OK))), OK)
expect("charge, review (fix-up late)", fix(EVENTS["review"](EVENTS["charge"](OK))), SUSPENDED)
# State descent fails at "over the limit" for review.
expect("fix(review(fix over))", fix(EVENTS["review"](fix(OVER))), OK)
expect("fix(review over)", fix(EVENTS["review"](OVER)), SUSPENDED)

if errors:
    for e in errors:
        print("FAIL:", e)
    sys.exit(1)
print("PASS: the shelf demo's steps and the account example match the guide")
