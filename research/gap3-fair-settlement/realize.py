"""Is a cycle of the abstract game realizable by a real network?  The run starts at state 0,
repeats the game cycle twice (so the state closes), and the local graph at each run state must be
the game forest (exactly), with the game token set as unstable set.
Modes: full ((A)+(B) everywhere), local ((B) at run states and cube neighbours, (A) at run states)."""
import sys, itertools, json
from pysat.solvers import Solver
from enc import Enc, elem_cycles
import verify as V
cyc=json.loads(sys.argv[1]); n=int(sys.argv[2]); mode=sys.argv[3]; reps=int(sys.argv[4]) if len(sys.argv)>4 else 2; cut=int(sys.argv[5]) if len(sys.argv)>5 else 10**9
e=Enc(n,A=(mode=="full"),B=(mode=="full"),target="none"); N=1<<n; cnf=e.cnf; P=e.pool
for x in range(N):
    for v in range(n): cnf.append([-e.arc[(x,v,v)]])
x=0; run=[]
for rep in range(reps):
    for (o,U),v in cyc:
        run.append((x,o,U)); x^=1<<v
run=run[:cut]
S=set(r[0] for r in run)
if mode=="local":
    near=set(S)|set(s^(1<<j) for s in S for j in range(n))
    for y in near:
        for j in range(n):
            for a in range(n):
                for b in range(a+1,n): cnf.append([-e.arc[(y,j,a)],-e.arc[(y,j,b)]])
    for y in S:
        for c in elem_cycles(n):
            if len(c)>1:
                L=len(c); cnf.append([-e.arc[(y,c[t],c[(t+1)%L])] for t in range(L)])
for (y,o,U) in run:
    for j in range(n):
        for i in range(n):
            cnf.append([e.arc[(y,j,i)] if o[j]==i else -e.arc[(y,j,i)]])
    for w in range(n):
        cnf.append([e.u(y,w)] if w in U else [-e.u(y,w)])
with Solver(name="cadical195",bootstrap_with=cnf.clauses) as s:
    print(mode, "SAT" if s.solve() else "UNSAT")
