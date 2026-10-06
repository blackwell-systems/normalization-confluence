"""Exploration: which sign of local cycle must a closed K-token run meet?  (B) everywhere, no
self-loops everywhere, and at the states of C forbid only negative (mode neg) or only positive
(mode pos) local cycles. SAT = a closed run exists under that weaker hypothesis.
Usage: signvar.py n K mode"""
import sys, itertools, json, time
from pysat.solvers import Solver
from enc import Enc, elem_cycles
import verify as V
n=int(sys.argv[1]); K=int(sys.argv[2]); mode=sys.argv[3]
e=Enc(n,A=False,B=True,target="cycle"); N=1<<n; P=e.pool; cnf=e.cnf
for x in range(N):
    for v in range(n): cnf.append([-e.arc[(x,v,v)]])
def neg(x,j,i):  # arc j->i at x is negative: f_i(x with x_j=1) = 0 while f_i(x with x_j=0) = 1
    hi=x|(1<<j)
    return e.arc[(x,j,i)], -e.F[i][hi]   # arc and f_i(hi)=0 means negative
for x in range(N):
    for c in elem_cycles(n):
        L=len(c)
        if L<2: continue
        arcs=[(c[t],c[(t+1)%L]) for t in range(L)]
        for sg in itertools.product([0,1],repeat=L):   # 1 = negative arc
            if (sum(sg)%2==1) != (mode=="neg"): continue
            cl=[-e.c[x]]
            for (j,i),s in zip(arcs,sg):
                hi=x|(1<<j)
                cl.append(-e.arc[(x,j,i)])
                cl.append(e.F[i][hi] if s else -e.F[i][hi])
            cnf.append(cl)
for x in range(N):
    for S in itertools.combinations(range(n),K+1): cnf.append([-e.c[x]]+[-e.u(x,w) for w in S])
    for S in itertools.combinations(range(n),n-K+1): cnf.append([-e.c[x]]+[e.u(x,w) for w in S])
t0=time.time()
with Solver(name="cadical195",bootstrap_with=cnf.clauses) as s:
    sat=s.solve(); r={"n":n,"K":K,"mode":mode,"sat":sat,"t":round(time.time()-t0,1)}
    if sat:
        tt=e.decode(s.get_model()); C=e.decode_c(s.get_model())
        r["C"]=[V.fmt(x,n) for x in C]
print(json.dumps(r))
