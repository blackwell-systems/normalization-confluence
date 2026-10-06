"""Exploration: closed K-token runs with (A) AND (B) required only at the states of C (no
self-loops everywhere). SAT = the conditions at the run states alone do not exclude the run.
Usage: localB.py n K [Bnbr]   (Bnbr: (B) also at the cube neighbours of C states)"""
import sys, itertools, json, time
from pysat.solvers import Solver
from enc import Enc, elem_cycles
import verify as V
n=int(sys.argv[1]); K=int(sys.argv[2]); nbr=len(sys.argv)>3
e=Enc(n,A=False,B=False,target="cycle"); N=1<<n; P=e.pool; cnf=e.cnf
for x in range(N):
    for v in range(n): cnf.append([-e.arc[(x,v,v)]])
guard={}
for x in range(N):
    if not nbr: guard[x]=e.c[x]
    else:
        g=P.id(("near",x)); guard[x]=g; cnf.append([-e.c[x],g])
        for v in range(n): cnf.append([-e.c[x^(1<<v)],g])
cyc=[c for c in elem_cycles(n) if len(c)>1]
for x in range(N):
    for c in cyc:
        L=len(c); cnf.append([-e.c[x]]+[-e.arc[(x,c[t],c[(t+1)%L])] for t in range(L)])
    for j in range(n):
        for a in range(n):
            for b in range(a+1,n): cnf.append([-guard[x],-e.arc[(x,j,a)],-e.arc[(x,j,b)]])
    for S in itertools.combinations(range(n),K+1): cnf.append([-e.c[x]]+[-e.u(x,w) for w in S])
    for S in itertools.combinations(range(n),n-K+1): cnf.append([-e.c[x]]+[e.u(x,w) for w in S])
t0=time.time()
with Solver(name="cadical195",bootstrap_with=cnf.clauses) as s:
    sat=s.solve(); r={"n":n,"K":K,"nbr":nbr,"sat":sat,"t":round(time.time()-t0,1)}
    if sat:
        m=s.get_model(); tt=e.decode(m); C=e.decode_c(m)
        r["C"]=[V.fmt(x,n) for x in C]; r["B_global"]=V.check_B(tt,n)
print(json.dumps(r))
