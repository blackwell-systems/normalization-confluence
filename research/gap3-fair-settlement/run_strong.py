"""Cycle target at size n with sound strengthenings (each keeps SAT if a counterexample of size n
exists whose smaller restrictions are already ruled out):
  sym   : a cycle state is 0 and its first move flips vertex 0 (translation + permutation symmetry)
  tok   : each chosen cycle edge x -v-> flip v x passes the token: v has an out-neighbour w in G(x)
          with w stable at x (Step 1: on a cycle the unstable count is constant)
  alldir: every vertex is flipped along some chosen edge (minimality: a cycle flipping only I
          lives in the subcube network on I, which satisfies (A)+(B) and is ruled out for |I| < n)
  k2    : every cycle state has >= 2 unstable vertices (single-token lemma; optional)
"""
import sys, time, json
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType
from enc import Enc
import verify as V
n=int(sys.argv[1]); opts=sys.argv[2].split(","); solver=sys.argv[3] if len(sys.argv)>3 else "cadical195"
e=Enc(n,A=("noA" not in opts),B=True,target="cycle"); N=1<<n; P=e.pool; cnf=e.cnf
if "noA" in opts:
    for x in range(N):
        for v in range(n): e.cnf.append([-e.arc[(x,v,v)]])
E=lambda x,v: P.id(("e",x,v))
if "sym" in opts: cnf.append([e.c[0]]); cnf.append([E(0,0)])
if "tok" in opts:
    for x in range(N):
        for v in range(n):
            ws=[]
            for w in range(n):
                if w==v: continue
                t=P.id(("tok",x,v,w)); ws.append(t)
                cnf.extend([[-t,e.arc[(x,v,w)]],[-t,-e.u(x,w)]])
            cnf.append([-E(x,v)]+ws)
if "alldir" in opts:
    for v in range(n): cnf.append([E(x,v) for x in range(N)])
if "k2" in opts:
    for x in range(N):
        for v in range(n):  # c[x] and only v unstable is impossible; c[x] and none unstable impossible
            cnf.append([-e.c[x]]+[e.u(x,w) for w in range(n) if w!=v])
t0=time.time()
with Solver(name=solver,bootstrap_with=cnf.clauses) as s:
    sat=s.solve(); m=s.get_model() if sat else None
r={"n":n,"opts":opts,"solver":solver,"sat":sat,"t":round(time.time()-t0,1)}
if sat:
    tt=e.decode(m); r.update(tt=tt,chkA=V.check_A(tt,n),chkB=V.check_B(tt,n),cyc=V.async_cyclic(tt,n),fair=bool(V.fair_witness(tt,n)))
print(json.dumps(r))
