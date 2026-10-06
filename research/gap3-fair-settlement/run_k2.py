"""k = 2 exactly: search for a network with (A)+(B) and a closed asynchronous run (a nonempty set C
of states, each with a chosen state-graph edge into C) such that every state of C has EXACTLY 2
unstable vertices. Sound strengthenings as in run_strong.py:
  sym    : a C state is 0 and its chosen edge flips vertex 0
  tok    : each chosen edge passes a token (implied here, kept as a hint)
  alldir : every vertex is flipped on some chosen edge (sound given k=2 decided UNSAT for all n'<n:
           a k=2 closed run flipping only I is a closed run of the subcube network on I with
           2 - (tokens outside I) tokens, and 0 or 1 tokens are ruled out by one_token_closed)
  rank   : encode (A) by a ranking (order encoding) instead of listing elementary cycles; under
           (B) both are equivalent to acyclicity of each G(x)
"""
import sys, time, json, itertools
from pysat.solvers import Solver
from enc import Enc
import verify as V
n=int(sys.argv[1]); opts=sys.argv[2].split(","); solver=sys.argv[3] if len(sys.argv)>3 else "cadical195"
rank="rank" in opts
noA="noA" in opts
e=Enc(n,A=(not rank and not noA),B=True,target="cycle"); N=1<<n; P=e.pool; cnf=e.cnf
if noA:
    for x in range(N):
        for v in range(n): e.cnf.append([-e.arc[(x,v,v)]])
if rank and not noA:
    for x in range(N):
        g=lambda i,t: P.id(("rk",x,i,t))   # rank(i) >= t, t = 1..n
        for i in range(n):
            cnf.append([-g(i,n)])  # rank < n
            for t in range(2,n+1): cnf.append([-g(i,t),g(i,t-1)])
        for j in range(n):
            for i in range(n):
                a=e.arc[(x,j,i)]
                if i==j: cnf.append([-a]); continue
                cnf.append([-a,g(j,1)])
                for t in range(1,n): cnf.append([-a,-g(i,t),g(j,t+1)])
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
K=2
for x in range(N):
    for S in itertools.combinations(range(n),K+1):
        cnf.append([-e.c[x]]+[-e.u(x,w) for w in S])
    for v in range(n):
        cnf.append([-e.c[x]]+[e.u(x,w) for w in range(n) if w!=v])
t0=time.time()
with Solver(name=solver,bootstrap_with=cnf.clauses) as s:
    sat=s.solve(); m=s.get_model() if sat else None
r={"n":n,"opts":opts,"solver":solver,"k":"exactly 2","sat":sat,"t":round(time.time()-t0,1),"vars":P.top,"clauses":len(cnf.clauses)}
if sat:
    tt=e.decode(m); r.update(tt=tt,chkA=V.check_A(tt,n),chkB=V.check_B(tt,n),cyc=V.async_cyclic(tt,n),fair=bool(V.fair_witness(tt,n)))
print(json.dumps(r),flush=True)
