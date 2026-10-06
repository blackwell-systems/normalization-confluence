"""SAT falsifier: (A)+(B), fixed point p=0 (translation WLOG), state x = bits 0..m-1 set,
v = m unstable with x_v = p_v ("bad" token), arc v -> w=0 in G(x), w stable at x (token passed),
optionally exactly k unstable at x. SAT = a bad token passes to a good receiver (good count rises)."""
import sys, time, itertools
from pysat.solvers import Solver
from enc import Enc
n=int(sys.argv[1]); k=int(sys.argv[2]) if len(sys.argv)>2 else 0
e=Enc(n,A=True,B=True,target="none"); N=1<<n; cnf=e.cnf
for i in range(n): cnf.append([-e.F[i][0]])
base=list(cnf.clauses)
for m in range(1,n):
    x=(1<<m)-1; v=m; w=0
    cl=list(base)
    cl.append([e.u(x,v)]); cl.append([e.arc[(x,v,w)]]); cl.append([-e.u(x,w)])
    if k:
        for S in itertools.combinations(range(n),k+1): cl.append([-e.u(x,q) for q in S])
        for q in range(n): cl.append([e.u(x,r) for r in range(n) if r!=q])
    t=time.time()
    with Solver(name="cadical195",bootstrap_with=cl) as s:
        r=s.solve()
        print(n,"k",k or "any","m",m,"SAT" if r else "UNSAT",round(time.time()-t,2),flush=True)
        if r: print(e.decode(s.get_model()))
