"""Does (A)+(B) allow a synchronous periodic orbit of length >= 2? Encoding: a nonempty set C of
non-fixed states with F(C) contained in C."""
import sys, time
from pysat.solvers import Solver
from enc import Enc
import verify as V
n=int(sys.argv[1]); B=sys.argv[2]=="1"; e=Enc(n,A=True,B=B,target="none"); N=1<<n; P=e.pool; cnf=e.cnf
c=[P.id(("sc",x)) for x in range(N)]; cnf.append(c)
for x in range(N):
    cnf.append([-c[x]]+[e.u(x,v) for v in range(n)])  # not fixed
    for y in range(N):  # c[x] and F(x)=y -> c[y]
        cnf.append([-c[x],c[y]]+[(-e.F[i][x] if (y>>i)&1 else e.F[i][x]) for i in range(n)])
t=time.time()
with Solver(name="cadical195",bootstrap_with=cnf.clauses) as s:
    r=s.solve(); print(n,"B" if B else "noB","sync cycle:",r,round(time.time()-t,1))
    if r:
        tt=e.decode(s.get_model()); x=[x for x in range(N) if V.unstable(tt,n,x)][0]
        seen=[]
        while x not in seen:
            seen.append(x); x=sum(tt[i][x]<<i for i in range(n))
        print(" orbit", [V.fmt(z,n) for z in seen[seen.index(x):]], "A",V.check_A(tt,n),"B",V.check_B(tt,n))
