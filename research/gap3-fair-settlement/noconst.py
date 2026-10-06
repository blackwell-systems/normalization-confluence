"""SAT: is there a network with (A)+(B) in which no coordinate f_i is a constant function?
Usage: noconst.py n [rank]"""
import sys, time, json
from pysat.solvers import Solver
from enc import Enc
import verify as V
n=int(sys.argv[1]); rank=len(sys.argv)>2
e=Enc(n,A=not rank,B=True,target="none"); N=1<<n; P=e.pool; cnf=e.cnf
if rank:
    for x in range(N):
        g=lambda i,t: P.id(("rk",x,i,t))
        for i in range(n):
            cnf.append([-g(i,n)])
            for t in range(2,n+1): cnf.append([-g(i,t),g(i,t-1)])
        for j in range(n):
            for i in range(n):
                a=e.arc[(x,j,i)]
                if i==j: cnf.append([-a]); continue
                cnf.append([-a,g(j,1)])
                for t in range(1,n): cnf.append([-a,-g(i,t),g(j,t+1)])
for i in range(n):
    # f_i takes value 1 somewhere and 0 somewhere
    cnf.append([e.F[i][x] for x in range(N)]); cnf.append([-e.F[i][x] for x in range(N)])
t0=time.time()
with Solver(name="cadical195",bootstrap_with=cnf.clauses) as s:
    sat=s.solve(); r={"n":n,"sat":sat,"t":round(time.time()-t0,1)}
    if sat:
        tt=e.decode(s.get_model()); r.update(chkA=V.check_A(tt,n),chkB=V.check_B(tt,n),tt=tt)
print(json.dumps(r))
