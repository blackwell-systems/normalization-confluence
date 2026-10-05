from pysat.solvers import Solver
from enc import Enc
import verify as V
def count(A,B):
    e=Enc(3,A=A,B=B,target="none"); Fv=[v for row in e.F for v in row]; k=0; agree=0
    with Solver(name="cadical195",bootstrap_with=e.cnf.clauses) as s:
        while s.solve():
            m=s.get_model(); pos=set(l for l in m if l>0)
            tt=e.decode(m); k+=1
            agree += (V.check_A(tt,3) or not A) and (V.check_B(tt,3) or not B)
            s.add_clause([-v if v in pos else v for v in Fv])
    return k,agree
print("A models",count(True,False)); print("A+B models",count(True,True))
from run import solve
for t in ("cycle","fair"):
    r=solve(3,False,True,t); print("B only",t,r["sat"],r.get("chk_B"),r.get("fair_ok"))
