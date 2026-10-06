"""Sample (A)+(B) networks with SAT random phases; cache to nets_n.json."""
import sys, random, json
from pysat.solvers import Solver
from enc import Enc
import verify as V
n=int(sys.argv[1]); lim=int(sys.argv[2]); seed=int(sys.argv[3]) if len(sys.argv)>3 else 1
e=Enc(n,A=True,B=True,target="none"); N=1<<n
Fv=[v for row in e.F for v in row]
out=[]
with Solver(name="cadical195",bootstrap_with=e.cnf.clauses) as s:
    rnd=random.Random(seed)
    while len(out)<lim:
        s.set_phases([v if rnd.random()<0.5 else -v for v in Fv])
        if not s.solve(): break
        m=s.get_model(); pos=set(l for l in m if l>0); tt=e.decode(m)
        s.add_clause([-v if v in pos else v for v in Fv])
        out.append(tt)
json.dump(out,open(f"nets_{n}_{seed}.json","w"))
print(n,len(out))
