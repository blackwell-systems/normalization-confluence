"""Sample (A)+(B) networks that contain a long count-2 asynchronous walk (random start and random
fired vertices, forced by assumptions), to stress the k=2 lemmas on non-degenerate instances."""
import sys, random, json, itertools
from pysat.solvers import Solver
from enc import Enc
n=int(sys.argv[1]); lim=int(sys.argv[2]); L=int(sys.argv[3]); seed=int(sys.argv[4])
e=Enc(n,A=True,B=True,target="none"); N=1<<n; P=e.pool
# selector-guarded "exactly 2 unstable at x"
def two(x):
    s=P.id(("two",x))
    for S in itertools.combinations(range(n),3): e.cnf.append([-s]+[-e.u(x,q) for q in S])
    for q in range(n): e.cnf.append([-s]+[e.u(x,r) for r in range(n) if r!=q])
    return s
sel={x:two(x) for x in range(N)}
Fv=[v for row in e.F for v in row]
rnd=random.Random(seed); out=[]; tries=0
with Solver(name="cadical195",bootstrap_with=e.cnf.clauses) as s:
    while len(out)<lim and tries<50*lim:
        tries+=1
        z=rnd.randrange(N); ass=[sel[z]]; prev=None
        for t in range(L):
            v=rnd.choice([q for q in range(n) if q!=prev]); ass.append(e.u(z,v)); z^=1<<v; ass.append(sel[z]); prev=v
        s.set_phases([v if rnd.random()<0.5 else -v for v in Fv])
        if s.solve(assumptions=ass):
            out.append(e.decode(s.get_model()))
json.dump(out,open(f"rich_{n}_{L}_{seed}.json","w")); print(n,L,len(out),"tries",tries)
