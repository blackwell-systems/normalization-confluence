import sys, random
from pysat.solvers import Solver
from enc import Enc
import verify as V
n=int(sys.argv[1]); lim=int(sys.argv[2])
e=Enc(n,A=True,B=True,target="none"); N=1<<n
Fv=[v for row in e.F for v in row]
cnt=0; geo_all=0; maxlen=0; viol=None
with Solver(name="cadical195",bootstrap_with=e.cnf.clauses) as s:
    rnd=random.Random(1)
    while cnt<lim:
        # random phases to diversify
        s.set_phases([v if rnd.random()<0.5 else -v for v in Fv])
        if not s.solve(): break
        m=s.get_model(); pos=set(l for l in m if l>0); tt=e.decode(m); cnt+=1
        s.add_clause([-v if v in pos else v for v in Fv])
        fps=[x for x in range(N) if not V.unstable(tt,n,x)]
        assert len(fps)==1; p=fps[0]
        geo=all(tt[v][x]==V.bit(p,v) for x in range(N) for v in V.unstable(tt,n,x))
        geo_all+=geo
        if not geo and viol is None: viol=tt
        # longest path in DAG
        g=V.state_graph(tt,n); memo={}
        def L(x):
            if x in memo: return memo[x]
            memo[x]=max([1+L(y) for y in g[x]],default=0); return memo[x]
        maxlen=max(maxlen,max(L(x) for x in range(N)))
print("models",cnt,"all-moves-geodesic",geo_all,"max path length",maxlen)
if viol: print("non-geodesic example", viol)
