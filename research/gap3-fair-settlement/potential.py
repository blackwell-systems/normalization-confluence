"""Test candidate potentials on (A)+(B) networks: Phi(x) = sum over unstable v of (h_x(v)+1),
where h_x(v) is the length of the out-path from v in the forest G(x)."""
import sys, random
from pysat.solvers import Solver
from enc import Enc
import verify as V
n=int(sys.argv[1]); lim=int(sys.argv[2])
e=Enc(n,A=True,B=True,target="none"); N=1<<n
Fv=[v for row in e.F for v in row]
def heights(tt,x):
    G=V.local_graph(tt,n,x); out={j:(next(iter(G[j])) if G[j] else None) for j in range(n)}
    h={}
    for v in range(n):
        k,u=0,v
        while out[u] is not None: u=out[u]; k+=1
        h[v]=k
    return h,out
def phi(tt,x):
    h,_=heights(tt,x); return sum(h[v]+1 for v in V.unstable(tt,n,x))
bad=0; cnt=0; ex=None; detail={"other_token_height_up":0,"mover_target_height_up":0}
with Solver(name="cadical195",bootstrap_with=e.cnf.clauses) as s:
    rnd=random.Random(7)
    while cnt<lim:
        s.set_phases([v if rnd.random()<0.5 else -v for v in Fv])
        if not s.solve(): break
        m=s.get_model(); pos=set(l for l in m if l>0); tt=e.decode(m); cnt+=1
        s.add_clause([-v if v in pos else v for v in Fv])
        for x in range(N):
            hx,outx=heights(tt,x)
            for v in V.unstable(tt,n,x):
                y=x^(1<<v); hy,_=heights(tt,y)
                if phi(tt,y)>=phi(tt,x):
                    bad+=1
                    if ex is None: ex=(tt,x,v)
                w=outx[v]
                if w is not None and hy[w]>hx[w]: detail["mover_target_height_up"]+=1
                for u in V.unstable(tt,n,x):
                    if u!=v and hy[u]>hx[u]: detail["other_token_height_up"]+=1
print("models",cnt,"moves violating strict decrease",bad,detail)
if ex: print("example",ex)
