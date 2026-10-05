"""On count-preserving moves (token passed v -> w) of (A)+(B) networks, test candidate potentials."""
import sys, random
from pysat.solvers import Solver
from enc import Enc
import verify as V
n=int(sys.argv[1]); lim=int(sys.argv[2])
e=Enc(n,A=True,B=True,target="none"); N=1<<n
Fv=[v for row in e.F for v in row]
def forest(tt,x):
    G=V.local_graph(tt,n,x); return {j:(next(iter(G[j])) if G[j] else None) for j in range(n)}
def chain(out,v):
    s=[v]
    while out[s[-1]] is not None: s.append(out[s[-1]])
    return s
def cands(tt,x):
    out=forest(tt,x); T=V.unstable(tt,n,x)
    R=set(); hs=[]
    for v in T:
        c=chain(out,v); R|=set(c); hs.append(len(c))
    p=[y for y in range(N) if not V.unstable(tt,n,y)][0]
    D=sum(V.bit(x,i)!=V.bit(p,i) for i in range(n))
    return {"sumh":sum(hs),"R":len(R),"sorted_h":tuple(sorted(hs,reverse=True)),"dist_p":D,
            "sumh_plus_D":sum(hs)+D}
names=None; viol={}; cnt=0; moves=0
with Solver(name="cadical195",bootstrap_with=e.cnf.clauses) as s:
    rnd=random.Random(11)
    while cnt<lim:
        s.set_phases([v if rnd.random()<0.5 else -v for v in Fv])
        if not s.solve(): break
        m=s.get_model(); pos=set(l for l in m if l>0); tt=e.decode(m); cnt+=1
        s.add_clause([-v if v in pos else v for v in Fv])
        for x in range(N):
            T=V.unstable(tt,n,x)
            for v in T:
                y=x^(1<<v)
                if len(V.unstable(tt,n,y))!=len(T): continue
                moves+=1
                a,b=cands(tt,x),cands(tt,y)
                for k in a:
                    if not (b[k]<a[k]): viol[k]=viol.get(k,0)+1
print("models",cnt,"count-preserving moves",moves,"violations per candidate",viol)
