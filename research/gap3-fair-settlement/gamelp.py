"""LP search for a linear potential over configuration features in the abstract game (game.py):
weights w with w.(f(next) - f(cur)) <= -1 on every move. Usage: python3 gamelp.py n K"""
import sys, itertools
import numpy as np
from scipy.optimize import linprog
import game
from game import forests, moves
def path(o,u):
    out=[u]
    while o[out[-1]]!=-1: out.append(o[out[-1]])
    return out
def feats(o,U,n):
    Us=set(U); P={z:path(o,z) for z in range(n)}
    fr=[]; 
    for u in U:
        c=0
        for z in P[u][1:]:
            if z in Us: break
            c+=1
        fr.append(c)
    dp=[len(P[u])-1 for u in U]
    anc=[sum(1 for z in range(n) if u in P[z][1:]) for u in U]
    Z=set(); R=set(); A=set()
    for u in U:
        R|=set(P[u])
        for z in P[u][1:]:
            if z in Us: break
            Z.add(z)
    for z in range(n):
        if any(q in Us for q in P[z]): A.add(z)
    blocked=sum(1 for u in U if any(q in Us for q in P[u][1:]))
    alld=sum(len(P[z])-1 for z in range(n)); roots=sum(1 for z in range(n) if o[z]==-1)
    tokroot=sum(1 for u in U if o[u]==-1)
    pairs_same=sum(1 for a,b in itertools.combinations(U,2) if set(P[a])&set(P[b]))
    return [sum(fr),max(fr),min(fr),len(Z),sum(dp),max(dp),min(dp),sum(anc),max(anc),min(anc),len(R),len(A),blocked,alld,roots,tokroot,pairs_same,
            sum(d*d for d in dp), sum(f*f for f in fr), sum(a*a for a in anc)]
names="sumfree maxfree minfree Z sumdepth maxdepth mindepth sumanc maxanc minanc reach A blocked alldepth roots tokroot pairs_same sumdepth2 sumfree2 sumanc2".split()
n=int(sys.argv[1]); K=int(sys.argv[2])
if len(sys.argv)>3: game.REFINE = sys.argv[3]=="refine"
rows=set()
for o in forests(n):
    for U in itertools.combinations(range(n),K):
        f0=feats(o,U,n)
        for v,o2,U2 in moves(o,U,n):
            f1=feats(o2,U2,n); rows.add(tuple(a-b for a,b in zip(f1,f0)))
A=np.array(sorted(rows),dtype=float); m=A.shape[1]
res=linprog(np.zeros(m),A_ub=A,b_ub=-np.ones(len(A)),bounds=[(-50,50)]*m,method="highs")
print("n",n,"K",K,"distinct deltas",len(A),"feasible",res.status==0)
if res.status==0: print({nm:round(w,3) for nm,w in zip(names,res.x) if abs(w)>1e-9})
