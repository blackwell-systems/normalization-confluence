"""Longest path in the abstract game DAG (game.py). Usage: gamelong.py n K"""
import sys, itertools
from game import forests, moves
n=int(sys.argv[1]); K=int(sys.argv[2])
F=forests(n); nodes=[(o,U) for o in F for U in itertools.combinations(range(n),K)]
idx={nd:i for i,nd in enumerate(nodes)}
adj=[[(v,idx[(o2,U2)]) for v,o2,U2 in moves(o,U,n)] for (o,U) in nodes]
h=[None]*len(nodes); nxt=[None]*len(nodes)
sys.setrecursionlimit(100000)
def H(i):
    if h[i] is not None: return h[i]
    best=0; b=None
    for v,j in adj[i]:
        if H(j)+1>best: best=H(j)+1; b=(v,j)
    h[i]=best; nxt[i]=b; return best
for i in range(len(nodes)): H(i)
m=max(h); i=h.index(m); print("n",n,"K",K,"longest",m)
from collections import Counter; print(sorted(Counter(h).items()))
while True:
    print("  ",nodes[i]); 
    if nxt[i] is None: break
    print("     fire",nxt[i][0]); i=nxt[i][1]
