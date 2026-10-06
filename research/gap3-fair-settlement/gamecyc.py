"""Find a shortest cycle of the abstract game (game.py) through a given configuration's SCC.
Usage: gamecyc.py n K   (prints a shortest cycle found by BFS from each node of a cyclic SCC)"""
import sys, itertools
from collections import deque
from game import forests, moves
n=int(sys.argv[1]); K=int(sys.argv[2])
F=forests(n); nodes=[(o,U) for o in F for U in itertools.combinations(range(n),K)]
idx={nd:i for i,nd in enumerate(nodes)}
adj=[None]*len(nodes)
def A(i):
    if adj[i] is None:
        o,U=nodes[i]; adj[i]=[(v,idx[(o2,U2)]) for v,o2,U2 in moves(o,U,n)]
    return adj[i]
start=idx[((2, -1, 1, -1, 5, 3), (0, 3, 5))]
best=None
# BFS from start back to start
prev={start:None}; q=deque([start]); found=None
while q and found is None:
    i=q.popleft()
    for v,j in A(i):
        if j==start: found=(i,v); break
        if j not in prev: prev[j]=(i,v); q.append(j)
cyc=[]; i,v=found; cyc.append((i,v))
while prev[i] is not None:
    pi,pv=prev[i]; cyc.append((pi,pv)); i=pi
cyc.reverse()
print("cycle length",len(cyc))
for i,v in cyc: print(nodes[i],"fire",v)
