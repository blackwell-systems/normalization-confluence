"""Exhaustive check of the last-pass conjecture over all networks with (B) and no self-loops at
n (enumerated by SAT), and over every simple cycle of the asynchronous graph:
claim: at some state x of the cycle (after one warm-up lap), the last-pass arcs u -> w_u that are
present in G(x) contain a cycle."""
import sys
from pysat.solvers import Solver
from enc import Enc
import verify as V
n=int(sys.argv[1]); maxnet=int(sys.argv[2]) if len(sys.argv)>2 else 10**9
mode=sys.argv[3] if len(sys.argv)>3 else "some"
e=Enc(n,A=False,B=True,target="none"); N=1<<n
for x in range(N):
    for v in range(n): e.cnf.append([-e.arc[(x,v,v)]])
Fv=[v for row in e.F for v in row]
def simple_cycles(g):
    out=[]
    for s in range(N):
        stack=[(s,[s])]
        while stack:
            x,p=stack.pop()
            for y in g[x]:
                if y==s: out.append(p+[s])
                elif y>s and y not in p: stack.append((y,p+[y]))
    return out
def claim(tt,cyc):
    L=len(cyc)-1; U=set((cyc[t]^cyc[t+1]).bit_length()-1 for t in range(L))
    res=[]
    for x in cyc[:-1]:
        G=V.local_graph(tt,n,x); res.append(all(G[u]&U for u in U))
    return any(res) if mode=="some" else all(res)
def claim_old(tt,cyc):
    L=len(cyc)-1; flips=[(cyc[t]^cyc[t+1]).bit_length()-1 for t in range(L)]
    last={}
    for t in range(L):
        G=V.local_graph(tt,n,cyc[t]); v=flips[t]; last[v]=next(iter(G[v])) if G[v] else None
    for t in range(L):
        G=V.local_graph(tt,n,cyc[t])
        adj=[set([last[u]]) if (u in last and last[u] is not None and last[u] in G[u]) else set() for u in range(n)]
        if V.has_cycle(adj,n): return True
        v=flips[t]; last[v]=next(iter(G[v])) if G[v] else None
    return False
nets=0; cyc_nets=0; cycles=0; fails=0; ex=None
with Solver(name="cadical195",bootstrap_with=e.cnf.clauses) as s:
    while nets<maxnet and s.solve():
        m=s.get_model(); pos=set(l for l in m if l>0); tt=e.decode(m); nets+=1
        s.add_clause([-v if v in pos else v for v in Fv])
        cs=simple_cycles(V.state_graph(tt,n))
        if cs: cyc_nets+=1
        for c in cs:
            cycles+=1
            if not claim(tt,c):
                fails+=1
                if ex is None: ex=(tt,c)
print("nets",nets,"with cycles",cyc_nets,"simple cycles",cycles,"claim fails",fails)
if ex: print("counterexample to claim", ex[0], [V.fmt(x,n) for x in ex[1]])
