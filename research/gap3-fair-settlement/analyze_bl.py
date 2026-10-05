"""Collect networks with (B) and no self-loops (A dropped) whose asynchronous graph has a cycle;
for each simple cycle found, test hypotheses about where a local cycle must appear.
H1: the 'last pass' arcs (u -> w_u used the last time u fired) all present in G(x) at some cycle state x
H2: some cycle state x has a local cycle in G(x)
H3: the local cycle at that state uses only last-pass arcs"""
import sys, random
from pysat.solvers import Solver
from enc import Enc
import verify as V
n=int(sys.argv[1]); lim=int(sys.argv[2])
e=Enc(n,A=False,B=True,target="cycle"); N=1<<n
for x in range(N):
    for v in range(n): e.cnf.append([-e.arc[(x,v,v)]])
Fv=[v for row in e.F for v in row]
def find_cycle(tt):
    g=V.state_graph(tt,n)
    for comp in V.sccs(g):
        if len(comp)>1:
            cs=set(comp); x0=comp[0]; path=[x0]; seen={x0:0}; x=x0
            while True:
                nxt=[y for y in g[x] if y in cs]
                # walk: choose successor, prefer unseen
                y=next((y for y in nxt if y not in seen), nxt[0]); 
                if y in seen: return path[seen[y]:]+[y]
                seen[y]=len(path); path.append(y); x=y
stats={"cycles":0,"H1_somestate":0,"H2":0,"allflip":0,"H1_everystate_after_warmup":0,"lastpass_arcs_cycle_in_G":0}
with Solver(name="cadical195",bootstrap_with=e.cnf.clauses) as s:
    rnd=random.Random(3); cnt=0
    while cnt<lim:
        s.set_phases([v if rnd.random()<0.5 else -v for v in Fv])
        if not s.solve(): break
        m=s.get_model(); pos=set(l for l in m if l>0); tt=e.decode(m); cnt+=1
        s.add_clause([-v if v in pos else v for v in Fv])
        cyc=find_cycle(tt)
        if not cyc: continue
        stats["cycles"]+=1
        L=len(cyc)-1; flips=[(cyc[t]^cyc[t+1]).bit_length()-1 for t in range(L)]
        U=set(flips); stats["allflip"]+= (len(U)==n)
        stats["H2"]+= any(V.has_cycle(V.local_graph(tt,n,x),n) for x in cyc[:-1])
        last={}
        for t in range(L):  # warm up
            x=cyc[t]; v=flips[t]; G=V.local_graph(tt,n,x); last[v]=next(iter(G[v])) if G[v] else None
        h1=False; h1all=True; h1cyc=False
        for t in range(L):
            x=cyc[t]; G=V.local_graph(tt,n,x)
            ok=all(w is not None and w in G[u] for u,w in last.items())
            h1|=ok; h1all&=ok
            adj=[set([last[u]]) if (u in last and last[u] is not None and last[u] in G[u]) else set() for u in range(n)]
            h1cyc|=V.has_cycle(adj,n)
            v=flips[t]; last[v]=next(iter(G[v])) if G[v] else None
        stats["H1_somestate"]+=h1; stats["H1_everystate_after_warmup"]+=h1all; stats["lastpass_arcs_cycle_in_G"]+=h1cyc
print(stats)
