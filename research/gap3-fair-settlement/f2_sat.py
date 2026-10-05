"""Exhaustive SAT test of Claim F2 at size n: networks with (B) and no self-loops; C a nonempty
set of states covered by chosen state-graph edges with in- and out-degree exactly one inside C
(a disjoint union of simple cycles); U the vertices flipped on chosen edges. Search for a state
x0 in C and u in U with no out-arc u -> w, w in U, in G(x0). UNSAT means F2 holds for every simple
cycle (one cycle is the special case of one component)."""
import sys, time, json
import verify as V
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType
from enc import Enc
n=int(sys.argv[1]); e=Enc(n,A=False,B=True,target="none"); N=1<<n; P=e.pool; cnf=e.cnf
for x in range(N):
    for v in range(n): cnf.append([-e.arc[(x,v,v)]])
c=[P.id(("C",x)) for x in range(N)]; E={(x,v):P.id(("E",x,v)) for x in range(N) for v in range(n)}
cnf.append(c)
for x in range(N):
    outs=[E[(x,v)] for v in range(n)]
    ins=[E[(x^(1<<v),v)] for v in range(n)]
    for v in range(n):
        cnf.extend([[-E[(x,v)],c[x]],[-E[(x,v)],c[x^(1<<v)]],[-E[(x,v)],e.u(x,v)]])
    cnf.append([-c[x]]+outs); cnf.append([-c[x]]+ins)
    for lits in (outs,ins):
        for i in range(n):
            for j in range(i+1,n): cnf.append([-lits[i],-lits[j]])
U=[P.id(("U",v)) for v in range(n)]
for v in range(n):
    cnf.append([-U[v]]+[E[(x,v)] for x in range(N)])
    for x in range(N): cnf.append([-E[(x,v)],U[v]])
r=[P.id(("r",x)) for x in range(N)]; q=[P.id(("q",u)) for u in range(n)]
cnf.append(r); cnf.append(q)
for x in range(N):
    cnf.append([-r[x],c[x]])
    for u in range(n):
        for w in range(n):
            if w!=u: cnf.append([-r[x],-q[u],-e.arc[(x,u,w)],-U[w]])
for u in range(n): cnf.append([-q[u],U[u]])
# single cycle: every state of C reachable from r along chosen edges
for p_ in range(N):
    for q_ in range(p_+1,N): cnf.append([-r[p_],-r[q_]])
T=N
d=[[P.id(("d",x,t)) for t in range(T)] for x in range(N)]
for x in range(N):
    cnf.append([-d[x][0],r[x]])
    for t in range(T-1):
        gs=[]
        for v in range(n):
            y=x^(1<<v); g=P.id(("dg",x,t,v)); gs.append(g)
            cnf.extend([[-g,d[y][t]],[-g,E[(y,v)]]])
        cnf.append([-d[x][t+1],d[x][t]]+gs)
    cnf.append([-c[x],d[x][T-1]])
t=time.time()
with Solver(name="cadical195",bootstrap_with=cnf.clauses) as s:
    ok=s.solve(); print(n,"F2 counterexample (single cycle):",ok,round(time.time()-t,1))
    if ok:
        m=s.get_model(); pos=set(l for l in m if l>0); tt=e.decode(m)
        C=[x for x in range(N) if c[x] in pos]; x0=[x for x in range(N) if r[x] in pos][0]; u=[v for v in range(n) if q[v] in pos][0]
        cyc=[x0]; x=x0
        while True:
            v=[v for v in range(n) if E[(x,v)] in pos][0]; x^=1<<v; cyc.append(x)
            if x==x0: break
        print(json.dumps({"tt":tt,"cycle":[V.fmt(z,n) for z in cyc],"x0":V.fmt(x0,n),"u":u,"B":V.check_B(tt,n)}))
        for z in cyc[:-1]:
            G=V.local_graph(tt,n,z); print(V.fmt(z,n),"unstable",V.unstable(tt,n,z),{j:sorted(G[j]) for j in range(n) if G[j]},"localcyc",V.has_cycle(G,n))
