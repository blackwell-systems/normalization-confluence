"""Sample (A)+(B) networks that contain a long asynchronous walk whose states all have exactly K
unstable vertices (default K = 3). The walk is symbolic (one-hot state per step, no repeated
state) and the SAT phases are random, so the solver chooses the network and the walk together.
This avoids the degenerate near-constant networks a plain random-phase sampler returns (K2.md,
section 2). Option nonconst=c also asks that at most c coordinates f_i are constant functions.
Usage: sample3.py n lim L seed [K] [nonconst=c]
Writes walk<K>_<n>_<L>_<seed>.json: a list of {"tt": network, "walk": [start, v1, v2, ...]}."""
import sys, random, json, itertools
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType
from enc import Enc
n=int(sys.argv[1]); lim=int(sys.argv[2]); L=int(sys.argv[3]); seed=int(sys.argv[4])
K=3; nonconst=None
for a in sys.argv[5:]:
    if a.startswith("nonconst="): nonconst=int(a.split("=")[1])
    else: K=int(a)
e=Enc(n,A=True,B=True,target="none"); N=1<<n; P=e.pool; cnf=e.cnf
def exact(x):
    s=P.id(("ex",x))
    for S in itertools.combinations(range(n),K+1): cnf.append([-s]+[-e.u(x,q) for q in S])
    for S in itertools.combinations(range(n),n-K+1): cnf.append([-s]+[e.u(x,q) for q in S])
    return s
sel={x:exact(x) for x in range(N)}
z=[[P.id(("z",t,x)) for x in range(N)] for t in range(L+1)]
for t in range(L+1):
    cnf.append(z[t][:])
    am=CardEnc.atmost(lits=z[t],bound=1,top_id=P.top,encoding=EncType.seqcounter)
    cnf.extend(am.clauses); P.occupy(P.top+1,am.nv); P.top=max(P.top,am.nv)
    for x in range(N): cnf.append([-z[t][x],sel[x]])
for x in range(N):  # no repeated state
    cnf.extend(CardEnc.atmost(lits=[z[t][x] for t in range(L+1)],bound=1,top_id=P.top,encoding=EncType.pairwise).clauses)
for t in range(L):
    for x in range(N):
        ms=[]
        for v in range(n):
            m=P.id(("m",t,x,v)); ms.append(m)
            cnf.extend([[-m,e.u(x,v)],[-m,z[t+1][x^(1<<v)]]])
        cnf.append([-z[t][x]]+ms)
if nonconst is not None:
    cs=[]
    for i in range(n):
        c=P.id(("const",i)); cs.append(c)
        for x in range(1,N):
            cnf.extend([[-c,-e.F[i][0],e.F[i][x]],[-c,e.F[i][0],-e.F[i][x]]])
        ds=[]
        for x in range(1,N):
            d=P.id(("dif",i,x)); ds.append(d)
            cnf.extend([[-d,e.F[i][0],e.F[i][x]],[-d,-e.F[i][0],-e.F[i][x]]])
        cnf.append([c]+ds)
    card=CardEnc.atmost(lits=cs,bound=nonconst,top_id=P.top,encoding=EncType.seqcounter)
    P.occupy(P.top+1,card.nv+1); cnf.extend(card.clauses)
Fv=[v for row in e.F for v in row]
rnd=random.Random(seed); out=[]
with Solver(name="cadical195",bootstrap_with=cnf.clauses) as s:
    while len(out)<lim:
        s.set_phases([v if rnd.random()<0.5 else -v for v in Fv])
        if not s.solve(): break
        mdl=s.get_model(); pos=set(l for l in mdl if l>0); tt=e.decode(mdl)
        st=[next(x for x in range(N) if z[t][x] in pos) for t in range(L+1)]
        walk=[st[0]]+[(st[t]^st[t+1]).bit_length()-1 for t in range(L)]
        out.append({"tt":tt,"walk":walk})
        s.add_clause([-v if v in pos else v for v in Fv])
json.dump(out,open(f"walk{K}_{n}_{L}_{seed}.json","w")); print(n,"K",K,"L",L,len(out))
