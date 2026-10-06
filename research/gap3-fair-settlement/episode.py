"""SAT falsification of episode orders for K = 3 (default). (A)+(B), fixed point p = 0 (translation),
a symbolic asynchronous walk x_0 -> ... -> x_L (one-hot states, no repeated state) with exactly K
unstable vertices at every state. A token at v is good iff x_v = 1 (v in D(x) = x xor p).
Modes:
  e30    : x_0 and x_L have no bad token, some state in between has one, and d(x_L) >= d(x_0)
           (does d fall between consecutive visits to all-good states?)
  sameU  : U(x_L) = U(x_0) as vertex sets and d(x_L) >= d(x_0)
           (does d fall over an episode that returns the tokens to the same vertices?)
  sameUt : as sameU, and every token keeps its type (good/bad)
  e21    : every state has exactly one bad token, U(x_L) = U(x_0), d(x_L) >= d(x_0)
SAT = the episode order is violated (a witness walk is printed and replayed by verify.py).
Usage: episode.py n L mode [K]"""
import sys, itertools, json, time
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType
from enc import Enc
import verify as V
n=int(sys.argv[1]); L=int(sys.argv[2]); mode=sys.argv[3]; K=int(sys.argv[4]) if len(sys.argv)>4 else 3
e=Enc(n,A=True,B=True,target="none"); N=1<<n; P=e.pool; cnf=e.cnf
for i in range(n): cnf.append([-e.F[i][0]])
def exact(x):
    s=P.id(("ex",x))
    for S in itertools.combinations(range(n),K+1): cnf.append([-s]+[-e.u(x,q) for q in S])
    for S in itertools.combinations(range(n),n-K+1): cnf.append([-s]+[e.u(x,q) for q in S])
    return s
sel={x:exact(x) for x in range(N)}
def nbad(x, op, b):
    """literal-free helper: clauses saying (#tokens v with x_v = 0) op b, guarded by selector"""
    s=P.id(("nb",x,op,b)); zeros=[v for v in range(n) if not (x>>v)&1]
    if op=="<=":
        for S in itertools.combinations(zeros,b+1): cnf.append([-s]+[-e.u(x,v) for v in S])
    elif op==">=":
        for S in itertools.combinations(zeros,max(len(zeros)-b+1,0)):
            if len(S)==0: cnf.append([-s]); break
            cnf.append([-s]+[e.u(x,v) for v in S])
    return s
pc=lambda x: bin(x).count("1")
z=[[P.id(("z",t,x)) for x in range(N)] for t in range(L+1)]
for t in range(L+1):
    cnf.append(z[t][:])
    am=CardEnc.atmost(lits=z[t],bound=1,top_id=P.top,encoding=EncType.seqcounter)
    cnf.extend(am.clauses); P.occupy(P.top+1,am.nv); P.top=max(P.top,am.nv)
    for x in range(N): cnf.append([-z[t][x],sel[x]])
for x in range(N):
    cnf.extend(CardEnc.atmost(lits=[z[t][x] for t in range(L+1)],bound=1,top_id=P.top,encoding=EncType.pairwise).clauses)
for t in range(L):
    for x in range(N):
        ms=[]
        for v in range(n):
            m=P.id(("m",t,x,v)); ms.append(m)
            cnf.extend([[-m,e.u(x,v)],[-m,z[t+1][x^(1<<v)]]])
        cnf.append([-z[t][x]]+ms)
# d(x_L) >= d(x_0)
for a in range(N):
    for b in range(N):
        if pc(b)<pc(a): cnf.append([-z[0][a],-z[L][b]])
def tokvar(t,v):
    q=P.id(("tk",t,v))
    for x in range(N):
        cnf.append([-z[t][x],-e.u(x,v),q]); cnf.append([-z[t][x],e.u(x,v),-q])
    return q
def goodvar(t,v):  # token at v and x_v = 1
    q=P.id(("gd",t,v))
    for x in range(N):
        if (x>>v)&1: cnf.extend([[-z[t][x],-e.u(x,v),q],[-z[t][x],e.u(x,v),-q]])
        else: cnf.append([-z[t][x],-q])
    return q
if mode=="e30":
    for t in (0,L):
        for x in range(N): cnf.append([-z[t][x],nbad(x,"<=",0)])
    mids=[]
    for t in range(1,L):
        for x in range(N):
            q=P.id(("mid",t,x)); mids.append(q)
            cnf.extend([[-q,z[t][x]],[-q,nbad(x,">=",1)]])
    cnf.append(mids)
if mode in ("sameU","sameUt","e21"):
    for v in range(n):
        a=tokvar(0,v); b=tokvar(L,v); cnf.extend([[-a,b],[a,-b]])
        if mode=="sameUt":
            a=goodvar(0,v); b=goodvar(L,v); cnf.extend([[-a,b],[a,-b]])
if mode=="e21":
    for t in range(L+1):
        for x in range(N):
            cnf.append([-z[t][x],nbad(x,"<=",1)]); cnf.append([-z[t][x],nbad(x,">=",1)])
t0=time.time()
with Solver(name="cadical195",bootstrap_with=cnf.clauses) as s:
    sat=s.solve(); r={"n":n,"L":L,"mode":mode,"K":K,"sat":sat,"t":round(time.time()-t0,1)}
    if sat:
        mdl=s.get_model(); pos=set(l for l in mdl if l>0); tt=e.decode(mdl)
        st=[next(x for x in range(N) if z[t][x] in pos) for t in range(L+1)]
        ok=V.check_A(tt,n) and V.check_B(tt,n) and all(len(V.unstable(tt,n,x))==K for x in st) and \
           all(bin(st[t]^st[t+1]).count("1")==1 and ((st[t]^st[t+1]).bit_length()-1) in V.unstable(tt,n,st[t]) for t in range(L))
        r["walk"]=[(V.fmt(x,n),"".join("g" if (x>>u)&1 else "b" for u in V.unstable(tt,n,x)),V.unstable(tt,n,x)) for x in st]
        r["verified"]=ok; r["d"]=[pc(x) for x in st]
print(json.dumps(r))
