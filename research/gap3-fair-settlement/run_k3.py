"""k = 3 exactly: search for a network with (A)+(B) and a closed asynchronous run (a nonempty set C
of states, each with a chosen state-graph edge into C) such that every state of C has EXACTLY K
unstable vertices (K = 3 by default; pass k=<K> in the options for another value).
Sound strengthenings as in run_k2.py:
  sym    : a C state is 0 and its chosen edge flips vertex 0 (translation and permutation symmetry)
  tok    : each chosen edge passes a token (implied by "exactly K" at both ends; kept as a hint)
  alldir : every vertex is flipped on some chosen edge. Sound once every smaller n is decided for
           k = K and k < K is excluded for every n: a closed run flipping only the vertices in I is a
           closed run of the subcube network on I (which keeps (A) and (B)); its token count inside I
           is constant on the run (ucnt_mono) and at most K, so it is a closed run with fewer than K
           tokens (excluded by one_token_closed / two_token_closed for K = 3) or with exactly K
           tokens on fewer than n vertices (excluded by the smaller-n decision).
  rank   : encode (A) by a ranking of each G(x) (order encoding) instead of one clause per
           elementary cycle; under (B) both say that each G(x) is acyclic
  noA    : replace (A) by "no self-loops" (sanity check: cycles must be found at once)
  Aon    : weaker hypothesis for exploring the proof: "no self-loops" everywhere and (A) only at
           the states of C (combine with fp0 to also require a fixed point, at 0 by translation;
           sym must then be dropped, since it also uses translation)
  fp0    : require f(0) = 0
  Aone   : "no self-loops" everywhere and (A) only at the single state 0 (with sym, 0 is in C)
  psym   : sound symmetry breaking through the fixed point instead of sym: under (A)+(B) the
           fixed point p is unique (Shih and Dong), so translate p to 0 (f(0) = 0); permutation
           symmetry still lets the chosen edge at some C state flip vertex 0 (implied by alldir)
  pbad   : implied facts with p = 0: at a C state at most floor(K/2) tokens v have x_v = 0
           (bad tokens), since |F(x)| = |x xor U(x)| <= |x| (non-expansiveness at p)
"""
import sys, time, json, itertools
from pysat.solvers import Solver
from enc import Enc
import verify as V
n=int(sys.argv[1]); opts=sys.argv[2].split(","); solver=sys.argv[3] if len(sys.argv)>3 else "cadical195"
K=3
for o in opts:
    if o.startswith("k="): K=int(o[2:])
rank="rank" in opts
noA="noA" in opts or "Aon" in opts or "Aone" in opts
t_build=time.time()
e=Enc(n,A=(not rank and not noA),B=True,target="cycle"); N=1<<n; P=e.pool; cnf=e.cnf
if noA:
    for x in range(N):
        for v in range(n): e.cnf.append([-e.arc[(x,v,v)]])
if "Aon" in opts:
    from enc import elem_cycles
    cyc=[c for c in elem_cycles(n) if len(c)>1]
    for x in range(N):
        for c in cyc:
            k=len(c); cnf.append([-e.c[x]]+[-e.arc[(x,c[t],c[(t+1)%k])] for t in range(k)])
if "Aone" in opts:
    from enc import elem_cycles
    for c in elem_cycles(n):
        if len(c)>1:
            k=len(c); cnf.append([-e.arc[(0,c[t],c[(t+1)%k])] for t in range(k)])
if "psym" in opts:
    for i in range(n): cnf.append([-e.F[i][0]])
if "pbad" in opts:
    for x in range(N):
        zeros=[v for v in range(n) if not (x>>v)&1]
        for S in itertools.combinations(zeros,K//2+1):
            cnf.append([-e.c[x]]+[-e.u(x,v) for v in S])
if "fp0" in opts:
    for i in range(n): cnf.append([-e.F[i][0]])
if rank and not noA:
    for x in range(N):
        g=lambda i,t: P.id(("rk",x,i,t))   # rank(i) >= t, t = 1..n
        for i in range(n):
            cnf.append([-g(i,n)])  # rank < n
            for t in range(2,n+1): cnf.append([-g(i,t),g(i,t-1)])
        for j in range(n):
            for i in range(n):
                a=e.arc[(x,j,i)]
                if i==j: cnf.append([-a]); continue
                cnf.append([-a,g(j,1)])
                for t in range(1,n): cnf.append([-a,-g(i,t),g(j,t+1)])
E=lambda x,v: P.id(("e",x,v))
if "sym" in opts: cnf.append([e.c[0]]); cnf.append([E(0,0)])
if "tok" in opts:
    for x in range(N):
        for v in range(n):
            ws=[]
            for w in range(n):
                if w==v: continue
                t=P.id(("tok",x,v,w)); ws.append(t)
                cnf.extend([[-t,e.arc[(x,v,w)]],[-t,-e.u(x,w)]])
            cnf.append([-E(x,v)]+ws)
if "alldir" in opts:
    for v in range(n): cnf.append([E(x,v) for x in range(N)])
for x in range(N):
    # at most K unstable
    for S in itertools.combinations(range(n),K+1):
        cnf.append([-e.c[x]]+[-e.u(x,w) for w in S])
    # at least K unstable: every (n-K+1)-set contains an unstable vertex
    for S in itertools.combinations(range(n),n-K+1):
        cnf.append([-e.c[x]]+[e.u(x,w) for w in S])
t_build=time.time()-t_build
t0=time.time()
with Solver(name=solver,bootstrap_with=cnf.clauses) as s:
    sat=s.solve(); m=s.get_model() if sat else None
r={"n":n,"opts":opts,"solver":solver,"k":"exactly %d"%K,"sat":sat,"t":round(time.time()-t0,1),
   "build":round(t_build,1),"vars":P.top,"clauses":len(cnf.clauses)}
if sat:
    tt=e.decode(m); C=e.decode_c(m)
    r.update(tt=tt,chkA=V.check_A(tt,n),chkB=V.check_B(tt,n),cyc=V.async_cyclic(tt,n),
             fair=bool(V.fair_witness(tt,n)),
             ucnt=sorted(set(len(V.unstable(tt,n,x)) for x in C)))
print(json.dumps(r),flush=True)
