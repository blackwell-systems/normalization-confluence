"""Exploration: weaker forms of (A) at the run states (B everywhere, no self-loops everywhere).
mode len2   : forbid only 2-cycles at run states
mode len3+  : forbid only cycles of length >= 3 at run states
mode tok    : forbid only cycles through at least one token (unstable vertex) at run states
mode notok  : forbid only cycles avoiding all tokens at run states
mode reach  : forbid cycles reachable from a token (a token's out-path enters a cycle) at run states
Usage: avar.py n K mode"""
import sys, itertools, json, time
from pysat.solvers import Solver
from enc import Enc, elem_cycles
import verify as V
n=int(sys.argv[1]); K=int(sys.argv[2]); mode=sys.argv[3]
e=Enc(n,A=False,B=True,target="cycle"); N=1<<n; P=e.pool; cnf=e.cnf
for x in range(N):
    for v in range(n): cnf.append([-e.arc[(x,v,v)]])
cyc=[c for c in elem_cycles(n) if len(c)>1]
for x in range(N):
    for c in cyc:
        L=len(c); base=[-e.c[x]]+[-e.arc[(x,c[t],c[(t+1)%L])] for t in range(L)]
        if mode=="len2" and L!=2: continue
        if mode=="len3+" and L<3: continue
        if mode=="tok":
            # some vertex of c unstable: clause  (not all arcs) or (all stable on c)  -> per vertex selector
            # forbid: arcs of c all present AND some vertex of c unstable  ==  for each w in c: clause
            for w in c: cnf.append(base+[-e.u(x,w)])
            continue
        if mode=="fired":
            for w in c: cnf.append(base+[-P.id(("e",x,w))])
            continue
        if mode=="tok2":
            for a,b in itertools.combinations(c,2): cnf.append(base+[-e.u(x,a),-e.u(x,b)])
            continue
        if mode=="notok":
            cnf.append(base+[e.u(x,w) for w in c]); continue
        if mode=="reach":
            # forbid cycle c with any token whose out-path enters c: approximate by token on c or a
            # token t with a path t -> ... -> c; encode reachability via helper vars below
            continue
        cnf.append(base)
if mode=="reach":
    for x in range(N):
        r=[P.id(("rch",x,i)) for i in range(n)]  # r_i: i reachable from a token at x
        for i in range(n):
            cnf.append([-e.c[x],-e.u(x,i),r[i]])
            for j in range(n):
                if j!=i: cnf.append([-e.c[x],-r[j],-e.arc[(x,j,i)],r[i]])
        for c in cyc:
            L=len(c); cnf.append([-e.c[x],-r[c[0]]]+[-e.arc[(x,c[t],c[(t+1)%L])] for t in range(L)])
for x in range(N):
    for S in itertools.combinations(range(n),K+1): cnf.append([-e.c[x]]+[-e.u(x,w) for w in S])
    for S in itertools.combinations(range(n),n-K+1): cnf.append([-e.c[x]]+[e.u(x,w) for w in S])
t0=time.time()
with Solver(name="cadical195",bootstrap_with=cnf.clauses) as s:
    sat=s.solve(); print(json.dumps({"n":n,"K":K,"mode":mode,"sat":sat,"t":round(time.time()-t0,1)}))
