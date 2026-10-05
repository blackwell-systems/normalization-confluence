"""Localized question: with (B) everywhere and no self-loops everywhere, can a cycle of the
asynchronous state graph avoid every state whose local graph has a cycle?  Mode 'on': (A) enforced
only at states of C.  Mode 'onnbr': (A) enforced at states of C and their cube neighbours."""
import sys, time, json
from pysat.solvers import Solver
from enc import Enc, elem_cycles
import verify as V
n=int(sys.argv[1]); mode=sys.argv[2]; Bflag=(len(sys.argv)<=3 or sys.argv[3]!="noB")
e=Enc(n,A=False,B=Bflag,target="cycle"); N=1<<n; cnf=e.cnf; P=e.pool
for x in range(N):
    for v in range(n): cnf.append([-e.arc[(x,v,v)]])
guard={}
for x in range(N):
    if mode=="on": guard[x]=e.c[x]
    else:
        g=P.id(("near",x)); guard[x]=g
        cnf.append([-e.c[x],g])
        for v in range(n): cnf.append([-e.c[x^(1<<v)],g])
cyc=[c for c in elem_cycles(n) if len(c)>1]
for x in range(N):
    for c in cyc:
        k=len(c); cnf.append([-guard[x]]+[-e.arc[(x,c[t],c[(t+1)%k])] for t in range(k)])
t0=time.time()
with Solver(name="cadical195",bootstrap_with=cnf.clauses) as s:
    sat=s.solve(); m=s.get_model() if sat else None
r={"n":n,"mode":mode,"B":Bflag,"sat":sat,"t":round(time.time()-t0,1)}
if sat:
    tt=e.decode(m); C=e.decode_c(m)
    r["C"]=[V.fmt(x,n) for x in C]; r["A_global"]=V.check_A(tt,n)
    r["localcyc_states"]=[V.fmt(x,n) for x in range(N) if V.has_cycle(V.local_graph(tt,n,x),n)]
print(json.dumps(r))
