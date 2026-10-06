"""Minimal unsatisfiable core of a game-cycle prefix (realize.py setting, local mode), by groups."""
import sys, json
from pysat.solvers import Solver
from enc import Enc, elem_cycles
cyc=json.loads(sys.argv[1]); n=int(sys.argv[2]); cut=int(sys.argv[3])
e=Enc(n,A=False,B=False,target="none"); N=1<<n; P=e.pool; hard=list(e.cnf.clauses)
for x in range(N):
    for v in range(n): hard.append([-e.arc[(x,v,v)]])
x=0; run=[]
for rep in range(2):
    for (o,U),v in cyc: run.append((x,o,U,v)); x^=1<<v
run=run[:cut]; S=[r[0] for r in run]
groups={}; soft=[]
def G(name):
    if name not in groups: groups[name]=P.id(("grp",name))
    return groups[name]
for t,(y,o,U,v) in enumerate(run):
    for j in range(n):
        for i in range(n):
            soft.append([-G(("arc",t,j))]+[e.arc[(y,j,i)] if o[j]==i else -e.arc[(y,j,i)]])
    for w in range(n):
        soft.append([-G(("tok",t,w))]+([e.u(y,w)] if w in U else [-e.u(y,w)]))
    for c in elem_cycles(n):
        if len(c)>1:
            L=len(c); soft.append([-G(("A",t))]+[-e.arc[(y,c[s],c[(s+1)%L])] for s in range(L)])
near=sorted(set(S)|set(s^(1<<j) for s in S for j in range(n)))
for z in near:
    for j in range(n):
        for a in range(n):
            for b in range(a+1,n): soft.append([-G(("B",z,j)),-e.arc[(z,j,a)],-e.arc[(z,j,b)]])
with Solver(name="cadical195",bootstrap_with=hard+soft) as s:
    ass=list(groups.values()); assert not s.solve(assumptions=ass)
    core=set(s.get_core())
    inv={v:k for k,v in groups.items()}
    cur=[a for a in ass if a in core]
    i=0
    while i<len(cur):
        trial=cur[:i]+cur[i+1:]
        if not s.solve(assumptions=trial): cur=trial
        else: i+=1
    def lab(k):
        if k[0]=="B": 
            z=k[1]; 
            where=[("run",S.index(z))] if z in S else [("nbr of t%d flip %d"%(S.index(s),(s^z).bit_length()-1)) for s in S if bin(s^z).count("1")==1][:2]
            return ("B", "state "+format(z,"0%db"%n)[::-1], "vertex",k[2], where)
        return k
    for a in cur: print(lab(inv[a]))
