"""Cycle target with sound symmetry breaking: translation x -> x xor a (g(x) = f(x xor a) xor a
has G_g(x) = G_f(x xor a) as unsigned graphs and an isomorphic state graph) lets a cycle state be 0;
a vertex permutation lets the cycle's first move from 0 flip vertex 0. Both preserve (A) and (B)."""
import sys, time, json
from pysat.solvers import Solver
from enc import Enc
import verify as V
n=int(sys.argv[1]); A=sys.argv[2]=="1"; B=sys.argv[3]=="1"; solver=sys.argv[4] if len(sys.argv)>4 else "cadical195"
t0=time.time(); e=Enc(n,A=A,B=B,target="cycle")
e.cnf.append([e.c[0]]); e.cnf.append([e.pool.id(("e",0,0))])
with Solver(name=solver,bootstrap_with=e.cnf.clauses) as s:
    sat=s.solve(); m=s.get_model() if sat else None
r={"n":n,"A":A,"B":B,"sym":True,"solver":solver,"sat":sat,"t":round(time.time()-t0,1)}
if sat:
    tt=e.decode(m); r.update(tt=tt,chkA=V.check_A(tt,n),chkB=V.check_B(tt,n),cyc=V.async_cyclic(tt,n),fair=bool(V.fair_witness(tt,n)))
print(json.dumps(r))
