"""Variant hypotheses, to locate what (A) contributes beyond (B).
flags: L = no self-loop in any G(x); P = NoLocalPos; Q = NoLocalNeg; B = OutDeg1; X = a fixed point exists.
Target: a cycle in the asynchronous state graph (optionally the exact fair target)."""
import sys, time, json, itertools
from pysat.solvers import Solver
from enc import Enc, elem_cycles
import verify as V
n=int(sys.argv[1]); flags=sys.argv[2]; target=sys.argv[3] if len(sys.argv)>3 else "cycle"
e=Enc(n,A=False,B=("B" in flags),target=target); N=1<<n; cnf=e.cnf
if "L" in flags:
    for x in range(N):
        for v in range(n): cnf.append([-e.arc[(x,v,v)]])
for want,flag in ((0,"P"),(1,"Q")):   # forbid cycles of sign 'want' (0 positive, 1 negative)
    if flag not in flags: continue
    for x in range(N):
        for c in elem_cycles(n):
            k=len(c); arcs=[e.arc[(x,c[t],c[(t+1)%k])] for t in range(k)]
            # sign = xor_t lneg(x, c[t], c[t+1]) = xor_t (F[c[t+1]][x] xor x_{c[t]}) = xor_i F[i][x] xor xor_i x_i over i in c
            const=0
            for i in c: const ^= (x>>i)&1
            for vals in itertools.product((0,1),repeat=k):
                s=const
                for b in vals: s^=b
                if s!=want: continue
                cnf.append([-a for a in arcs]+[(-e.F[i][x] if b else e.F[i][x]) for i,b in zip(c,vals)])
if "X" in flags:
    ps=[]
    for p in range(N):
        a=e.pool.id(("fp",p)); ps.append(a)
        for i in range(n): cnf.append([-a, e.F[i][p] if (p>>i)&1 else -e.F[i][p]])
    cnf.append(ps)
t0=time.time()
with Solver(name="cadical195",bootstrap_with=cnf.clauses) as s:
    sat=s.solve(); m=s.get_model() if sat else None
r={"n":n,"flags":flags,"target":target,"sat":sat,"t":round(time.time()-t0,1)}
if sat:
    tt=e.decode(m); r["tt"]=tt; r["chkB"]=V.check_B(tt,n); r["chkA"]=V.check_A(tt,n)
    r["fixed_points"]=[V.fmt(x,n) for x in range(N) if all(tt[i][x]==V.bit(x,i) for i in range(n))]
    fw=V.fair_witness(tt,n); r["fair"]=bool(fw)
    if fw: r["fair_start"]=V.fmt(fw[0][0],n); r["fair_word"]=fw[1]; r["fair_ok"]=V.verify_fair_run(tt,n,fw[0][0],fw[1])
print(json.dumps(r))
