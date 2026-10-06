"""SAT falsifiers for the k = 3 structural facts F1 and F2 (both follow from non-expansiveness at
the fixed point; this is the exhaustive check). (A)+(B), fixed point p = 0 (translation), state x =
bits 0..m-1 set (permutation symmetry), exactly 3 unstable vertices at x.
  F1: two of the tokens have x_v = 0 (two bad tokens).                        SAT = F1 fails.
  F2: one bad token, and some j in D(x) = supp(x) has an out-arc j -> i in G(x) with f_i(x) = 0
      (i not in M = F(x) xor p).                                              SAT = F2 fails.
Usage: fals_f12.py n"""
import sys, itertools, time
from pysat.solvers import Solver
from enc import Enc
n=int(sys.argv[1]); K=3
e=Enc(n,A=True,B=True,target="none"); N=1<<n; base=list(e.cnf.clauses)
for i in range(n): base.append([-e.F[i][0]])
def exact(x):
    cl=[]
    for S in itertools.combinations(range(n),K+1): cl.append([-e.u(x,q) for q in S])
    for S in itertools.combinations(range(n),n-K+1): cl.append([e.u(x,q) for q in S])
    return cl
res={"F1":False,"F2":False}; t0=time.time()
with Solver(name="cadical195",bootstrap_with=base) as s:
    for m in range(0,n+1):
        x=(1<<m)-1; zeros=list(range(m,n)); ones=list(range(m))
        for cl in exact(x): s.add_clause([-(P:=e.pool.id(("sel",x)))]+cl)
        sel=e.pool.id(("sel",x))
        # F1: two bad tokens (by symmetry: the first two zeros)
        if len(zeros)>=2:
            if s.solve(assumptions=[sel,e.u(x,zeros[0]),e.u(x,zeros[1])]): res["F1"]=True; print("F1 SAT m",m)
        # F2: exactly one bad token (zeros[0]), j = 0 in D, arc 0 -> i with f_i(x) = 0, for each i
        if zeros and ones:
            for i in range(1,n):
                ass=[sel,e.u(x,zeros[0])]+[-e.u(x,z) for z in zeros[1:]]+[e.arc[(x,0,i)],-e.F[i][x]]
                if s.solve(assumptions=ass): res["F2"]=True; print("F2 SAT m",m,"i",i)
print("n",n,"F1 violated" if res["F1"] else "F1 holds","|","F2 violated" if res["F2"] else "F2 holds","t",round(time.time()-t0,1))
