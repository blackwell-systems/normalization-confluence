"""Independent second encoding (z3): (A) via an integer topological rank of each G(x),
(B) via pseudo-Boolean AtMost, and a closed walk x_0 -> ... -> x_L = x_0 of exact length L in the
asynchronous state graph, states as bit-vectors, each step flipping one unstable vertex."""
import sys, time
from z3 import *
n=int(sys.argv[1]); N=1<<n; Ls=[int(a) for a in sys.argv[2:]]
F=[[Bool(f"F_{i}_{x}") for x in range(N)] for i in range(n)]
base=[]
def arc(x,j,i): return Xor(F[i][x],F[i][x^(1<<j)])
for x in range(N):
    rk=[Int(f"rk_{x}_{v}") for v in range(n)]
    for j in range(n):
        for i in range(n):
            base.append(Implies(arc(x,j,i), rk[j] < rk[i]))
        if 0: base.append(AtMost(*[arc(x,j,i) for i in range(n)],1))
def fv(i,s):  # f_i at bit-vector state s
    return Or([And(s==x,F[i][x]) for x in range(N)])
for L in Ls:
    t0=time.time(); S=Solver(); S.add(base)
    st=[BitVec(f"s_{L}_{k}",n) for k in range(L)]
    vs=[Int(f"v_{L}_{k}") for k in range(L)]
    for k in range(L):
        s=st[k]; t=st[(k+1)%L]
        S.add(vs[k]>=0, vs[k]<n)
        for v in range(n):
            bitv = Extract(v,v,s)==1
            S.add(Implies(vs[k]==v, And(t==s^BitVecVal(1<<v,n), fv(v,s)!=bitv)))
    r=S.check(); print("L",L,r,round(time.time()-t0,1),flush=True)
