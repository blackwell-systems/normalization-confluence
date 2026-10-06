"""Check the k=2 proof steps on sampled (A)+(B) networks with verify.py primitives.
L0  every 2-token state has g >= 1 (non-expansiveness)
L1  rigidity at g=1 states: every j in D has an out-arc into (D minus b) + {v}; out(v), if any, is not in D
L2  g non-increasing along count-preserving 2-token moves
L3  swap: from a g=1 state z, if 'tail then head' keeps 2 tokens then 'head then tail' does too
L4  'tail then head' and 'head then tail' both reach F(z)"""
import sys, json, collections
import verify as V
n=int(sys.argv[1]); nets=[tt for f in sys.argv[2:] for tt in json.load(open(f))]; N=1<<n
st=collections.Counter()
def outs(tt,x):
    G=V.local_graph(tt,n,x); return [next(iter(G[j])) if G[j] else None for j in range(n)]
for tt in nets:
    p=[y for y in range(N) if not V.unstable(tt,n,y)][0]
    for z in range(N):
        U=V.unstable(tt,n,z)
        if len(U)!=2: continue
        D={i for i in range(n) if V.bit(z,i)!=V.bit(p,i)}
        g=len(set(U)&D); st["states"]+=1
        if g<1: st["L0_fail"]+=1
        o=outs(tt,z)
        if g==1:
            b=[u for u in U if u in D][0]; v=[u for u in U if u not in D][0]
            if any(o[j] is None or o[j] not in (D-{b})|{v} for j in D): st["L1a_fail"]+=1
            if o[v] is not None and o[v] in D: st["L1b_fail"]+=1
            zb=z^(1<<b)
            if len(V.unstable(tt,n,zb))==2 and v in V.unstable(tt,n,zb):
                zbv=zb^(1<<v)
                if len(V.unstable(tt,n,zbv))==2:
                    st["L3_cases"]+=1
                    zv=z^(1<<v)
                    ok=len(V.unstable(tt,n,zv))==2 and b in V.unstable(tt,n,zv) and len(V.unstable(tt,n,zv^(1<<b)))==2
                    if not ok: st["L3_fail"]+=1
            Fz=z^(1<<b)^(1<<v)
            if Fz!=sum((tt[i][z]<<i) for i in range(n)): st["L4_fail"]+=1
        for u in U:
            y=z^(1<<u); U2=V.unstable(tt,n,y)
            if len(U2)!=2: continue
            D2={i for i in range(n) if V.bit(y,i)!=V.bit(p,i)}
            if len(set(U2)&D2)>g: st["L2_fail"]+=1
print(n,dict(st))
