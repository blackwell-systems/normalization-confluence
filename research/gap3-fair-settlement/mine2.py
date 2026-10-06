import sys, json, collections
import verify as V
n=int(sys.argv[1]); files=sys.argv[2:]
nets=[tt for f in files for tt in json.load(open(f))]
N=1<<n
def outs(tt,x):
    G=V.local_graph(tt,n,x); return [next(iter(G[j])) if G[j] else None for j in range(n)]
def path(out,v):
    s=[v]
    while out[s[-1]] is not None: s.append(out[s[-1]])
    return s
st=collections.Counter(); ex={}
for tt in nets:
    p=[y for y in range(N) if not V.unstable(tt,n,y)][0]
    for x in range(N):
        U=V.unstable(tt,n,x)
        if len(U)!=2: continue
        ox=outs(tt,x)
        Rx=set(path(ox,U[0]))|set(path(ox,U[1]))
        for v in U:
            y=x^(1<<v); U2=V.unstable(tt,n,y)
            if len(U2)!=2: continue
            w=ox[v]; b=[u for u in U if u!=v][0]
            oy=outs(tt,y); Ry=set(path(oy,U2[0]))|set(path(oy,U2[1]))
            st["moves"]+=1
            vb = V.bit(x,v)==V.bit(p,v); wg = V.bit(x,w)!=V.bit(p,w)
            if vb and wg: st["good_inc"]+=1; ex.setdefault("good_inc",(tt,x,v))
            if not Ry<=Rx: st["R_notsub"]+=1; ex.setdefault("R_notsub",(tt,x,v))
            if not Ry<=Rx-{v}: st["R_notsub_minus_v"]+=1
            if len(Ry)>len(Rx): st["R_inc"]+=1
            if v in Ry: st["v_in_Ry"]+=1
            if b in path(ox,v): st["b_down_v_x"]+=1
            if v in path(ox,b): st["v_down_b_x"]+=1
print(n,len(nets),dict(st))
for k in ex: print(k, ex[k])
