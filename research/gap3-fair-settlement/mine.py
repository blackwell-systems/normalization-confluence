"""Mine k=2 count-preserving moves of sampled (A)+(B) networks for monotone token-pair quantities."""
import sys, json, itertools, collections
import verify as V
n=int(sys.argv[1]); files=sys.argv[2:]
nets=[tt for f in files for tt in json.load(open(f))]
N=1<<n
def info(tt,x):
    G=V.local_graph(tt,n,x)
    out=[next(iter(G[j])) if G[j] else None for j in range(n)]
    return out
def path(out,v):
    s=[v]
    while out[s[-1]] is not None: s.append(out[s[-1]])
    return s
def undist(out,a,b):
    pa,pb=path(out,a),path(out,b)
    ia={v:i for i,v in enumerate(pa)}
    for j,v in enumerate(pb):
        if v in ia: return ia[v]+j
    return 99
def cands(tt,x,p,U):
    out=info(tt,x); a,b=U
    pa,pb=path(out,a),path(out,b)
    D=[i for i in range(n) if V.bit(x,i)!=V.bit(p,i)]
    up=lambda v: {u for u in range(n) if v in path(out,u)}
    c={}
    c["dist"]=undist(out,a,b)
    c["anc"]=int(b in pa or a in pb)
    c["meet"]=int(bool(set(pa)&set(pb)))
    c["hsum"]=len(pa)+len(pb)
    c["hmax"]=max(len(pa),len(pb))
    c["dp"]=len(D)
    c["good"]=sum(1 for v in U if v in D)
    c["Dpaths"]=len((set(pa)|set(pb))&set(D))
    c["union"]=len(set(pa)|set(pb))
    c["upcone"]=len(up(a)|up(b))
    c["upmeet"]=int(bool(up(a)&up(b)))
    c["roots_eq"]=int(pa[-1]==pb[-1])
    c["arcs"]=sum(1 for o in out if o is not None)
    c["arcsD"]=sum(1 for j in range(n) if out[j] is not None and j in D)
    c["toD"]=sum(1 for j in range(n) if out[j] is not None and out[j] in D)
    return c
stat=collections.defaultdict(lambda:[0,0,0]); moves=0; states=0
for tt in nets:
    fps=[y for y in range(N) if not V.unstable(tt,n,y)]; p=fps[0]
    for x in range(N):
        U=V.unstable(tt,n,x)
        if len(U)!=2: continue
        states+=1
        cx=cands(tt,x,p,U)
        for v in U:
            y=x^(1<<v); U2=V.unstable(tt,n,y)
            if len(U2)!=2: continue
            moves+=1
            cy=cands(tt,y,p,U2)
            for k in cx:
                d=cy[k]-cx[k]; stat[k][0 if d<0 else (1 if d==0 else 2)]+=1
print("n",n,"nets",len(nets),"k2 states",states,"k2 moves",moves)
for k,(a,b,c) in stat.items(): print(f"{k:10s} dec {a:7d} eq {b:7d} inc {c:7d}")
