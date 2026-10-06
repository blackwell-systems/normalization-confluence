import sys, json
from collections import Counter
from stats3 import fixed_points
C=Counter()
for f in sys.argv[1:]:
    for item in json.load(open(f)):
        tt=item["tt"] if isinstance(item,dict) else item; n=len(tt); N=1<<n
        X=list(range(N))
        while True:
            img=set(sum(tt[i][x]<<i for i in range(n)) for x in X)
            fixed0=[i for i in range(n) if all(not (y>>i)&1 for y in img)]
            fixed1=[i for i in range(n) if all((y>>i)&1 for y in img)]
            X2=[x for x in range(N) if all(not (x>>i)&1 for i in fixed0) and all((x>>i)&1 for i in fixed1)]
            if len(X2)==len(X): break
            X=X2
        C[(n,len(X)==1)]+=1
print(sorted(C.items()))
