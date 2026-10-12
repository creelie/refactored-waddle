import sys, time; sys.path.insert(0,'.')
from forms import *
from rays import extreme_rays
from edges import tstar
from collections import Counter
J51 = frac_mat([[2*x for x in r] for r in [[2,-1,-1,0,0,1],[-1,2,1,0,0,0],[-1,1,2,0,0,-1],[0,0,0,2,0,-1],[0,0,0,0,2,-1],[1,0,-1,-1,-1,2]]])
mv=min_vectors(J51)
R=extreme_rays(mv)
t0=time.time()
res=Counter(); unb=[]
for i,y in enumerate(R):
    Y=sym_from_vec(y,6)
    ts=tstar(J51,Y)
    if ts is None: unb.append(y)
    else:
        M=[[J51[a][b]+ts*Y[a][b] for b in range(6)] for a in range(6)]
        Q,r,s=blocks(M)
        res[(ts, det(Q), det(M), len(min_vectors(M)))]+=1
print(time.time()-t0, len(unb))
for k,v in sorted(res.items(), key=lambda kv:-kv[1]): print(v, k)
