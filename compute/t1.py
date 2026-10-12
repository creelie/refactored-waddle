import sys, time; sys.path.insert(0,'.')
from forms import *
from rays import extreme_rays
J51 = frac_mat([[2*x for x in r] for r in [[2,-1,-1,0,0,1],[-1,2,1,0,0,0],[-1,1,2,0,0,-1],[0,0,0,2,0,-1],[0,0,0,0,2,-1],[1,0,-1,-1,-1,2]]])
mv=min_vectors(J51)
t=time.time(); R=extreme_rays(mv); print(len(R), time.time()-t)
