import sys, time; sys.path.insert(0,'.')
from forms import *
from rays import extreme_rays
import edges
J51 = frac_mat([[2*x for x in r] for r in [[2,-1,-1,0,0,1],[-1,2,1,0,0,0],[-1,1,2,0,0,-1],[0,0,0,2,0,-1],[0,0,0,0,2,-1],[1,0,-1,-1,-1,2]]])
mv=min_vectors(J51)
R=extreme_rays(mv)
Y=sym_from_vec(R[0],6)
print(R[0])
t=time.time(); v=values_upto(J51,F(8)); print(len(v),time.time()-t)
t=time.time(); v=values_upto(J51,F(16)); print(len(v),time.time()-t)
t=time.time(); up=edges.find_upper(J51,Y); print('up',up,time.time()-t)
