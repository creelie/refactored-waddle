import sys, time; sys.path.insert(0,'.')
from forms import *
from rays import extreme_rays
from edges import tstar
J51 = frac_mat([[2*x for x in r] for r in [[2,-1,-1,0,0,1],[-1,2,1,0,0,0],[-1,1,2,0,0,-1],[0,0,0,2,0,-1],[0,0,0,0,2,-1],[1,0,-1,-1,-1,2]]])
mv=min_vectors(J51)
R=extreme_rays(mv)
import cProfile, pstats
t0=time.time()
pr=cProfile.Profile(); pr.enable()
for y in R[:20]:
    Y=sym_from_vec(y,6); print(tstar(J51,Y), end=' ', flush=True)
pr.disable()
print(time.time()-t0)
pstats.Stats(pr).sort_stats('cumulative').print_stats(12)
