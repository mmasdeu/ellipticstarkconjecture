### Experimenting with Lauder's code # THIS EXAMPLE WORKS
import functions
reload(functions)
from functions import *

set_verbose(1)

tt = ZZ(0)
ll = tt + ZZ(2)
mm = ZZ(4) # Set parameter - weight of third form
kk = mm - ll + ZZ(2)

N = ZZ(53)
E = EllipticCurve('%sa1'%str(N))
f = E.modular_form()
g = Newforms(Gamma0(N),4,names='a')[0]

p = 7
prec = 10
R = Qp(p,prec)

set_verbose(1)

M = g.parent()

Lp, ell = Lpvalue(g,f,g,p,prec)
Lpgood = Qp(p,prec)(-12581507765759084963366603)

print Lp / Lpgood
