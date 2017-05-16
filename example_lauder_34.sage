### Experimenting with Lauder's code # THIS EXAMPLE WORKS
import functions
reload(functions)
from functions import *

tt = ZZ(0)
ll = tt + ZZ(2)
mm = ZZ(2) # Set parameter
kk = mm - ll + ZZ(2)

N = ZZ(77)
E = EllipticCurve('%sa1'%str(N))
f0 = E.modular_form()
g0 = Newforms(Gamma0(11),names='a')[0]

p = 7
prec = 30
R = Qp(p,prec)

P = E((2,3))
Plog = P.padic_elliptic_logarithm(p,prec)

set_verbose(1)

Lpgood = (-1861584104004734313229493 * 7)
Lp, ell = Lpvalue(g0,f0,g0,p,prec)
print -Lp/Lpgood
