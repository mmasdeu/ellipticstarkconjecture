### Experimenting with Lauder's code # THIS EXAMPLE WORKS
import functions
reload(functions)
from functions import *

tt = ZZ(0)
ll = tt + ZZ(2)
mm = ZZ(2) # Set parameter
kk = mm - ll + ZZ(2)

N = ZZ(89)
E = EllipticCurve('%sa1'%str(N))
f = E.modular_form()
g = Newforms(Gamma0(N),names='a')[1]

p = 89
prec = 10
R = Qp(p,prec)

set_verbose(1)
Lp, ell = Lpvalue(g,f,g,p,prec)

P = E((0,0))
Plog = P.padic_elliptic_logarithm(p,prec)

Lpgood = 72*Plog/89

print -Lp / Lpgood
