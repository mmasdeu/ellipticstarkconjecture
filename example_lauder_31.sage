### Experimenting with Lauder's code # THIS EXAMPLE WORKS
import functions
reload(functions)
from functions import *

tt = ZZ(0)
ll = tt + ZZ(2)
mm = ZZ(2) # Set parameter
kk = mm - ll + ZZ(2)

N = ZZ(57)
E = EllipticCurve('%sa1'%str(N))
f0 = E.modular_form()
_,g2,g1 = Newforms(Gamma0(57),names='a')
assert g1 != f0
assert g2 != f0
assert g2 != g1

p = 5
prec = 20
R = Qp(p,prec)

set_verbose(1)
Lp_g1_f_g1, ell  = Lpvalue(g1,f0,g1,p,prec)
# Lp2_g2_f_g2, ell2 = Lpvalue(g2,f0,g2,p,prec)

L5good_g1_f_g1 = R(-260429402433721822483)
# L5good_g2_f_g2 = 1/p * Qp(p,prec + 1)(-279706401244025789341)

P = E((2,-2))
Plog = P.padic_elliptic_logarithm(p,prec)
P1log = -16 * Plog
P2log = 4 * Plog

# print algdep(P1log/L5good_g1_f_g1/eps0(R,g1)/eps1(R,g1) * eps(R,g1,f,g1),1)
# print algdep(P1log/L5good_g1_f_g1,2)
# print algdep(L5good_g1_f_g1 / Lp_g1_f_g1,1)
# print algdep(L5good_g2_f_g2 / Lp_g2_f_g2,1)

print -Lp_g1_f_g1 / L5good_g1_f_g1

