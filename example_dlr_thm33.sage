# This example works

import functions
reload(functions)
from functions import *

p = 11
prec = 10 # Paper uses 70
QQp = Qp(p,prec)
N = 83
E = EllipticCurve(str('%sa1'%N))
f0 = E.modular_form()

x = QQ['x'].gen()
K.<a> = NumberField(x^2+N)

M = 30000
eps = kronecker_character(-N)
g1qexp = sage_character_to_magma(eps,magma=magma).ModularForms(1).EisensteinSeries()[1].qExpansion(M).Eltseq().sage()

# # Test that we did it right
# test_qexp = convolution(g1qexp,g1qexp)

# S = ModularForms(Gamma0(N),2)
# Sbasis = S.echelon_basis()
# print test_qexp[:100] ==  (9/4*Sbasis[0] + 3*Sbasis[1]+1*Sbasis[2]+6*Sbasis[3]+7*Sbasis[4]+2*Sbasis[5]+4*Sbasis[6]+10*Sbasis[7]).coefficients(range(100))

g0 = ModFormqExp(g1qexp, Qp(p,prec), weight=1,character = eps)

weight = 1
# alpha, beta = sorted_roots(QQp,g0)
alpha = 1

qexp_plus = [QQ(o) for o in g1qexp]
qexp_minus = [QQ(o) for o in g1qexp]
for i in range(len(g1qexp) // p):
    qexp_plus[p * i] += g1qexp[i]
    qexp_minus[p * i] -= g1qexp[i]

gammaplus = ModFormqExp(qexp_plus, Qp(p,prec), weight=1)
gammaminus = ModFormqExp(qexp_minus, Qp(p,prec), weight=1)

set_verbose(1)
Lp, ell = Lpvalue(gammaplus, f0, g0, p, prec, N,modformsring=False, weightbound=6,eps=kronecker_character(-N),orthogonal_form=gammaminus,derivative_order=3)

ratio = test_formula_display45(Lp, p, E, K, remove_numpoints = True)

# Lp = Lpa
# P0 = E.heegner_point(-N)

# PK = E(201/361, -14137/6859)
# Hp = QQp
# nn = 1
# while True:
#     PKpn = E.change_ring(QQp)(nn*PK)
#     tvar = -PKpn[0] / PKpn[1]
#     try:
#         logPK = E.change_ring(Hp).formal_group().log(prec)(tvar) / nn
#         break
#     except ValueError:
#         nn+=1
#         print 'nn=',nn

# hK = K.class_number()
# EFp = p+1 - f0.coefficients([p])[0]

# phi = K.hom([K.gen().minpoly().roots(QQp)[0][0]])
# u = phi((K.ideal(7).factor()[0][0]**3).gens_reduced()[0])
# if u.valuation() == 0:
#     u = phi((K.ideal(7).factor()[1][0]**3).gens_reduced()[0])
# assert u.valuation() > 0
# ulog = u.log(0)
# ratio = Lp / ( (EFp**2 * logPK**2 ) / (p * (p-1) * hK * ulog) )
# print algdep(ratio, 1).roots(QQ)[0][0]

