# This example works

import functions
reload(functions)
from functions import *


### Find examples following Alan's email
admissible_pairs = []
for p in prime_range(5,20):
    for D in range(11,100):
        if D % 4 != 3:
            continue
        try:
            E = EllipticCurve(str(D))
            if E.rank() != 1:
                continue
        except:
            continue
        if len(QuadraticField(-D,'a').ideal(p).factor()) != 2:
            continue
        print p,D
        admissible_pairs.append((p,D))


###
set_verbose(1)
for p, N in admissible_pairs:
    prec = 20 # Paper uses 70
    QQp = Qp(p,prec)
    E = EllipticCurve(str('%sa1'%N))
    f0 = E.modular_form()

    x = QQ['x'].gen()
    K.<a> = NumberField(x^2+N)

    M = 30000
    eps = kronecker_character(-N)
    g1qexp = sage_character_to_magma(eps,magma=magma).ModularForms(1).EisensteinSeries()[1].qExpansion(M).Eltseq().sage()

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
    Lp, ell = Lpvalue(gammaplus, f0, g0, p, prec, N,modformsring=False, weightbound=6,eps=kronecker_character(-N),lauders_advice=True,derivative_order=3)
    ratio = test_formula_display45(Lp, p, E, K)
    print p, N, ratio

