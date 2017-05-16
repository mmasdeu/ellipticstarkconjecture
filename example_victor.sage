##### THIS EXAMPLE WORKS
import functions
reload(functions)
from functions import *

p = 7
prec = 10 # Paper uses 70
QQp = Qp(p,prec)
f0 = EllipticCurve('91a').modular_form()

x = QQ['x'].gen()


K.<a> = NumberField(x^2+7)
Km = magma(K)
Im = sage_F_ideal_to_magma(Km,K.ideal(1),magma)
G = magma.HeckeCharacterGroup(1*Km.RingOfIntegers()) #Km.HeckeCharacterGroup(Im)
chi_magma = G(1)

# Get the values of chi(p) for primes p, order doesn't really matter
# Construct a dictionary indexed by primes in the number field
M = 5000
Om = Km.RingOfIntegers()
chi_val = {}
for p0 in prime_range(M):
    pOK = K.ideal(p0).factor()
    if len(pOK) == 2:
        ans = [magma.eval('%s(Factorization(%s * %s)[1][1])'%(chi_magma.name(),p0,Om.name())),magma.eval('%s(Factorization(%s * %s)[2][1])'%(chi_magma.name(),p0,Om.name()))]
    else:
        ans = [magma.eval('%s(Factorization(%s * %s)[1][1])'%(chi_magma.name(),p0,Om.name()))]
    ans = [sage_eval(o) for o in ans]
    for i,pp in enumerate(pOK):
        chi_val[pp[0]] = ans[i]

def chi(nn):
    return prod(chi_val[pp]**e for pp,e in nn.factor())


ideals_bounded_norm = K.ideals_of_bdd_norm(M)
qexp = [QQ(0)]
for n in range(1,M):
    an = sum([chi(nn) for nn in ideals_bounded_norm[n]])
    qexp.append(an)

h0 = ModFormqExp(qexp, Qp(p,prec), weight=1)


K.<a> = NumberField(x^2+91)
Km = magma(K)
Im = sage_F_ideal_to_magma(Km,K.ideal(1),magma)
G = magma.HeckeCharacterGroup(1*Km.RingOfIntegers()) #Km.HeckeCharacterGroup(Im)
chi_magma = G(1)

# Get the values of chi(p) for primes p, order doesn't really matter
# Construct a dictionary indexed by primes in the number field
M = 5000
Om = Km.RingOfIntegers()
chi_val = {}
for p0 in prime_range(M):
    pOK = K.ideal(p0).factor()
    if len(pOK) == 2:
        ans = [magma.eval('%s(Factorization(%s * %s)[1][1])'%(chi_magma.name(),p0,Om.name())),magma.eval('%s(Factorization(%s * %s)[2][1])'%(chi_magma.name(),p0,Om.name()))]
    else:
        ans = [magma.eval('%s(Factorization(%s * %s)[1][1])'%(chi_magma.name(),p0,Om.name()))]
    ans = [sage_eval(o) for o in ans]
    for i,pp in enumerate(pOK):
        chi_val[pp[0]] = ans[i]

def chi(nn):
    return prod(chi_val[pp]**e for pp,e in nn.factor())


ideals_bounded_norm = K.ideals_of_bdd_norm(M)
qexp = [QQ(0)]
for n in range(1,M):
    an = sum([chi(nn) for nn in ideals_bounded_norm[n]])
    qexp.append(an)

g0 = ModFormqExp(qexp, Qp(p,prec), weight=1)


qexp_plus = [QQ(o) for o in qexp]
qexp_minus = [QQ(o) for o in qexp]
for i in range(len(qexp) // p):
    qexp_plus[p * i] += qexp[i]
    qexp_minus[p * i] -= qexp[i]

gammaplus = ModFormqExp(qexp_plus, Qp(p,prec), weight=1)
gammaminus = ModFormqExp(qexp_minus, Qp(p,prec), weight=1)

set_verbose(1)

Lp, ell = Lpvalue(gammaplus, f0, h0, p, prec, 91,modformsring=False, weightbound=6,eps=kronecker_character(-91),magma=magma,orthogonal_form=gammaminus)

print Lp
