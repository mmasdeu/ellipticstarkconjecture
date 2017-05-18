##### THIS EXAMPLE WORKS
import functions
reload(functions)
from functions import *

p = 5
prec = 20 # Paper uses 70
QQp = Qp(p,prec)
f0 = EllipticCurve('83a').modular_form()

# Resulting values in DLR
Lp1good = QQp(-1688341751390720654446425615337716320464561776401)
Lp2good = QQp(-2981481189608571355501040629889815717824676581453)

x = QQ['x'].gen()
K.<a> = NumberField(x^2+83)
Km = magma(K)

Im = sage_F_ideal_to_magma(Km,K.ideal(1),magma)

G = magma.HeckeCharacterGroup(1*Km.RingOfIntegers()) #Km.HeckeCharacterGroup(Im)
chi_magma = G.1

# Get the values of chi(p) for primes p, order doesn't really matter
# Construct a dictionary indexed by primes in the number field
M = 10000
Om = Km.RingOfIntegers()
chi_val = {}
Qzeta3 = CyclotomicField(3)
zeta3 = Qzeta3.gen()
for p0 in prime_range(M):
    pOK = K.ideal(p0).factor()
    if len(pOK) == 2:
        ans = [magma.eval('%s(Factorization(%s * %s)[1][1])'%(chi_magma.name(),p0,Om.name())),magma.eval('%s(Factorization(%s * %s)[2][1])'%(chi_magma.name(),p0,Om.name()))]
    else:
        ans = [magma.eval('%s(Factorization(%s * %s)[1][1])'%(chi_magma.name(),p0,Om.name()))]
    ans = [sage_eval(o,{'zeta_3':zeta3}) for o in ans]
    for i,pp in enumerate(pOK):
        chi_val[pp[0]] = ans[i]

def chi(nn):
    return prod(chi_val[pp]**e for pp,e in nn.factor())


ideals_bounded_norm = K.ideals_of_bdd_norm(M)
qexp = [Qzeta3(0)]
for n in range(1,M):
    an = sum([chi(nn) for nn in ideals_bounded_norm[n]])
    qexp.append(an)


# # Test that we did it right
# test_qexp = convolution(qexp,qexp)

# S = ModularForms(Gamma0(83),2).cuspidal_subspace()
# Sbasis = S.echelon_basis()
# print test_qexp[:100] ==  (Sbasis[1] - 2*Sbasis[3]+2*Sbasis[4]+Sbasis[5]-2*Sbasis[6]).coefficients(range(100))


g0 = ModFormqExp(qexp, Qp(p,prec), weight=1)

qexp_plus = [QQ(o) for o in qexp]
qexp_minus = [QQ(o) for o in qexp]
for i in range(len(qexp) // p):
    qexp_plus[p * i] += qexp[i]
    qexp_minus[p * i] -= qexp[i]

gammaplus = ModFormqExp(qexp_plus, Qp(p,prec), weight=1)
gammaminus = ModFormqExp(qexp_minus, Qp(p,prec), weight=1)

set_verbose(1)

Lp, ell = Lpvalue(gammaplus, f0, g0, p, prec, 83,modformsring=False, weightbound=6,eps=kronecker_character(-83),orthogonal_form=gammaminus,algorithm='threestage',force_computation=False)
print Lp / Lp1good

g1qexp = sage_character_to_magma(kronecker_character(-83),magma=magma).ModularForms(1).EisensteinSeries()[1].qExpansion(M).Eltseq().sage()
g1 = ModFormqExp(g1qexp, Qp(p,prec), weight=1)
Lp2, ell2 = Lpvalue(gammaplus, f0, g1, p, prec, 83,modformsring=False, weightbound=6,eps=kronecker_character(-83),orthogonal_form=gammaminus)
print Lp2 / Lp2good


