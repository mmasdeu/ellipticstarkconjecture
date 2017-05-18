##### THIS EXAMPLE WORKS
import functions
reload(functions)
from functions import *



# p:=83;
# E := EllipticCurve("83A1");
# ap:=TraceOfFrobenius(E,p);
# print "a_p = ", ap;
# K<r> := QuadraticField(-p);OK:=Integers(K);
# f5 := Factorization(5*OK)[1][1];
# H := HeckeCharacterGroup(f5);
# EltsH := Elements(H);
# chi := EltsH[4];
# eps := CentralCharacter(chi);
# P:= (Factorization(p*OK)[1][1]);
# print "chi^2(p*OK)= ", (chi^2)(P);



p = 83
prec = 5
QQp = Qp(p,prec)
f0 = EllipticCurve('83a').modular_form()

x = QQ['x'].gen()


K.<a> = NumberField(x^2+83)
Km = magma(K)
Im = sage_F_ideal_to_magma(Km,K.ideal(1),magma)
H = magma.HeckeCharacterGroup((5*Km.RingOfIntegers()).Factorization()[1][1]) #Km.HeckeCharacterGroup(Im)
chi_magma = H.Elements()[4]
eps_magma = chi_magma.CentralCharacter()
Pm = (p*Km.RingOfIntegers()).Factorization()[1][1]
print 'chi_magma^2(Pm) = %s'%magma.eval('%s(%s)^2'%(chi_magma.name(),Pm.name()))

# Get the values of chi(p) for primes p, order doesn't really matter
# Construct a dictionary indexed by primes in the number field
M = 5000
Om = Km.RingOfIntegers()
Qcyc.<zeta12> = CyclotomicField(12)
chi_val = {}
for p0 in prime_range(M):
    pOK = K.ideal(p0).factor()
    if len(pOK) == 2:
        ans = [magma.eval('%s(Factorization(%s * %s)[1][1])'%(chi_magma.name(),p0,Om.name())),magma.eval('%s(Factorization(%s * %s)[2][1])'%(chi_magma.name(),p0,Om.name()))]

    else:
        ans = [magma.eval('%s(Factorization(%s * %s)[1][1])'%(chi_magma.name(),p0,Om.name()))]
    ans = [sage_eval(o,locals={'zeta_12':zeta12,'zeta_3':zeta12**4,'zeta_4':zeta12**3,'zeta_6':zeta12**2}) for o in ans]
    for i,pp in enumerate(pOK):
        chi_val[pp[0]] = ans[i]

def chi(nn):
    return prod(chi_val[pp]**e for pp,e in nn.factor())

ideals_bounded_norm = K.ideals_of_bdd_norm(M)
qexp = [QQ(0)]
qexp_inv = [QQ(0)]
for n in range(1,M):
    vals = [chi(nn) for nn in ideals_bounded_norm[n]]
    an = sum(vals)
    bn = sum([o**-1 for o in vals if o != 0])
    qexp.append(an)
    qexp_inv.append(bn)

Cycp.<r> = Qq(p,prec).extension((zeta12**3).minpoly())
Qi.<i> = QuadraticField(-1)
phi = Qi.hom([r])

qexp = [phi(Qi(o)) for o in qexp]
qexp_inv = [phi(Qi(o)) for o in qexp_inv]

g0 = ModFormqExp(qexp, Cycp, weight=1)
h0 = ModFormqExp(qexp_inv, Cycp, weight=1)

set_verbose(1)

Lp, ell = Lpvalue(g0, f0, h0, p, prec, 83,modformsring=True, weightbound=4,eps=kronecker_character(-83*5))

print Lp
