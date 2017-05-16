
### Experimenting with Lauder's code
from functions import *

tt = ZZ(0)
ll = tt + ZZ(2)
mm = ZZ(2) # Set parameter
kk = mm - ll + ZZ(2)

N = ZZ(57)
E = EllipticCurve('%sa1'%str(N))
f = E.modular_form()
_,g2,g1 = Newforms(Gamma0(57),names='a')
assert g1 != f
assert g2 != f
assert g2 != g1

p = 5
prec = 30
R = Qp(p,prec)

set_verbose(1)

L5good_g1_f_g1 = R(-260429402433721822483)
L5good_g2_f_g2 = 1/p * Qp(p,prec + 1)(-279706401244025789341)

P = E((2,-2))
Plog = P.padic_elliptic_logarithm(p,prec)
P1log = -16 * Plog
P2log = 4 * Plog

print algdep(P1log/L5good_g1_f_g1/eps0(R,g1)/eps1(R,g1) * eps(R,g1,f,g1),1)


print algdep(P1log/L5good_g1_f_g1,2)

# set_verbose(1)

# A = UpOperator(p, N, k=2, m=prec, modformsring=True, weightbound=4)

# # ntotal = factorial(5)
# # H = multiply_and_integrate_after_depletion(f,g1,p,prec,t=0)
# # num_coeffs = A.nrows()
# # print vector(H[:num_coeffs]) * (A**ntotal)



tt = ZZ(0)
ll = tt + ZZ(2)
mm = ZZ(2) # Set parameter
kk = mm - ll + ZZ(2)

N = ZZ(77)
E = EllipticCurve('%sa1'%str(N))
f = E.modular_form()
g = Newforms(Gamma0(11),names='a')[0]

p = 7
prec = 10
R = Qp(p,prec)

P = E((2,3))
Plog = P.padic_elliptic_logarithm(p,prec)

set_verbose(1)
# Lp = Lpvalue(g,f,g,p,prec)
Lpgood = Qp(p,prec)(-1861584104004734313229493 * 7)

f, g, h = g, f, g
kk,ll,mm = f.weight(),g.weight(),h.weight()
N = LCM([ZZ(f.level()),ZZ(g.level()),ZZ(h.level())])
p = ZZ(p)
N = N.prime_to_m_part(p)

print("Tame level N = %s, prime p = %s"%(N,p))
prec = ZZ(prec)

print("Step 1: Compute the Up matrix")
A, eimat, elldash = UpOperator(p, N, k=kk, m=prec, modformsring=True, weightbound=4)
print("Step 2: p-depletion, Coleman primitive, and multiply")
H = depletion_coleman_multiply(g, h, p, p * elldash, t=0)

print("Step 3a: Compute Up(H)")
UpH = vector([H[p * n] for n in range(elldash)])

mdash = RR(eimat.parent().base_ring().cardinality()).log(p).round()

Emat = eimat.lift().submatrix(0,0,ncols=elldash)

alphas = solve_xAb_echelon(Emat,UpH)
print [o.valuation(p) for o in alphas]

print("Step 3b: Apply Up^(r-1) to H")
f_degree = A.change_ring(GF(p)).charpoly().splitting_field(names='a').degree()
r = (p**f_degree - 1) * p**prec
M = f.parent()
Apow = take_power(A, r-1)
Hord = (alphas * Apow.lift()) * Emat
Hord = Hord.change_ring(A.parent().base_ring())
print("Step 4: Project onto f-component")
x = QQ['x'].gen()
rts = (x^2 - f[p] * x + p).roots(Qp(p,prec))
ell, pi = projector_onto_eigenspace(ModularForms(Gamma0(77),2),f,(7,rts[1][0])) #ModularForms(Gamma0(77),2)(f))
n = 1
while f[n] == 0:
    n += 1
Lp = pi(Hord)[n] / f[n]
