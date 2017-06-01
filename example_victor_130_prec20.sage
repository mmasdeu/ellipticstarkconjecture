##### THIS EXAMPLE WORKS
import functions
reload(functions)
from functions import *
from util import *
p = 5
prec = 20
QQp = Qp(p,prec)
f0 = EllipticCurve('130a1').modular_form()

x = QQ['x'].gen()


K.<a> = NumberField(x^2+5)
Km = magma(K)
H = magma.HeckeCharacterGroup((17*Km.RingOfIntegers()).Factorization()[1][1]) #Km.HeckeCharacterGroup(Im)
chi_magma = H.Elements()[74]
eps_magma = chi_magma.CentralCharacter()
Pm = (p*Km.RingOfIntegers()).Factorization()[1][1]
print 'chi_magma^2(Pm) = %s'%magma.eval('%s(%s)^2'%(chi_magma.name(),Pm.name()))

# Get the values of chi(p) for primes p, order doesn't really matter
# Construct a dictionary indexed by primes in the number field
M = 50000
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
##
Qi.<i> = QuadraticField(-1)
ip = QQp(-1).sqrt() # Kp.<ip> = QQp.extension((zeta12**3).minpoly())
phi = Qi.hom([ip])


qexp = [phi(Qi(o)) for o in qexp]
qexp_inv = [phi(Qi(o)) for o in qexp_inv]

g0 = ModFormqExp(qexp, QQp, weight=1)
h0 = ModFormqExp(qexp_inv, QQp, weight=1)

set_verbose(1)

##### THIS EXAMPLE WORKS
import functions
reload(functions)
from functions import *

# Lp, ell = Lpvalue(g0, f0, h0, p, prec, 21,modformsring=True, weightbound=4, derivative_order=1, eps =kronecker_character(-7))

f, g, h = g0, f0, h0
eps = kronecker_character(17*-20)
N = 130
modformsring=True
weightbound=4
derivative_order=1
force_computation=False
lauders_advice=True
algorithm = 'threestage'
magma_args = {}

from sage.interfaces.magma import Magma
magma = Magma(**magma_args)
ll,mm = g.weight(),h.weight()
t = 0 # Assume t = 0 here
kk = ll + mm - 2 * (1 + t) # Is this correct?
p = ZZ(p)
if N is None:
    N = LCM([ZZ(f.level()),ZZ(g.level()),ZZ(h.level())])
    nu = N.valuation(p)
    N = N.prime_to_m_part(p)
else:
    N = ZZ(N)
    nu = N.valuation(p)
print("Tame level N = %s, prime p = %s"%(N,p))
prec = ZZ(prec)

print("Step 1: Compute the Up matrix")
if algorithm == "twostage":
    computation_name = '%s_%s_%s_%s_%s_%s'%(p,N,kk,prec,'triv' if eps is None else 'char',algorithm)
else:
    computation_name = '%s_%s_%s_%s_%s'%(p,N,kk,prec,'triv' if eps is None else 'char')
tmp_filename = '/tmp/magma_mtx_%s.tmp'%computation_name
import os.path
from sage.misc.persist import db, db_save
try:
    if force_computation:
        raise IOError
    V = db('Lpvalue_Apow_ordbasis_eimat_%s'%computation_name)
    ord_basis, eimat, zetapm, elldash, mdash = V[:5]
    Apow_data = V[5:]
except IOError:
    if force_computation or not os.path.exists(tmp_filename):
        if eps is not None:
            eps_magma = sage_character_to_magma(eps,magma=magma)
            print 'Running magma.UpOperatorData(p, eps, kk, prec)'
            print 'p = %s'%p
            print 'eps = %s (modulus = %s)'%(eps_magma,eps_magma.Modulus())
            print 'kk = %s'%kk
            print 'prec = %s'%prec
            Am, zetapm, eimatm, elldash, mdash = magma.UpOperatorData(p, eps_magma, kk, prec,nvals=5)
        else:
            print 'Running magma.UpOperatorData(p, N, kk, prec)'
            print 'p = %s'%p
            print 'N = %s'%(N)
            print 'kk = %s'%kk
            print 'prec = %s'%prec
            Am, zetapm, eimatm, elldash, mdash = magma.UpOperatorData(p, N, kk, prec,nvals=5)
        print(" ..Converting to Sage...")
        Amodulus = Am[1,1].Parent().Modulus().sage()
        Aprec = Amodulus.valuation(p)
        Arows = Am.NumberOfRows().sage()
        Acols = Am.NumberOfColumns().sage()
        Emodulus = eimatm[1,1].Parent().Modulus().sage()
        Eprec = Emodulus.valuation(p)
        Erows = eimatm.NumberOfRows().sage()
        Ecols = eimatm.NumberOfColumns().sage()
        magma.eval('F := Open("%s", "w");'%tmp_filename)
        magma.eval('fprintf F, "Matrix(Qp(%s,%s),%s, %s, "'%(p,Aprec,Arows,Acols))
        magma.eval('fprintf F, "%%o", ElementToSequence(%s)'%Am.name())
        magma.eval('fprintf F, ") \\n"')
        magma.eval('fprintf F, "Matrix(Qp(%s,%s),%s, %s, "'%(p,Eprec,Erows, Ecols))
        magma.eval('fprintf F, "%%o", ElementToSequence(%s)'%eimatm.name())
        magma.eval('fprintf F, ") \\n"')
        magma.eval('fprintf F, "%%o\\n", %s'%zetapm.name())
        magma.eval('fprintf F, "%%o\\n", %s'%elldash.name())
        magma.eval('fprintf F, "%%o\\n", %s'%mdash.name())
        # magma.eval('delete F;')
        magma.quit()

    # Read A and eimat from file
    from sage.structure.sage_object import load
    from sage.misc.sage_eval import sage_eval
    with open(tmp_filename,'r') as fmagma:
        A = sage_eval(fmagma.readline(),preparse=False)
        eimat = sage_eval(fmagma.readline(),preparse=False)
        zetapm = sage_eval(fmagma.readline())
        elldash = sage_eval(fmagma.readline())
        mdash = sage_eval(fmagma.readline())

    print("Step 3b: Apply Up^(r-1) to H")
    if algorithm == 'twostage':
        V0  = list(find_Apow_and_ord_two_stage(A, eimat, p, prec))
    else:
        V0 = list(find_Apow_and_ord_three_stage(A,eimat,p,prec))
    ord_basis = V0[0]
    Apow_data = V0[1:]
    V = [ord_basis]
    V.extend([eimat, zetapm, elldash, mdash])
    V.extend(Apow_data)
    db_save(V,'Lpvalue_Apow_ordbasis_eimat_%s'%computation_name)
    from posix import remove
    remove(tmp_ficlename)

print("Step 2: p-depletion, Coleman primitive, and multiply")
H = depletion_coleman_multiply(g, h, p, p**(nu+1) * elldash, t=0)

print("Step 3a: Compute ordinary projection")
if len(Apow_data) == 1:
    Hord = compute_ordinary_projection_two_stage(H, Apow_data, eimat, elldash,p)
else:
    Hord = compute_ordinary_projection_three_stage(H, [ord_basis] + Apow_data, eimat, elldash,p,nu)
print 'Changing Hord to ring %s'%g[1].parent()
Hord = Hord.change_ring(h[1].parent())

print("Step 4: Project onto f-component")
if lauders_advice == True:
    ell, piHord = project_onto_eigenspace(f, ord_basis, Hord, kk, N * p, eps, derivative_order=derivative_order)
    n = 1
    while f[n] == 0:
        n += 1
    Lpa =  piHord[n] / f[n]
    print "Checking Lauder's coincidence... (following should be a bunch of 'large' valuations)"
    print [(Lpa * f[i] - piHord[i]).valuation(p) for i in range(1,20)]
    print "Done"

elif orthogonal_form is None:
    ell, piHord = project_onto_eigenspace(f, ord_basis, Hord, kk, N * p, eps, derivative_order=derivative_order, p = p)
    n = 1
    while f[n] == 0:
        n += 1
    Lpa =  piHord[n] / f[n]
else:
    ell, piHord = project_onto_eigenspace(f, ord_basis, Hord, kk, N * p, eps, derivative_order=derivative_order, p = p)
    gplus, gminus = f, orthogonal_form
    l1 = 2
    while N*p*ell % l1 == 0 or gplus[l1] == 0:
        l1 = next_prime(l1)
    proj_mat = matrix([[gplus[l1],gplus[p]],[gminus[l1],gminus[p]]])
    Lpalist =  (matrix([piHord[l1],piHord[p]]) * proj_mat**-1).list()
    Lpa = Lpalist[0]
    if Lpa.valuation() > prec / 2: # this is quite arbitrary!
        Lpa = Lpalist[1]
    n = 1
    while f[n] == 0:
        n += 1
    Lpa = Lpa / f[n]

set_verbose(0)
Lp = Lpa
E = EllipticCurve('21a1')
qElog = E.tate_curve(p).parameter(2*prec).log(pi_branch = 0)
PKlog = log_of_heegner_point(E,K,p,2*prec)
x = QQ['x'].gen()
ualg = (1+our_sqrt(Lp.parent()(5)))/2
# ualg = (x^2 - x - 1).roots(Lp.parent())[0][0]
# ulog = get_ulog(ualg, K, p, 2 * prec)
ulog = ualg.log()
V = (PKlog/PKlog.parent().gen()).list()
PKlog_2 = 0
for i,v in enumerate(V):
    if i % 2 == 1:
        assert v == 0
    else:
        PKlog_2 += v * p**ZZ(i/2)

LHS = Lp
RHS = ulog.parent()((qElog * PKlog_2)) / ulog
print our_algdep(LHS/RHS, 2)
print our_algdep(LHS/RHS, 3)
print our_algdep(LHS/RHS, 4)
