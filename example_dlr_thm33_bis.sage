
import functions
reload(functions)
from functions import *

set_verbose(1)

p = 13
prec = 20 # Paper uses 70
QQp = Qp(p,prec)
N = 79
E = EllipticCurve(str('%sa1'%N))
f0 = E.modular_form()

x = QQ['x'].gen()
K.<a> = NumberField(x^2+N)

M = 25060
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

# set_verbose(1)
# Lp, ell = Lpvalue(gammaplus, f0, g0, p, prec, N,modformsring=False, weightbound=6,eps=kronecker_character(-11),magma=magma)

### DEBUG BELOW
f, g, h = gammaminus, f0, g0
modformsring=False
weightbound=6
eps=kronecker_character(-N)
orthogonal_form=gammaplus

magma = Magma()
ll,mm = g.weight(),h.weight()
t = 0 # Assume t = 0 here
kk = ll + mm - 2 * (1 + t) # Is this correct?
p = ZZ(p)
if N is None:
    N = LCM([ZZ(f.level()),ZZ(g.level()),ZZ(h.level())])
    N = N.prime_to_m_part(p)

print("Tame level N = %s, prime p = %s"%(N,p))
prec = ZZ(prec)

print("Step 1: Compute the Up matrix")
# A, eimat, elldash, mdash = UpOperator(p, N, k=kk, m=prec, modformsring=modformsring, weightbound=weightbound)
computation_name = '%s_%s_%s_%s_%s'%(p,N,kk,prec,'triv' if eps is None else 'char')
tmp_filename = '/tmp/magma_mtx_%s.tmp'%computation_name
import os.path
from sage.misc.persist import db, db_save
try:
    Apow, ord_basis, eimat, zetapm, elldash, mdash = db('Lpvalue_Apow_ordbasis_eimat_%s'%computation_name)
except IOError:
    if not os.path.exists(tmp_filename):
        if eps is not None:
            eps_magma = sage_character_to_magma(eps,magma=magma)
            Am, zetapm, eimatm, elldash, mdash = magma.UpOperatorData(p, eps_magma, kk, prec,nvals=5)
        else:
            Am, zetapm, eimatm, elldash, mdash = magma.UpOperatorData(p, N, kk, prec,nvals=5)
        print(" ..Converting to Sage...")
        Amodulus = Am[1,1].Parent().Modulus().sage()
        Arows = Am.NumberOfRows().sage()
        Acols = Am.NumberOfColumns().sage()
        Emodulus = eimatm[1,1].Parent().Modulus().sage()
        Erows = eimatm.NumberOfRows().sage()
        Ecols = eimatm.NumberOfColumns().sage()
        magma.eval('F := Open("%s", "w");'%tmp_filename)
        magma.eval('fprintf F, "Matrix(Zmod(%s),%s, %s, "'%(Amodulus,Arows,Acols)) #%%o) \\n", ElementToSequence(%s)'%Am.name())
        magma.eval('fprintf F, "%%o", ElementToSequence(%s)'%Am.name())
        magma.eval('fprintf F, ") \\n"')
        magma.eval('fprintf F, "Matrix(Zmod(%s),%s, %s, "'%(Emodulus,Erows, Ecols)) #%%o) \\n", ElementToSequence(%s)'%eimatm.name())
        magma.eval('fprintf F, "%%o", ElementToSequence(%s)'%eimatm.name())
        magma.eval('fprintf F, ") \\n"')
        magma.eval('fprintf F, "%%o\\n", %s'%zetapm.name())
        magma.eval('fprintf F, "%%o\\n", %s'%elldash.name())
        magma.eval('fprintf F, "%%o\\n", %s'%mdash.name())
        magma.eval('delete F;')
        # zetapm, elldash, mdash = zetapm.sage(), elldash.sage(), mdash.sage()
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
    V = list(find_Apow_and_ord(A, eimat, p, prec))
    Apow, ord_basis = V
    V.extend([eimat, zetapm, elldash, mdash])
    db_save(V,'Lpvalue_Apow_ordbasis_eimat_%s'%computation_name)
    from posix import remove
    remove(tmp_filename)

print("Step 2: p-depletion, Coleman primitive, and multiply")
H = depletion_coleman_multiply(g, h, p, p * elldash, t=0)

print("Step 3a: Compute Up(H)")
UpH = vector([H(p * n) for n in range(elldash)])

try:
    Emat = eimat.apply_map(lambda x:x.lift()).submatrix(0,0,ncols=elldash)
except AttributeError:
    Emat = eimat.submatrix(0,0,ncols=elldash)

alphas = solve_xAb_echelon(Emat,UpH)
Hord = (alphas * Apow.apply_map(lambda x:x.lift())) * Emat
Hord = Hord.change_ring(Apow.parent().base_ring())

print("Step 4: Project onto f-component")
R = Qp(p,prec)
ell, piHord = project_onto_eigenspace(f, ord_basis, Hord.change_ring(R), kk, N * p, eps, derivative_order=3)

gplus, gminus = f, orthogonal_form
l1 = 2
while N*p*ell % l1 == 0 or gplus[l1] == 0:
    l1 = next_prime(l1)
proj_mat = matrix([[gplus[l1],gplus[p]],[gminus[l1],gminus[p]]])
Lpa =  (matrix([piHord[l1],piHord[p]]) * proj_mat**-1)[0,1]

####

ratio = test_formula_display45(Lpa, p, E, K, remove_numpoints = False)
