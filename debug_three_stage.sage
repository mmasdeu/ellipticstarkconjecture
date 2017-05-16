
### Experimenting with Lauder's code # THIS EXAMPLE WORKS
import functions
reload(functions)
from functions  import *

set_verbose(1)

tt = ZZ(0)
ll = tt + ZZ(2)
mm = ZZ(4) # Set parameter - weight of third form
kk = mm - ll + ZZ(2)

N = ZZ(53)
E = EllipticCurve('%sa1'%str(N))
f0 = E.modular_form()
g0 = Newforms(Gamma0(N),4,names='a')[0]

p = 7
prec = 30
R = Qp(p,prec)

set_verbose(1)

M = g0.parent()

Lpgood = Qp(p,prec)(-12581507765759084963366603)

set_verbose(1)

force_computation = False
modformsring = False
weightbound = 6
eps = None
orthogonal_form = None

f,g,h = g0, f0, g0
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
computation_name = '%s_%s_%s_%s_%s'%(p,N,kk,prec,'triv' if eps is None else 'char')
tmp_filename = '/tmp/magma_mtx_%s.tmp'%computation_name
import os.path
from sage.misc.persist import db, db_save
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
magma.eval('fprintf F, "Matrix(Zmod(%s),%s, %s, "'%(Amodulus,Arows,Acols))
magma.eval('fprintf F, "%%o", ElementToSequence(%s)'%Am.name())
magma.eval('fprintf F, ") \\n"')
magma.eval('fprintf F, "Matrix(Zmod(%s),%s, %s, "'%(Emodulus,Erows, Ecols))
magma.eval('fprintf F, "%%o", ElementToSequence(%s)'%eimatm.name())
magma.eval('fprintf F, ") \\n"')
magma.eval('fprintf F, "%%o\\n", %s'%zetapm.name())
magma.eval('fprintf F, "%%o\\n", %s'%elldash.name())
magma.eval('fprintf F, "%%o\\n", %s'%mdash.name())
magma.eval('delete F;')
magma.quit()

# Read A and eimat from file
print 'Read A and eimat from file...'
from sage.structure.sage_object import load
from sage.misc.sage_eval import sage_eval
with open(tmp_filename,'r') as fmagma:
    A = sage_eval(fmagma.readline(),preparse=False)
    eimat = sage_eval(fmagma.readline(),preparse=False)
    zetapm = sage_eval(fmagma.readline())
    elldash = sage_eval(fmagma.readline())
    mdash = sage_eval(fmagma.readline())
print 'Done reading'

print("Step 3b: Apply Up^(r-1) to H")
# V0 = list(find_Apow_and_ord(A, eimat, p, prec))
V0 = list(find_Apow_and_ord_three_stage(A,eimat,p,prec))
ord_basis = V0[0]
Apow_data = V0[1:]
V = [ord_basis]
V.extend([eimat, zetapm, elldash, mdash])
V.extend(Apow_data)
db_save(V,'Lpvalue_Apow_ordbasis_eimat_%s'%computation_name)
from posix import remove
remove(tmp_filename)

print("Step 2: p-depletion, Coleman primitive, and multiply")
H = depletion_coleman_multiply(g, h, p, p * elldash, t=0)

print("Step 3a: Compute Up(H)")
UpH = vector([H(p * n) for n in range(elldash)])

if len(Apow_data) == 1:
    print "Using two-stage projection"
    Hord = compute_ordinary_projection_two_stage(UpH, Apow_data, eimat, elldash)
else:
    print "Using three-stage projection"
    Hord = compute_ordinary_projection_three_stage(UpH, [ord_basis] + Apow_data, eimat, elldash)
Hord = Hord.change_ring(Apow_data[0].parent().base_ring())

print("Step 4: Project onto f-component")
R = Qp(p,prec)
if orthogonal_form is None:
    ell, piHord = project_onto_eigenspace(f, ord_basis, Hord.change_ring(R), kk, N * p, eps)
    n = 1
    while f[n] == 0:
        n += 1
    Lpa =  R(piHord[n])/ R(f[n])
else:
    ell, piHord = project_onto_eigenspace(f, ord_basis, Hord.change_ring(R), kk, N * p, eps, derivative_order=2)
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

print Lpa/Lpgood
