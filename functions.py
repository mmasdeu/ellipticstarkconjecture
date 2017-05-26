from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.rings.all import ZZ,QQ,RR
from sage.rings.polynomial.convolution import _convolution_naive as convolution
from sage.arith.misc import next_prime,LCM
from sage.functions.other import factorial
from sage.modules.free_module_element import free_module_element as vector
from sage.rings.padics.factory import Qp
from sage.matrix.constructor import Matrix
from sage.modular.overconvergent.hecke_series import *
from sage.modular.arithgroup.congroup_gamma1 import Gamma1_constructor as Gamma1
from sage.modular.modform.constructor import ModularForms
from sage.modular.modform.hecke_operator_on_qexp import hecke_operator_on_basis, hecke_operator_on_qexp
from sage.rings.power_series_ring import PowerSeriesRing
from sage.structure.sage_object import SageObject
from sage.interfaces.magma import magma
from sage.modular.dirichlet import DirichletGroup
from sage.rings.padics.factory import ZpCA,ZpCR,Qp
import sys

def argmax(iterable, fun=None):
    if fun is None:
        fun = lambda x : x
    return max(enumerate(iterable), key=lambda x: fun(x[1]))[0]

def argmin(iterable, fun=None):
    if fun is None:
        fun = lambda x : x
    return min(enumerate(iterable), key=lambda x: fun(x[1]))[0]

def multiply_and_reduce(x,y):
    r'''

    TESTS::

        sage: from functions import *
        sage: A = Matrix(Zmod(3,10),5,5,range(10,10+25))
        sage: B = Matrix(Zmod(3,10),5,5,range(30,30+25))
        sage: multiply_and_reduce(A,B) == A * B
        True

    '''
    return (try_lift(x) * try_lift(y)).change_ring(x.parent().base_ring())


def take_power(x,n):
    r'''

    TESTS::

        sage: from functions import *
        sage: A = Matrix(Zmod(3,10),5,5,range(10,10+25))
        sage: take_power(A,10) == A ** 10
        True

    '''
    if n == 1:
        return x
    R = x.parent().base_ring()
    y = x.parent()(1)
    if n == 0:
        return y
    while n > 1:
        verbose("log_2(n) = %s"%RR(n).log(2))
        if n % 2 == 0:
            n = n // 2
        else:
            y = multiply_and_reduce(x,y)
            n = (n - 1) // 2
        x = multiply_and_reduce(x,x)
    return multiply_and_reduce(x, y)

def first_nonzero_pos(v,prec=None,return_val=False):
    r'''

    TESTS::

        sage: from functions import *
        sage: first_nonzero_pos([0,0,1,0,0,4,1])
        2
        sage: first_nonzero_pos([0,1,2])
        1
        sage: first_nonzero_pos([0,0,0])
        +Infinity
        sage: first_nonzero_pos([])
        +Infinity

    '''
    try:
        if prec is not None:
            ans = next(((i,o) for i,o in enumerate(v) if o.valuation() >= prec))
        else:
            ans = next(((i,o) for i,o in enumerate(v) if o != 0))
        if return_val:
            return ans
        else:
            return ans[0]
    except StopIteration:
        if return_val:
            return Infinity, None
        else:
            return Infinity

def is_echelon(E,prec=None):
    r'''

    TESTS::

        sage: from functions import *
        sage: A = Matrix(ZZ,2,3,[1,0,2,0,2,3])
        sage: is_echelon(A)
        True
        sage: A = Matrix(ZZ,2,3,[1,0,2,2,2,3])
        sage: is_echelon(A)
        False

    '''
    old_index = -1
    for i,row in enumerate(E.rows()):
        new_index = first_nonzero_pos(row,prec)
        if not new_index >= old_index + 1:
            return False
        old_index = new_index
    return True

def solve_xAb_echelon(A,b, p=None, prec=None, check=False):
    r'''

    TESTS::

        sage: from functions import *
        sage: A = Matrix(ZZ,2,3,[1,0,2,0,2,3])
        sage: is_echelon(A)
        True
        sage: b = vector(QQ,3,[4,5,6])
        sage: solve_xAb_echelon(A,b)
        (4, 5/2)
        sage: _ * A - b
        (0, 0, 19/2)

    '''
    R = b.parent().base_ring()
    try:
        R = R.fraction_field()
    except (AttributeError,TypeError): pass
    if p is None:
        try:
            p = R.cardinality().factor()[0][0] # DEBUG
        except AttributeError:
            p = 0
    if check and not is_echelon(A):
        raise ValueError("Not in echelon form")
    hnew = try_lift(b.parent()(b))
    ell = A.nrows()
    A = try_lift(A)
    col_list = []
    for j in range(ell):
        ej = A.row(j)
        ejleadpos, val = first_nonzero_pos(ej,return_val=True)
        newcol = [hnew[i,ejleadpos] / val for i in range(hnew.nrows())]
        hnew -= Matrix(hnew.parent().base_ring(), hnew.nrows(),1, newcol) * Matrix(ej.parent().base_ring(),1,len(ej),ej.list())
        col_list.append(newcol)

    alphas = Matrix(R,ell,hnew.nrows(),col_list).transpose()
    if check and p > 0:
        # print 'Check with p = %s'%p
        err = min([o.valuation(p) for o in (alphas * try_lift(A) - try_lift(b)).list()])
        if err < 5:
            raise RuntimeError("System appears not to be solvable. Minimal valuation is %s"%err)
    return alphas

def sorted_roots(R, f, p = None):
    H = PolynomialRing(R, names='x')
    x = H.gen()
    if p is None:
        p = R.prime()
    k = f.weight()
    chi = f.character()
    pol = H([R(chi(p) * p**(k-1)), R(-f.coefficients([p])[0]), R(1)])
    alpha,beta = [o[0] for o in pol.roots()]
    if alpha.valuation() > beta.valuation():
        alpha, beta = beta, alpha
    return alpha, beta

def eps_i(i,R,f):
    alpha, beta = sorted_roots(R,f)
    p = R.prime()
    k = f.weight()
    chi = f.character()
    return 1 - beta**2 * chi(p) * p**(1-k-i)

eps0 = lambda R,f : eps_i(0,R,f)
eps1 = lambda R,f : eps_i(1,R,f)

def epsilon_factor(R,f,g,h):
    alphaf, betaf = sorted_roots(R, f)
    alphag, betag = sorted_roots(R, g)
    alphah, betah = sorted_roots(R, h)
    k, l, m = f.weight(), g.weight(), h.weight()
    pmc = p**-(ZZ(k+l+m-2)//2)
    ans = (1 - betaf * alphag * alphah * pmc)
    ans *= (1 - betaf * alphag * betah * pmc)
    ans *= (1 - betaf * betag * alphah * pmc)
    ans *= (1 - betaf * betag * betah * pmc)
    return ans

def try_lift(A):
    if hasattr(A,'nrows') or hasattr(A,'dot_product'):
        try:
            return A.apply_map(lambda x:x.lift())
        except AttributeError: pass
        return A
    try:
        newA = [o.lift() for o in A]
    except AttributeError:
        return A
    try:
        return A.parent()(newA)
    except AttributeError:
        return newA

def depletion_coleman_multiply(g,h,p,prec,t=0):
    r"""
    Returns d^{-(1+t)}g^{[p]} x h as a function
    """
    prec = ZZ(prec)
    # Get coefficients of h
    try:
        hn = h.coefficients(range(prec + 1))
    except IndexError:
        hn = [QQ(0)] + h.coefficients(prec)
    assert len(hn) == prec + 1

    # Compute the p-depletion and Coleman primitive of g
    ans = []
    for n in xrange(prec):
        if n % p == 0:
            ans.append(QQ(0))
        else:
            ans.append(QQ(g.coefficients([n])[0]) / QQ(n)**ZZ(1+t))
    assert len(ans) == prec
    class conv(SageObject):
        def __init__(self,A,B):
            self.A = A
            self.B = B
        def __getitem__(self,M):
            return sum((self.A[i] * self.B[M-i] for i in xrange(M+1)))
        def __repr__(self):
            return "Convolution object"

    return conv(ans,hn)

def project_onto_eigenspace(gamma, ord_basis, hord, weight=2, level=1, epstwist = None, derivative_order = 1, p = None):
    ell = 1
    level = ZZ(level)
    R = hord.parent().base_ring()
    while True:
        ell = next_prime(ell)
        if level % ell == 0:
            continue
        verbose('Using ell = %s'%ell)
        T = hecke_matrix_on_ord(ell, ord_basis, weight, level, epstwist)
        aell = gamma[ell] / gamma[1]
        verbose('a_ell = %s'%aell)
        pp = T.charpoly().change_ring(hord.parent().base_ring())
        verbose('deg charpoly(T_ell) = %s'%pp.degree())
        x = pp.parent().gen()
        this_is_zero = pp.subs(R(aell))
        if this_is_zero.valuation(p) < 8: # DEBUG this value is arbitrary...
            verbose('!!! Should we skip ell = %s (because %s != 0 (val = %s))?????'%(ell,this_is_zero,this_is_zero.valuation(p)))
        if pp.derivative(derivative_order).subs(R(aell)).valuation(p) >= 8: # DEBUG this value is arbitrary...
            verbose('pp.derivative(derivative_order).subs(R(aell)) = %s'%pp.derivative().subs(R(aell)))
            verbose('... Skipping ell = %s because polynomial has repeated roots'%ell)
            continue
        qq = pp.quo_rem((x-R(aell))**ZZ(derivative_order))[0]
        break

    # qq = qq.parent()([o.lift() for o in qq.list()])
    qqT = try_lift(qq(T))
    qq_aell = qq.subs(R(aell))
    ord_basis_small = try_lift(ord_basis.submatrix(0,0,ncols=len(hord)))
    hord_in_katz = qexp_to_basis(hord, ord_basis_small)
    qT_hord_in_katz = hord_in_katz * qqT
    qT_hord = qT_hord_in_katz * try_lift(ord_basis)
    return ell, (qq_aell**-1 * try_lift(qT_hord)).change_ring(R)

def find_Apow_and_ord_three_stage(A, E, p, prec):
    R = ZpCA(p,prec)
    s0inv = QQ(2)
    first_power = QQ(prec * s0inv).ceil()
    Upa = take_power(A, first_power)
    ord_basis_qexp = []
    Apow_echelon = Upa.parent()(Upa)
    Apow_echelon = my_ech_form(try_lift(Apow_echelon).change_ring(R), p) # In place!
    ord_basis_0 = multiply_and_reduce(Apow_echelon,E)
    for qexp in ord_basis_0.rows():
        if qexp != 0: #min(o.valuation(p) for o in qexp) < prec: # != 0:
            ord_basis_qexp.append(qexp)

    ord_basis = try_lift(Matrix(ord_basis_qexp)).change_ring(R)
    Up_on_ord = hecke_matrix_on_ord(p, ord_basis, None, level = p).change_ring(R)
    f_degree = try_lift(Up_on_ord).change_ring(GF(p)).charpoly().splitting_field(names='a').degree()
    r = (p**f_degree - 1) * p**prec
    Upb_on_ord = take_power(Up_on_ord, r - first_power - 1)
    return ord_basis, Upa, Upb_on_ord

def find_Apow_and_ord_two_stage(A, E, p, prec):
    f_degree = A.change_ring(GF(p)).charpoly().splitting_field(names='a').degree()
    r = (p**f_degree - 1) * p**prec
    A = A.change_ring(ZpCA(p,prec))
    Apow = take_power(A, r-1)
    Ar = multiply_and_reduce(Apow, A)
    Ar = my_ech_form(Ar,p) # In place!
    ord_basis = []
    for o in Ar.rows():
        if o.is_zero():
            break
        ord_basis.append(o)
    E = try_lift(E)
    ord_basis_qexp = try_lift(Matrix(ord_basis)).change_ring(QQ) * E
    return ord_basis_qexp, Apow

def qexp_to_basis(f, E, p=None):
    ncols = len(list(f))
    fmat = Matrix(f.parent().base_ring(),1,len(f), f.list())
    return vector(solve_xAb_echelon(E.submatrix(0,0,ncols = ncols),fmat,p).list())

def katz_to_qexp(fvec, E):
    return fvec * E

def my_convolution(f,g):
    try:
        f0 = f.list()
    except AttributeError:
        f0 = f
    try:
        g0 = g.list()
    except AttributeError:
        g0 = g
    N = len(f0)
    ans = []
    for n in range(N):
        ans.append(sum(f0[i] * g0[n-i] for i in xrange(n+1)))
    try:
        return f.parent()(ans)
    except AttributeError:
        return ans

def compute_ordinary_projection_three_stage(H, Apow_data, E, elldash,p,nu=0):
    ord_basis, Upa_katz_exp, Upb_on_ord = Apow_data

    ord_basis = try_lift(ord_basis)
    Upa_katz_exp = try_lift(Upa_katz_exp)
    Upb_on_ord = try_lift(Upb_on_ord)
    E = try_lift(E)

    UpH = vector([H[p * n] for n in range(elldash * p**nu)])
    for i in range(nu):
        UpH = vector([UpH[p * n]for n in range(elldash * p**(nu-i-1))])
    ap = ZZ(1)
    if p == 3:
        ap = ZZ(3)
    elif p == 2:
        ap = ZZ(4)
    loss = ZZ((nu * (ap - 1) / (p+1) ).floor()+1)
    ploss = p**loss
    new_UpH = [ ploss * o for o in UpH ]
    UpH = UpH.parent()(new_UpH)


    UpH_katz = qexp_to_basis(UpH, E, p)
    UpH_katz_exp_a = UpH_katz * Upa_katz_exp
    UpH_a = katz_to_qexp(UpH_katz_exp_a, E)
    UpH_a_ord = qexp_to_basis(UpH_a, ord_basis,p)
    Hord_vec = UpH_a_ord * Upb_on_ord
    return (ploss**-1 * (Hord_vec * ord_basis))

def compute_ordinary_projection_two_stage(H, Apow_data, E, elldash,p):
    UpH = vector([H[p * n] for n in range(elldash)])
    Emat = try_lift(E).submatrix(0,0,ncols=elldash)
    Apow = Apow_data[0]
    alphas = qexp_to_basis(UpH, Emat,p)
    betas = alphas * try_lift(Apow)
    ans = katz_to_qexp(betas, Emat)
    return ans

def hecke_matrix_on_ord(ll, ord_basis, weight = 2, level = 1, eps = None, p=None, prec=None):
    R = ord_basis.parent().base_ring()
    if prec is None:
        try:
            prec = R.precision_cap()
        except AttributeError:
            pass
    ncols = ZZ(floor( (ord_basis.ncols() - 1) / ll)) + 1
    M = Matrix(R, ord_basis.nrows(), ncols, 0)
    if eps is None:
        if level % ll == 0:
            llpow_eps = ZZ(0)
        else:
            llpow_eps = ll**(weight-1)
    else:
        llpow_eps = ll**(weight-1) * eps(ll)

    for i, b in enumerate(ord_basis):
        for j in range(ncols):
            M[i, j] = b[j * ll]
            if j % ll == 0:
                M[i, j] += R(llpow_eps) * b[j // ll]
    small_mat = ord_basis.submatrix(0,0,ncols = M.ncols())
    assert is_echelon(small_mat)
    return solve_xAb_echelon(small_mat,M,p, prec)

def Lpvalue(f,g,h,p,prec,N = None,modformsring = False, weightbound = 6, eps = None, orthogonal_form = None, magma_args = None,force_computation=False, algorithm='threestage', derivative_order=1, lauders_advice = False):
    if magma_args is None:
        magma_args = {}
    if algorithm not in ['twostage','threestage']:
        raise ValueError('Algorithm should be one of "twostage" (default) or "threestage"')
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
    print("Tame level N = %s, prime p = %s, nu = %s"%(N,p,nu))
    prec = ZZ(prec)

    print("Step 1: Compute the Up matrix")
    if algorithm == "twostage":
        computation_name = '%s_%s_%s_%s_%s_%s'%(p,N,nu,kk,prec,'triv' if eps is None else 'char',algorithm)
    else:
        computation_name = '%s_%s_%s_%s_%s'%(p,N,nu,kk,prec,'triv' if eps is None else 'char')
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
                eps_magma = sage_character_to_magma(eps,N,magma=magma)
                Am, zetapm, eimatm, elldash, mdash = magma.UpOperatorData(p, eps_magma, kk, prec,nvals=5)
            else:
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
        remove(tmp_filename)

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
    return Lpa, ell


############################################################
# Code below is essentially what is in Sage,
# the existing functions just need to return more values
############################################################

def my_complementary_spaces_modp(N,p,k0,n,elldash,LWBModp,bound):
    r"""
    Returns a list of lists of lists of lists ``[j,a]``. The pairs ``[j,a]``
    encode the choice of the `a`-th element in the `j`-th list of the input
    ``LWBModp``, i.e., the `a`-th element in a particular basis modulo
    `(p,q^\text{elldash})` for the space of modular forms of level
    `\Gamma_0(N)` and weight `2(j+1)`. The list ``[[j_1,a_1],...,[j_r,a_r]]``
    then encodes the product of the r modular forms associated to each
    ``[j_i,a_i]``; this has weight `k + (p-1)i` for some `0 \le i \le n`; here
    the i is such that this *list of lists* occurs in the ith list of the
    output. The ith list of the output thus encodes a choice of basis for the
    complementary space `W_i` which occurs in Step 2 of Algorithm 2 in [Lau2011]_.
    The idea is that one searches for this space `W_i` first modulo
    `(p,q^\text{elldash})` and then, having found the correct products of
    generating forms, one can reconstruct these spaces modulo
    `(p^\text{mdash},q^\text{elldashp})` using the output of this function.
    (This idea is based upon a suggestion of John Voight.)

    INPUT:

    - ``N`` -- positive integer at least 2 and not divisible by p (level).
    - ``p`` -- prime at least 5.
    - ``k0`` -- integer in range 0 to `p-1`.
    - ``n,elldash`` -- positive integers.
    - ``LWBModp`` -- list of lists of `q`-expansions over `GF(p)`.
    - ``bound`` -- positive even integer (twice the length of the list ``LWBModp``).

    OUTPUT:

    - list of list of list of lists.

    EXAMPLES::

        sage: from sage.modular.overconvergent.hecke_series import random_low_weight_bases, complementary_spaces_modp
        sage: LWB = random_low_weight_bases(2,5,2,4,6)
        sage: LWBModp = [[f.change_ring(Zmod(5)) for f in x] for x in LWB]
        sage: complementary_spaces_modp(2,5,0,3,4,LWBModp,6) # random, indirect doctest
        [[[]], [[[0, 0], [0, 0]]], [[[0, 0], [2, 1]]], [[[0, 0], [0, 0], [0, 0], [2, 1]]]]
    """
    CompSpacesCode = []
    ell = dimension_modular_forms(N,k0 + n*(p-1))
    TotalBasisModp = matrix(GF(p),ell,elldash); # zero matrix

    print('n = %s'%n)
    print('k0 = %s'%k0)

    for i in range(n+1):
        NewBasisCodemi = random_new_basis_modp(N,p,k0 + i*(p-1),LWBModp,TotalBasisModp,elldash,bound)
        # TotalBasisModp is passed by reference and updated in function
        CompSpacesCode.append(NewBasisCodemi)

    return CompSpacesCode

def my_complementary_spaces(N,p,k0,n,mdash,elldashp,elldash,modformsring,bound):
    r"""
    Returns a list ``Ws``, each element in which is a list ``Wi`` of
    q-expansions modulo `(p^\text{mdash},q^\text{elldashp})`. The list ``Wi`` is
    a basis for a choice of complementary space in level `\Gamma_0(N)` and
    weight `k` to the image of weight `k - (p-1)` forms under multiplication by
    the Eisenstein series `E_{p-1}`.

    The lists ``Wi`` play the same role as `W_i` in Step 2 of Algorithm 2 in
    [Lau2011]_. (The parameters ``k0,n,mdash,elldash,elldashp = elldash*p`` are
    defined as in Step 1 of that algorithm when this function is used in
    :func:`hecke_series`.) However, the complementary spaces are computed in a
    different manner, combining a suggestion of David Loeffler with one of John
    Voight. That is, one builds these spaces recursively using random products
    of forms in low weight, first searching for suitable products modulo
    `(p,q^\text{elldash})`, and then later reconstructing only the required
    products to the full precision modulo `(p^\text{mdash},q^{elldashp})`. The
    forms in low weight are chosen from either bases of all forms up to weight
    ``bound`` or from a (tentative) generating set for the ring of all modular
    forms, according to whether ``modformsring`` is ``False`` or ``True``.

    INPUT:

    - ``N`` -- positive integer at least 2 and not divisible by p (level).
    - ``p`` -- prime at least 5.
    - ``k0`` -- integer in range 0 to ``p-1``.
    - ``n,mdash,elldashp,elldash`` -- positive integers.
    - ``modformsring`` -- True or False.
    - ``bound`` -- positive (even) integer (ignored if ``modformsring`` is True).

    OUTPUT:

    - list of lists of q-expansions modulo
      ``(p^\text{mdash},q^\text{elldashp})``.

    EXAMPLES::

        sage: from sage.modular.overconvergent.hecke_series import complementary_spaces
        sage: complementary_spaces(2,5,0,3,2,5,4,true,6) # random
        [[1],
        [1 + 23*q + 24*q^2 + 19*q^3 + 7*q^4 + O(q^5)],
        [1 + 21*q + 2*q^2 + 17*q^3 + 14*q^4 + O(q^5)],
        [1 + 19*q + 9*q^2 + 11*q^3 + 9*q^4 + O(q^5)]]
        sage: complementary_spaces(2,5,0,3,2,5,4,false,6) # random
        [[1],
        [3 + 4*q + 2*q^2 + 12*q^3 + 11*q^4 + O(q^5)],
        [2 + 2*q + 14*q^2 + 19*q^3 + 18*q^4 + O(q^5)],
        [6 + 8*q + 10*q^2 + 23*q^3 + 4*q^4 + O(q^5)]]
    """
    if modformsring == False:
        LWB = random_low_weight_bases(N,p,mdash,elldashp,bound)
    else:
        LWB,bound = low_weight_generators(N,p,mdash,elldashp)

    LWBModp = [ [ f.change_ring(GF(p)).truncate_powerseries(elldash) for f in x] for x in LWB]

    CompSpacesCode = my_complementary_spaces_modp(N,p,k0,n,elldash,LWBModp,bound)

    Ws = []
    Epm1 = eisenstein_series_qexp(p-1, prec=elldashp, K = Zmod(p**mdash), normalization="constant")
    for i in range(n+1):
        CompSpacesCodemi = CompSpacesCode[i]
        Wi = []
        for k in range(len(CompSpacesCodemi)):
            CompSpacesCodemik = CompSpacesCodemi[k]
            Wik = Epm1.parent()(1)
            for j in range(len(CompSpacesCodemik)):
                l = CompSpacesCodemik[j][0]
                index = CompSpacesCodemik[j][1]
                Wik = Wik*LWB[l][index]
            Wi.append(Wik)
        Ws.append(Wi)

    return Ws

def my_higher_level_katz_exp(p,N,k0,m,mdash,elldash,elldashp,modformsring,bound):
    r"""
    Returns a matrix `e` of size ``ell x elldashp`` over the integers modulo
    `p^\text{mdash}`, and the Eisenstein series `E_{p-1} = 1 + .\dots \bmod
    (p^\text{mdash},q^\text{elldashp})`. The matrix e contains the coefficients
    of the elements `e_{i,s}` in the Katz expansions basis in Step 3 of
    Algorithm 2 in [Lau2011]_ when one takes as input to that algorithm
    `p`,`N`,`m` and `k` and define ``k0``, ``mdash``, ``n``, ``elldash``,
    ``elldashp = ell*dashp`` as in Step 1.

    INPUT:

    - ``p`` -- prime at least 5.
    - ``N`` -- positive integer at least 2 and not divisible by p (level).
    - ``k0`` -- integer in range 0 to p-1.
    - ``m,mdash,elldash,elldashp`` -- positive integers.
    - ``modformsring`` -- True or False.
    - ``bound`` -- positive (even) integer.

    OUTPUT:

    - matrix and q-expansion.

    EXAMPLES::

        sage: from sage.modular.overconvergent.hecke_series import higher_level_katz_exp
        sage: e,Ep1 = higher_level_katz_exp(5,2,0,1,2,4,20,true,6)
        sage: e
        [ 1  0  0  0  0  0  0  0  0  0  0  0  0  0  0  0  0  0  0  0]
        [ 0  1 18 23 19  6  9  9 17  7  3 17 12  8 22  8 11 19  1  5]
        [ 0  0  1 11 20 16  0  8  4  0 18 15 24  6 15 23  5 18  7 15]
        [ 0  0  0  1  4 16 23 13  6  5 23  5  2 16  4 18 10 23  5 15]
        sage: Ep1
        1 + 15*q + 10*q^2 + 20*q^3 + 20*q^4 + 15*q^5 + 5*q^6 + 10*q^7 +
        5*q^9 + 10*q^10 + 5*q^11 + 10*q^12 + 20*q^13 + 15*q^14 + 20*q^15 + 15*q^16 +
        10*q^17 + 20*q^18 + O(q^20)
    """
    ordr = 1/(p+1)
    S = Zmod(p**mdash)
    Ep1 = eisenstein_series_qexp(p-1,prec=elldashp,K=S, normalization="constant")

    n = floor(((p+1)/(p-1))*(m+1))
    Wjs = my_complementary_spaces(N,p,k0,n,mdash,elldashp,elldash,modformsring,bound)

    Basis = []
    if k0 == p:
        rng = range(2,n+1)
    else:
        rng = range(n+1)
    for j in rng:
        Wj = Wjs[j]
        dimj = len(Wj)
        Ep1minusj = Ep1**(-j)
        for i in range(dimj):
            wji = Wj[i]
            b = p**floor(ordr*j) * wji * Ep1minusj
            Basis.append(b)

    # extract basis as a matrix
    ell = len(Basis)

    M = matrix(S,ell,elldashp)
    for i in range(ell):
        for j in range(elldashp):
            M[i,j] = Basis[i][j]

    M = my_ech_form(M,p) # put it into echelon form. In place!

    return M,Ep1

def my_ech_form(A,p):
    r"""
    Returns echelon form of matrix ``A`` over the ring of integers modulo
    `p^m`, for some prime `p` and `m \ge 1`.
    """

    S = A[0,0].parent()
    a = A.nrows()
    b = A.ncols()

    k = 0 # position pivoting row will be swapped to
    for j in range(b):
        if k < a:
            pivj = argmin(A.column(j).list()[k:], fun = lambda x:x.valuation(p)) + k
            if A[pivj,j] != 0: #.valuation(p) < +Infinity: # else column already reduced
                A.swap_rows(pivj, k)
                A.set_row_to_multiple_of_row(k, k, ~S(ZZ(A[k,j].unit_part())))
                for i in range(k+1,a):
                    A.add_multiple_of_row(i, k, S(-ZZ(A[i,j])/ZZ(A[k,j])))
                k = k + 1

    return A


def my_levelN_UpGj(p,N,k,m,modformsring,bound):
    r"""

    INPUT:

    - ``p`` -- prime at least 5.
    - ``N`` -- integer at least 2 and not divisible by p (level).
    - ``k`` -- the weight of f.
    - ``m`` -- positive integer.
    - ``modformsring`` -- True or False.
    - ``bound`` -- (even) positive integer.

    OUTPUT:

    - the matrix A and the matrix E.
    """
    t = cputime()
    # Step 1

    if k == 1:
        k0 = p
    else:
        k0 = k % (p-1)
    n = floor(((p+1)/(p-1)) * (m+1))
    elldash = compute_elldash(p,N,k0,n)
    elldashp = elldash*p
    mdash = m + ceil(n/(p+1))

    verbose("done step 1",t)
    t = cputime()
    # Steps 2 and 3
    e,Ep1 = my_higher_level_katz_exp(p,N,k0,m,mdash,elldash,elldashp,modformsring,bound)
    ell = dimension(transpose(e)[0].parent())
    S = e[0,0].parent()

    verbose("done steps 2+3", t)
    t = cputime()
    # Step 4

    R = Ep1.parent()
    G = compute_G(p, Ep1)
    Alist = []

    verbose("done step 4a", t)
    t = cputime()

    k = ZZ(k) # convert to sage integer

    if k == 1:
        kdiv = -1
    else:
        kdiv = k // (p-1)
    Gkdiv = G**kdiv

    T = matrix(S,ell,elldash)
    for i in range(ell):
        ei = R(e[i].list())
        Gkdivei = Gkdiv*ei; # act by G^kdiv
        for j in range(0, elldash):
            T[i,j] = Gkdivei[p*j]

    verbose("done steps 4b and 5", t)
    t = cputime()

    # Step 6: solve T = AE using fact E is upper triangular.
    # Warning: assumes that T = AE (rather than pT = AE) has
    # a solution over Z/(p^mdash). This has always been the case in
    # examples computed by the author, see Note 3.1.

    A = matrix(S,ell,ell)
    verbose("solving a square matrix problem of dimension %s" % ell)
    verbose("elldash is %s" % elldash)

    for i in range(0,ell):
        Ti = T[i]
        for j in range(0,ell):
            ej = Ti.parent()([e[j][l] for l in range(0,elldash)])
            ejleadpos = ej.nonzero_positions()[0]
            lj = ZZ(ej[ejleadpos])
            A[i,j] = S(ZZ(Ti[j])/lj)
            Ti = Ti - A[i,j]*ej

    A =  MatrixSpace(Zmod(p**m),ell,ell)(A)
    verbose("done step 6", t)
    return A, e, elldash, mdash

def my_level1_UpGj(p,k,m):
    r"""
    Returns a square matrix `A` over ``IntegerRing(p^m)``. The matrix `A` is the finite
    square matrix which occurs on input p,k and m in Step 6 of Algorithm 1 in
    [Lau2011]_. Notational change from paper: In Step 1 following Wan we defined
    j by `k = k_0 + j(p-1)` with `0 \le k_0 < p-1`. Here we replace j by
    ``kdiv`` so that we may use j as a column index for matrices.

    INPUT:

    - ``p`` -- prime at least 5.
    - ``k`` -- the weight.
    - ``m`` -- positive integer.

    OUTPUT:

    - the matrix A and the matrix E.
    """
    # Step 1
    t = cputime()

    if k == 1:
        k0 = p
    else:
        k0 = k % (p-1)

    n = floor(((p+1)/(p-1)) * (m+1))
    ell = dimension_modular_forms(1, k0 + n*(p-1))
    ellp = ell*p
    mdash = m + ceil(n/(p+1))

    verbose("done step 1", t)
    t = cputime()
    # Steps 2 and 3

    e,Ep1 = katz_expansions(k0,p,ellp,mdash,n)

    verbose("done steps 2+3", t)
    t=cputime()
    # Step 4

    G = compute_G(p, Ep1)

    verbose("done step 4a", t)
    t=cputime()
    k = ZZ(k) # convert to sage integer
    if k == 1:
        kdiv = -1
    else:
        kdiv = k // (p-1)
    Gkdiv = G**kdiv
    u = []
    for i in range(0,ell):
        ei = e[i]
        ui = Gkdiv*ei
        u.append(ui)

    verbose("done step 4b", t)
    t = cputime()
    # Step 5 and computation of T in Step 6

    S = e[0][0].parent()
    T = matrix(S,ell,ell)

    for i in range(0,ell):
        for j in range(0,ell):
            T[i,j] = u[i][p*j]

    verbose("done step 5", t)
    t = cputime()
    # Step 6: solve T = AE using fact E is upper triangular.
    # Warning: assumes that T = AE (rather than pT = AE) has
    # a solution over Z/(p^mdash). This has always been the case in
    # examples computed by the author, see Note 3.1.

    A = matrix(S,ell,ell)
    verbose("solving a square matrix problem of dimension %s" % ell, t)

    for i in range(ell):
        Ti = T[i]
        for j in range(ell):
            ej = Ti.parent()([e[j][l] for l in range(0,ell)])
            lj = ZZ(ej[j])
            A[i,j] = S(ZZ(Ti[j])/lj)
            Ti = Ti - A[i,j]*ej

    A = MatrixSpace(Zmod(p**m),ell,ell)(A)
    verbose("done step 6", t)

    e = Matrix(ZZ,ell,ell,[e[j][l] for j in range(ell) for l in range(ell)])
    return A, e, ell, mdash

def UpOperator(p,N,k,m, modformsring = False, weightbound = 6):
    r"""

    INPUT:

    - ``p`` -- a prime greater than or equal to 5.
    - ``N`` -- a positive integer not divisible by `p`.
    - ``k`` -- an integer.
    - ``m`` -- a positive integer.
    - ``modformsring`` -- ``True`` or ``False`` (optional, default ``False``).
      Ignored if `N = 1`.
    - ``weightbound`` -- a positive even integer (optional, default 6). Ignored
      if `N = 1` or ``modformsring`` is True.

    OUTPUT:

    A single polynomial over the integers modulo `p^m`.
    """

    # convert to sage integers
    p = ZZ(p)
    N = ZZ(N)
    m = ZZ(m)
    weightbound = ZZ(weightbound)

    # algorithm may finish with false output unless:
    if not p.is_prime():
        raise ValueError("p (=%s) is not prime" % p)
    if p < 5:
        raise ValueError("p = 2 and p = 3 not supported")
    if not N%p:
        raise ValueError("Level (=%s) should be prime to p (=%s)" % (N, p))

    if N == 1:
        return my_level1_UpGj(p,k,m)
        # Alist,E,elldash,mdash =  level1_UpGj(p,[k],m)
    else:
        return my_levelN_UpGj(p,N,k,m,modformsring,weightbound)
        # Alist,E,elldash,mdash = higher_level_UpGj(p,N,[k],m,modformsring,weightbound)
    return Alist[0], E, elldash, mdash

def sage_F_ideal_to_magma(F_magma,x,magma):
    Zm = F_magma.MaximalOrder()
    gens = x.gens_reduced()
    return magma.bar_call(Zm,'ideal',[Zm(magma(o)) for o in gens])

class ModFormqExp(SageObject):
    def __init__(self, v, R = None, weight = 2, character = None):
        if R is None:
            R = v[0].parent()
        self._qexp = [R(o) for o in v]
        self._weight = ZZ(weight)
        self._character = character
    def __getitem__(self, idx):
        return self._qexp[idx]
    def coefficients(self,idx):
        try:
            n = len(idx)
            return [self._qexp[i] for i in idx]
        except TypeError:
            return self._qexp[idx]
    def weight(self):
        return self._weight
    def character(self):
        return self._character

def sage_character_to_magma(chi,N=None,magma=None):
    if magma is None:
        magma = sage.interfaces.magma
    if N is None:
        N = chi.modulus()
    else:
        N = ZZ(N)
        chi = chi.extend(N)
    G = chi.parent()
    order = chi.order()
    gens = G.unit_gens()
    ElGm = magma.DirichletGroupFull(N)
    target = [chi(g) for g in gens]
    for chim in ElGm.Elements():
        if chim.Order().sage() == order:
            this = [chim.Evaluate(g).sage() for g in gens]
            K = this[0].parent()
            if this == [K(o) for o in target]:
                return chim
    raise RuntimeError("Should not get to this point")

def log_of_heegner_point(E,K,p,prec):
    QQp = Qp(p,prec)
    try:
        phi = K.hom([K.gen().minpoly().roots(QQp)[0][0]])
        Kp = QQp
    except IndexError:
        Kp = QQp.extension(K.gen().minpoly(),names=str(K.gen())+'_p')
        ap = Kp.gen()
        phi = K.hom([ap])
    PH = E.heegner_point(K.discriminant())
    PH = PH.point_exact(2000) # Hard-coded, DEBUG
    H = PH[0].parent()
    try:
        H1, H_to_H1, K_to_H1, _  = H.composite_fields(K,both_maps = True)[0]
        Hrel = H1.relativize(K_to_H1,'b')
        def tr(x):
            return x.trace(K) / Hrel.relative_degree()
    except AttributeError:
        H1, H_to_H1, K_to_H1 = K, lambda x:x, lambda x:x
        Hrel = K
        def tr(x):
            return x
    Kgen = K.gen(0)
    sigmas = [sigma for sigma in Hrel.automorphisms() if sigma(Kgen) == Kgen]
    EH1 = E.change_ring(H1)
    EHrel = E.change_ring(Hrel)
    EK = E.change_ring(K)
    PK = EHrel(0)
    for sigma in sigmas:
        PK += EHrel([Hrel(sigma(H_to_H1(PH[0]))),Hrel(sigma(H_to_H1(PH[1])))])

    EFp = (p**Kp.degree()+1-E.ap(p))
    PK = EK([tr(PK[0]),tr(PK[1])])
    n = 1
    nPK = PK
    while not (phi(nPK[0]).valuation() < 0 and phi(nPK[1]).valuation() < 0):
        n += 1
        nPK += PK
    tvar = -phi(nPK[0]/nPK[1])
    logPK = E.change_ring(Kp).formal_group().log(prec)(tvar) / n
    return logPK

def get_ulog(ualg, K, p, prec):
    QQp = Qp(p,prec)
    K = ualg.parent()
    try:
        phi = K.hom([K.gen().minpoly().roots(QQp)[0][0]])
        Kp = QQp
    except IndexError:
        Kp = QQp.extension(K.gen().minpoly(),names=str(K.gen())+'_p')
        ap = Kp.gen()
        phi = K.hom([ap])
    return phi(ualg).log(p_branch = 0)

def test_formula_display45(Lp, p, E, K, outfile=None):
    from sage.arith.misc import algdep
    prec = Lp.parent().precision_cap() + 100
    QQp = Qp(p,prec)
    hK = K.class_number()
    EFp = p+1 - E.ap(p)
    phi = K.hom([K.gen().minpoly().roots(QQp)[0][0]])
    ualg = (K.ideal(p).factor()[0][0]**hK).gens_reduced()[0]

    ulog = get_ulog(ualg, K, p, prec)
    logPK = log_of_heegner_point(E,K)

    fwrite("------------------------------------", outfile)
    fwrite("p = %s, cond(E) = %s, disc(K) = %s"%(p,E.conductor(),K.discriminant()), outfile)
    fwrite("------------------------------------", outfile)
    fwrite("h_K = %s"%hK, outfile)
    fwrite("# E(F_p) = %s"%EFp, outfile)
    fwrite("u satisfies: %s"%ualg.minpoly(), outfile)
    fwrite("ulog = %s"%ulog, outfile)
    fwrite("PK = %s"%PK, outfile)
    fwrite("logPK = %s"%logPK, outfile)
    ratio = Lp / ( (EFp**2 * logPK**2 ) / (p * (p-1) * hK * ulog) )
    fwrite("ratio = %s"%ratio, outfile)
    fwrite("ratio ~ %s"%algdep(ratio, 1).roots(QQ)[0][0], outfile)
    return ratio

def print_table_examples(Dbound):
    for D,h in [(D,h) for D,h in [(D,QuadraticField(D,'a').class_number()) for D in range(-1,-Dbound,-1)] if h % 2 == 1 and ZZ(-D).is_prime() and h > 2]:
        try:
            E = EllipticCurve(str(-D))
        except ValueError:
            continue
        if E.rank() != 1:
            continue
        print D,h, E.conductor()
        print '----'
        for p in prime_range(5,50):
            print p,E.change_ring(GF(p)).count_points().factor()
        print ''

def fwrite(string, outfile,newline = True):
    if outfile is None:
        fout = sys.stdout
        if newline:
            fout.write(string + '\n')
        else:
            fout.write(string)
    else:
        with open(outfile,"a") as fout:
            if newline:
                fout.write(string + '\n')
            else:
                fout.write(string)
        return

