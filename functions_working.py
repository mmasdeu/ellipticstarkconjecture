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

def multiply_and_reduce(x,y):
    r'''

    TESTS::

        sage: from functions import *
        sage: A = Matrix(Zmod(3,10),5,5,range(10,10+25))
        sage: B = Matrix(Zmod(3,10),5,5,range(30,30+25))
        sage: multiply_and_reduce(A,B) == A * B
        True

    '''
    return (x.apply_map(lambda x:x.lift()) * y.apply_map(lambda x:x.lift())).change_ring(x.parent().base_ring())


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
    while n > 1:
        verbose("log_2(n) = %s"%RR(n).log(2))
        if n % 2 == 0:
            n = n // 2
        else:
            y = multiply_and_reduce(x,y)
            n = (n - 1) // 2
        x = multiply_and_reduce(x,x)
    return multiply_and_reduce(x, y)

def first_nonzero_pos(v):
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
        ans = next((i for i,o in enumerate(v) if o != 0))
        return ans
    except StopIteration:
        return Infinity

def is_echelon(E):
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
        new_index = first_nonzero_pos(row)
        if not new_index >= old_index + 1:
            return False
        old_index = new_index
    return True

def solve_xAb_echelon(A,b):
    r'''

    TESTS::

        sage: from functions import *
        sage: A = Matrix(ZZ,2,3,[1,0,2,0,2,3])
        sage: is_echelon(A)
        True
        sage: b = vector(ZZ,3,[4,5,6])
        sage: solve_xAb_echelon(A,b)
        (4, 5/2)
        sage: _ * A - b
        (0, 0, 19/2)

    '''
    # verbose("Solving xAb...")
    R = b.parent().base_ring()
    if not is_echelon(A):
        raise ValueError("Not in echelon form")
    hnew = b.parent()(b)
    ell = A.nrows()
    alphas = vector(R,ell)
    for j in range(ell):
        ej = A.row(j)
        ejleadpos = first_nonzero_pos(ej)
        alphas[j] = hnew[ejleadpos] / ej[ejleadpos]
        hnew -= alphas[j] * ej
    # verbose("Done solving xAb")
    return alphas

def solve_XAB_echelon(A,B):
    return Matrix([solve_xAb_echelon(A, rw) for rw in B.rows()])

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
    def conv(M):
        return sum((ans[i] * hn[M-i] for i in xrange(M)))
    return conv

def project_onto_eigenspace(gamma, ord_basis, hord, weight=2, level=1, epstwist = None, derivative_order = 1):
    ell = 1
    level = ZZ(level)
    R = hord.parent().base_ring()
    while True:
        ell = next_prime(ell)
        if level % ell == 0:
            continue
        verbose('Using ell = %s'%ell)
        T = hecke_matrix_on_ord(ell, ord_basis, weight, level, epstwist)
        aell = gamma[ell]/gamma[1]
        verbose('a_ell = %s'%aell)
        pp = T.charpoly().change_ring(hord.parent().base_ring())
        verbose('deg charpoly(T_ell) = %s'%pp.degree())
        x = pp.parent().gen()
        this_is_zero = pp.subs({x:R(aell)})
        if this_is_zero.valuation() < 8: # DEBUG this value is arbitrary...
            verbose('!!! Should we skip ell = %s (because %s != 0 (val = %s))?????'%(ell,this_is_zero,this_is_zero.valuation()))
        if pp.derivative(derivative_order).subs({x:R(aell)}).valuation() >= 8: # DEBUG this value is arbitrary...
            verbose('pp.derivative(derivative_order).subs({x:R(aell)}) = %s'%pp.derivative().subs({x:R(aell)}))
            verbose('... Skipping ell = %s because polynomial has repeated roots'%ell)
            continue
        qq = pp.quo_rem((x-R(aell))**ZZ(derivative_order))[0]
        break

    qqT = qq(T).apply_map(lambda x:x.lift())
    qq_aell = R(qq.subs({x:R(aell)}))
    ord_basis_small = ord_basis.submatrix(0,0,ncols=len(hord))
    try:
        ord_basis_small = ord_basis_small.apply_map(lambda x:x.lift())
    except AttributeError:
        pass
    hord_in_katz = solve_xAb_echelon(ord_basis_small, hord)
    qT_hord_in_katz = hord_in_katz * qqT
    qT_hord = qT_hord_in_katz * ord_basis
    return ell, (qq_aell.lift()**-1 * qT_hord.apply_map(lambda x:x.lift())).change_ring(R)

def find_ord_three_stage(A,e,p,prec):
    # Take first step of projection
    s0inv = QQ(2)
    first_power = QQ(prec * s0inv).ceil()
    Apow = take_power(A, first_power)
    try:
        E = E.apply_map(lambda x:x.lift())
    except AttributeError:
        pass
    ord_basis_qexp = []
    for o in ech_form(Apow,p):
        qexp = (o * E).change_ring(Zmod(p**prec))
        if qexp != 0:
            ord_basis_qexp.append(qexp)

    ord_basis_qexp = (Matrix(ord_basis).apply_map(lambda x:x.lift()).change_ring(QQ) * E).change_ring(Zmod(p**prec))
    for b in ord_basis_qexp.rows():
        # Compute Up(b)
        pass
        # Write it in the ordinary basis
        pass


def find_Apow_and_ord_three_stage(A, E, p, prec):

    f_degree = A.change_ring(GF(p)).charpoly().splitting_field(names='a').degree()
    r = (p**f_degree - 1) * p**prec

    ord_basis, Upa_katz_exp, Upb_on_ord = find_ord_three_stage(A,E,p,prec)

    return

def find_Apow_and_ord(A, E, p, prec):
    f_degree = A.change_ring(GF(p)).charpoly().splitting_field(names='a').degree()
    r = (p**f_degree - 1) * p**prec
    Apow = take_power(A, r-1)
    Ar = multiply_and_reduce(Apow, A)
    Ar = ech_form(Ar,p)
    Ar.change_ring(Qp(p,prec))
    ord_basis = []
    for o in Ar.rows():
        if o.is_zero():
            break
        ord_basis.append(o)
    try:
        E = E.apply_map(lambda x:x.lift())
    except AttributeError:
        pass
    ord_basis_qexp = Matrix(ord_basis).apply_map(lambda x:x.lift()).change_ring(QQ) * E
    return Apow, ord_basis_qexp

def hecke_matrix_on_ord(ll, ord_basis, weight = 2, level = 1, eps = None):
    R = ord_basis.parent().base_ring()
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
                M[i, j] += llpow_eps * b[j // ll]
    small_mat = ord_basis.submatrix(0,0,ncols = M.ncols())
    return Matrix([solve_xAb_echelon(small_mat, rw) for rw in M.rows()])

def Lpvalue(f,g,h,p,prec,N = None,modformsring = False, weightbound = 6, eps = None, orthogonal_form = None, magma_args = None,force_computation=False,derivative_order=2):
    if magma_args is None:
        magma_args = {}
    from sage.interfaces.magma import Magma
    magma = Magma(**magma_args)
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
        if force_computation:
            raise IOError
        Apow, ord_basis, eimat, zetapm, elldash, mdash = db('Lpvalue_Apow_ordbasis_eimat_%s'%computation_name)
    except IOError:
        if force_computation or not os.path.exists(tmp_filename):
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
    if orthogonal_form is None:
        ell, piHord = project_onto_eigenspace(f, ord_basis, Hord.change_ring(R), kk, N * p, eps)
        n = 1
        while f[n] == 0:
            n += 1
        Lpa =  R(piHord[n])/ R(f[n])

    else:
        ell, piHord = project_onto_eigenspace(f, ord_basis, Hord.change_ring(R), kk, N * p, eps, derivative_order=derivative_order)
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

    ech_form(M,p) # put it into echelon form

    return M,Ep1

def my_ech_form(A,p,extramats = None):
    r"""
    Returns echelon form of matrix ``A`` over the ring of integers modulo
    `p^m`, for some prime `p` and `m \ge 1`.

    .. todo::

        This should be moved to :mod:`sage.matrix.matrix_modn_dense` at some
        point.

    INPUT:

    - ``A`` -- matrix over ``Zmod(p^m)`` for some m.
    - ``p`` - prime p.

    OUTPUT:

    - matrix over ``Zmod(p^m)``.

    EXAMPLES::

        sage: from sage.modular.overconvergent.hecke_series import ech_form
        sage: A = MatrixSpace(Zmod(5**3),3)([1,2,3,4,5,6,7,8,9])
        sage: ech_form(A,5)
        [1 2 3]
        [0 1 2]
        [0 0 0]
    """

    S = A[0,0].parent()
    a = A.nrows()
    b = A.ncols()
    if extramats is None:
        extramats = []
    k = 0 # position pivoting row will be swapped to
    for j in range(b):
        if k < a:
            pivj = k # find new pivot
            for i in range(k+1,a):
                if valuation(A[i,j],p) < valuation(A[pivj,j],p):
                    pivj = i
            if valuation(A[pivj,j],p) < +Infinity: # else column already reduced
                A.swap_rows(pivj, k)
                lam0 = S(ZZ(A[k,j])/(p**valuation(A[k,j],p)))**(-1)
                A.set_row_to_multiple_of_row(k, k, lam0)
                lam1 = [S(-ZZ(A[o,j])/ZZ(A[k,j])) for o in range(k+1,a)]
                for A0 in extramats:
                    A0.swap_rows(pivj, k)
                    A0.set_row_to_multiple_of_row(k, k, lam0)
                for A0 in extramats + [A]:
                    for i in range(k+1,a):
                        A0.add_multiple_of_row(i, k, lam1[i-k-1])
                k += 1
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

    # A = solve_XAB_echelon(e.submatrix(0,0,nrows=ell,ncols=ell),T.submatrix(0,0,ncols=ell))

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

    #A = solve_XAB_echelon(e.submatrix(0,0,nrows=ell,ncols=ell), T)

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


def sage_character_to_magma(chi,magma=None):
    if magma is None:
        magma = sage.interfaces.magma
    G = chi.parent()
    N = chi.modulus()
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


def test_formula_display45(Lp, p, E, K, remove_numpoints = False):
    from sage.arith.misc import algdep
    prec = Lp.parent().precision_cap() + 100
    QQp = Qp(p,prec)
    hK = K.class_number()
    EFp = p+1 - E.ap(p)
    phi = K.hom([K.gen().minpoly().roots(QQp)[0][0]])
    u = phi((K.ideal(p).factor()[0][0]**hK).gens_reduced()[0])
    if u.valuation() == 0:
        u = phi((K.ideal(p).factor()[1][0]**hK).gens_reduced()[0])
    assert u.valuation() > 0
    ulog = u.log(0)


    PH = E.heegner_point(K.discriminant())
    PH = PH.point_exact(200) # Hard-coded, DEBUG
    H = PH[0].parent()
    H1, H_to_H1, K_to_H1, _  = H.composite_fields(K,both_maps = True)[0]
    kgen = K_to_H1(K.gen())
    sigmas = [o for o in H1.automorphisms() if o(kgen) == kgen]
    EH1 = E.change_ring(H1)
    EK = E.change_ring(K)
    PK = EH1(0)
    for sigma in sigmas:
        PK += EH1(sigma(H_to_H1(PH[0])),sigma(H_to_H1(PH[1])))

    PK = EK(K(PK[0]),K(PK[1]))
    nn = 1
    while True:
        nPK = nn * PK
        PKpn = E.change_ring(QQp)((phi(nPK[0]),phi(nPK[1])))
        try:
            tvar = -phi(nPK[0]/nPK[1])
            logPK = E.change_ring(QQp).formal_group().log(prec)(tvar) / nn
            break
        except (ZeroDivisionError,ValueError):
            nn+=1
            print 'nn=',nn
    assert PK.order() == Infinity

    print "------------------------------------"
    print "p = %s, cond(E) = %s, disc(K) = %s"%(p,E.conductor(),K.discriminant())
    print "------------------------------------"
    print "h_K = %s"%hK
    print "# E(F_p) = %s"%EFp
    if remove_numpoints:
        EFp = 1
        print "  (not taking them into account)"
    print "PK = %s"%PK

    ratio = Lp / ( (EFp**2 * logPK**2 ) / (p * (p-1) * hK * ulog) )

    print "ratio = %s"%algdep(ratio, 1).roots(QQ)[0][0]
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
