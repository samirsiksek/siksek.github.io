"""
Compute polynomials associated to modular Galois representations
using complex approximations.

First type the following in a shell to turn it into pure Python code:
    sage modular_representation.sage
    
And in sage, import the resulting module:
    sage: from modular_representation import *

EXAMPLES:

Let's give an example for the Delta function modulo 13::
    sage: S = CuspForms(1, 12)
    sage: Delta = S.newforms()[0]
    sage: mgr = ModularGaloisRepresentation(Delta, 13)
    Searching symbols basis a = 1, c = 13
    ...
    Found a new symbol in basis
    sage: mgr.compute_rational_projective_polynomial()  # long time
    ...
    2535853*x^14 - 943257351*x^13 + 153486374093*x^12 - 13892268280150*x^11 + 696676904078194*x^10 - 10173822030475831*x^9 - 1170271007566197862*x^8 + 102377723494587456110*x^7 - 4460857890198398169442*x^6 + 126541325904151202440747*x^5 - 2466173719269665297684467*x^4 + 32912098920527666899213687*x^3 - 287983356231660946864164404*x^2 + 1488202496049226922783231139*x - 3437149493176190240933534819

AUTHOR:
 - Johan Bosman (2010, 2011)
"""


import cProfile
import itertools


# Some constants to tweak with
# Remark: we want to change STARTING_PRECISION to 53 but complex embeddings
#         of number fields are not well sorted for precision 53.

STARTING_PRECISION = 60
# STARTING_PRECISION = 53
PRECISION_LOSS = 30
MAX_STEPS = 2000
MAX_STEPS_ON_HIGH_PRECISION = 10
MAX_CPUS = 8

# Some multiprocessing stuff:

def execute_in_child_process(f):
    """
    Decorator that makes a function execute in a child process.

    INPUT:
     - ``f`` - function
     
    OUTPUT:
     - function - make a child process, call f from there and return f's result

    REMARKS:
     - This decorator wraps a sage.parallel.use_fork.p_iter_fork around f.
     - The side effects of f (such as caching) are thrown away.  So make
       sure that all important information is in the output of f.  In fact,
       reducing memory leaks is the intended use of the decorator.
     
    EXAMPLES: TODO
    """
    def new_f(*args, **kwargs):
        X = sage.parallel.use_fork.p_iter_fork(1, verbose=True)
        return list(X(f, [(args, kwargs)]))[0][1]
    return new_f


# Some lattice stuff that really sucks:

def LLL(M):
    """
    Perform LLL reduction on a lattice given by row vectors.

    INPUT:
     - ``M`` - a matrix, over ZZ, QQ, RR or CC - row vectors span lattice.

    OUTPUT:
     - a matrix whose row vectors form an LLL-reduced basis of the lattice.

    EXAMPLES:
     Don't bother, this code should be replaced by something better.
    """
    try:  # In case we're over ZZ or QQ
        d = M.denominator()
        return matrix(ZZ, d * M).LLL() / d
    except TypeError:
        pass

    if isinstance(M[0][0], sage.rings.real_mpfr.RealNumber) or \
       isinstance(M[0][0], sage.rings.real_double.RealDoubleElement):
        EXTRA_PRECISION = 20  # Arbitrary number, one can tweak with this.
        R = parent(M[0][0])
        fp_exponents = [0] + map(lambda x: log(x.abs(), 2),
                                 filter(lambda x: x != 0, M.list()))
        discrepancy = ceil(-min(fp_exponents))
        prec = R.prec() + discrepancy + EXTRA_PRECISION
        MM = matrix([ [(x *(1 << prec)).round() for x in row] for row in M ])
        return matrix([ [R(x) / (1 << prec) for x in row]
                         for row in MM.LLL() ])

    if isinstance(M[0][0], sage.rings.complex_number.ComplexNumber) or \
       isinstance(M[0][0], sage.rings.complex_double.ComplexDoubleElement):
        MM = matrix([reduce(operator.add, map(list, row)) for row in M])
        NN = LLL(MM)
        C = parent(M[0][0])
        result = []
        for row in NN:
            result_row = []
            for i in range(len(row) // 2):
                result_row.append( C(row[2*i], row[2*i + 1]) )
            result.append(result_row)
        return matrix(result)

    # If we reach this, then LLL has not been implemented for the matrix type.
    raise TypeError("Matrix entries do not have the right type for LLL")


def close_vector(M, w, apply_LLL=True):
    """
    Find lattice vector that is close to given vector.

    INPUT:
     - ``M`` - matrix over ZZ, QQ, RR or CC - row vectors span lattice
     - ``w`` - vector over ZZ, QQ, RR or CC of same degree as vectors in M
     - ``apply_LLL`` - boolean (default: True) - apply LLL to M or not

    OUTPUT:
     - vector in the lattice spanned by M that is close to w

    REMARK: Uses a `plane` algorithm.

    EXAMPLES:
     Don't bother, this code should be replaced by something better.
    """
    # Test for small w, should be improved:
    if not apply_LLL and 1000*w.norm() < M[0].norm():
        # print "close_vector with small w"
        return parent(w)(0)

    if isinstance(M[0][0], sage.rings.complex_number.ComplexNumber) or \
       isinstance(M[0][0], sage.rings.complex_double.ComplexDoubleElement):
        MM = matrix([reduce(operator.add, map(list, vec)) for vec in M])
        ww = vector(reduce(operator.add, map(list, w)))
        result = close_vector(MM, ww, apply_LLL)
        C = parent(M[0][0])
        return vector([ C(result[2*i], result[2*i+1]) for i in range(len(w)) ])

    if apply_LLL:
        M = LLL(M)
    G, _ = M.gram_schmidt()
    v = []
    for i in range(M.nrows()-1, -1, -1):
        L = [(w * G[j]) / (G[j] * G[j]) for j in range(i+1)]
        v.append(L[i].round() * M[i])
        w = sum([L[j]*G[j] for j in range(i)]) + L[i].round()*G[i] - v[-1]
    return sum(v)


def norm_modulo_lattice(M, w, apply_LLL=True):
    """
    Compute the norm of a vector modulo a lattice.

    INPUT:
     - ``M`` - matrix over ZZ, QQ, RR or CC - row vectors span lattice
     - ``w`` - vector over ZZ, QQ, RR or CC of same degree as vectors in M
     - ``apply_LLL`` - boolean (default: True) - apply LLL to M or not
    OUTPUT:
     - real number - smallest value of norm(w-lamda) for lambda in lattice

    REMARK:
     - When the norm is large, the output may not be correct as it relies
       on a close point computation.
    """
    return (w - close_vector(M, w, apply_LLL)).norm().n()


def approximate_sum(L, vecs, w, m):
    """
    Find a sum of vectors that approximates a given vector modulo a lattice.

    INPUT:
     - ``L`` - matrix over ZZ, QQ, RR or CC whose row vectors span a lattice
     - ``vecs`` - list of vectors of dimension rk(L)
     - ``w`` - vector over ZZ, QQ, RR or CC of same degree as vectors in L
     - ``m`` - integer - number of terms in the sum

    OUTPUT:
     - list of m indices such that the sum of vecs is close to w mod L

    EXAMPLES: TODO
    """
    C = Combinations(len(vecs), m)
    best_dist = Infinity
    for _ in range(100):
        indices = C.random_element()
        v = sum([vecs[i] for i in indices])
        dist = norm_modulo_lattice(L, v - w)
        if dist < best_dist:
            best_indices = indices
            best_dist = dist
    return best_indices


# Some global functions that we use:

def random_upper_half_plane_point(prec=53, max_entry=100):
    """
    Output a random UpperHalfPlanePoint.

    INPUT:
     - ``prec`` - integer (default: 53) - precision
     - ``max_entry`` - integer (default: 100) - maximum entry of SL2Z-matrix

    OUTPUT:
     - UpperHalfPlanePoint

    EXAMPLES: TODO
    """
    if prec == 53:
        R = RDF
        C = CDF
    else:
        R = RealField(prec)
        C = ComplexField(prec)
    while True:
        x = R.random_element(-1/2, 1/2)
        y = R(1) / R.random_element(0, R(sqrt(4/3)))
        if x^2 + y^2 >= 1:
            break
    z = C(x + I*y)
    gamma = MatrixSpace(ZZ,2)(list(SL2Z.random_element(max_entry)))
    return UpperHalfPlanePoint(z, gamma)


def adjust_precision(obj, prec=53):
    """
    Adjust the precision of an object.

    INPUT:
     - ``obj`` - an object that could be several things having a precision
     - ``prec`` - integer (default: 53) - precision

    OUTPUT:
     - obj with precision adjusted to prec

    EXAMPLES: TODO
    """
    try:
        return obj.adjust_precision(prec)
    except AttributeError:
        pass

    if isinstance(obj, list):
        return [adjust_precision(x, prec) for x in obj]
    if isinstance(obj, tuple):
        return tuple(adjust_precision(list(obj), prec))

    if isinstance(obj, (sage.rings.complex_number.ComplexNumber,
                        sage.rings.complex_double.ComplexDoubleElement)):
        if prec == obj.prec():
            return obj
        if prec == 53:
            C = CDF
        else:
            C = ComplexField(prec)
        return C(obj)

    if isinstance(obj, (sage.rings.real_mpfr.RealNumber,
                        sage.rings.real_double.RealDoubleElement)):
        if prec == obj.prec():
            return obj
        if prec == 53:
            R = RDF
        else:
            R = RealField(prec)
        return R(obj)

    try:
        if obj.is_vector():
            return vector([adjust_precision(x, prec) for x in obj])
    except AttributeError:
        pass
    try:
        obj.ncols()  # Trick to check whether it's a matrix
        return matrix([adjust_precision(x, prec) for x in obj])
    except AttributeError:
        pass

    if isinstance(obj, sage.rings.power_series_poly.PowerSeries_poly):
        if isinstance(obj[0], sage.rings.complex_number.ComplexNumber):
            if prec == 53:
                C = CDF
            else:
                C = ComplexField(prec)
            R.<qq> = C[[]]
            return R(adjust_precision(list(obj), prec)).add_bigoh(obj.prec())
    # This code should not be reached:
    raise TypeError("precision adjustment not implemented for input type")


def real_denominator(number, quality=30):
    """
    Compute a denominator for a rational approximation of given real number.

    INPUT:
     - ``number`` - real number
     - ``quality`` - Integer (default: 30) - see common_denominator's docstring

    OUTPUT:
     - Integer - not guaranteed to have the right quality

    REMARKS:
     - Uses continued fractions, the quality is used to cut off the convergents

    EXAMPLES: TODO
    """
    cont_frac = continued_fraction(number)
    sub_frac = [cont_frac[0]] + \
           list(itertools.takewhile(lambda x: x < (1<<quality), cont_frac[1:]))
    return continued_fraction(sub_frac).denominator()


@execute_in_child_process
def common_denominator(numbers, quality=30, ncpus=None):
    """
    Try to find a common denominator for a list of reals close to rationals.

    INPUT:
     - ``numbers`` - list of real numbers of the same fixed precision
     - ``quality`` - Integer(default: 30) - see remarks
     - ``ncpus`` - Integer(default: None) - number of parallel cpu's used

    OUTPUT:
     - Integer - common denominator for rationals that approximate the reals

    REMARKS:
     - The output will be 0 if the input has insufficient precision to find
       a convincing common denominator
     - The quality indicates what 'convincing' means.  We call a common
       denominator q convincing if |p - q*x| < 2^-quality * q^(-1/n) for the
       approximations p/q of each of the n numbers x.

    TODO:
     - Sometimes a computed quality is +infinity, which is nonsense.  Repair!
     - LLL stuff is currently very bad (Sage has no floating point LLL) so
       add some continued fraction stuff as well.
    
    EXAMPLES: TODO
    """
    # Note that one can tweak a lot with the implementation.
    if ncpus is None:
        ncpus = min(MAX_CPUS, sage.parallel.ncpus.ncpus())
    n = len(numbers)
    prec = max(100, 3 * n, numbers[0].prec())
    R = RealField(prec)
    mat = [[R(0)]*i + [R(1)] + [R(0)]*(n-i) for i in range(n)]
    mat.append(map(R, numbers) + [R(0)])
    
    def qualities(c):
        mat[n][n] = R(1/1 >> c)
        matlll = LLL(matrix(mat))
        q = max(1, (matlll[0][n] * R(1 << c)).round().abs())
        # print "common_denominator: testing q =", q
        if (n+1)/n*log(q,2) >= numbers[0].prec() - quality:  # q is too big
            return (0, [0])
        p = [(number*q).round() for number in numbers]
        approx = [((R(p[i]/q) - numbers[i])*R(q)^(1+1/n)).abs() for i
                  in range(n)]
        qualities = [(-log(appr, 2)) for appr in approx]
        # print "qualities:", [qq.n(quality) for qq in qualities]
        return (q, [(-log(appr, 2)) for appr in approx])

    X = sage.parallel.use_fork.p_iter_fork(ncpus, verbose=True)
    result = X(qualities, [((c,),{}) for c in sxrange(prec - 30, 29, -30)])
    result = [x for x in result if min(x[1][1]) > quality]
    if result != []:
        return sorted(result)[-1][1][0]
    else:
        return 0


def character_values(f):
    """
    Determine the values of the character associated to an eigenform.

    INPUT:
     - ``f`` - eigenform of some level N, weight k and character epsilon

    OUTPUT:
     - list of length N whose n-th entry is epsilon(n).

    EXAMPLES: TODO
    """
    N = f.level()
    k = f.weight()
    result = []
    coeffs = list(f.qexp(N^2))
    for n in srange(N):
        if gcd(n, N) != 1 or n == 0:
            result.append(0)
        else:
            epsilon_value = 1
            for p, e in n.factor():
                ap = coeffs[p]
                ap2 = coeffs[p^2]
                epsilon_value *= ((ap^2 - ap2) / p^(k-1))^e
            result.append(epsilon_value)
    return result


# Implementation of classes:

class UpperHalfPlanePoint(SageObject):
    """
    Data type to represent points in the upper half plane.

    A point in the upper half plane H is represented as gamma(z) where
    gamma is a 2x2-matrix and z is in the upper half plane.  The action
    of gamma on H is meant by linear fractional transformations.  For
    numerical stability it is wise to choose gamma in SL_2(ZZ) and z in
    the standard fundamental domain of SL_2(ZZ) acting on H.

    INPUT:
     - ``z`` - complex number in the upper half plane
     - ``gamma`` - 2x2 matrix (default: the identity matrix over ZZ)

    EXAMPLES:
    ::
        sage: UpperHalfPlanePoint(CC(1.234 + 23.5 * I))
        [1 0]
        [0 1] (1.23400000000000 + 23.5000000000000*I)
    """

    def __init__(self, z, gamma=MatrixSpace(ZZ, 2)(1)):
        assert z.imag() > 0
        self.z = z
        self.gamma = gamma

    def _repr_(self):
        return self.gamma.__repr__() + " (" + self.z.__repr__() + ")"

    def __eq__(self, other):
        return (self.gamma == other.gamma or self.gamma == -gamma) and \
                self.z == other.z

    def prec(self):
        """
        Output the precision of the z-part of self.
        """
        return self.z.prec()

    def adjust_precision(self, prec=53):
        """
        Cut down the precision of self.

        INPUT:
         - ``prec`` - integer(default: 53) - indicates precision

        OUTPUT:
         - UpperHalfPlanePoint - self approximated to precision at most prec

        REMARK:
         - If prec >= self.prec(), simply output self.

        EXAMPLES: TODO
        """
        if prec == self.prec():
            return self
        return UpperHalfPlanePoint(adjust_precision(self.z, prec), self.gamma)

    def to_complex(self):
        """
        Output the point as a plain complex number.

        EXAMPLES:
        ::
            sage: gamma = matrix(ZZ, [[2, 3], [1, 4]])
            sage: P = UpperHalfPlanePoint(CC(1.234 + 23.5 * I), gamma)
            sage: P.to_complex()
            1.95485165745207 + 0.202710364898048*I
        """
        try:
            (a, b), (c, d) = self.gamma
        except ValueError:
            a, b, c, d = list(self.gamma)
        return (a * self.z + b) / (c * self.z + d)

    def star(self):
        """
        Output self, mirrored in the imaginary axis

        OUTPUT: UpperHalfPlanePoint

        EXAMPLES: TODO
        """
        try:
            (a, b), (c, d) = self.gamma
        except ValueError:
            a, b, c, d = list(self.gamma)
        return UpperHalfPlanePoint(-self.z.conjugate(),
                                   matrix([[a, -b], [-c, d]]))

    def normalize(self, N=0):
        """
        Normalize the representation of the point `self`.

        INPUT:
         - ``N`` - integer (default: 0) - if nonzero, adjust self.gamma
           modulo Gamma1(N)

        OUTPUT:
         - UpperHalfPlanePoint - the point represented as gamma(z) with
           gamma in SL_2(ZZ) and z in the standard fundamental domain of
           the SL_2(ZZ)-action on the upper half plane

        EXAMPLES:
        ::
            sage: z = CC(0.332631762888569 + 0.00462163299905621*I)
            sage: gamma = Matrix(ZZ,2,[1,2,3,7])
            sage: P = UpperHalfPlanePoint(z, gamma)
            sage: P.normalize()
            [ 7 23]
            [24 79] (0.233999999999068 + 23.5000000000003*I)

        TODO: more examples

        TODO:
         - Give implementation in case where det(gamma) != 1.
        """
        # First adjust the imaginary part of z:
        prec = self.z.prec() - min(0, self.z.imag().abs().log2().floor())
        lattice = Matrix(ZZ, 2,
            [(self.z.real() * (1 << prec)).round(),
             (self.z.imag() * (1 << prec)).round(),
                1 << prec, 0] )
        small_vector = lattice.LLL()[0]
        c, d = small_vector * lattice.inverse()
        _, a, b = xgcd(d, -c)
        gamma1 = Matrix(ZZ, 2, [a, b, c, d])

        # Now adjust the real part:
        z = (a * self.z + b) / (c * self.z + d)
        h = z.real().round()
        gamma1 = Matrix(ZZ, 2, [1, -h, 0, 1]) * gamma1
        gamma2 = matrix(ZZ, self.gamma * gamma1.inverse())

        # Then adjust the matrix:
        if N != 0:
            (a, b), (c, d) = gamma2
            c %= N
            d %= N
            if d == 0:
                d = N
            while gcd(c, d) != 1:
                c += N
            _, a, b = xgcd(d, -c)
            gamma2 = Matrix(ZZ, 2, [a, b, c, d])

        return UpperHalfPlanePoint(z - h,  gamma2)

    def __add__(self, h):
        """
        Add a small complex number h to the z-part of the current point.

        INPUT:
         - ``h`` - complex number, meant to be small

        OUTPUT:
         - gamma(z+h) where the current point is represented as gamma(z)

        EXAMPLES: TODO
        """
        return UpperHalfPlanePoint(self.z + h, self.gamma)

    def __rmul__(self, n):
        """
        Multiply the point by an integer.

        INPUT:
         - ``n`` - integer

        OUTPUT:
         - upper half plane point n*gamma(z) written as gamma'(z') with
           gamma' in SL2(ZZ)

        EXAMPLES:
        ::
            sage: z = CC(0.332631762888569 + 0.00462163299905621*I)
            sage: gamma = Matrix(ZZ, 2, [1, 2, 3, 7])
            sage: P = UpperHalfPlanePoint(z, gamma)
            sage: 18*P
            [ 6 -1]
            [ 1  0] (1.33298254811095 + 0.00231081649952810*I)
        """
        assert n > 0
        z, gamma = self.z, self.gamma
        for p, e in n.factor():
            for _ in xrange(e):
                (a, b), (c, d) = gamma
                if p.divides(gamma[1][0]):
                    z *= p
                    gamma = Matrix(ZZ, 2, [a, p*b, c//p, d])
                else:
                    _, d1, b1 = xgcd(p*a, -c)
                    gamma1 = Matrix(ZZ, 2, [p*a, p*b, c, d])
                    gamma = Matrix(ZZ, 2, [p*a, b1, c, d1])
                    (a2, b2), (c2, d2) = gamma.inverse() * gamma1
                    z = (a2*z + b2) / d2
        return UpperHalfPlanePoint(z, gamma)


class EvaluableEigenform(SageObject):
    """
    Data type for eigenforms that we intend to evaluate numerically.

    TODO: description

    INPUT:
     - ``f`` - ModularFormElement - a newform
     - ``r`` - Integer (default: 1) - means f(rz) is our eigenform

    EXAMPLES: TODO

    TODO:
     - Store numerical series for several precisions, not just one.
     - Compute period integrals by twisting.
     - The current implementation is restricted to prime levels only.
       Generalize to square-free or all levels.
    """

    def __init__(self, f, r=1):
        """
        Put basic information about the pair (f,r) into attributes.

        - Compute a table of values for the character of f.
        - Determine an index n such that K_f = Q(a_n(f)).
        (- Determine the homomorphism K_f->Q(a_n(f)).)
        - Determine a K_f-basis of symbols {oo, a/c} that pair well with f.

        TODO:
         - Move the things above to different methods.
        """
        self._f = f
        self._r = r
        self._stored_series_oo = {}
        self._stored_series_oo_int = {}

        N = f.level()
        if not N.is_prime():
            raise NotImplementedError, "The level of f must be prime."
        k = f.weight()
        self._epsilon_values = character_values(f)

        # Determine generating coefficient for K_f:
        Kf = f.base_ring()
        if Kf == QQ:
            self.generating_index = 1
            _.<x> = QQ[]
            Qan = NumberField(x - 1, 'a')  # NumberField has methods we use.
            self._hom_Qan_Kf = Qan.hom([1],Kf)
        else:
            for n in itertools.count(1):
                K, m = Kf.subfield(f.qexp(n+1)[n])
                if K.degree() == Kf.degree():
                    break
            self.generating_index = n
            self._hom_Qan_Kf = m
        # M = matrix([ list( m(K.0)^n ) for n in range(K.degree()) ])
        # self.generating_field_hom = Kf.hom( [K(M.inverse()[1])], K )

        # Determine modular symbols basis of elements of the form {oo, a/c}:
        SS = ModularSymbols(f.group(), k).cuspidal_subspace()
        subSSf = f.modular_symbols()
        kerSSf = SS.module().subspace([0])
        kerSSf += sum([x.module() for x in SS.decomposition() if x != subSSf])
        quoSSf = SS.module() / kerSSf
        self._modsym_basis = []
        submodule = quoSSf.submodule([])
        symbols = []
        T = SS.ambient().T(self.generating_index).matrix()
        try:
            for c1 in itertools.count(1):
                c = c1 * N
                for a in [1 + a1*N for a1 in range(c1) if gcd(c,1+a1*N) == 1]:
                    # print "Searching symbols basis a = %d, c = %d" % (a, c)
                    # assert SS == loads(dumps(SS))  # Somewhere is a pickl. bug
                    alpha = vector(SS([0, Infinity, a/c]))
                    if quoSSf(alpha) not in submodule:
                        # print "Found a new symbol in basis"
                        self._modsym_basis += [a/c]
                        symbols += [alpha * T^d for d in range(Kf.degree())]
                        submodule += quoSSf.submodule(map(quoSSf, symbols))
                        if len(self._modsym_basis) == 2:
                            raise StopIteration()
        except StopIteration:
            pass
        self._SS = SS
        self._modsym_quotient = quoSSf
        self._modsym_matrix = matrix(map(quoSSf, symbols))

    def form(self):
        """
        Return the modular form that was used to construct self.

        OUTPUT:
         - ModularFormElement - the one used in self.__init__(f, r)

        EXAMPLES: TODO
        """
        return self._f

    def r(self):
        """
        Return the degeneracy parameter that was used to construct self.

        OUTPUT:
         - Integer - the number r used in self.__init__(f, r)

        EXAMPLES: TODO
        """
        return self._r

    def _repr_(self):
        if self.r() == 1:
            s = self.form().__repr__()
        else:
            s = "alpha_%s(%s)" % (self.r().__repr__(), self.form().__repr__())
        return "Evaluable eigenform " + s

    def epsilon(self, d):
        """
        Output epsilon(d) in K_f where f=self and epsilon its character.

        INPUT:
         - ``d`` - integer

        OUTPUT:
         - element of K_f

        EXAMPLES: TODO
        """
        return self._epsilon_values[d % self.form().level()]

    def _compute_series_oo(self, C, qprec):
        """
        Numerically compute and store the series of f and its integral.

        INPUT:
         - ``C`` - a complex field - the field of coefficients
         - ``qprec`` - integer - the q-precision

        TODO:
         - figure out whether we should execute some stuff in a child process
        """
        R.<qq> = C[[]]
        Kf = self.form().base_ring()
        sigmas = Kf.embeddings(C)
        self._stored_series_oo[C.prec()] = \
            [R(map(sigma, list(self.form().qexp(qprec)))).add_bigoh(qprec) for
             sigma in sigmas]
        self._stored_series_oo_int[C.prec()] = \
            [(f/qq).integral() for f in self._stored_series_oo[C.prec()]]

    def series_oo(self, C, qprec):
        """
        Get the q-series of self, numerically computed for each C-embedding.

        INPUT:
         - ``C`` - complex field - field of coefficients
         - ``qprec`` - integer - number of terms in the series to be output

        OUTPUT:
         - list of power series over C, one for each C-embedding of Kf

        EXAMPLES: TODO
        """
        if C.prec() not in self._stored_series_oo or \
           self._stored_series_oo[C.prec()][0].prec() < qprec:
            self._compute_series_oo(C, qprec)
        # I'm not sure if add_bigoh(qprec) should be here:
        return [f.add_bigoh(qprec) for f in self._stored_series_oo[C.prec()]]

    def series_oo_int(self, C, qprec):
        """
        Get the q-series of the integral of self numerically.

        INPUT:
         - ``C`` - complex field - field of coefficients
         - ``qprec`` - integer - number of terms in the series to be output

        OUTPUT:
         - list of power series over C, one for each C-embedding of Kf

        EXAMPLES: TODO
        """
        if C.prec() not in self._stored_series_oo_int or \
           self._stored_series_oo_int[C.prec()][0].prec() < qprec:
            self._compute_series_oo(C, qprec)
        # I'm not sure if add_bigoh(qprec) should be here:
        return [f.add_bigoh(qprec)
                for f in self._stored_series_oo_int[C.prec()]]

    def evaluate_naively(self, z, r=0):
        """
        Evaluate f=self numerically at z for all complex embeddings of Kf.

        We simply plug in q(z) into the q-expansion of f.

        INPUT:
         - ``z`` - Complex number or UpperHalfPlanePoint
         - ``r `` - integer (default: 0) - if nonzero change degeneracy of f

        OUTPUT:
         - a list of values of f(z) for all complex embeddings of K_f

        EXAMPLES: TODO
        """
        if isinstance(z, UpperHalfPlanePoint):
            z = z.to_complex()
        if r == 0:
            r = self.r()
        z = r * z
        C = z.parent()
        q = C(exp(2*pi*I*z))
        qprec = Integer(max(100, round(3/25 * C.prec() / z.imag())))
        return vector([f(q) for f in self.series_oo(C,qprec)])

    def lambda_N(self, prec=53):
        """
        Compute Atkin-Lehnerpseudo-eigenvalues lambda_N to precision prec.

        INPUT:
         - ``prec`` - integer (default: 53) - indicates precision

        OUTPUT
         - lambda_N - list of complex numbers, indexed by K_f->C

        EXAMPLES: TODO
        """
        if prec == 53:
            C = CDF
        else:
            C = ComplexField(prec)
        if hasattr(self, '_stored_lambda_N'):
            if self._stored_lambda_N[0].prec() == prec:
                return self._stored_lambda_N
            if self._stored_lambda_N[0].prec() > prec:
                return map(C, self._stored_lambda_N)
        N = self.form().level()
        k = self.form().weight()
        z = C((I + C.random_element() / 10) / sqrt(N))
        gz = [x.conjugate() for x in self.evaluate_naively(-z.conjugate())]
        wnfz = [x / (N^(k/2) * z^k) for x in self.evaluate_naively(-1/(N*z))]
        self._stored_lambda_N = map(operator.div, wnfz, gz)
        return self._stored_lambda_N

    def evaluate_by_wN(self, z, r=0):
        """
        Evaluate f=self numerically at z for all complex embeddings of Kf.

        We use W_N(f) and plug in -1/Nz.

        INPUT:
         - ``z`` - Complex number or UpperHalfPlanePoint
         - ``r `` - integer (default: 0) - if nonzero change degeneracy of f

        OUTPUT:
         - a list of values of f(z) for all complex embeddings of K_f

        EXAMPLES: TODO
        """
        if isinstance(z, UpperHalfPlanePoint):
            z = z.to_complex()
        if r == 0:
            r = self.r()
        z = r * z
        N = self.form().level()
        k = self.form().weight()
        z1 = -1 / (N*z)
        gz1 = [x.conjugate() for x in self.evaluate_naively(-z1.conjugate(),1)]
        factor = N^(k/2) * z1^k
        values = vector(map(operator.mul, self.lambda_N(z.prec()), gz1))
        return factor * values

    def evaluate(self, P):
        """
        Evaluate f=self numerically at z for all complex embeddings of Kf.

        We use transformation properties as well as the q-expansion of f.

        INPUT:
         - ``P`` - UpperHalfPlanePoint

        OUTPUT:
         - a vector of values of f(z) for all complex embeddings of K_f

        EXAMPLES: TODO

        TODO: Make this work for other levels than prime ones.
        """
        if self.r() > 1:
            P = (self.r() * P).normalize()
        (a, b), (c, d) = P.gamma
        C = P.z.parent()
        sigmas = self.form().base_ring().embeddings(C)
        N = self.form().level()
        k = self.form().weight()
        if N.divides(c):
            result = [(c * P.z + d) ^ k * sigma(self.epsilon(d)) * x for
                      sigma, x in zip(sigmas, self.evaluate_naively(P.z, 1))]
        else:
            j = -d * inverse_mod(c,N) % N
            z1 = 1 / (j - P.z)
            if z1.norm() > 1/N:
                fz1 = self.evaluate_naively(z1, 1)
            else:
                fz1 = self.evaluate_by_wN(z1, 1)
            (a1, b1), (c1, d1) = P.gamma * matrix([[j,-1],[1,0]])
            result = [(c1 * z1 + d1) ^ k * sigma(self.epsilon(d1)) * x
                      for sigma, x in zip(sigmas, fz1)]
        return vector(result)

    def integrate_naively(self, z, r=0):
        """
        Integrate f=self from oo to z for all complex embeddings of Kf.

        We simply plug in q(z) into the q-expansion of f.

        INPUT:
         - ``z`` - Complex number or UpperHalfPlanePoint
         - ``r `` - integer (default: 0) - if nonzero change degeneracy of f

        OUTPUT:
         - a vector of values of f(z) for all complex embeddings of K_f

        EXAMPLES: TODO
        """
        if isinstance(z, UpperHalfPlanePoint):
            z = z.to_complex()
        if r == 0:
            r = self.r()
        z = r * z
        C = z.parent()
        q = C(exp(2*pi*I*z))
        qprec = Integer(max(100, round(3/25 * C.prec() / z.imag())))
        return vector([f(q) / r for f in self.series_oo_int(C,qprec)])

    def basis_integrals(self, prec=53):
        """
        Compute period integrals over the symbols in basis=self._modsym_basis

        INPUT:
         - ``prec`` - integer (default: 53) - indicates precision

        OUTPUT:
         - [(integrals of embeddings of f over {oo, a/c}) for a/c in basis]

        EXAMPLES: TODO
        """
        if prec == 53:
            C = CDF
        else:
            C = ComplexField(prec)
        if hasattr(self, '_stored_basis_integrals'):
            if self._stored_basis_integrals[0][0].prec() == prec:
                return self._stored_basis_integrals
            if self._stored_basis_integrals[0][0].prec() > prec:
                return map(lambda x: vector(map(C, x)),
                           self._stored_basis_integrals)
        self._stored_basis_integrals = []
        for a, c in map(lambda x: (x.numer(), x.denom()), self._modsym_basis):
            _, b, d = xgcd(-c, a)
            z = C((-d + I) / c)
            z1 = (a*z + b) / (c*z + d)
            intz = self.integrate_naively(z, 1)
            intz1 = self.integrate_naively(z1, 1)
            self._stored_basis_integrals.append(intz1 - intz)
        return self._stored_basis_integrals

    def K_f_coefficients(self, alpha):
        """
        Map modular symbol to K_f^2 (f=self) wrt self._modsym_basis.

        INPUT:
         - ``alpha`` - modular symbol with the same parameters as self

        OUTPUT:
         - a list of 2 elements of K_f

        If (alpha_1, alpha_2) is the basis given by self._modsym_basis,
        then the output [a,b] is such that
        <alpha, f> = a * <alpha_1, f> + b * <alpha_2, f>
        holds for all embeddings K_f -> CC. Here <,> denotes the integral
        pairing between modular symbols and cusp forms.

        EXAMPLES: TODO
        """
        period_mapping = self._SS.integral_period_mapping().matrix()
        alpha0 = vector(alpha) * period_mapping * self._SS.module().matrix()
        alpha1 = self._modsym_quotient(alpha0) * self._modsym_matrix.inverse()
        d = self.form().base_ring().degree()
        alpha2 = alpha1[:d]
        alpha3 = alpha1[d:]
        Qan = self._hom_Qan_Kf.domain()
        return map(lambda x: self._hom_Qan_Kf(Qan(x)), [alpha2, alpha3])

    # @cached_method  # Maybe we shouldn't cache everything here, just {oo, 0}.
    def cuspidal_integral(self, cusp, prec=53, r=0):
        """
        Evaluate the integral of self dq/q over path to cusp numerically.

        INPUT:
         - ``cusp`` - Cusp or modular symbol
         - ``prec`` - integer (default: 53) - indicates precision
         - ``r`` - integer (default: 0) - if nonzero change degeneracy of f
        OUTPUT:
         - vector of complex numbers (the integrals for all Kf->CC)

        Compute integral_oo^cusp self dq/q

        EXAMPLES: TODO
        """
        try:
            return self._stored_cuspidal_integrals[tuple([cusp, prec, r])]
        except AttributeError:
            self._stored_cuspidal_integrals = {}
        except KeyError:
            pass

        if r == 0:
            r1 = self.r()
        else:
            r1 = r
        try:
            cusp = Cusp(cusp.numerator() * r1, cusp.denominator())
            alpha = self._SS.ambient()([0, Infinity, cusp])
            cusp_has_right_type = True
        except AttributeError:
            cusp_has_right_type = False
            alpha = self._SS.ambient()(sum(x[0] * x[1].apply([r1,0,0,1]) for
                                       x in list(cusp.modular_symbol_rep())))

        coeffs = self.K_f_coefficients(alpha)
        if prec == 53:
            C = CDF
        else:
            C = ComplexField(prec)
        sigmas = self.form().base_ring().embeddings(C)

        result = sum( vector([ sigma(coeff) * integral
                             for sigma, integral in zip (sigmas, integrals)
                          ])
                    for coeff, integrals in
                    zip(coeffs, self.basis_integrals(prec))
                  ) / r1
        # Not sure what should be cached and what shouldn't:
        if cusp_has_right_type and cusp == 0:
            self._stored_cuspidal_integrals[tuple([0, prec, r])] = result
        return result

    def integrate_by_wN(self, z, r=0):
        """
        Evaluate the integral of f = self from oo to P numerically.

        We use W_N(f) and plug in -1/Nz.

        INPUT:
         - ``z`` - complex number or UpperHalfPlanePoint
         - ``r`` - integer (default: 0) - if nonzero change degeneracy of f

        OUTPUT:
         - vector of complex numbers, one for each K_f -> CC
        """
        if isinstance(z, UpperHalfPlanePoint):
            z = z.to_complex()
        if r == 0:
            r = self.r()
        z = r * z
        N = self.form().level()
        k = self.form().weight()
        z1 = -1 / (N*z)

        winding_integral = self.cuspidal_integral(0, z.prec(), 1)
        intz1 = [x.conjugate() for x in
                 self.integrate_naively(-z1.conjugate(), 1)]
        values = vector(map(operator.mul, self.lambda_N(z.prec()), intz1))
        factor = N ^ ((k - 2) / 2)
        return (factor * values + winding_integral) / r

    def integrate(self, P):
        """
        Evaluate the integral of self from oo to P numerically.

        This probably only works if the weight is 2.

        INPUT:
         - ``P`` - UpperHalfPlanePoint

        OUTPUT:
         - vector of complex numbers - one for each Kf -> CC

        EXAMPLES: TODO
        """
        if self.r() > 1:
            P = (self.r() * P).normalize()
        try:
            (a, b), (c, d) = P.gamma
        except ValueError:
            a, b, c, d = list(P.gamma)
        C = P.z.parent()
        N = self.form().level()
        k = self.form().weight()
        sigmas = self.form().base_ring().embeddings(C)

        if N.divides(c):
            cusp_int = self.cuspidal_integral(Cusp(a, c), C.prec(), 1)
            int1 = self.integrate_naively(P.z, 1)
            result = vector([ sigma(self.epsilon(d)) * integral for
                              sigma, integral in zip(sigmas, int1)
                           ])
            result += cusp_int
        else:
            j = -d * inverse_mod(c, N) % N
            z1 = 1 / (j - P.z)
            if z1.norm() > 1/N:
                intz1 = self.integrate_naively(z1, 1)
            else:
                intz1 = self.integrate_by_wN(z1, 1)
            (a1, b1), (c1, d1) = P.gamma * matrix([[j,-1],[1,0]])
            cusp_int = self.cuspidal_integral(Cusp(a1, c1), C.prec(), 1)
            result = vector([ sigma(self.epsilon(d1)) * x for
                              sigma, x in zip(sigmas, intz1)
                           ])
            result += cusp_int

        return  (c*P.z+d)^(k-2) * result / self.r()


class NumericalModularJacobian(SageObject):
    """
    Create the Jacobian variety J(G) with which we can perform certain
    numerical computations.

    INPUT:
     - ``G`` - CongruenceSubgroup - has to contain some Gamma1(N)
     - ``plus`` - bool (default: false) - divide out w_N or not

    REMARKS:
     - plus is only useful if G is some Gamma0(N)
     - currently it only works if the level is prime

    TODO:
     - implement integral hecke operators for plus space
     - make it work for composite levels

    EXAMPLES: TODO
    """

    def __init__(self, G, plus=False):
        self._group = G
        N = G.level()
        self._plus = plus
        if not N.is_prime():
            raise NotImplementedError, "the level has to be prime"
        if plus == False:
            self._forms_space = CuspForms(G)
            self._forms = map(EvaluableEigenform,
                               self._forms_space.newforms('a'))
            self._modular_symbols = ModularSymbols(G).cuspidal_subspace()
            self._H1_basis = self._modular_symbols.integral_basis()
        else:  # This case is more elaborate
            if G != Gamma0(N):
                raise ValueError, "plus=True requires G to be some Gamma0(N)"
            S = CuspForms(G)
            newforms = [f for f in S.newforms('a') if
                        f.atkin_lehner_eigenvalue() == 1]
            self._forms = map(EvaluableEigenform, newforms)
            # Modular symbols space:
            symbols = ModularSymbols(G).cuspidal_subspace()
            wN = symbols.atkin_lehner_operator(N)
            plus_stuff = []
            for space in symbols.decomposition():
                if wN(space.basis()[0]) == space.basis()[0]:
                    plus_stuff.append(space)
            self._modular_symbols = reduce(operator.add, plus_stuff)
            # Modular forms space:
            q_prec = S.basis()[-1].valuation() + 1
            q_module_large = symbols.q_expansion_module(q_prec)
            q_module_small = self._modular_symbols.q_expansion_module(q_prec)
            forms = []
            for v in q_module_small.basis():
                coords = q_module_large.coordinates(v)
                form = sum([coords[i] * S.basis()[i] for
                            i in range(len(coords))])
                forms.append(form)
            self._forms_space = S.submodule(forms)
            # Homology basis: WARNING the given implementation uses N is prime
            mat = matrix(map(self._modular_symbols.rational_period_mapping(),
                             self._modular_symbols.basis()))
            self._H1_basis = [sum([row[i] * self._modular_symbols.basis()[i]
                                   for i in range(len(row))]) for row in ~mat]

    def group(self):
        """
        Return the congruence group that was used to construct self with.

        OUTPUT:
         - CongruenceSubgroup

        EXAMPLES: TODO
        """
        return self._group

    def forms_space(self):
        """
        Return the space of cusp forms attached to self

        OUTPUT:
         - modular forms space
        """
        return self._forms_space

    def forms(self):
        """
        Return the Atkin-Lehner-Li basis of the cusp forms attached to self.

        OUTPUT:
         - list of EvaluableEigenforms

        EXAMPLES: TODO
        """
        return self._forms

    def modular_symbols(self):
        """
        Return the modular symbols space that forms self's rational homology.

        OUTPUT:
         - modular symbols space

        EXAMPLES: TODO
        """
        return self._modular_symbols

    def H1_basis(self):
        """
        Return the computed basis for self's integral homology.

        OUTPUT:
         - list of modular symbols

        EXAMPLES: TODO
        """
        return self._H1_basis

    def dimension(self):
        """
        Return the dimension of self as a variety.

        EXAMPLES: TODO
        """
        return self.modular_symbols().dimension() // 2

    def level(self):
        """
        Return the level of self.

        EXAMPLES: TODO
        """
        return self.group().level()

    def plus(self):
        """
        Return whether self is of the form J_0^+(N).

        OUTPUT: bool

        EXAMPLES: TODO
        """
        return self._plus

    def _name(self):
        from sage.modular.arithgroup import congroup_gamma0, congroup_gamma1
        if self.plus() == True:
            return "J_0^+(%d)" % self.level()
        elif isinstance(self.group(), congroup_gamma0.Gamma0_class):
            return "J_0(%d)" % self.level()
        elif isinstance(self.group(), congroup_gamma1.Gamma1_class):
            return "J_1(%d)" % self.level()
        else:
            grp = str(self.group()).replace('Congruence Subgroup ', '')
            return "J(%s)" % grp
        
    def _repr_(self):
        """
        EXAMPLES: TODO
        """
        return "Modular Jacobian variety %s of dimension %d" % (self._name(),
                                                            self.dimension())
    
    def _latex_(self):
        return self._name().replace("Gamma", "\\Gamma")

    def period_integral(self, alpha, prec=53):
        """
        Compute the period of a specific modular symbol.

        INPUT:
         - ``alpha`` - modular symbol
         - prec - integer (default: 53) - indicates precision

        OUTPUT:
         - vector - period of the basis of eigenforms along alpha

        EXAMPLES: TODO
        """
        vec = []
        for form in self.forms():
            vec += list(form.cuspidal_integral(alpha, prec))
        return vector(vec)

    def period_lattice(self, prec=53):
        """
        Compute the period lattice of self, wrt the newforms basis.

        INPUT:
         - ``prec`` - integer (default: 53) - indicates precision

        OUTPUT:
         - matrix whose rows span the period lattice

        REMARK:
         - The matrix will be LLL-reduced.

        EXAMPLES: TODO
        """
        if hasattr(self, '_stored_period_lattice'):
            if self._stored_period_lattice[0][0].prec() == prec:
                return self._stored_period_lattice
            elif self._stored_period_lattice[0][0].prec() > prec:
                return adjust_precision(self._stored_period_lattice, prec)
        periods = []
        for alpha in self.H1_basis():
            periods.append(self.period_integral(alpha, prec))
        self._stored_period_lattice = LLL(matrix(periods))
        return self._stored_period_lattice

    def abel_jacobi(self, P):
        """
        Map a point or list of points to C^g/lattice a la Abel-Jacobi.

        The base point of the integration is 0 (which is in X_1(N)(QQ)).

        INPUT:
         - ``P`` - UpperHalfPlanePoint or list of UpperHalfPlanePoints

        OUTPUT:
         - vector over the complex numbers: the (sum of) the integral(s)
           from 0 to P wrt newform basis

        EXAMPLES: TODO
        """
        if isinstance(P, list):
            return sum([self.abel_jacobi(Q) for Q in P])
        result = []
        for form in self.forms():
            result += list( form.integrate(P) -
                            form.cuspidal_integral(0, P.z.prec()) )
        return vector(result)

    def newton_raphson_step(self, P, Q, image_P=None, max_change=1/2,
                            use_lattice=True):
        """
        Perform a Newton-Raphson iteration step for inverting Abel-Jacobi.

        INPUT:
         - ``P`` - list of g UpperHalfPlanePoints where g = self.dimension()
         - ``Q`` - element of CC^g - typically of higher precision than P
         - ``image_P`` - in CC^g (default: None) - equals abel_jacobi(P),
           precision should be that of Q
         - ``max_change`` - number (default: 1/2) - how much P may change
         - ``use_lattice`` - Boolean (default: True) - reduce Q mod periods

        OUTPUT:
         - list of UpperHalfPlanePoints - should map closer to Q than P does.

        REMARKS:
         - P is seen as a point in X_1(N)^g and Q in C^g/lattice.
         - if use_lattice is set to False, Q is in C^g.
         - If one knows where P is mapped to, then this can be given as
           optional parameter.
         - If P does not map close to Q, the adjusted point may map
           farther to Q than P does.

        EXAMPLES: TODO
        """
        C = parent(Q[0])
        P = [UpperHalfPlanePoint(C(pt.z), pt.gamma) for pt in P]
        if image_P is None:
            image_P = vector(map(C, self.abel_jacobi(P)))
        if use_lattice:
            Q -= close_vector(self.period_lattice(C.prec()), Q-image_P, False)
        # print "NR-step: distance = ", (Q - image_P).norm()
        mat = []
        for pt in P:
            _, (c, d) = pt.gamma
            factor = C(2 * pi * I) * (c * pt.z + d) ^ (-2)
            v = [list(f.evaluate(pt)) for f in self.forms()]
            v = vector(reduce(operator.add, v))
            mat.append(factor * v)
        # print "matrix = ", matrix(mat)
        # print "determinant = ", matrix(mat).det()
        h = (Q - image_P) * matrix(mat).inverse()
        if h.norm() > max_change:
            h *= max_change / h.norm()
        return [(P[i] + h[i]).normalize(self.level()) for i in range(len(P))]

    def _store_random_points(self, prec):
        """
        Add some random points of given precision to self for to use in
        self._close_point_generator.
        """
        if not hasattr(self, '_stored_random_points'):
            self._stored_random_points = []
            for _ in range(max(100, 10 * self.dimension())):
                    point = random_upper_half_plane_point(prec)
                    point = point.normalize(self.level())
                    self._stored_random_points.append(
                        (point, self.abel_jacobi(point))
                    )

    def _close_point_generator(self, Q):
        """
        Generator that gives points in X_1(N)^g mapping close to Q.

        INPUT:
         - ``Q`` - element of CC^g, seen as element of CC^g mod period_lattice

        OUTPUT (yielded):
         - pair (P, P') with P a g-tuple of UpperHalfPlanePoints and P' the
           image of P under Abel-Jacobi, supposedly close to Q
        """
        C = parent(Q[0])
        prec = C.prec()
        # TODO: using this sort here is slow, optimize this
        if hasattr(self, '_stored_aj_mappings'):
            def comparison_key(P):
                return norm_modulo_lattice(self.period_lattice(prec),
                                           P[1], False)
            output_list = sorted(self._stored_aj_mappings, key=comparison_key)
            for x in output_list:
                yield adjust_precision(x, prec)
        self._store_random_points(prec)

        while True:
            indices = approximate_sum(
                          self.period_lattice(prec),
                          [x[1] for x in self._stored_random_points],
                          Q, self.dimension()
                      )
            result1 = [self._stored_random_points[index][0]
                       for index in indices]
            result2 = [self._stored_random_points[index][1]
                       for index in indices]
            yield (result1, sum(result2))

    def abel_jacobi_inverse(self, Q, previous_result=None):
        """
        Compute the inverse of a point along the Abel-Jacobi map.

        INPUT:
         - ``Q`` - g-dimensional vector over CC where g = self.dimension()
         - ``previous_result`` - None or g-tuple of UpperHalfPlanePoints -
           (default: None) - output of this function to same Q with less
           precision

        OUTPUT:
         - list - g-tuple of UpperHalfPlanePoints, mapping to Q modulo the
           period lattice
        """
        # print "Entering AJ-inverse"  # Check where stuff slows down
        Q_precision = Q[0].prec()

        if previous_result is None:
            precision_aim = STARTING_PRECISION
            Q1 = adjust_precision(Q, precision_aim)
            close_points = self._close_point_generator(Q1)
            steps = MAX_STEPS
        else:
            previous_prec = previous_result[0].prec()
            precision_aim = max(2 * (previous_prec - PRECISION_LOSS),
                                2 * STARTING_PRECISION)
            precision_aim = min(precision_aim, Q_precision)
            P1 = adjust_precision(previous_result, precision_aim)
            close_points = [(P1, self.abel_jacobi(P1))]
            steps = MAX_STEPS_ON_HIGH_PRECISION

        # print "AJ-inverse: entering outer loop"
        while True:
            Q_aim = adjust_precision(Q, precision_aim)
            L = self.period_lattice(precision_aim)
            test_factor = 1 << (precision_aim - PRECISION_LOSS)
            try:
                # print "AJ-inverse: entering inner loop"
                for P1, Q1 in close_points:
                    Q_aim += close_vector(L, Q1 - Q_aim, False)
                    step = 0
                    old_distance = None
                    # print "AJ_inverse: entering inner inner loop"
                    while step < steps:
                        step += 1
                        # print "P1 = ", P1
                        # print "Q1 =", Q1
                        # print "Q_aim =", Q_aim
                        P1 = self.newton_raphson_step(P1, Q_aim, Q1,
                                                      use_lattice=False)
                        Q1 = self.abel_jacobi(P1)
                        Q_aim += close_vector(L, Q1 - Q_aim, False)
                        distance = (Q1 - Q_aim).norm()
                        # print "AJ-inverse: distance =", adjust_precision(distance, 30)
                        if distance * test_factor < 1:
                            raise StopIteration()
                        if old_distance and distance > old_distance:
                            step += steps // 10
                        old_distance = distance
                # This code should not be reached:
                raise ValueError("approximation of Abel-Jacobi inverse fails")
            except StopIteration:
                pass

            if precision_aim == Q_precision:  # Goal reached, iteration stops.
                if not hasattr(self, '_stored_aj_mappings'):
                    self._stored_aj_mappings = []
                if previous_result is None:
                    self._stored_aj_mappings.append((P1, Q1))
                return P1

            # print "Doubling precision now."
            precision_aim = max(2 * (precision_aim - PRECISION_LOSS),
                                2 * STARTING_PRECISION)
            precision_aim = min(precision_aim, Q_precision)
            # print "P1 = ", P1
            # print "precision_aim = ", precision_aim
            P1 = adjust_precision(P1, precision_aim)
            close_points = [(P1, self.abel_jacobi(P1))]
            steps = MAX_STEPS_ON_HIGH_PRECISION

    def integral_hecke_matrix(self, n):
        """
        Determine the n-th Hecke operator as matrix relative to self.H1_basis()

        INPUT:
         - ``n`` - Integer

        OUTPUT:
         - square matrix over ZZ

        EXAMPLES: TODO
        """
        S = self.modular_symbols()
        if self.plus() == False:
            return S.integral_hecke_matrix(n)
        hecke_matrix = S.hecke_matrix(n)
        basis_matrix = matrix([S.coordinate_vector(x) for
                               x in self.H1_basis()])
        result = basis_matrix * hecke_matrix * ~basis_matrix
        return MatrixSpace(ZZ, 2 * self.dimension())(result)

    @cached_method
    @execute_in_child_process
    def hecke_algebra_generators(self):
        """
        Compute Z-module generators for the Hecke algebra acting on self.

        OUTPUT:
         - list of Hecke operators, as pairs (index, matrix) where
           matrix is relative to self.H1_basis()

        EXAMPLES: TODO
        """
        S = self.forms_space()
        if S.integral_basis() == S.echelon_basis():
            indices = [f.valuation() for f in S.echelon_basis()]
            return [(n, self.integral_hecke_matrix(n))
                     for n in indices]

        # TODO: the following is very inefficient, it needs to be improved.
        bound = S.sturm_bound()
        result = []
        matrix_space = self.integral_hecke_matrix(1).parent()
        V = FreeModule(ZZ, matrix_space.dimension())
        f = lambda m: V(reduce(operator.add, map(list, list(m))))
        subspace = V.submodule([])
        gens = []
        for n in range(1, bound+1):
            print "Building up Hecke algebra at %d of %d." % (n, bound)
            hecke_matrix = self.integral_hecke_matrix(n)
            if f(hecke_matrix) not in subspace:
                result.append((n, hecke_matrix))
                subspace += V.submodule([f(hecke_matrix)])
                gens.append(f(hecke_matrix))
        for hecke in reversed(result):
            print "Breaking down Hecke algebra at %d." % hecke[0]
            gens1 = copy(gens)
            gens1.remove(f(hecke[1]))
            if f(hecke[1]) in V.submodule(gens1):
                result.remove(hecke)
                gens = gens1
        return result


class ModularGaloisRepresentation(SageObject):
    """
    Compute polynomials associated to a modular Galois representation.

    INPUT:
     - ``f`` - a modular form.
     - ``LL`` - a prime ideal of f's coefficient field

    REMARKS:
     - When the coefficient field is QQ, LL is allowed to be an integer.
     - Currently, f has to have prime level and weight 2 or level one
       and arbitrary weight.

    TODO:
     - Write some functions that store and restore computations in a way
       that allows the implementation of the class to be changed.
     - Store approximations to torsion points as dictionaries, as soon as
       pickling bugs have been removed.

    EXAMPLES: TODO
    """

    def __init__(self, f, LL):
        """
        Initialise basic object for computation with Galois representations.

        TODO: make it work for arbitrary f
        TODO: move some stuff from the implementation to separate methods
        """
        self._f = f
        self._LL = LL
        N = f.level()
        k = f.weight()
        Kf = f.base_ring()
        OKf = Kf.maximal_order()
        self._residue_field = OKf.residue_field(LL)
        L = self.residue_field().characteristic()
        self._L = L
        if k == 2:
            N1 = N
        else:
            N1 = N * L
            
        self._max_cpus = MAX_CPUS

        # Let us determine if Gamma0(N1) suffices
        charvals_f = character_values(f)
        for n in range(N):
            if charvals_f[n] == 0:
                charvals_f[n] = 1
        OKfmodL = OKf.quotient(L, 'a')
        charvals = [OKfmodL(n)^(k-2 + L-1) * OKfmodL(charvals_f[n%N]) for
                    n in srange(N1)]  # L-1 is there to avoid 0^0
        if all(x in [0, 1] for x in charvals):
            G = Gamma0(N1)
            if L == 2:
                plus = True
            elif k == 2:
                plus = (f.atkin_lehner_eigenvalue() == 1)
            else:
                plus = False
        else:
            G = Gamma1(N1)
            plus = False
        # TODO: We could also take a group between Gamma0 and Gamma1

        self._jacobian = NumericalModularJacobian(G, plus)
        hecke_generators = self.jacobian().hecke_algebra_generators()
        # print "Hecke generators:\n", hecke_generators
        hecke_ngens = len(hecke_generators)

        # Compute the Hecke map associated to (f, LL)
        q_prec = hecke_generators[-1][0] + 1
        qexp = f.q_expansion(q_prec).padded_list(q_prec)
        coefficients = [qexp[hecke[0]] for hecke in hecke_generators]
        hecke_images = map(self.residue_field(), coefficients)

        # Compute the representation space in terms of modular symbols,
        # i.e. using the identification of modsym (x) F_L with J[L]
        domain = FreeModule(GF(L), hecke_ngens)
        codomain = FreeModule(GF(L), self.residue_field().degree())
        try:
            homomorphism = domain.hom(map(vector, hecke_images), codomain)
        except TypeError:
            homomorphism = domain.hom(hecke_images, codomain)
        hecke_ideal_matrices = [ sum([v[n]*hecke_generators[n][1]
                                      for n in range(hecke_ngens)])
                                 for v in homomorphism.kernel().basis()
                               ]
        ambient_space = (GF(L)(0)*hecke_generators[0][1]).kernel()
        self._hecke_space = reduce(lambda x, y: x.intersection(y),
                                   map(kernel, hecke_ideal_matrices),
                                   ambient_space)

        # The following is incorrect if O_f is not O_K_f. TODO: repair this!
        dim = self.hecke_space().dimension()
        if dim != 2*self.residue_field().degree():
            raise ValueError, \
              "representation space has dimension %d instead of %d" % \
               (dim, 2*self.residue_field().degree())

        # Compute a complete set of hecke operators acting on the repr. space
        residue_space = codomain.submodule([])
        hecke_residue_gens = []
        for n in range(len(hecke_generators)):
            try:
                residue_element = vector(hecke_images[n])
            except TypeError:
                residue_element = vector([hecke_images[n]])
            if residue_element not in residue_space:
                hecke_residue_gens.append(
                                     hecke_generators[n][1].base_extend(GF(L)))
                residue_space += codomain.submodule([residue_element])
        m = len(hecke_residue_gens)
        self._residue_hecke_operators = []
        for vec in FreeModule(GF(L), m):
            new_element = sum([vec[n]*hecke_residue_gens[n] for n in range(m)])
            self._residue_hecke_operators.append(new_element)
        self._residue_hecke_operators.remove(0)

    def _repr_(self):
        return "Galois representation associated to %s modulo %s" % (self._f,
                                                                     self._LL)
    
    def _latex_(self):
        return "\\rho_{f, \\lambda} \quad\\text{for}\\quad f = %s \\quad"\
               "\\text{and}\\quad\\lambda = %s" % (latex(self._f), latex(self._LL))

    def max_cpus(self):
        """
        Return the maximum number of cpu's we may use in parallel.
        """
        return self._max_cpus

    def set_max_cpus(self, n):
        """
        Set the maximum number of cpu's we may use in parallel.
        """
        self._max_cpus = n
        
    def ncpus(self):
        """
        Return the number of cpu's used in parallel computations.
        """
        return min(self.max_cpus(), sage.parallel.ncpus.ncpus())

    def form(self):
        """
        Return the modular form to which self is a Galois representation.

        OUTPUT:
         - modular form

        EXAMPLES: TODO
        """
        return self._f

    def prime(self):
        """
        Return the prime (number or ideal) modulo which self is a Galois
        representation.

        OUTPUT:
         - integer or prime ideal of number field

        EXAMPLES: TODO
        """
        return self._LL

    def jacobian(self):
        """
        Return the Jacobian variety in which the representation exists.

        OUTPUT:
         - NumericalModularJacobian

        EXAMPLES: TODO
        """
        return self._jacobian

    def hecke_space(self):
        """
        Return the torsion subspace of J = self.jacobian() that defines
        the representation.

        If S is the modular symbols space associated to J, then we can
        identify J[L] with S \otimes F_L.  This function returns the
        representation subspace of J[L] with respect to J.H1_basis().

        OUTPUT:
         - Vector space over a finite prime field.

        EXAMPLES: TODO
        """
        return self._hecke_space

    def residue_field(self):
        """
        Return the field K such that self is a representation to GL_2(K).

        OUTPUT:
         - Finite field that is a residue field of a number field at a prime.

        REMARK:
         - The field may not be minimal.  TODO: repair this.

        EXAMPLES: TODO
        """
        return self._residue_field

    def L(self):
        """
        Return the prime number L lying over the prime ideal attached to self.

        OUTPUT:
         - Integer

        EXAMPLES: TODO
        """
        return self._L

    def torsion_symbols(self):
        """
        Output the set of torsion points that we use to compute the Galois
        representation.

        OUTPUT:
         - list of lists: [[modular symbols], ..., [modular symbols]]

        Each member of the output represents a line.  A modular symbol x
        represents the point (x/L) modulo the period lattice of
        self.jacobian(), where L is the residue characteristic.

        EXAMPLES: TODO
        """
        try:
            return self._stored_torsion_symbols
        except AttributeError:
            pass
        # print "Computing torsion symbols"
        all_points = self.hecke_space().list()[1:]
        result = []
        J = self.jacobian()
        while all_points != []:
            point = all_points[0]
            line = [point * op for op in self._residue_hecke_operators]
            line_symbols = []
            for pt in line:
                all_points.remove(pt)
                vec = lift(pt)
                pt_symbol = sum([vec[n] * J.H1_basis()[n] for
                                 n in range(len(vec))])
                line_symbols.append(pt_symbol)
            result.append(line_symbols)
        self._stored_torsion_symbols = result
        return result

    def approximate_torsion(self, prec=None):
        """
        Approximate the torsion points that define the representation.

        INPUT:
         - ``prec`` - Integer (default: None -> set to STARTING_PRECISION)

        OUTPUT:
         - list of lists of tuples of UpperHalfPlanePoints

        REMARKS:
         - The list structure coincides with the one from self.torsion_symbols()
         - The tuples of UpperHalfPlanePoints correspond to points of X^g
           mapping numerically to the torsion points in CC^g/periods on which
           the representation is defined.

        EXAMPLES: TODO
        """
        if prec is None:
            prec = STARTING_PRECISION
        L = self.L()
        J = self.jacobian()

        if hasattr(self, '_stored_approximated_torsion') and \
           self._stored_approximated_torsion[-1][-1][-1].prec() >= prec:
            return self._stored_approximated_torsion
        print "Computing lattice points"
        aimed_points = [[(1/L) * J.period_integral(alpha, prec) for
                 alpha in line] for line in self.torsion_symbols()]
        if not hasattr(self,'_stored_approximated_torsion'):
            self._stored_approximated_torsion = \
                  [[None for point in line] for line in aimed_points]
            J._store_random_points(prec)
        num_points = len(aimed_points) * len(aimed_points[0])
        points_per_line = len(aimed_points[0])
        # The following reduces memory usage a lot:
        if prec <= 200:
            aj_inverse = execute_in_child_process(J.abel_jacobi_inverse)
            use_subprocessing = True
        else:
            use_subprocessing = False
        
        X = sage.parallel.use_fork.p_iter_fork(self.ncpus(), verbose=True)
        for n in range(len(aimed_points)):
            def function_to_iterate(m):
                # WEIRD?!?: the following is printed to the screen twice
                # This is a bug in Sage: stdout is propagated without being flushed.
                point_number = n * points_per_line + m + 1
                # print "Now doing point %s of %s" % (point_number, num_points)
                # sys.stdout.flush()
                # TODO: Check if the point is the complex conjugate
                # of an already computed point.
                previous_result = self._stored_approximated_torsion[n][m]
                point = aimed_points[n][m]
                # print "This is a test"
                if use_subprocessing:
                    result = aj_inverse(point, previous_result)
                else:
                    result = J.abel_jacobi_inverse(point, previous_result)
                print "Point %s of %s computed" % (point_number, num_points)
                return (result, previous_result, point)
            
            inputs = [((m,),{}) for m in xrange(len(aimed_points[n]))]
            iter_result = X(function_to_iterate, inputs)
            for stuff in iter_result:
                m = stuff[0][0][0]
                result, previous_result, point = stuff[1]
                self._stored_approximated_torsion[n][m] = result
                if previous_result is None:
                    if not hasattr(J, '_stored_aj_mappings'):
                        J._stored_aj_mappings = []
                    # We store the point for the close point generator in J.
                    # However, it is not important to be accurate here already.
                    J._stored_aj_mappings.append((result, point))
                    nof_mappings = len(J._stored_aj_mappings)
                    if nof_mappings > 50:
                        J._stored_aj_mappings = \
                        random_sublist(J._stored_aj_mappings, 50/nof_mappings)

        return self._stored_approximated_torsion

    def _evaluate_cusp_forms_at_torsion(self):
        """
        Evaluate all the cusp forms in the basis of S_2 corresponding to
        self.jacobian() at the torsion points in
        self._stored_approximated_torsion.

        OUTPUT:
         - list of lists of tuples of vectors over CC.
           Nested list structure is as in self.torsion_symbols().
           Third nesting is over components of the point.

        REMARK:
         - We adjust things by W_N

        TODO:
         - Change implementation so that it works for all weights.
        """
        N = self.jacobian().level()
        WN_tor = [[[UpperHalfPlanePoint(-1/((N*pt).to_complex())).normalize(N)
                        for pt in point] for point in line] for
                       line in self._stored_approximated_torsion]

        fn = lambda pt: vector(reduce(operator.add, [list(f.evaluate(pt)) for
                                f in self.jacobian().forms()]))
        
        fn2 = lambda line: [tuple(map(fn, point)) for point in line]
        X = sage.parallel.use_fork.p_iter_fork(self.ncpus(), verbose=True)
        result = [x[1] for x in X(fn2, [((line,),{}) for line in WN_tor])]
        return result

    def _evaluate_good_function_at_torsion(self):
        """
        Evaluate a function of small degree at the torsion points in
        self._approximated_torsion.

        OUTPUT:
         - list of lists complex numbers.
           Nested list structure is as in self.torsion_symbols().

        REMARK:
         - The good function here is a naive one: use the quotient of the
           last two forms in the integral basis of S_2, adjusted with W_N.

        TODO:
         - This function is too long, divide it up in several functions.
        """
        evaluations = self._evaluate_cusp_forms_at_torsion()
        C = parent(evaluations[0][0][0][0])
        # print C

        basis = self.jacobian().forms_space().integral_basis()
        h = 1 + basis[-1].valuation()
        trace_matrix = []
        forms = [F.form() for F in self.jacobian().forms()]
        for f in forms:
            Kf = f.base_ring()
            generators = Kf.gens()
            assert len(generators) == 1
            a = generators[0]
            for n in srange(Kf.degree()):
                g = a^n * f.q_expansion(h)
                listg = list(g)[1:]
                listg += [Kf(0)] * (h - 1 - len(listg))
                trace_matrix.append([x.trace() for x in listg])

        trace_matrix = matrix(trace_matrix)
        v_num = list(basis[-2].q_expansion(h))[1:]
        v_den = list(basis[-1].q_expansion(h))[1:]
        v_num += [0] * (len(v_den) - len(v_num))

        # REMARK: in the following two lines, [0] is added because of a bug
        #         in solve_left: it returns a matrix instead of a vector.
        #         When this bug has been resolved, remove the [0]'s.
        a_num = trace_matrix.solve_left(vector(v_num))
        a_den = trace_matrix.solve_left(vector(v_den))

        K_f = [f.base_ring() for f in forms]
        K_f_num = [0] * len(forms)
        K_f_den = [0] * len(forms)
        j = 0
        for i in range(len(forms)):
            K_f_num[i] = K_f[i](0)
            K_f_den[i] = K_f[i](0)
            b = K_f[i](1)
            for _ in range(K_f[i].degree()):
                K_f_num[i] += b * a_num[j]
                K_f_den[i] += b * a_den[j]
                j += 1
                b *= K_f[i].gens()[0]
        C_num = []
        C_den = []
        for i in range(len(forms)):
            sigmas = K_f[i].embeddings(C)
            for sigma in sigmas:
                C_num.append(sigma(K_f_num[i]))
                C_den.append(sigma(K_f_den[i]))

        result = []
        for line in evaluations:
            line_result = []
            for point in line:
                point_sum = 0
                for pt in point:
                    num_ev = sum([C_num[i] * pt[i] for i in range(len(pt))])
                    den_ev = sum([C_den[i] * pt[i] for i in range(len(pt))])
                    point_sum += num_ev / den_ev
                line_result.append(point_sum)
            result.append(line_result)
        return result

    def compute_real_projective_polynomial(self, prec=None,
                                           save_results=None):
        """
        Compute real approximation of a polynomial attached to the
        projectivised representation of self.

        INPUT:
         - ``prec`` - Integer (default: None -> set to STARTING_PRECISION)
         - ``save_results`` - string or None (default: None) - see remarks

        OUTPUT:
         - polynomial over RR with real precision prec

        REMARKS:
         - If save_results is not None, then we save intermediate results
           to a file whose name starts with save_results.  This might be
           useful in case the machine crashes during an extensive
           computation.  In choosing a name, be aware of the fact that files
           will be overwritten.

        TODO:
         - Cache the polynomial.

        EXAMPLES: TODO
        """
        if prec is None:
            prec = STARTING_PRECISION
        self.approximate_torsion(prec)
        if save_results is not None:
            filename = save_results + ".complex." + str(prec)
            Sequence(self._stored_approximated_torsion).save(filename)
        evaluations = self._evaluate_good_function_at_torsion()
        # print evaluations
        if prec == 53:
            C = CDF
            R = RDF
        else:
            C = ComplexField(prec)
            R = RealField(prec)
        PC.<X> = C[]
        result = prod([X - sum(line) for line in evaluations])
        result = R['X']([x.real() for x in list(result)])
        if save_results is not None:
            filename = save_results + ".real_polynomial." + str(prec)
            result.save(filename)
        return result


    def compute_rational_projective_polynomial(self, save_results=None):
        """
        Compute a polynomial attached to the projectivised representation.

        INPUT:
         - ``save_results`` - string or None (default: None) - see remarks

        OUTPUT:
         - polynomial over ZZ (in general not monic).

        REMARKS:
         - If save_results is not None, then we save intermediate results
           to a file whose name starts with save_results.  This might be
           useful in case the machine crashes during an extensive
           computation.  In choosing a name, be aware of the fact that files
           will be overwritten.

        EXAMPLES: TODO
        """
        try:
            return self._stored_rational_projective_polynomial
        except AttributeError:
            pass

        if hasattr(self, '_real_projective_polynomial'):
            current_prec = self._real_projective_polynomial.base_ring().prec()
            current_prec = max(150, 2 * (current_prec - PRECISION_LOSS))
        else:
            current_prec = STARTING_PRECISION
        while True:
            print "Computing precision is now set to %s bits" % current_prec
            pol = self.compute_real_projective_polynomial(current_prec,
                                                          save_results)
            self._real_projective_polynomial = pol
            # if save_results is not None:
            #     filename = save_results + ".complex." + str(current_prec)
                # Think a bit better about what to save here.
            #     Sequence(self._stored_approximated_torsion).save(filename)
            print "Real polynomial computed with precision %s" % current_prec 
            print "Seeking common denominator"
            if current_prec < 150:
                print "No common denominator found"
            else:
                q = common_denominator(list(pol)[:-1], ncpus=self.ncpus())
                if q:
                    print "Ok\xc3\xa4se!"
                    poly = ZZ['x']([(coeff*q).round() for coeff in list(pol)])
                    self._stored_rational_projective_polynomial = poly
                    return poly
                else:
                    print "No good common denominator found"
            current_prec = max(150, 2 * (current_prec - PRECISION_LOSS))

    def restore_from_file(self, filename):
        """
        Restore an interrupted computation from a file.

        INPUT:
         - ``filename`` - string

        REMARKS:
         - Currently, we just restore torsion approximations and then compute
           a polynomial over the reals.  We can't do much more because of
           pickling bugs.

        EXAMPLES: TODO
        """

        self._stored_approximated_torsion = load(filename)
        prec = self._stored_approximated_torsion[-1][-1][-1].prec()
        try:
            pol_file = filename.replace("complex", "real_polynomial")
            self._real_projective_polynomial = load(pol_file)
        except IOError:
            print "Computing real polynomial with precision", prec
            self._real_projective_polynomial = \
                            self.compute_real_projective_polynomial(prec)

    def smaller_polynomial(self):
        """
        Compute a polynomial in ZZ[x] for the projective representation,
        but with smaller coefficients.

        OUTPUT:
         - polynomial in ZZ[x]

        REMARKS:
         - Uses PARI's polredabs
         - If no polynomial is known yet, we compute it first
         - Be aware of the fact that Ctrl-C might not work here, as we use PARI
         - Doesn't work if the height of the polynomial is too big; in that
           case it's better to do things by hand.

        EXAMPLES: TODO
        """
        pol = self.compute_rational_projective_polynomial()
        # print "Making polynomial smaller"
        # The 16 means: make use of the fact that the number field has no
        # large ramified primes.  However, it still seems to be important
        # for polredabs that it know a lot of small primes.
        pari.init_primes(10000000)
        poly = pari(pol).polredabs(16)
        self._stored_rational_projective_polynomial = ZZ['x'](poly)
        return self._stored_rational_projective_polynomial