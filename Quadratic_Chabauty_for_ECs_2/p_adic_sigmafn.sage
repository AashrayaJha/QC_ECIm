def padic_sigma_imquad(E, p, N=20, E2=None, check=False, check_hypotheses=True):
    r"""
    Computes the p-adic sigma function with respect to the standard
    invariant differential `dx/(2y + a_1 x + a_3)`, as
    defined by Mazur and Tate, as a power series in the usual
    uniformiser `t` at the origin.

    The equation of the curve must be minimal at `p`.

    INPUT:

    - ``E``- an elliptic curve defined over an imaginary quadratic field K.
   
    -  ``p`` - prime >= 5 such that for all primes above p
         the curve has good reduction.


    -  ``N`` - integer >= 1 (default 20), indicates precision of result;
       see OUTPUT section for description

    -  ``E2`` - precomputed value of E2. If not supplied,
       this function will call padic_E2 to compute it. The value supplied
       must be correct mod `p^{N-2}`.

    -  ``check`` - boolean, whether to perform a
       consistency check (i.e. verify that the computed sigma satisfies
       the defining

    -  ``differential equation`` - note that this does NOT
       guarantee correctness of all the returned digits, but it comes
       pretty close :-))

    -  ``check_hypotheses`` - boolean, whether to check
       that this is a curve for which the p-adic sigma function makes
       sense


    OUTPUT: A power series `t + \cdots` with coefficients in
    `\ZZ_p`.

    The output series will be truncated at `O(t^{N+1})`, and
    the coefficient of `t^n` for `n \geq 1` will be
    correct to precision `O(p^{N-n+1})`.

    In practice this means the following. If `t_0 = p^k u`,
    where `u` is a `p`-adic unit with at least
    `N` digits of precision, and `k \geq 1`, then the
    returned series may be used to compute `\sigma(t_0)`
    correctly modulo `p^{N+k}` (i.e. with `N` correct
    `p`-adic digits).

    ALGORITHM: Described in "Efficient Computation of p-adic Heights"
    (David Harvey), which is basically an optimised version of the
    algorithm from "p-adic Heights and Log Convergence" (Mazur, Stein,
    Tate).

    Running time is soft-`O(N^2 \log p)`, plus whatever time is
    necessary to compute `E_2`.

    AUTHORS:

    - David Harvey (2006-09-12)

    - David Harvey (2007-02): rewrote

    EXAMPLES::

        sage: EllipticCurve([-1, 1/4]).padic_sigma(5, 10)
        O(5^11) + (1 + O(5^10))*t + O(5^9)*t^2 + (3 + 2*5^2 + 3*5^3 + 3*5^6 + 4*5^7 + O(5^8))*t^3 + O(5^7)*t^4 + (2 + 4*5^2 + 4*5^3 + 5^4 + 5^5 +               O(5^6))*t^5 + O(5^5)*t^6 + (2 + 2*5 + 5^2 + 4*5^3 + O(5^4))*t^7 + O(5^3)*t^8 + (1 + 2*5 + O(5^2))*t^9 + O(5)*t^10 + O(t^11)

    Run it with a consistency check::

        sage: EllipticCurve("37a").padic_sigma(5, 10, check=True)
        O(5^11) + (1 + O(5^10))*t + O(5^9)*t^2 + (3 + 2*5^2 + 3*5^3 + 3*5^6 + 4*5^7 + O(5^8))*t^3 + (3 + 2*5 + 2*5^2 + 2*5^3 + 2*5^4 + 2*5^5 + 2*5^6 +         O(5^7))*t^4 + (2 + 4*5^2 + 4*5^3 + 5^4 + 5^5 + O(5^6))*t^5 + (2 + 3*5 + 5^4 + O(5^5))*t^6 + (4 + 3*5 + 2*5^2 + O(5^4))*t^7 + (2 + 3*5 + 2*5^2 +         O(5^3))*t^8 + (4*5 + O(5^2))*t^9 + (1 + O(5))*t^10 + O(t^11)

    Boundary cases::

        sage: EllipticCurve([1, 1, 1, 1, 1]).padic_sigma(5, 1)
         (1 + O(5))*t + O(t^2)
        sage: EllipticCurve([1, 1, 1, 1, 1]).padic_sigma(5, 2)
         (1 + O(5^2))*t + (3 + O(5))*t^2 + O(t^3)

    Supply your very own value of E2::

        sage: X = EllipticCurve("37a")
        sage: my_E2 = X.padic_E2(5, 8)
        sage: my_E2 = my_E2 + 5**5    # oops!!!
        sage: X.padic_sigma(5, 10, E2=my_E2)
        O(5^11) + (1 + O(5^10))*t + O(5^9)*t^2 + (3 + 2*5^2 + 3*5^3 + 4*5^5 + 2*5^6 + 3*5^7 + O(5^8))*t^3 + (3 + 2*5 + 2*5^2 + 2*5^3 + 2*5^4 + 2*5^5 +         2*5^6 + O(5^7))*t^4 + (2 + 4*5^2 + 4*5^3 + 5^4 + 3*5^5 + O(5^6))*t^5 + (2 + 3*5 + 5^4 + O(5^5))*t^6 + (4 + 3*5 + 2*5^2 + O(5^4))*t^7 + (2 + 3*5         + 2*5^2 + O(5^3))*t^8 + (4*5 + O(5^2))*t^9 + (1 + O(5))*t^10 + O(t^11)

    Check that sigma is "weight 1".

    ::

        sage: f = EllipticCurve([-1, 3]).padic_sigma(5, 10)
        sage: g = EllipticCurve([-1*(2**4), 3*(2**6)]).padic_sigma(5, 10)
        sage: t = f.parent().gen()
        sage: f(2*t)/2
        (1 + O(5^10))*t + (4 + 3*5 + 3*5^2 + 3*5^3 + 4*5^4 + 4*5^5 + 3*5^6 + 5^7 + O(5^8))*t^3 + (3 + 3*5^2 + 5^4 + 2*5^5 + O(5^6))*t^5 + (4 + 5 +             3*5^3 + O(5^4))*t^7 + (4 + 2*5 + O(5^2))*t^9 + O(5)*t^10 + O(t^11)
        sage: g
        O(5^11) + (1 + O(5^10))*t + O(5^9)*t^2 + (4 + 3*5 + 3*5^2 + 3*5^3 + 4*5^4 + 4*5^5 + 3*5^6 + 5^7 + O(5^8))*t^3 + O(5^7)*t^4 + (3 + 3*5^2 + 5^4 +         2*5^5 + O(5^6))*t^5 + O(5^5)*t^6 + (4 + 5 + 3*5^3 + O(5^4))*t^7 + O(5^3)*t^8 + (4 + 2*5 + O(5^2))*t^9 + O(5)*t^10 + O(t^11)
        sage: f(2*t)/2 -g
        O(t^11)

    Test that it returns consistent results over a range of precision::

        sage: max_N = 30   # get up to at least p^2         # long time
        sage: E = EllipticCurve([1, 1, 1, 1, 1])            # long time
        sage: p = 5                                         # long time
        sage: E2 = E.padic_E2(5, max_N)                     # long time
        sage: max_sigma = E.padic_sigma(p, max_N, E2=E2)    # long time
        sage: for N in range(3, max_N):                     # long time
        ....:    sigma = E.padic_sigma(p, N, E2=E2)         # long time
        ....:    assert sigma == max_sigma
        """

    #if check_hypotheses:
    #    p = __check_padic_hypotheses(self, p)

    # todo: implement the p == 3 case
    # NOTE: If we ever implement p == 3, it's necessary to check over
    # the precision loss estimates (below) very carefully; I think it
    # may become necessary to compute E2 to an even higher precision.

    if p<5:
        raise NotImplementedError("p (=%s) must be at least 5" % p)

    N = int(N)
    K=E.base_field()
    OK=K.maximal_order()

    p1,p2=factor(p*OK)
    p1=(p1[0])
    p2=(p2[0])
    
    
    sigma1=p1adic_sigma_imquad(E, p1, N=20, E2=None, check=False, check_hypotheses=True)
    sigma2=p1adic_sigma_imquad(E, p2, N=20, E2=None, check=False, check_hypotheses=True)
    
    return sigma1,sigma2

def p1adic_sigma_imquad(E, p1, N=20, E2=None, check=False, check_hypotheses=True):
    r"""
    Computes the p-adic sigma function with respect to the standard
    invariant differential `dx/(2y + a_1 x + a_3)`, as
    defined by Mazur and Tate, as a power series in the usual
    uniformiser `t` at the origin.

    The equation of the curve must be minimal at `p1`.

    INPUT:

    - ``E``- an elliptic curve defined over an imaginary quadratic field K.
   
    -  ``p1`` - prime with norm(p1)>= 5 such that the curve has good reduction
        at p1.


    -  ``N`` - integer >= 1 (default 20), indicates precision of result;
       see OUTPUT section for description

    -  ``E2`` - precomputed value of E2. If not supplied,
       this function will call padic_E2 to compute it. The value supplied
       must be correct mod `p^{N-2}`.

    -  ``check`` - boolean, whether to perform a
       consistency check (i.e. verify that the computed sigma satisfies
       the defining

    -  ``differential equation`` - note that this does NOT
       guarantee correctness of all the returned digits, but it comes
       pretty close :-))

    -  ``check_hypotheses`` - boolean, whether to check
       that this is a curve for which the p-adic sigma function makes
       sense


    OUTPUT: A power series `t + \cdots` with coefficients in
    `\ZZ_p`.

    The output series will be truncated at `O(t^{N+1})`, and
    the coefficient of `t^n` for `n \geq 1` will be
    correct to precision `O(p^{N-n+1})`.

    In practice this means the following. If `t_0 = p^k u`,
    where `u` is a `p`-adic unit with at least
    `N` digits of precision, and `k \geq 1`, then the
    returned series may be used to compute `\sigma(t_0)`
    correctly modulo `p^{N+k}` (i.e. with `N` correct
    `p`-adic digits).

    ALGORITHM: Described in "Efficient Computation of p-adic Heights"
    (David Harvey), which is basically an optimised version of the
    algorithm from "p-adic Heights and Log Convergence" (Mazur, Stein,
    Tate).

    Running time is soft-`O(N^2 \log p)`, plus whatever time is
    necessary to compute `E_2`.

    AUTHORS:

    - David Harvey (2006-09-12)

    - David Harvey (2007-02): rewrote

    EXAMPLES::

        sage: EllipticCurve([-1, 1/4]).padic_sigma(5, 10)
        O(5^11) + (1 + O(5^10))*t + O(5^9)*t^2 + (3 + 2*5^2 + 3*5^3 + 3*5^6 + 4*5^7 + O(5^8))*t^3 + O(5^7)*t^4 + (2 + 4*5^2 + 4*5^3 + 5^4 + 5^5 +               O(5^6))*t^5 + O(5^5)*t^6 + (2 + 2*5 + 5^2 + 4*5^3 + O(5^4))*t^7 + O(5^3)*t^8 + (1 + 2*5 + O(5^2))*t^9 + O(5)*t^10 + O(t^11)

    Run it with a consistency check::

        sage: EllipticCurve("37a").padic_sigma(5, 10, check=True)
        O(5^11) + (1 + O(5^10))*t + O(5^9)*t^2 + (3 + 2*5^2 + 3*5^3 + 3*5^6 + 4*5^7 + O(5^8))*t^3 + (3 + 2*5 + 2*5^2 + 2*5^3 + 2*5^4 + 2*5^5 + 2*5^6 +         O(5^7))*t^4 + (2 + 4*5^2 + 4*5^3 + 5^4 + 5^5 + O(5^6))*t^5 + (2 + 3*5 + 5^4 + O(5^5))*t^6 + (4 + 3*5 + 2*5^2 + O(5^4))*t^7 + (2 + 3*5 + 2*5^2 +         O(5^3))*t^8 + (4*5 + O(5^2))*t^9 + (1 + O(5))*t^10 + O(t^11)

    Boundary cases::

        sage: EllipticCurve([1, 1, 1, 1, 1]).padic_sigma(5, 1)
         (1 + O(5))*t + O(t^2)
        sage: EllipticCurve([1, 1, 1, 1, 1]).padic_sigma(5, 2)
         (1 + O(5^2))*t + (3 + O(5))*t^2 + O(t^3)

    Supply your very own value of E2::

        sage: X = EllipticCurve("37a")
        sage: my_E2 = X.padic_E2(5, 8)
        sage: my_E2 = my_E2 + 5**5    # oops!!!
        sage: X.padic_sigma(5, 10, E2=my_E2)
        O(5^11) + (1 + O(5^10))*t + O(5^9)*t^2 + (3 + 2*5^2 + 3*5^3 + 4*5^5 + 2*5^6 + 3*5^7 + O(5^8))*t^3 + (3 + 2*5 + 2*5^2 + 2*5^3 + 2*5^4 + 2*5^5 +         2*5^6 + O(5^7))*t^4 + (2 + 4*5^2 + 4*5^3 + 5^4 + 3*5^5 + O(5^6))*t^5 + (2 + 3*5 + 5^4 + O(5^5))*t^6 + (4 + 3*5 + 2*5^2 + O(5^4))*t^7 + (2 + 3*5         + 2*5^2 + O(5^3))*t^8 + (4*5 + O(5^2))*t^9 + (1 + O(5))*t^10 + O(t^11)

    Check that sigma is "weight 1".

    ::

        sage: f = EllipticCurve([-1, 3]).padic_sigma(5, 10)
        sage: g = EllipticCurve([-1*(2**4), 3*(2**6)]).padic_sigma(5, 10)
        sage: t = f.parent().gen()
        sage: f(2*t)/2
        (1 + O(5^10))*t + (4 + 3*5 + 3*5^2 + 3*5^3 + 4*5^4 + 4*5^5 + 3*5^6 + 5^7 + O(5^8))*t^3 + (3 + 3*5^2 + 5^4 + 2*5^5 + O(5^6))*t^5 + (4 + 5 +             3*5^3 + O(5^4))*t^7 + (4 + 2*5 + O(5^2))*t^9 + O(5)*t^10 + O(t^11)
        sage: g
        O(5^11) + (1 + O(5^10))*t + O(5^9)*t^2 + (4 + 3*5 + 3*5^2 + 3*5^3 + 4*5^4 + 4*5^5 + 3*5^6 + 5^7 + O(5^8))*t^3 + O(5^7)*t^4 + (3 + 3*5^2 + 5^4 +         2*5^5 + O(5^6))*t^5 + O(5^5)*t^6 + (4 + 5 + 3*5^3 + O(5^4))*t^7 + O(5^3)*t^8 + (4 + 2*5 + O(5^2))*t^9 + O(5)*t^10 + O(t^11)
        sage: f(2*t)/2 -g
        O(t^11)

    Test that it returns consistent results over a range of precision::

        sage: max_N = 30   # get up to at least p^2         # long time
        sage: E = EllipticCurve([1, 1, 1, 1, 1])            # long time
        sage: p = 5                                         # long time
        sage: E2 = E.padic_E2(5, max_N)                     # long time
        sage: max_sigma = E.padic_sigma(p, max_N, E2=E2)    # long time
        sage: for N in range(3, max_N):                     # long time
        ....:    sigma = E.padic_sigma(p, N, E2=E2)         # long time
        ....:    assert sigma == max_sigma
        """

    #if check_hypotheses:
    #    p = __check_padic_hypotheses(self, p)

    # todo: implement the p == 3 case
    # NOTE: If we ever implement p == 3, it's necessary to check over
    # the precision loss estimates (below) very carefully; I think it
    # may become necessary to compute E2 to an even higher precision
    p=ZZ(norm(p1))
    if p<5:
        raise NotImplementedError("p (=%s) must be at least 5" % p)

    N = int(N)

    K=E.base_field()
    OK=K.maximal_order()
    
    psi1,psi2=embeddings(K,p,25)
    
    psi=chooseembedding(psi1,psi2,p1)
    

    # a few special cases for small N
    if N < 1:
        raise ValueError("N (=%s) must be at least 1" % N)

    if N == 1:
        # return simply t + O(t^2)
        H = Qp(p, 2)
        return PowerSeriesRing(K, "t")([H(0), H(1, 1)], prec=2)

    if N == 2:
        # return t + a_1/2 t^2 + O(t^3)
        H = Qp(p, 3)
        return PowerSeriesRing(H, "t")([H(0), H(1, 2),
                                        H(psi1(E.a1()/2), 1)], prec=3)

    if E.discriminant().valuation(p1) != 0:
        raise NotImplementedError("equation of curve must be minimal at p")
        
    if E2 is None:
       _,E2=mofandE2prime(E,p1,25,prec=20,algorithm="auto",check=True)
        
    elif E2.precision_absolute() < N-2:
        raise ValueError("supplied E2 has insufficient precision")
       
    QQt = LaurentSeriesRing(RationalField(), "x")

    R = Qp(p).residue_ring(N-2)
    X = E.base_extend(psi)
    X= X.change_ring(Qp(p).residue_ring(N-2))
    
    c = (X.a1()**2 + 4*X.a2() - R(E2)) / 12
    
    f = X.formal_group().differential(N+2)   # f = 1 + ... + O(t^{N+2})=\omega in Harvey's paper-section 4
    x = X.formal_group().x(N)                # x = t^{-2} + ... + O(t^N)

    Rt = x.parent()

    A  = (x + c) * f
    # do integral over QQ, to avoid divisions by p
    A = Rt(QQt(A).integral())
    A = (-X.a1()/2 - A) * f
    
    # Convert to a power series and remove the -1/x term.
    # Also we artificially bump up the accuracy from N-2 to N-1 digits;
    # the constant term needs to be known to N-1 digits, so we compute
    # it directly
    assert A.valuation() == -1 and A[-1] == 1
    A = A - A.parent().gen() ** (-1)
    A = A.power_series().list()
    R = Integers(p**(N-1))
    A = [R(u) for u in A]
    A[0] = E.base_extend(psi).change_ring(R).a1()/2     # fix constant term
    A = PowerSeriesRing(R, "x")(A, len(A))
    
    theta = _brent(A, p, N)
    
    
    sigma = theta * theta.parent().gen()

    # Convert the answer to power series over p-adics; drop the precision
    # of the t^k coefficient to p^(N-k+1).
    # [Note: there are actually more digits available, but it's a bit
    # tricky to figure out exactly how many, and we only need p^(N-k+1)
    # for p-adic height purposes anyway]
    QQp = pAdicField(p, N + 1)

    sigma = sigma.padded_list(N+1)

    sigma[0] = QQp(0, N +1)
    sigma[1] = QQp(1, N)
    for n in range(2, N+1):
        sigma[n] = QQp(sigma[n].lift(), N - n + 1)

    S = PowerSeriesRing(QQp, "t", N+1)
    sigma = S(sigma, N+1)
    
    if check:
        R = Integers(p**N)
        X = E.base_extend(psi)
        X= X.change_ring(Qp(p).residue_ring(N-2))
        x = X.formal_group().x(N+5)       # few extra terms for safety
        f = X.formal_group().differential(N+5)
        c = (X.a1()**2 + 4*X.a2() - R(E2)) / 12

        # convert sigma to be over Z/p^N
        s = f.parent()(sigma)
        sinv = s**(-1)
        finv = f**(-1)

        # apply differential equation
        temp = (s.derivative() * sinv * finv).derivative() * finv + c + x

        # coefficient of t^k in the result should be zero mod p^(N-k-2)
        for k in range(N-2):
            assert temp[k].lift().valuation(p) >= N - k - 2, \
                        "sigma correctness check failed!"

    return sigma



