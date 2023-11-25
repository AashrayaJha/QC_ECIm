def matrix_of_frobenius_andE2_imquad(E,p,M, prec=20, check=False,  algorithm="auto"):

    r"""
    Returns the matrix of Frobenius on the Monsky Washnitzer cohomology of
    the short Weierstrass model of the minimal model of the elliptic curve for the two embeddings 

    INPUT:
    - ``K``- An imaginary quadratic field. (New,1/3,AJ)
    - ``E``- The minimal model of an elliptic curve over a quadratic imaginary field K (New,1/3.AJ. Try and change this so minimal model is not                 required)

    Used to take a polynomial Q=x^3+ax+b, which has coefficient in a Z/p^MZ algebra.
    -  ``p`` - prime (> 3) for which `E` is good
       and ordinary and splits in the number field K. Add check for p ordinary later, and also p=3. (1/3,AJ)

    -  ``prec`` - (relative) `p`-adic precision for
       result  (default 20)

    -  ``check`` - boolean (default: False), whether to perform a
       consistency check. This will slow down the computation by a
       constant factor 2. (The consistency check is to verify
       that its trace is correct to the specified precision. Otherwise,
       the trace is used to compute one column from the other one
       (possibly after a change of basis).)

       Since we are working with a elliptic curve not over the rationals, the trace method is not available right now.
       So putting Trace=True as default right now(I think, AJ, 3/1)

    -  ``check_hypotheses`` - boolean, whether to check
       that this is a curve for which the `p`-adic sigma function makes
       sense

    -  ``algorithm`` - one of "standard", "sqrtp", or
       "auto". This selects which version of Kedlaya's algorithm is used.
       The "standard" one is the one described in Kedlaya's paper. The
       "sqrtp" one has better performance for large `p`, but only
       works when `p > 6N` (`N=` prec). The "auto" option
       selects "sqrtp" whenever possible.

       Note that if the "sqrtp" algorithm is used, a consistency check
       will automatically be applied, regardless of the setting of the
       "check" flag.

    OUTPUT: a matrix of `p`-adic number to precision ``prec``

    See also the documentation of padic_E2.

    EXAMPLES::

        sage: E = EllipticCurve('37a1')
        sage: E.matrix_of_frobenius(7)
        [             2*7 + 4*7^2 + 5*7^4 + 6*7^5 + 6*7^6 + 7^8 + 4*7^9 + 3*7^10 + 2*7^11 + 5*7^12 + 4*7^14 + 7^16 + 2*7^17 + 3*7^18 + 4*7^19 + 3*7^20          + O(7^21)                                   2 + 3*7 + 6*7^2 + 7^3 + 3*7^4 + 5*7^5 + 3*7^7 + 7^8 + 3*7^9 + 6*7^13 + 7^14 + 7^16 + 5*7^17 +              4*7^18 + 7^19 + O(7^20)]
        [    2*7 + 3*7^2 + 7^3 + 3*7^4 + 6*7^5 + 2*7^6 + 3*7^7 + 5*7^8 + 3*7^9 + 2*7^11 + 6*7^12 + 5*7^13 + 4*7^16 + 4*7^17 + 6*7^18 + 6*7^19 + 4*7^20          + O(7^21) 6 + 4*7 + 2*7^2 + 6*7^3 + 7^4 + 6*7^7 + 5*7^8 + 2*7^9 + 3*7^10 + 4*7^11 + 7^12 + 6*7^13 + 2*7^14 + 6*7^15 + 5*7^16 + 4*7^17 + 3*7^18         + 2*7^19 + O(7^20)]
        sage: M = E.matrix_of_frobenius(11,prec=3); M
        [   9*11 + 9*11^3 + O(11^4)          10 + 11 + O(11^3)]
        [     2*11 + 11^2 + O(11^4) 6 + 11 + 10*11^2 + O(11^3)]
        sage: M.det()
        11 + O(11^4)
        sage: M.trace()
        6 + 10*11 + 10*11^2 + O(11^3)
        sage: E.ap(11)
        -5
        sage: E = EllipticCurve('83a1')
        sage: E.matrix_of_frobenius(3,6)
        [                      2*3 + 3^5 + O(3^6)             2*3 + 2*3^2 + 2*3^3 + O(3^6)]
        [              2*3 + 3^2 + 2*3^5 + O(3^6) 2 + 2*3^2 + 2*3^3 + 2*3^4 + 3^5 + O(3^6)]
    """
    prec = int(prec)

    if p < 3:
        raise NotImplementedError("p (=%s) must be at least 3" % p)
    if prec < 1:
        raise ValueError("prec (=%s) must be at least 1" % prec)

    #if check_hypotheses:
    #    p = __check_padic_hypotheses(E, p)  #Can add this later, right now just enter primes of good reduction.
    K=E.base_field()
    OK=K.maximal_order()
    p1,p2=factor(p*OK)
    p1=(p1[0])
    p2=(p2[0])

    if algorithm == "auto":
        algorithm = "standard" if norm(p1) < 6*prec else "sqrtp"
    elif algorithm == "sqrtp" and norm(p1) < 6*prec:
        raise ValueError("sqrtp algorithm is only available when p > 6*prec")
    if algorithm not in ["standard", "sqrtp"]:
        raise ValueError("unknown algorithm '%s'" % algorithm)

    # for p = 3, we create the corresponding hyperelliptic curve
    # and call matrix of frobenius on it
    #if p == 3:
       # from sage.schemes.hyperelliptic_curves.constructor import HyperellipticCurve
        #f,g = self.hyperelliptic_polynomials()
        #return HyperellipticCurve(f + (g/2)**2).matrix_of_frobenius(p,prec)

                 #Do p=3 later.(AJ,1/3)

    # To run matrix_of_frobenius(), we need to have the equation in the
    # form y^2 = x^3 + ax + b, whose discriminant is invertible mod p.
    # When we change coordinates like this, we might scale the invariant
    # differential, so we need to account for this. We do this by
    # comparing discriminants: if the discriminants differ by u^12,
    # then the differentials differ by u. There's a sign ambiguity here,
    # but it doesn't matter because E2 changes by u^2 :-)

    # todo: In fact, there should be available a function that returns
    # exactly *which* coordinate change was used. If I had that I could
    # avoid the discriminant circus at the end.

    # todo: The following strategy won't work at all for p = 2, 3.

    # TODO change the basis back to the original equation.
    X = E.short_weierstrass_model()

    assert X.discriminant().valuation(p1) == 0, "Something's gone wrong. " \
           "The discriminant of the Weierstrass model should be a unit " \
           " at p." #Get the prime to

    if algorithm == "standard":
        # Need to increase precision a little to compensate for precision
        # losses during the computation. (See monsky_washnitzer.py
        # for more details.)
        adjusted_prec = sage.schemes.hyperelliptic_curves.monsky_washnitzer.adjusted_prec(p, prec)

        if check:
            trace = None
        else:
            trace = E.ap(p)


        psi1,psi2=embeddings(K,p,50)
        EQp1=E.base_extend(psi1)
        EQp2=E.base_extend(psi2)
        A=pAdicField(p,25).residue_ring(50)
        
        R, x = PolynomialRing(A, 'x').objgen()
        
        Q = x**3 + A(psi1(X.a4()))* x + A(psi1(X.a6()))

        frob_p = sage.schemes.hyperelliptic_curves.monsky_washnitzer.matrix_of_frobenius(
                         Q, p, adjusted_prec, trace)
        
    else:   # algorithm == "sqrtp"
        p_to_prec = p**prec
        R = PolynomialRing(Integers(), "x")
        Q = R([X.a6() % p_to_prec, X.a4() % p_to_prec, 0, 1])
        frob_p = sage.schemes.hyperelliptic_curves.hypellfrob.hypellfrob(p, prec, Q)

        # let's force a trace-check since this algorithm is fairly new
        # and we don't want to get caught with our pants down...
        check = True

    if check:
        trace_of_frobenius = frob_p.trace().lift() % p**prec
        #correct_trace = E.ap(p) % p**prec
        #assert trace_of_frobenius == correct_trace, \
         #       "Consistency check failed! (correct = %s, actual = %s)" % \    (correct_trace, trace_of_frobenius)
    frob_p_n=frob_p**prec
    E2_of_X =(-12*frob_p_n[0,1]/frob_p_n[1,1]).lift() + O(p**prec)

    frobp1,E2p1=mofandE2prime(E,p1,M,prec=20,algorithm="auto",check=True) #see below
    
    frobp2,E2p2=mofandE2prime(E,p2,M,prec=20,algorithm="auto",check=True)
    
    return p1,frobp1,E2p1,p2,frobp2,E2p2

def mofandE2prime(E,p1,M,prec=20,algorithm="auto",check=False):
    
    r"""Returns the matrix of Frobenius on the Monsky Washnitzer cohomology of
    the short Weierstrass model of the minimal model of the elliptic curve and E2 for 
    a curve defined over an imaginary quadratic field K and a choice of prime p1 in K such
    that p1 is one of the factors of a prime p>3 in $$\mathbb{Q}$$ which splits in $K$
    
    Requires an elliptic curve over a number field and a prime of the number field. Also reuqires a couple of 
    precision estimates, one for .    
    """
    
    p=ZZ(norm(p1))
    
    prec = int(prec)

    if p < 3:
        raise NotImplementedError("p (=%s) must be at least 3" % p)
    if prec < 1:
        raise ValueError("prec (=%s) must be at least 1" % prec)

    #if check_hypotheses:
    #    p = __check_padic_hypotheses(E, p)  #Can add this later, right now just enter primes of good reduction.
    K=E.base_field()
    OK=K.maximal_order()
    
    if algorithm == "auto":
        algorithm = "standard" if norm(p1) < 6*prec else "sqrtp"
    elif algorithm == "sqrtp" and norm(p1) < 6*prec:
        raise ValueError("sqrtp algorithm is only available when p > 6*prec")
    if algorithm not in ["standard", "sqrtp"]:
        raise ValueError("unknown algorithm '%s'" % algorithm)

    # for p = 3, we create the corresponding hyperelliptic curve
    # and call matrix of frobenius on it
    #if p == 3:
       # from sage.schemes.hyperelliptic_curves.constructor import HyperellipticCurve
        #f,g = self.hyperelliptic_polynomials()
        #return HyperellipticCurve(f + (g/2)**2).matrix_of_frobenius(p,prec)

                 #Do p=3 later.(AJ,1/3)

    # To run matrix_of_frobenius(), we need to have the equation in the
    # form y^2 = x^3 + ax + b, whose discriminant is invertible mod p.
    # When we change coordinates like this, we might scale the invariant
    # differential, so we need to account for this. We do this by
    # comparing discriminants: if the discriminants differ by u^12,
    # then the differentials differ by u. There's a sign ambiguity here,
    # but it doesn't matter because E2 changes by u^2 :-)

    # todo: In fact, there should be available a function that returns
    # exactly *which* coordinate change was used. If I had that I could
    # avoid the discriminant circus at the end.

    # todo: The following strategy won't work at all for p = 2, 3.

    # TODO change the basis back to the original equation.
    X = E.short_weierstrass_model()
    
    assert X.discriminant().valuation(p1) == 0, "Something's gone wrong. " \
           "The discriminant of the Weierstrass model should be a unit " \
           " at p." #Get the prime to

    if algorithm == "standard":
        # Need to increase precision a little to compensate for precision
        # losses during the computation. (See monsky_washnitzer.py
        # for more details.)
        adjusted_prec = sage.schemes.hyperelliptic_curves.monsky_washnitzer.adjusted_prec(p, prec)

        if check:
            trace = None
        else:
            trace = E.ap(p)


        psi1,psi2=embeddings(K,p,25)
        
        #embedding is chosen so that p1 is 'pi'
        if psi1(p1).valuation() > 0:
            psi = psi1
        else:
            psi = psi2
        EQp=E.base_extend(psi)
        
        A=pAdicField(p,25).residue_ring(20)
        R, x = PolynomialRing(A, 'x').objgen()
        
        Q = x**3 + A(psi(X.a4()))* x + A(psi(X.a6()))
        
        frob_p = sage.schemes.hyperelliptic_curves.monsky_washnitzer.matrix_of_frobenius(
                         Q, p, adjusted_prec, trace)
        
    else:   # algorithm == "sqrtp"
        p_to_prec = p**prec
        R = PolynomialRing(Integers(), "x")
        Q = R([X.a6() % p_to_prec, X.a4() % p_to_prec, 0, 1])
        frob_p = sage.schemes.hyperelliptic_curves.hypellfrob.hypellfrob(p, prec, Q)

        # let's force a trace-check since this algorithm is fairly new
        # and we don't want to get caught with our pants down...
        check = True

    if check:
        trace_of_frobenius = frob_p.trace().lift() % p**prec      
        #correct_trace = E.ap(p) % p**prec
        #assert trace_of_frobenius == correct_trace, \
         #       "Consistency check failed! (correct = %s, actual = %s)" % \    (correct_trace, trace_of_frobenius)
    frob_p_n=frob_p**prec
    E2_of_X =(-12*frob_p_n[0,1]/frob_p_n[1,1]).lift() + O(p**prec)
    fudge_factor = (X.discriminant() / E.discriminant()).nth_root(6)
    # todo: here I should be able to write:
    #  return E2_of_X / fudge_factor
    # However, there is a bug in Sage (#51 on trac) which makes this
    # crash sometimes when prec == 1. For example,
    #    EllipticCurve([1, 1, 1, 1, 1]).padic_E2(5, 1)
    # makes it crash. I haven't figured out exactly what the bug
    # is yet, but for now I use the following workaround:
    
    output_ring =pAdicField(p, prec)
    fudge_factor_inverse = output_ring(1 / fudge_factor)
    
    E2_of_X= output_ring(E2_of_X * fudge_factor_inverse)       
  
    return frob_p.change_ring(Zp(p, prec)), E2_of_X


def _brent(F, p, N):
    r"""
    This is an internal function; it is used by padic_sigma().
    `F` is a assumed to be a power series over
    `R = \ZZ/p^{N-1}\ZZ`.
    It solves the differential equation `G'(t)/G(t) = F(t)`
    using Brent's algorithm, with initial condition `G(0) = 1`.
    It is assumed that the solution `G` has
    `p`-integral coefficients.
    More precisely, suppose that `f(t)` is a power series with
    genuine `p`-adic coefficients, and suppose that
    `g(t)` is an exact solution to `g'(t)/g(t) = f(t)`.
    Let `I` be the ideal
    `(p^N, p^{N-1} t, \ldots,
        p t^{N-1}, t^N)`. The input
    `F(t)` should be a finite-precision approximation to
    `f(t)`, in the sense that `\int (F - f) dt` should
    lie in `I`. Then the function returns a series
    `G(t)` such that `(G - g)(t)` lies in `I`.
    Complexity should be about `O(N^2 \log^2 N \log p)`, plus
    some log-log factors.
    For more information, and a proof of the precision guarantees, see
    Lemma 4 in "Efficient Computation of p-adic Heights" (David
    Harvey).
    AUTHORS:
    - David Harvey (2007-02)
    EXAMPLES: Carefully test the precision guarantees::
        sage: brent = sage.schemes.elliptic_curves.padics._brent
        sage: for p in [2, 3, 5]:
        ....:   for N in [2, 3, 10, 50]:
        ....:     R = Integers(p**(N-1))
        ....:     Rx.<x> = PowerSeriesRing(R, "x")
        ....:     for _ in range(5):
        ....:       g = [R.random_element() for i in range(N)]
        ....:       g[0] = R(1)
        ....:       g = Rx(g, len(g))
        ....:       f = g.derivative() / g
        ....:       # perturb f by something whose integral is in I
        ....:       err = [R.random_element() * p**(N-i) for i in range(N+1)]
        ....:       err = Rx(err, len(err))
        ....:       err = err.derivative()
        ....:       F = f + err
        ....:       # run brent() and compare output modulo I
        ....:       G = brent(F, p, N)
        ....:       assert G.prec() >= N, "not enough output terms"
        ....:       err = (G - g).list()
        ....:       for i in range(len(err)):
        ....:         assert err[i].lift().valuation(p) >= (N - i), \
        ....:                "incorrect precision output"
    """
    
    Rx = F.parent()           # Rx = power series ring over Z/p^{N-1} Z
    Qx = PowerSeriesRing(RationalField(), "x")
    F=Qx(F)
    # initial approximation:
    G = Qx.one()

    # loop over an appropriate increasing sequence of lengths s
    for s in newton_method_sizes(N):
        # zero-extend to s terms
        # todo: there has to be a better way in Sage to do this...
        G = Qx(G.list(), s)
        # extend current approximation to be correct to s terms
        H = G.derivative() / G - F
        
        # Do the integral of H over QQ[x] to avoid division by p problems
        H = Qx(H).integral()
        
        G = (Qx(G) * (1 - H))
        
    return Rx(G)

def chooseembedding(psi1,psi2,p1):

    if psi1(p1).valuation() > 0:
            psi = psi1
    else:
            psi = psi2
    return psi

def Zp_base_change(E,p,n):
    QQp = pAdicField(p, n)
    L=E.base_field()
    ZZp = Zp(p, prec = n, type = 'fixed-mod', print_mode = 'series')
    _.<x> = PolynomialRing(E.base_ring())
    Eshort = E.short_weierstrass_model()
    phi = Eshort.isomorphism_to(E)
    psi = E.isomorphism_to(Eshort)
    a4 = Eshort.a4()
    a6 = Eshort.a6()
    #[u, rr, s, tt] = psi.tuple()
    S.<y>=PolynomialRing(QQp)
    f=L.defining_polynomial()
    f=f.base_extend(pAdicField(p,20))
    alpha1,alpha2=f.roots()
    alpha1=alpha1[0]
    alpha2=alpha2[0];
    psi1=L.hom([alpha1])
    psi2=L.hom([alpha2])
    R.<x> = ZZp['x']
    HZZp1 = HyperellipticCurve(x^3 + ZZp(psi1(a4))*x + ZZp(psi1(a6)))
    HZZp2 = HyperellipticCurve(x^3 + ZZp(psi2(a4))*x + ZZp(psi2(a6)))
    return HZZp1,HZZp2

def lin_indep_generators(E):
    allgens=E.gens()
    n=len(allgens)
    if n==1:
        print("Sage could only find one point of infinte order")
        return allgens
    P1=allgens[0]
    for i in range(1,n):
        M=E.height_pairing_matrix([P1,allgens[i]])
        print(M)
        if det(M)<=10^(-10):
            pass
        else:
            P2=allgens[i]
            break
    assert(det(M)>=10^(-10)) #find the actual precisison
    
    return [P1,P2]

def IsinWeierstrassdisk(P,EFp1,EFp2):#prime1,prime2):
    #if 
    PFp1=EFp1(P)
    PFp2=EFp1(P)

        #print(PFp1)
        #print(PFp2)
    if PFp1.is_zero():
        return true
    elif PFp1[1]==0:
        return true
    elif PFp2.is_zero():
        return true
    elif PFp2[1]==0:
        return true
    else:
        return false
#This is a bit ad-hoc, should find a better way of doing this to get an actual point each time
    
def finding_nonWeierstrass_pts(A,B,EFp1,EFp2):

    for i in range(1,5):
            #print("this is for P1")
            A=i*A
            #print(i,A)
            if IsinWeierstrassdisk(A,EFp1,EFp2):
                pass
            else:
                break
                
    for i in range(1,5):  
            #print("this is for P2")
            B=i*B
            
            if IsinWeierstrassdisk(B,EFp1,EFp2):
                pass
            else:
                break
                
    #for i in range(1,5):
            #for j in range(1,5):
                #print("this is for P3", "i is ",i, "j is ",j)
                #C=i*A+j*B
                #if IsinWeierstrassdisk(C,EFp1,EFp2):
                    #pass
                #else:
                    #break
            #if not IsinWeierstrassdisk(C,EFp1,EFp2):
                #break
        #print(A)        
    return A,B #,C


def SmallIntegralPoints_1(E,n,gens):
    K=E.base_field()
    OK=K.maximal_order()
    IntegralPoints=[]
    P,Q=gens
    for i in range(-n,n+1):
        for j in range(-n,n+1):
            R=i*P+j*Q
            try:
                OK(R[0])
                OK(R[1])
                print(R)
                IntegralPoints.append(R)
            except TypeError:
                continue
    IntegralPoints.remove(E([0,1,0]))            
    return IntegralPoints
def SmallIntegralPoints(E,n):
    K=E.base_field()
    OK=K.maximal_order()
    a=OK.ring_generators()[0]
    IntegralPoints=[]
    
    for i in range(-n,n+1):
        for j in range(-n,n+1):
            try:
                x=i+j*a
                P=E.lift_x(x,all)
                #if x==2*a:
                #    print(P)

                if len(P)==0:
                    pass
                else:
                    if P[0][1].is_integral():
                    #n=len(IntegralPoints)
        #print(IntegralPoints,len(IntegralPoints))
                    #if n==0:
                        IntegralPoints.extend(P)
                        #elif P==IntegralPoints[n-1]:
                        #    pass
                        #else:
                        #    IntegralPoints.extend(P)
            except ValueError:
                pass
    return IntegralPoints  

def finding_primes(E,n):
    K=E.base_field()
    OK=K.maximal_order()
    P=[Primes()[i] for i in range(1,n)]

    is_split = lambda K,x:len(factor(x*OK))==K.degree()

    PK=[p for p in P if is_split(K,p) and K.discriminant()%p!=0]
    PE=[p for p in PK if E.conductor().norm()%p!=0]
    Pacceptable=[]
    Pgood=[]
    #print(P,PE)
    for p in PE:
        for q in PE:
            if q>p:
                #print(p,q)
                P1,P2=compatible_primes_and_embeddings_and_residue_fields(K,p)
                p1=P1[0];p2=P2[0];psi1=P1[2];psi2=P2[2]
                EFp1,EFp2,EQp1,EQp2=find_base_change(E,p1,psi1,p2,psi2)
                Q1,Q2=compatible_primes_and_embeddings_and_residue_fields(K,q)
                q1=Q1[0];q2=Q2[0];phi1=Q1[2];phi2=Q2[2]
                EFq1,EFq2,EQq1,EQq2=find_base_change(E,q1,phi1,q2,phi2)
                if not (EFp1.is_ordinary()and EFp2.is_ordinary() and EFq1.is_ordinary() and EFq2.is_ordinary()):
                    continue
                countp1=EFp1.cardinality()
                countq1=EFq1.cardinality()
                countp2=EFp2.cardinality()
                countq2=EFq2.cardinality()
                if (countp1%q==0 or countp2%q==0) and (countq1%p==0 or countq2%p==0):
                    Pacceptable.append([p,q])
                    if countp1==countp2 or countq1==countq2:
                        Pgood.append([p,q])
    return Pacceptable,Pgood


def sorting_fct(L):
    r"""
    Return `0` if input has length `2`, `1` otherwise.
    """
    if len(L) == 2:
        return 0
    else:
        return 1