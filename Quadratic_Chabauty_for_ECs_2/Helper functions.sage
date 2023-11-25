def mofandE2prime(E,p1,M,prec=20,algorithm="auto",check=False)
    
    r"""Returns the matrix of Frobenius on the Monsky Washnitzer cohomology of
    the short Weierstrass model of the minimal model of the elliptic curve and E2 for 
    a curve defined over an imaginary quadratic field K and a choice of prime p1 in K such
    that p1 is one of the factors of a prime p>3 in $$\mathbb{Q}$$ which splits in $K$.    
    """
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

                 #Do p=3 later.(AJ,1/3/2021)

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
    
    p=norm(p1)
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
        EQp1=E.base_extend(psi1)
        EQp2=E.base_extend(psi2)
        A=pAdicField(p,25).residue_ring(20)

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
    
    
    #We have all the data for E2 now so just find it using the formula given in say Jen's AWS notes.
    E2_of_X =(-12*frob_p_n[0,1]/frob_p_n[1,1]).lift() + O(p**prec)

    return frob_p.change_ring(Zp(p, prec)), E2_of_X

