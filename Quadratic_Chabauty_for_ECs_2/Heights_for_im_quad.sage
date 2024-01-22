r"""
This code in this file is based on Francesca Bianchi's implementation at 
https://github.com/bianchifrancesca/QC_elliptic_imaginary_quadratic_rank_2/blob/master/quad_chab_ell_im_quad.sage.

We have extended the code so that we can also handle curves which are not base changes from the rationals and 
"""
REFERENCES:

- [BBBM19] \J. S. Balakrishnan, A. Besser, F. Bianchi, J. S. Mueller,
  "Explicit quadratic Chabauty over number fields". To appear in
  "Isr. J. Math.".

- [BcL+16] \J. S. Balakrishnan, M. Ciperiani, J. Lang, B. Mirza, and R. Newton,
  "Shadow lines in the arithmetic of elliptic curves".
  In" Directions in number theory, volume 3".

- [Bia19] \F. Bianchi, "Quadratic Chabauty for (bi)elliptic curves
  and Kim's conjecture". To appear in "Algebra Number Theory".

- [MST06] Barry Mazur, William Stein, and John Tate. 
  "Computation of p-adic heights and log convergence."
  Doc. Math, pages 577–614, 2006.
"""

def anticyc_padic_height(E, P, p, prec=25, bernardi=False, multi=1,M=25):
    r"""
    Compute the anticyclotomic height of a point on an elliptic curve over `K = \QQ(\{sqrt{d}})`.
    This is the code used for [BcL+16], with a few documented changes (e.g. added
    supersingular case) and extended to curves not over `\QQ`.

    INPUT:

    -``E`` -- an elliptic curve over a number field K=\QQ(\sqrt(d)). For simplicity, let the class number of K be 1.

    -``d`` -- a rational number which is not a perfect square.

     (This will give ``K``-- a (imaginary) quadratic number field.)
    - ``P`` -- a point on `E(\QQ(\sqrt(d))`.

    -``p`` -- a prime of QQ splits in `\QQ(\sqrt(d))` such that E has good reduction at both primes above p.

    - ``prec`` -- the `p`-adic precision.

    - ``bernardi``-- True/False (default False). If False, you must have
      `p` is `\ge 5` and ordinary. Then the Mazur-Tate sigma function is used.
      If True, the Bernardi sigma function is used.

    - ``multi`` -- parameter to check quadraticity of output.
    _ ``M`` -- Paramtre which is used in the precision of calculating E2 and the matrix of frobenius.
    OUTPUT:

    A p-adic number: the anticyclotomic height of P1.
    """
    assert isinstance(P, sage.schemes.elliptic_curves.ell_point.EllipticCurvePoint_field), "P is not a point on an elliptic curve."
    K=E.base_field()
    #K.<D> = QuadraticField(d)
    h = K.class_number()
    OK = K.maximal_order()
    
    assert len(factor(p*OK)) == 2, "Given prime does not split in choice of number field. "
    p1, p2 = factor(p*OK)
    assert E.conductor().norm()%p!=0, "The prime divides the conductor of the elliptic curve!"
    #some funny business to see what the role of order of primes plays in the final heights. 
    #Changed it back and it works!
    
    P1=p1[0]
    P2=p2[0]
    p1 = (p1[0]^h).gens_reduced()[0]
    p2 = (p2[0]^h).gens_reduced()[0]
    psi1, psi2 = embeddings(K,p,prec)
    
    if psi1(p1).valuation() > 0:
            psi1 = psi1
            psi2 = psi2
            
    else:
            x=psi1
            psi1=psi2
            psi2=x
    
    Fp1=OK.residue_field(p1)
    Fp2=OK.residue_field(p2)
    EQp1=E.change_ring(psi1)
    EQp2=E.change_ring(psi2)
    EFp1=E.change_ring(Fp1)
    EFp2=E.change_ring(Fp2)
    #Fp1.<a1>=K.residue_field(p1)
    #Fp2.<a2>=K.residue_field(p2)
    
    #print(Fp1)
    #EFp1=E.base_ring(Fp1)
    #EFp2=E.base_ring(Fp2)
    assert E.has_good_reduction(P1)  and E.has_good_reduction(P2), "The elliptic curve does not have good reduction above given prime."
    assert EFp1.is_ordinary() and EFp2.is_ordinary(), "The elliptic curve is not ordinary above given prime."
    # FB 28/04 and E.is_ordinary(p), AJ E.has_good_reduction
    #if bernardi == False:
    #    assert E.has_good_reduction(p1) and E.has_good_reduction(p2)
    
    
    #embedding is chosen so that p1 is 'pi'
    #if psi1(p1.gen(1)).valuation() > 0:
    #   embedding = psi1
    #  EQp=EQp1
    #else:
    #    embedding = psi2
    #    EQp=EQp2
    #assert embedding(p1.gen(1)).valuation() > 0
    tam = lcm(E.tamagawa_numbers())
    A = tam*P
    
    #print(A,"This is the point times the Tamagawa numbers")
    #A=P
    try_orders1 = divisors(EQp1.change_ring(Fp1).cardinality())
    #print("this is tryorders",try_orders1)
    for ord in try_orders1:
        B1 = ord*A
        B1 = EQp1(psi1(B1[0]), psi1(B1[1]))
        if B1[1]!=0 : #FB - Modification so that it does't give errors when B1[1]=0 24/11/2017
            tB1 = -B1[0]/B1[1]
            if tB1.valuation() > 0 and B1[0].valuation() < 0 and B1[1].valuation() <0:
                n1 = ord
                break
    #print("this is n1",n1)            
    try_orders2 = divisors(EQp2.change_ring(Fp2).cardinality())
    #print("this is tryorders2", try_orders2)
    for ord in try_orders2:
        B2 = ord*A
        B2= EQp2(psi2(B2[0]),psi2(B2[1]))
        if B2[1]!=0:
            tB2=-B2[0]/B2[1]
            if tB2.valuation() > 0 and B2[0].valuation() < 0 and B2[1].valuation() <0:
                n2 = ord
                break
    #print("This is n2",n2)            
    n = lcm(n1,n2)*multi
    #print(n)
    B=n*A
    B1=EQp1(psi1(B[0]), psi1(B[1]))
    B2=EQp2(psi2(B[0]),psi2(B[1]))
    #print(B1, " This is B1")
    #print(B2, " This is B2")
    tB1=-B1[0]/B1[1]
    tB2=-B2[0]/B2[1]
    if n%2 == 1:
        fn = E.division_polynomial(n) #This probably does nothing
    else:
        fn = E.division_polynomial(n, two_torsion_multiplicity=1)
        
    xA = A[0]
    xB1= B1[0]
    xB2= B2[0]
    #print("n is",n)
    if n%2 == 1:
        fn_at_A = fn(xA)
    else:
        fn_at_A = fn((A[0], A[1]))

    if xA == 0:
        d_at_A = 1
    else:
        d_at_A = K.ideal(xA).denominator()
    try:
        #print("going to factor denominator now")
        d_at_A = prod([a^ZZ(e/2) for (a,e) in factor(d_at_A)]) 
        d_at_A = (d_at_A).gens_reduced()[0]
    except AttributeError:
        d_at_A = prod([a^(e/2) for (a,e) in factor(d_at_A)])

    d_of_nA_to_h = d_at_A^(n^2)*fn_at_A
    #print(d_of_nA_to_h)
    dbydconjA=d_of_nA_to_h/d_of_nA_to_h.conjugate()
    NA = K.ideal(dbydconjA).numerator()
    NAg = NA.gens_reduced()[0]
    NAgconj = NAg.conjugate()
    p1val= (NAgconj/NAg).valuation(p1)
    p2val= (NAgconj/NAg).valuation(p2)
    NAval = (NAgconj/NAg)
    #A1_sum_away_from_p_via_embedding = 1/(p*h)*log(embedding(NA1val),0)
    #FB: changed normalisation

    A_sum_away_from_p_via_embedding = -log(psi1(NAval),0)
    #print(A_sum_away_from_p_via_embedding," away from p")
    #print(A_sum_away_from_p_via_embedding)
    #FB: added Bernardi sigma function option
    #if bernardi == False:
    #    sig = E.change_ring(QQ).padic_sigma(p,prec)
    #else:
    #    sig = bernardi_sigma_function(E.change_ring(QQ),prec=prec+5)  ## 18/3 try and do bernadi sigma functions later, just see the +usual p-adic         sigma function implemented by Harvey rn.
    #   sig = sig(E.change_ring(QQ).formal().log(prec+5))
    
    
    #FB: changed normalisation
    #height_at_p_A1  = 1/(p)*log(sig(embedding(-B1[0]/B1[1]))/sig(embedding(-B1conj[0]/B1conj[1])),0)
    #print(tB1, " this is tB1")
    #print(tB2, "this is tB2")
    sigma1=p1adic_sigma_imquad(E, p1, N=20, E2=None, check=False, check_hypotheses=True)
    sigma2=p1adic_sigma_imquad(E, p2, N=20, E2=None, check=False, check_hypotheses=True)
    
    height_at_p_A=-log(sigma1(tB1),0)+log(sigma2(tB2),0)
    #print(height_at_p_A, " ht at p")
    height_A = 1/n^2*(height_at_p_A + A_sum_away_from_p_via_embedding)
    #print(height_A)
    height_P = 1/(tam^2)*height_A
    
    
    #Add a check!
    return height_P


def local_height_away_from_p_anti(P,p):
    E=P.curve()
    n=find_n(E,P,p)
    p = 7
    (prime1,p1,psi1,Fp1),(prime2,p2,psi2,Fp2)=compatible_primes_and_embeddings_and_residue_fields(L,p)

    P=n*P
    dsquare=P[0].denominator_ideal()
    d=prod(a^ZZ(e/2) for (a,e) in factor(dsquare))
    d=d.gens()[0]
    e1=ZZ(d.valuation(prime1))
    e2=ZZ(d.valuation(prime2))

    d1=psi1(d);d2=psi2(d)
    ht=-log(d1/d2,0)+log(psi1(p2^e2)/psi2(p1^e1))
    return ht

def non_archimedean_local_height(P, v, p, prec, weighted=False, is_minimal=None,embeddings=None):
    """r
    Return the local `p`-adic height of `P` at the place `v`.
    This is a modified version of the built-in function `non_archimedean_local_height`:
    the symbolic logarithm (or real logarithm) is replaced by the `p`-adic logarithm.

    INPUT:

    - ``P`` -- a point on an elliptic curve over a number field `K`.

    - ``v`` -- a non-archimedean place of `K`` or `None`.

    - ``p`` -- an odd prime.

    - ``prec`` -- integer. The precision of the computation.

    - ``weighted`` -- boolean. If False (default), the height is
      normalised to be invariant under extension of `K`. If True,
      return this normalised height multiplied by the local degree.

    OUTPUT:

    A p-adic number: the `v`-adic component of the `p`-adic height of `P`
    if `v` is a place; the sum of the components away from `p` of the
    `p`-adic height of `P` if `v` is `None`.
    """
    K = P.curve().base_ring()
    if embeddings==None:
        (prime1,p1,psi1,Fp1), (prime2,p2,psi2,Fp2)=compatible_primes_and_embeddings_and_residue_fields(K,p)
    else:
        psi1=embeddings[0]
        psi2=embeddings[1]
    if v is None:
        D = P.curve().discriminant()
        
        if K is QQ:
            factorD = D.factor()
            if P[0] == 0:
                c = 1
            else:
                c = P[0].denominator()
            # The last sum is for bad primes that divide c where
            # the model is not minimal.
            h = (log(Qp(p, prec)(c))
                 + sum(non_archimedean_local_height(P, q, p, prec, weighted=True, is_minimal=(e < 12))
                       for q,e in factorD if not q.divides(c))
                 + sum(non_archimedean_local_height(P, q, p, prec, weighted=True)
                       - c.valuation(q) * log(Qp(p, prec)(q))
                       for q,e in factorD if e >= 12 and q.divides(c)))
        else:
            factorD = K.factor(D)
            if P[0] == 0:
                c = K.ideal(1)
            else:
                c = K.ideal(P[0]).denominator()
            # The last sum is for bad primes that divide c where
            # the model is not minimal.
            c=c.gens_reduced()[0]
            hcyc = (log(Qp(p, prec)(c.norm()))
                 + sum(non_archimedean_local_height(P, v, p, prec, weighted=True, is_minimal=(e < 12))[0]
                       for v,e in factorD if not v.divides(c))
                 + sum(non_archimedean_local_height(P, v, p, prec, weighted=True)[0]
                       - c.valuation(v) * log(Qp(p, prec)(v.norm()))
                       for v,e in factorD if e >= 12 and v.divides(c)))
            hanti= (log(psi1(c)/psi2(c))
                 + sum(non_archimedean_local_height(P, v, p, prec, weighted=True, is_minimal=(e < 12))[1]
                       for v,e in factorD if not v.divides(c))
                 + sum(non_archimedean_local_height(P, v, p, prec, weighted=True)[1]
                       - c.valuation(v) * log(Qp(p, prec)(v.norm()))
                       for v,e in factorD if e >= 12 and v.divides(c)))
            
            if not weighted:
                hcyc /= K.degree()
                hanti /= K.degree()
        return hcyc,hanti

    if is_minimal:
        E = P.curve()
        offset = ZZ.zero()
        Pmin = P
    else:
        E = P.curve().local_minimal_model(v)
        Pmin = P.curve().isomorphism_to(E)(P)
        # Silverman's normalization is not invariant under change of model,
        # but it all cancels out in the global height.
        offset = (P.curve().discriminant()/E.discriminant()).valuation(v)

    a1, a2, a3, a4, a6 = E.a_invariants()
    b2, b4, b6, b8 = E.b_invariants()
    c4 = E.c4()
    x, y = Pmin.xy()
    D = E.discriminant()
    N = D.valuation(v)
    A = (3*x**2 + 2*a2*x + a4 - a1*y).valuation(v)
    B = (2*y+a1*x+a3).valuation(v)
    C = (3*x**4 + b2*x**3 + 3*b4*x**2 + 3*b6*x + b8).valuation(v)
    if A <= 0 or B <= 0:
        r = max(0, -x.valuation(v))
    elif c4.valuation(v) == 0:
        n = min(B, N/2)
        r = -n*(N-n)/N
    elif C >= 3*B:
        r = -2*B/3
    else:
        r = -C/4
    r -= offset/6
    if not r:
        return Qp(p,prec)(0)
    else:
        if E.base_ring() is QQ:
            Nv = Integer(v)
        else:
            Nv = v.norm()
            if not weighted:
                r = r / (v.ramification_index() * v.residue_class_degree())
        hcyc= r * log(Qp(p,prec)(Nv))
        v_gen=v.gens_reduced()[0]
        hanti= r*log((psi1(v_gen)/psi2(v_gen)),0)
        return hcyc,hanti

    
def local_heights_at_bad_primes_number_field(E, L, p,embeddings=None):
    """r
    Finds all possible sums of local heights at bad places for an integral point.

    INPUT:

    - ``E`` -- an elliptic curve over the number field ``L``.

    - ``L`` -- a number field with class number 1.

    - ``p`` -- a rational prime such that `E/L` has good reduction at all primes of L
      above `p`.

    OUTPUT:

    A list of `p`-adic numbers such that if `P\in E(L)` is integral (with respect to the
    given model), then the sum of the local heights away from p of the cyclotomic `p`-adic
    height of `P` belongs to this list.
    """
    if embeddings==None:
        (prime1,p1,psi1,Fp1), (prime2,p2,psi2,Fp2)=compatible_primes_and_embeddings_and_residue_fields(L,p)
    else:
        psi1=embeddings[0]
        psi2=embeddings[1]
    K=Qp(p)
    E = E.change_ring(L)
    BadPrimes = E.base_ring()(E.integral_model().discriminant()).support()
    W = []
    W_anti=[]
    BadPrimesNew = []
    for q in BadPrimes:
        Eq = E.local_minimal_model(q)
        deltaq = E.discriminant()/Eq.discriminant()
        qnorm = q.norm()
        qanti= psi1(q.gens_reduced()[0])/psi2(q.gens_reduced()[0])
        if Eq.tamagawa_number(q) == 1 and deltaq.valuation(q) == 0:
            W.append([0])
            W_anti.append([0])
            continue
        BadPrimesNew.append(q)
        ks = E.kodaira_symbol(q)
        if Eq.tamagawa_number(q) == 1 and deltaq.valuation(q) != 0:
            W.append([2*K(k)*K(qnorm).log()] for k in range(1,ZZ(deltaq.valuation(q)/12)+1))
            W_anti.append([2*K(k)*K(qanti).log() for k in range(1,ZZ(deltaq.valuation(q)/12)+1)])
        elif Eq.has_additive_reduction(q):
            if ks == KodairaSymbol(3): #III
                W.append([-1/2*(K(qnorm)).log()])
                W_anti.append([-1/2*(K(qanti)).log()])
            elif ks == KodairaSymbol(4): #IV
                W.append([-2/3*K(qnorm).log()])
                W_anti.append([-2/3*K(qanti).log()])
            elif ks == KodairaSymbol(-1): #I0*
                W.append([-K(qnorm).log()])
                W_anti.append([-K(qanti).log()])
            elif ks == KodairaSymbol(-4): #IV*
                W.append([-(4/3)*K(qnorm).log()])
                W_anti.append([-(4/3)*K(qanti).log()])
            elif ks == KodairaSymbol(-3): #III*
                W.append([-(3/2)*K(qnorm).log()])
                W_anti.append([-(3/2)*K(qanti).log()])
            else: #Im*
                if E.tamagawa_number(q) == 2:
                    W.append([-K(qnorm).log()])
                    W_anti.append([-K(qanti).log()])
                else:
                    n = -5
                    while ks != KodairaSymbol(n):
                        n = n-1
                    m = -n-4
                    W.append([-K(qnorm).log(),-(m+4)/4*K(qnorm).log()])
                    W_anti.append([-K(qanti).log(),-(m+4)/4*K(qanti).log()])
        else: #multiplicative
            n = 5
            while ks != KodairaSymbol(n):
                n = n+1
            m = n-4
            if E.tamagawa_number(q) == 2:
                W.append([-m/4*K(qnorm).log()])
                W_anti.append([-m/4*K(qanti).log()])
            else:
                W.append([-i*(m-i)/m*(K(qnorm)).log() for i in range(1,(m/2).floor()+1)]) #enough to go to m/2 -see Silverman's article
                W_anti.append([-i*(m-i)/m*(K(qanti)).log() for i in range(1,(m/2).floor()+1)]) #enough to go to m/2 -see Silverman's article
        if qnorm != 2 or E.has_split_multiplicative_reduction(q) == False:
            W[-1].append(0)
            W_anti[-1].append(0)
        if deltaq != 1:  #If not a minimal model
            W[-1] = list(Set(W[-1] + [2*K(k)*K(qnorm).log() for k in range(1,ZZ(deltaq.valuation(q)/12)+1)]))
            W_anti[-1] = list(Set(W_anti[-1] + [2*K(k)*K(qanti).log() for k in range(1,ZZ(deltaq.valuation(q)/12)+1)]))
            W[-1] = [w - 1/6*L(deltaq).valuation(q)*K(qnorm).log() for w in W[-1]]
            W_anti[-1] = [w - 1/6*L(deltaq).valuation(q)*K(qanti).log() for w in W[-1]]
    #print("this is W_anti",W_anti,len(W_anti))
    W_both=[[] for j in range(len(W))]
    for j in range(len(W)):
        for i in range(len(W[j])):
            W_both[j].append([W[j][i],W_anti[j][i]])
    W_both = list(itertools.product(*W_both))
    sums_possible=[]
    for w in W_both:
        x=[];y=[]
        for t in w:
            x.append(t[0])
            y.append(t[1])
        sums_possible.append([sum(x),sum(y)])
    return sums_possible

# def generators_over_quadratic_field(EL):
#     r"""
#     Find generators of (a finite index subgroup) of the free part of
#     the Mordell--Weil group of the base-change over a quadratic field
#     of an elliptic curve over ``\QQ``.
#     This is essentially the built-in function `gens_quadratic`.

#     INPUT:

#     - ``EL`` -- the base-change over a quadratic field `L` of an elliptic
#       curve over ``\QQ``.

#     OUTPUT:

#     The generators of `EL(L)` modulo torsion. When E has rank `1` over
#     `\QQ` and `2` over `L`, the first point returned generates E(Q);
#     the second one is in  `EL(L)^-`, up to automorphism, provided that E
#     is not isomorphic over Q to the quadratic twist of E by disc(L)
#     (which can only happen if `j=1728 ` and `L=Q(i) `).


#     EXAMPLES:

#         sage: E = EllipticCurve("143a1")
#         sage: L.<a> = QuadraticField(6)
#         sage: generators_over_quadratic_field(E.change_ring(L))
#         [(4 : 6 : 1), (301/150 : 1001/4500*a - 1/2 : 1)]

#     An example with `j`-invariant 1728:

#         sage: E = EllipticCurve("256b1")
#         sage: L.<a> = QuadraticField(-1)
#         sage: EL = E.change_ring(L)
#         sage: generators_over_quadratic_field(EL)
#         [(-1 : 1 : 1), (-1/2*a : -3/4*a - 3/4 : 1)]
#         sage: E.j_invariant()
#         1728

#     An example with extra automorphisms:

#         sage: E = EllipticCurve([0,-4])
#         sage: L.<a> = QuadraticField(-3)
#         sage: EL = E.change_ring(K)
#         sage: gens = generators_over_quadratic_field(EL)
#         sage: gens
#         [(2 : 2 : 1), (-a + 1 : 2*a : 1)]
#         sage: auts = EL.automorphisms()
#         sage: auts[1](gens[1])
#         (-2 : 2*a : 1)
#     """
#     L = EL.base_ring()
#     EE = EL.descend_to(QQ)
    
#     if EE[0] == EL.change_ring(QQ):
#         EQ1 = EE[0]
#         EQ2 = EE[1]
#     else:
#         EQ1 = EE[1]
#         EQ2 = EE[0]
#     iso1 = EQ1.change_ring(L).isomorphism_to(EL)
#     iso2 = EQ2.change_ring(L).isomorphism_to(EL)
#     gens1 = [iso1(P) for P in EQ1.gens()]
#     gens2 = [iso2(P) for P in EQ2.gens()]
#     return gens1 + gens2


# def sorting_fct(L):
#     r"""
#     Return `0` if input has length `2`, `1` otherwise.
#     """
#     if len(L) == 2:
#         return 0
#     else:
#         return 1
    
def cyc_padic_height_francesca(E,P,p,m=20):
    r"""
    Compute the cyclotomic p-adic height for an elliptic curve over an imaginary quadratic number field

    The equation of the curve must be minimal at `p`.

    
    """
    assert isinstance(P, sage.schemes.elliptic_curves.ell_point.EllipticCurvePoint_field), "P is not a point on an elliptic curve."
    
    (prime1,p1,psi1,Fp1),(prime2,p2,psi2,Fp2)=compatible_primes_and_embeddings_and_residue_fields(K,p)
    h=K.class_number()
    
    assert E.conductor().norm()%p!=0, "The prime divides the conductor of the elliptic curve!"
    
    EFp1,EFp2,EQp1,EQp2=find_base_change(E,p1,psi1,p2,psi2)
    
    """Input:an elliptic curve E defined over an imaginary quadratic field K and ordered pairs (p1,psi1),(p2,psi2) where p1,p2 lie over a split rational prime and .
    Output: E_Fp1,E_Fp2,E_Qp1,E_Qp2 where Fp_i,Qp_i are the residue filed and completions at the primes p_1,p_2.
    
    Remark: Use compatible_primes_and_embeddings_and residue_fields to find (p1,psi1),(p2,psi2)
    """
    
    assert E.has_good_reduction(prime1)  and E.has_good_reduction(prime2), "The elliptic curve does not have good reduction above given prime."
    assert EFp1.is_ordinary() and EFp2.is_ordinary(), "The elliptic curve is not ordinary above given prime."
    # FB 28/04 and E.is_ordinary(p), AJ E.has_good_reduction
    #if bernardi == False:
    #    assert E.has_good_reduction(p1) and E.has_good_reduction(p2)
    #if check_hypotheses:
       # if not p.is_prime():
    #        raise ValueError("p = (%s) must be prime"%p)
    #    if p == 2:
    #        raise ValueError("p must be odd")   # todo
    #    if E.conductor() % (p2) == 0:
    #        raise ArithmeticError("p must be a semi-stable prime")

    #prec = int(prec)
    #if prec < 1:
    #    raise ValueError("prec (=%s) must be at least 1" % prec)

    #if self.conductor() % p == 0:
    #    Eq = self.tate_curve(p)
    #    return Eq.padic_height(prec=prec)
    #elif self.ap(p) % p == 0:
    #    
    #lp = self.padic_lseries(p)
    #    return lp.Dp_valued_height(prec=prec)

    # else good ordinary case

    # For notation and definitions, see "Efficient Computation of
    # p-adic Heights", David Harvey (unpublished)
    n=find_n(E,P,p)
    #print("This is n",n)
    nP=n*P
    fn=E.division_polynomial(n)
    #adjusted_prec = prec + 2 * valuation(n, p)   # this is M'
    #R = Integers(p ** adjusted_prec)
    sigma1 = p1adic_sigma_imquad(E, p1, N=20, E2=None, check=False, check_hypotheses=True)
    sigma2 = p1adic_sigma_imquad(E, p2, N=20, E2=None, check=False, check_hypotheses=True)
    #print(fn(P[0]),-nP[0],nP[1])
    s1=psi1(-nP[0]/nP[1])
    s2=psi2(-nP[0]/nP[1])
    #print(s1,s2)
    #print(s1.valuation(),s2.valuation())
    t1= sigma1(s1)
    #/psi1(fn(P[0]))
    t2= sigma2(s2)
    #/psi2(fn(P[0]))
    
    hP2 =  -(log(t1,0) + log(t2,0))/n^2 + non_archimedean_local_height(P, None, p, m)

def non_archimedean_local_height_old(P, v, p, prec, weighted=False, is_minimal=None):
    """r
    Return the local `p`-adic height of `P` at the place `v`.
    This is a modified version of the built-in function `non_archimedean_local_height`:
    the symbolic logarithm (or real logarithm) is replaced by the `p`-adic logarithm.

    INPUT:

    - ``P`` -- a point on an elliptic curve over a number field `K`.

    - ``v`` -- a non-archimedean place of `K`` or `None`.

    - ``p`` -- an odd prime.

    - ``prec`` -- integer. The precision of the computation.

    - ``weighted`` -- boolean. If False (default), the height is
      normalised to be invariant under extension of `K`. If True,
      return this normalised height multiplied by the local degree.

    OUTPUT:

    A p-adic number: the `v`-adic component of the `p`-adic height of `P`
    if `v` is a place; the sum of the components away from `p` of the
    `p`-adic height of `P` if `v` is `None`.
    """
    if v is None:
        D = P.curve().discriminant()
        K = P.curve().base_ring()
        if K is QQ:
            factorD = D.factor()
            if P[0] == 0:
                c = 1
            else:
                c = P[0].denominator()
            # The last sum is for bad primes that divide c where
            # the model is not minimal.

            h = (log(Qp(p, prec)(c))
                 + sum(non_archimedean_local_height(P, q, p, prec, weighted=True, is_minimal=(e < 12))
                       for q,e in factorD if not q.divides(c))
                 + sum(non_archimedean_local_height(P, q, p, prec, weighted=True)
                       - c.valuation(q) * log(Qp(p, prec)(q))
                       for q,e in factorD if e >= 12 and q.divides(c)))
        else:
            factorD = K.factor(D)
            if P[0] == 0:
                c = K.ideal(1)
            else:
                c = K.ideal(P[0]).denominator()
            # The last sum is for bad primes that divide c where
            # the model is not minimal.
            h = (log(Qp(p, prec)(c.norm()))
                 + sum(non_archimedean_local_height_old(P, v, p, prec, weighted=True, is_minimal=(e < 12))
                       for v,e in factorD if not v.divides(c))
                 + sum(non_archimedean_local_height_old(P, v, p, prec, weighted=True)
                       - c.valuation(v) * log(Qp(p, prec)(v.norm()))
                       for v,e in factorD if e >= 12 and v.divides(c)))
            if not weighted:
                h /= K.degree()
        return h

    if is_minimal:
        E = P.curve()
        offset = ZZ.zero()
        Pmin = P
    else:
        E = P.curve().local_minimal_model(v)
        Pmin = P.curve().isomorphism_to(E)(P)
        # Silverman's normalization is not invariant under change of model,
        # but it all cancels out in the global height.
        offset = (P.curve().discriminant()/E.discriminant()).valuation(v)

    a1, a2, a3, a4, a6 = E.a_invariants()
    b2, b4, b6, b8 = E.b_invariants()
    c4 = E.c4()
    x, y = Pmin.xy()
    D = E.discriminant()
    N = D.valuation(v)
    A = (3*x**2 + 2*a2*x + a4 - a1*y).valuation(v)
    B = (2*y+a1*x+a3).valuation(v)
    C = (3*x**4 + b2*x**3 + 3*b4*x**2 + 3*b6*x + b8).valuation(v)
    if A <= 0 or B <= 0:
        r = max(0, -x.valuation(v))
    elif c4.valuation(v) == 0:
        n = min(B, N/2)
        r = -n*(N-n)/N
    elif C >= 3*B:
        r = -2*B/3
    else:
        r = -C/4
    r -= offset/6
    if not r:
        return Qp(p,prec)(0)
    else:
        if E.base_ring() is QQ:
            Nv = Integer(v)
        else:
            Nv = v.norm()
            if not weighted:
                r = r / (v.ramification_index() * v.residue_class_degree())
        return r * log(Qp(p,prec)(Nv))

def cyc_quad_ht2(E,P,p):
    
    """Will find the square root of the denominator paadically instead of factoring since that might be quicker"""
    
    
    assert isinstance(P, sage.schemes.elliptic_curves.ell_point.EllipticCurvePoint_field), "P is not a point on an elliptic curve."

    K=E.base_field()
    OK = K.maximal_order()
    (prime1,p1,psi1,Fp1),(prime2,p2,psi2,Fp2)=compatible_primes_and_embeddings_and_residue_fields(K,p)
    assert E.conductor().norm()%p!=0, "The prime divides the conductor of the elliptic curve!"
    assert(psi1(p1).valuation()>0 and psi2(p2).valuation()>0)
    EFp1,EFp2,EQp1,EQp2=find_base_change(E,p1,psi1,p2,psi2)
    #Fp1.<a1>=K.residue_field(p1)
    #Fp2.<a2>=K.residue_field(p2)
    
    #print(Fp1)
    #EFp1=E.base_ring(Fp1)
    #EFp2=E.base_ring(Fp2)
    assert E.has_good_reduction(p1)  and E.has_good_reduction(p2), "The elliptic curve does not have good reduction above given prime."
    assert EFp1.is_ordinary() and EFp2.is_ordinary(), "The elliptic curve is not ordinary above given prime."
    n=find_n(E,P,p,tam)
    
    
    
    sigma1 = p1adic_sigma_imquad(E, p1, N=20, E2=None, check=False, check_hypotheses=True)
    sigma2 = p1adic_sigma_imquad(E, p2, N=20, E2=None, check=False, check_hypotheses=True)
    
    #adjusted_prec = prec + 2 * valuation(n, p)   # this is M'
    #R = Integers(p ** adjusted_prec)
    
    Q = n*P
    
    #print("here1")
    d = find_denominator_naive(Q)
    #print("here 2")
    d2=psi1(d);d1=psi2(d)
    #print("here 3")
    t=-Q[0]/Q[1]
        
    t1=psi1(t);t2=psi2(t)
    
    #print("here4")    
    cycht=(1/n^2)*(log(t1/d1,0)+log(t2/d2,0))    
    
    return cycht
    
def cyc_quad_ht1(E,P,p):
    r""" Assuming that the base field has class number 1."""

    assert isinstance(P, sage.schemes.elliptic_curves.ell_point.EllipticCurvePoint_field), "P is not a point on an elliptic curve."

    K=E.base_field()

    OK = K.maximal_order()

    (prime1,p1,psi1,Fp1),(prime2,p2,psi2,Fp2)=compatible_primes_and_embeddings_and_residue_fields(K,p)
    assert E.conductor().norm()%p!=0, "The prime divides the conductor of the elliptic curve!"
    assert(psi1(p1).valuation()>0 and psi2(p2).valuation()>0)
    EFp1,EFp2,EQp1,EQp2=find_base_change(E,p1,psi1,p2,psi2)

    assert E.has_good_reduction(p1)  and E.has_good_reduction(p2), "The elliptic curve does not have good reduction above given prime."
    assert EFp1.is_ordinary() and EFp2.is_ordinary(), "The elliptic curve is not ordinary above given prime."
    # FB 28/04 and E.is_ordinary(p), AJ E.has_good_reduction
    #if bernardi == False:
    #    assert E.has_good_reduction(p1) and E.has_good_reduction(p2)
    #if check_hypotheses:
       # if not p.is_prime():
    #        raise ValueError("p = (%s) must be prime"%p)
    #    if p == 2:
    #        raise ValueError("p must be odd")   # todo
    #    if E.conductor() % (p2) == 0:
    #        raise ArithmeticError("p must be a semi-stable prime")

    #prec = int(prec)
    #if prec < 1:
    #    raise ValueError("prec (=%s) must be at least 1" % prec)

    #if self.conductor() % p == 0:
    #    Eq = self.tate_curve(p)
    #    return Eq.padic_height(prec=prec)
    #elif self.ap(p) % p == 0:
    #
    #lp = self.padic_lseries(p)

    #    return lp.Dp_valued_height(prec=prec)

    # else good ordinary case

    # For notation and definitions, see "Efficient Computation of
    # p-adic Heights", David Harvey (unpublished)
    tam = lcm(E.tamagawa_numbers())
    n=find_n(E,P,p) #find n such that n*P always lies in the identity component of the special fibre over p

    sigma1 = p1adic_sigma_imquad(E, p1, N=20, E2=None, check=False, check_hypotheses=True)
    sigma2 = p1adic_sigma_imquad(E, p2, N=20, E2=None, check=False, check_hypotheses=True)

    #adjusted_prec = prec + 2 * valuation(n, p)   # this is M'
    #R = Integers(p ** adjusted_prec)

    Q = tam*P
    d = find_denominator_naive(Q,K)

    if n%2 == 1:
        fn = E.division_polynomial(n) #This probably does nothing
    else:
        fn = E.division_polynomial(n, two_torsion_multiplicity=1)

    if n%2 == 1:
        fn_at_Q = fn(Q[0])
    else:
        fn_at_Q = fn((Q[0], Q[1]))

    d=d^(n^2)*fn_at_Q
    d1=psi1(d);d2=psi2(d)

    E1Q=EQp1([psi1(Q[0]),psi1(Q[1])])
    E2Q=EQp2([psi2(Q[0]),psi2(Q[1])])
    nQ1=n*E1Q
    nQ2=n*E2Q
    #print(nQ1,nQ2)
    t1=-nQ1[0]/nQ1[1];t2=-nQ2[0]/nQ2[1]
    #print(t1==t2)
    #print(sigma1(t1))
    
    cycht=(1/(n*tam)^2)*(log(sigma1(t1)/d1,0)+log(sigma2(t2)/d2,0))    

    return cycht


def cyc_quad_ht3(E,P,p):
    r""" Assuming that the base field has class number 1."""

    assert isinstance(P, sage.schemes.elliptic_curves.ell_point.EllipticCurvePoint_field), "P is not a point on an elliptic curve."

    K=E.base_field()

    OK = K.maximal_order()

    (prime1,p1,psi1,Fp1),(prime2,p2,psi2,Fp2)=compatible_primes_and_embeddings_and_residue_fields(K,p)
    assert E.conductor().norm()%p!=0, "The prime divides the conductor of the elliptic curve!"
    assert(psi1(p1).valuation()>0 and psi2(p2).valuation()>0)
    EFp1,EFp2,EQp1,EQp2=find_base_change(E,p1,psi1,p2,psi2)

    assert E.has_good_reduction(p1)  and E.has_good_reduction(p2), "The elliptic curve does not have good reduction above given prime."
    assert EFp1.is_ordinary() and EFp2.is_ordinary(), "The elliptic curve is not ordinary above given prime."
    # FB 28/04 and E.is_ordinary(p), AJ E.has_good_reduction

    tam = lcm(E.tamagawa_numbers())
    n=find_n(E,P,p) #find n such that n*P always lies in the identity component of the special fibre over p

    sigma1 = p1adic_sigma_imquad(E, p1, N=20, E2=None, check=False, check_hypotheses=True)
    sigma2 = p1adic_sigma_imquad(E, p2, N=20, E2=None, check=False, check_hypotheses=True)

    #adjusted_prec = prec + 2 * valuation(n, p)   # this is M'
    #R = Integers(p ** adjusted_prec)

    Q = tam*P
    d = find_denominator_naive(Q,K)

    if n%2 == 1:
        fn = E.division_polynomial(n) #This probably does nothing
    else:
        fn = E.division_polynomial(n, two_torsion_multiplicity=1)

    if n%2 == 1:
        fn_at_Q = fn(Q[0])
    else:
        fn_at_Q = fn((Q[0], Q[1]))

    d=d^(n^2)*fn_at_Q
    d1=psi1(d);d2=psi2(d)

    E1Q=EQp1([psi1(Q[0]),psi1(Q[1])])
    E2Q=EQp2([psi2(Q[0]),psi2(Q[1])])
    #print(E1Q,E2Q)
    nQ1=n*E1Q
    nQ2=n*E2Q
    #print(nQ1,nQ2)
    t1=-nQ1[0]/nQ1[1];t2=-nQ2[0]/nQ2[1]
    #print(t1==t2)
    #print(sigma1(t1))
    
    cycht=(1/(n*tam)^2)*(log(sigma1(t1)/d1,0)+log(sigma2(t2)/d2,0))    

    return cycht
def cyc_ht_francesca (E,P,p,m):
    assert isinstance(P, sage.schemes.elliptic_curves.ell_point.EllipticCurvePoint_field), "P is not a point on an elliptic curve."
    
    n=find_n(E,P,p)
    #n=19
    #print("This is n",n)
    #n=2*n
    K=E.base_field()

    OK = K.maximal_order()

    (prime1,p1,psi1,Fp1),(prime2,p2,psi2,Fp2)=compatible_primes_and_embeddings_and_residue_fields(K,p)
    EFp1,EFp2,EQp1,EQp2=find_base_change(E,p1,psi1,p2,psi2)
    fn = E.division_polynomial(n, two_torsion_multiplicity=1)
    nP = n*P
    #print("This is nP",n,nP)
    nP1=EQp1(psi1(nP[0]),psi1(nP[1]))
    nP2=EQp2(psi2(nP[0]),psi2(nP[1]))
    #print("these are the embedded points",nP1,nP2)
    fnP = fn(P[0], P[1])

    sigma1 = p1adic_sigma_imquad(E, p1, N=20, E2=None, check=False, check_hypotheses=True)
    sigma2 = p1adic_sigma_imquad(E, p2, N=20, E2=None, check=False, check_hypotheses=True)

    fnP_1 = psi1(fnP)
    fnP_2 = psi2(fnP)

    
    t1=-nP1[0]/nP1[1]
    t2=-nP2[0]/nP2[1]
    #print("this is franfunc nP1,nP2",nP1,nP2)
    #print("this is franfunc sigma", sigma1(t1),sigma2(t2))
    #print("this is franfunc fnP", fnP_1,fnP_2)
    hP =  -(log(sigma1(t1)/fnP_1,0) + log(sigma2(t2)/fnP_2,0))/n^2 + non_archimedean_local_height(P, None, p, m)

    return hP

def find_denominator_padic(P,p,n):
    xP=P[0]

    if xP == 0:
        d_at_P = 1
    else:
        d_at_P = xP.denominator_ideal()
    #print(d_at_P)    
    dP=d_at_P.gens_reduced()[0]    
    #print(dP)
    E=P.scheme()  #P.parent will give the group structure of the elliptic curve not the elliptic curve itself
    K=E.base_field()
    OK=K.maximal_order()
    assert(len(factor(p*OK))==2)

    psi1, psi2 = embeddings(K,p,prec=20)
    d1=psi1(dP);d2=psi2(dP)
    d1=d1.sqrt();d2=d2.sqrt()
    
    return d1,d2
def find_denominator_naive(A,K):
    
    xA=A[0]
    if xA == 0:
        d_at_A = 1
    else:
        d_at_A = K.ideal(xA).denominator()
    #print("found the denominator ideal, going to factor")    
    try:
        d_at_A = prod([a^ZZ(e/2) for (a,e) in factor(d_at_A)]) 
        d_at_A = (d_at_A).gens_reduced()[0]
    except AttributeError:
        d_at_A = prod([a^(e/2) for (a,e) in factor(d_at_A)])
    #print("did the factorisation")    
    return d_at_A    

def find_n(E,P,p):
    
    """" The input is the following:
    
    1)An elliptic curve E over an imaginary quadratic field K
    2)p a prime which splits in  K
    3)P a point on E
    4) The lcm of the tamagawa numbers
    The ouput is an integer n such that nP reduces to the identity on E_p and on bad fibres it reduces to a point on the idenity component
    """
    K=E.base_field()
    (prime1,p1,psi1,Fp1),(prime2,p2,psi2,Fp2)=compatible_primes_and_embeddings_and_residue_fields(K,p)

    EFp1,EFp2,EQp1,EQp2=find_base_change(E,p1,psi1,p2,psi2)
    tam = lcm(E.tamagawa_numbers())
    A=tam*P
    try_orders1 = divisors(EQp1.change_ring(Fp1).cardinality())
    for ord in try_orders1:
        B1=ord*A
        B1 = EQp1(psi1(B1[0]), psi1(B1[1]))
        if B1[1]!=0 : #FB - Modification so that it does't give errors when B1[1]=0 24/11/2017
            tB1 = -B1[0]/B1[1]
            if tB1.valuation() > 0 and B1[0].valuation() < 0 and B1[1].valuation() <0:
                n1 = ord
                break
    try_orders2 = divisors(EQp2.change_ring(Fp2).cardinality())
    for ord in try_orders2:
        B2 = ord*A
        B2= EQp2(psi2(B2[0]),psi2(B2[1]))
        if B2[1]!=0:
            tB2=-B2[0]/B2[1]
            if tB2.valuation() > 0 and B2[0].valuation() < 0 and B2[1].valuation() <0:
                n2 = ord
                break
                
    n = lcm(n1,n2)
    
    return n


def _multiply_point_imquad(E, p, prec, P,R, m):
    
    
    """
    Computes coordinates of a multiple of P with entries in a ring.
    INPUT:
    - ``E`` -- elliptic curve over an imaginary quadratic field with integral
      coefficients
    - ``p``-- a prime which splits in the base field of E.  
    - ``P`` -- a OK point on P that reduces to a
      non-singular point at all primes
    - ``R`` -- a ring in which 2 is invertible (typically
      `\ZZ/L\ZZ` for some positive odd integer
      `L`).
    - ``m`` -- an integer, = 1
    OUTPUT: A triple `(a', b', d')`,(a``,b``,d``) such that if the point
    `mP` has coordinates `(a/d^2, b/d^3)`, then we have
    `a' \equiv a`, `b' \equiv \pm b`,
    `d' \equiv \pm d` all in `R` with respect to both embeddings of E (i.e. modulo
    `L`).
    Note the ambiguity of signs for `b'` and `d'`.
    There's not much one can do about this, but at least one can say
    that the sign for `b'` will match the sign for
    `d'`.
    ALGORITHM: Proposition 9 of "Efficient Computation of p-adic
    Heights" (David Harvey, to appear in LMS JCM).
    Complexity is soft-`O(\log L \log m + \log^2 m)`.
    AUTHORS:
    - David Harvey (2008-01): replaced _DivPolyContext with
      _multiply_point
    EXAMPLES:
    37a has trivial Tamagawa numbers so all points have nonsingular
    reduction at all primes::
        sage: E = EllipticCurve("37a")
        sage: P = E([0, -1]); P
        (0 : -1 : 1)
        sage: 19*P
        (-59997896/67387681 : 88075171080/553185473329 : 1)
        sage: R = Integers(625)
        sage: from sage.schemes.elliptic_curves.padics import _multiply_point
        sage: _multiply_point(E, R, P, 19)
        (229, 170, 541)
        sage: -59997896 % 625
        229
        sage: -88075171080 % 625         # note sign is flipped
        170
        sage: -67387681.sqrt() % 625     # sign is flipped here too
        541
    Trivial cases (:trac:`3632`)::
        sage: _multiply_point(E, R, P, 1)
        (0, 624, 1)
        sage: _multiply_point(E, R, 19*P, 1)
        (229, 455, 84)
        sage: (170 + 455) % 625       # note the sign did not flip here
        0
        sage: (541 + 84) % 625
        0
    Test over a range of `n` for a single curve with fairly
    random coefficients::
        sage: R = Integers(625)
        sage: E = EllipticCurve([4, -11, 17, -8, -10])
        sage: P = E.gens()[0] * LCM(E.tamagawa_numbers())
        sage: from sage.schemes.elliptic_curves.padics import _multiply_point
        sage: Q = P
        sage: for n in range(1, 25):
        ....:      naive = R(Q[0].numerator()), \
        ....:              R(Q[1].numerator()), \
        ....:              R(Q[0].denominator().sqrt())
        ....:      triple = _multiply_point(E, R, P, n)
        ....:      assert (triple[0] == naive[0]) and ( \
        ....:        (triple[1] == naive[1] and triple[2] == naive[2]) or \
        ....:        (triple[1] == -naive[1] and triple[2] == -naive[2])), \
        ....:           "_multiply_point() gave an incorrect answer"
        ....:      Q = Q + P
    """
    assert m >= 1, "m should be a positive integer."
    K= E.base()
    OK = K.maximal_order()
    h=K.class_number()
    
    (prime1,p1,psi1,Fp1), (prime2,p2,psi2,Fp2)=compatible_primes_and_embeddings_and_residue_fields(K,p)
    
    alpha_1 = R(psi1(P1[0].numerator()))
    beta_1 = R(psi1(P1[1].numerator()))
    d_1 = R(psi1(P1[0].denominator().sqrt()))
   
    alpha_2=R(psi2(P2[0].numerator()))
    d_2 = R(psi2(P2[0].denominator().sqrt()))
    beta_2=R(psi2(P2[1].numerator()))
    
    #print(alpha_1,beta_1,d_1,alpha_2,d_2,beta_2)
    
    if m == 1:
        return alpha_1, beta_1, d_1 ,alpha_2,beta_2,d_2

    a1_1 = R(psi1(E.a1())) * d_1
    a3_1 = R(psi1(E.a3())) * d_1**3

    b2_1 = R(psi1(E.b2())) * d_1**2
    b4_1 = R(psi1(E.b4())) * d_1**4
    b6_1 = R(psi1(E.b6())) * d_1**6
    b8_1 = R(psi1(E.b8())) * d_1**8

    B4_1 = 6*alpha_1**2 + b2_1*alpha_1 + b4_1
    B6_1 = 4*alpha_1**3 + b2_1*alpha_1**2 + 2*b4_1*alpha_1 + b6_1
    B6_sqr_1 = B6_1*B6_1
    B8_1 = 3*alpha_1**4 + b2_1*alpha_1**3 + 3*b4_1*alpha_1**2 + 3*b6_1*alpha_1 + b8_1

    T_1 = 2*beta_1 + a1_1*alpha_1 + a3_1

    a1_2 = R(psi1(E.a1())) * d_2
    a3_2 = R(psi1(E.a3())) * d_2**3

    b2_2 = R(psi1(E.b2())) * d_2**2
    b4_2 = R(psi1(E.b4())) * d_2**4
    b6_2 = R(psi1(E.b6())) * d_2**6
    b8_2 = R(psi1(E.b8())) * d_2**8

    B4_2 = 6*alpha_2**2 + b2_2*alpha_2 + b4_2
    B6_2 = 4*alpha_2**3 + b2_2*alpha_2**2 + 2*b4_2*alpha_2 + b6_2
    B6_sqr_2 = B6_2*B6_2
    B8_2 = 3*alpha_2**4 + b2_2*alpha_2**3 + 3*b4_2*alpha_2**2 + 3*b6_2*alpha_2 + b8_2
    print(B8_2,B8_1)
    T_2 = 2*beta_2 + a1_2*alpha_2 + a3_2
         
    # make a list of disjoint intervals [a[i], b[i]) such that we need to
    # compute g(k) for all a[i] <= k <= b[i] for each i
    intervals = []
    interval = (m - 2, m + 3)
    while interval[0] < interval[1]:
        intervals.append(interval)
        interval = max((interval[0] - 3) >> 1, 0), \
                   min((interval[1] + 5) >> 1, interval[0])
    # now walk through list and compute g(k)
    g_1 = {0 : R(0), 1 : R(1), 2 : R(-1), 3 : B8_1, 4 : B6_1**2 - B4_1*B8_1}
    for i in reversed(intervals):
        k = i[0]
        while k < i[1]:
            if k > 4:
                j = k >> 1
                if k & 1:
                    t1_1 = g_1[j]
                    t2_1 = g_1[j+1]
                    prod1_1 = g_1[j+2] * t1_1^3
                    prod2_1 = g_1[j-1] * t2_1^3
                    g_1[k] = prod1_1 - B6_sqr_1 * prod2_1 if j & 1 else B6_sqr_1 * prod1_1 - prod2_1
                else:
                    t1_1 = g_1[j-1]
                    t2_1 = g_1[j+1]
                    g_1[k] = g_1[j] * (g_1[j-2] * t2_1*t2_1 - g_1[j+2] * t1_1*t1_1)
            k = k + 1

    if m & 1:
        psi_m_1 = g_1[m]
        psi_m_m1_1 = g_1[m-1] * T_1
        psi_m_p1_1 = g_1[m+1] * T_1
        
    else:
        psi_m_1 = g_1[m] * T_1
        psi_m_m1_1 = g_1[m-1]
        psi_m_p1_1 = g_1[m+1]

    theta_1 = alpha_1 * psi_m_1 * psi_m_1 - psi_m_m1_1 * psi_m_p1_1
    t1_1 = g_1[m-2] * g_1[m+1] * g_1[m+1] - g_1[m+2] * g_1[m-1] * g_1[m-1]
    if m & 1:
        t1_1 = t1_1 * T_1
    omega_1 = (t1_1 + (a1_1 * theta_1 + a3_1 * psi_m_1 * psi_m_1) * psi_m_1) / -2
    
    g_2 = {0 : R(0), 1 : R(1), 2 : R(-1), 3 : B8_2, 4 : B6_2**2 - B4_2*B8_2}
    for i in reversed(intervals):
        k = i[0]
        while k < i[1]:
            if k > 4:
                j = k >> 1
                if k & 1:
                    t1_2 = g_2[j]
                    t2_2 = g_2[j+1]
                    prod1_2 = g_2[j+2] * t1_2^3
                    prod2_2 = g_2[j-1] * t2_2^3
                    g_2[k] = prod1_2 - B6_sqr_2 * prod2_2 if j & 1 else B6_sqr_2 * prod1_2 - prod2_2
                else:
                    t1_2 = g_2[j-1]
                    t2_2 = g_2[j+1]
                    g_2[k] = g_2[j] * (g_2[j-2] * t2_2*t2_2 - g_2[j+2] * t1_2*t1_2)
            k = k + 1

    if m & 1:
        psi_m_2 = g_2[m]
        psi_m_m1_2 = g_2[m-1] * T_2
        psi_m_p1_2 = g_2[m+1] * T_2
    else:
        psi_m_2 = g_2[m] * T_2
        psi_m_m1_2 = g_2[m-1]
        psi_m_p1_2 = g_2[m+1]

    theta_2 = alpha_2 * psi_m_2 * psi_m_2 - psi_m_m1_2 * psi_m_p1_2
    t1_2 = g_2[m-2] * g_2[m+1] * g_2[m+1] - g_2[m+2] * g_2[m-1] * g_2[m-1]
    if m & 1:
        t1_2 = t1_2 * T_2
    omega_2 = (t1_2 + (a1_2 * theta_2 + a3_2 * psi_m_2 * psi_m_2) * psi_m_2) / -2
    
    return theta_1, omega_1, psi_m_1 * d_1, theta_2, omega_2,psi_m_2*d_2

    

def find_base_change(E,p1,psi1,p2,psi2):
    
    """Input:an elliptic curve E defined over an imaginary quadratic field K and ordered pairs (p1,psi1),(p2,psi2) where p1,p2 lie over a split rational prime and .
    Output: E_Fp1,E_Fp2,E_Qp1,E_Qp2 where Fp_i,Qp_i are the residue filed and completions at the primes p_1,p_2.
    
    Remark: Use compatible_primes_and_embeddings_and residue_fields to find (p1,psi1),(p2,psi2)
    """
    K = E.base_field()
    OK=K.maximal_order()
    Fp1=OK.residue_field(p1)
    Fp2=OK.residue_field(p2)
    
    EQp1=E.change_ring(psi1)
    EQp2=E.change_ring(psi2)
    EFp1=E.change_ring(Fp1)
    EFp2=E.change_ring(Fp2)
    
    return EFp1,EFp2,EQp1,EQp2

"""def find_residue_fields(E,p):
    
    K = E.base_field()
    h = K.class_number()
    OK = K.maximal_order()
    p1, p2 = factor(p*OK)
    
    P1=p1[0]
    P2=p2[0]
    p1 = (p1[0]^h).gens_reduced()[0]
    p2 = (p2[0]^h).gens_reduced()[0]
    
    Fp1=OK.residue_field(p1)
    Fp2=OK.residue_field(p2)
    
    return(Fp1,Fp2)
    """

def compatible_primes_and_embeddings_and_residue_fields(K,p):
    #Need to think about precision sometime...
    """Input: number field K, and a rational prime p which splits in K with class number h.
       Output:(P1,p1,psi1,Fp1) and (P2,p2,psi2,FP2) where prime1, prime2 are primes lying over p, p1,p2 are genrators of P1^h,P2^h and psi1,psi2 are and embeddings K\to K_{p1} and K\to K_{p2} along with residue fields in an ordered tuple"""
    
    OK = K.maximal_order()
    #print(K, 'this is from compatible primes code')
    h=K.class_number()
    #print(factor(p*OK),len(factor(p*OK)), "this is from compatible primes code")
    assert(len(factor(p*OK))==2), " the prime chosen does not split in the chosen number field"
    
    p1, p2 = factor(p*OK)
    prime1=p1[0]
    prime2=p2[0]
    p1 = (prime1^h).gens_reduced()[0]
    p2 = (prime2^h).gens_reduced()[0]
    psi1, psi2 = embeddings(K,p,prec=20)
    
    if psi1(p1).valuation() > 0:
            psi1 = psi1
            psi2 = psi2
            
    else:
            x=psi1
            psi1=psi2
            psi2=x
            
    Fp1=OK.residue_field(p1)
    Fp2=OK.residue_field(p2)
            
    return (prime1,p1,psi1,Fp1), (prime2,p2,psi2,Fp2)
