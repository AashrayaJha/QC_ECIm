r"""
Given an imaginary quadratic field $L$ (of class number 1), and an elliptic curve $E$ such that $E(L)$ has rank $2$,
the code will output the quadratic Chabauty set for integral points of a chosen integral model of $E$.

The main function is `quad_chab_ell_im_quad`.

The code has been built on the code by Francesca Bianchi at 
https://github.com/bianchifrancesca/quadratic_chabauty. The novel features of this code are:

1)It can deal with curves which are not base changes from the rationals.
2)It can deal with curves which have non-trivial contributions at bad places for the anticyclotmic height. 


REFERENCES:

- [BBBM19] \J. S. Balakrishnan, A. Besser, F. Bianchi, J. S. Mueller,
  "Explicit quadratic Chabauty over number fields". To appear in
  "Isr. J. Math.".

- [BcL+16] \J. S. Balakrishnan, M. Ciperiani, J. Lang, B. Mirza, and R. Newton,
  "Shadow lines in the arithmetic of elliptic curves".
  In" Directions in number theory, volume 3".

- [Bia20] Francesca Bianchi, Q(√−3)-Integral Points on a Mordell curve,
   International Congress on Mathematical Software, Springer, 2020, pp. 39–50.


"""


############## MAIN FUNCTION ###############
from sage.schemes.elliptic_curves.weierstrass_morphism import *

def quad_chab_ell_im_quad(E, p, n, double_root_prec, int_list = [], gens=[], up_to_auto = False):
    r"""
    Do quadratic Chabauty for an elliptic curve `E` over
    an imaginary quadratic field `L`.
    INPUT:
    - ``E``  -- An elliptic curve over an imaginary quadratic field $L$, such that rank(E(L))=2
    - ``p`` -- a prime of good, ordinary reduction for `E`, split in `L`.

    - ``n`` -- `p`-adic precision.

    - ``double_root_prec`` -- auxiliary precision used in the solution of
      `2`-variable systems of `2`-equations when these have double roots
      modulo `p`. Cf. the variable `prec1` in `two_variable_padic_system_solver`.

    - ``int_list``(optional) -- a list of known integral points of `E/L`.
      If `double_root_prec` is not large enough to resolve a double root
      in a residue pair containing some point in `int_list`, the resolution
      is attempted with `double_root_prec + 2`. If this does not suffice and
      the given residue pair contains the points `P_1,..,P_m` in
      `int_list`, then the statement "A double root in a disc with the known
      integral points [P_1,..., P_m]" is printed.

    - ``up_to_auto`` -- True/False (default False): If True, the points in the
      output will be up to hyperelliptic involution and reversing.

    OUTPUT: A tuple consisting of

    (1) A list of points in `E(\ZZ)`: the points in the `p`-adic quadratic Chabauty
      output which were recognised as points in `E(\ZZ)`. If one of such points in
      `int_list` is not recovered in the computation, the statement "The following

    (2) A list of points in `E(O_L)`: the points in the `p`-adic quadratic Chabauty
      output which were recognised as points in `E(O_L) \setminus E(\ZZ)`.If one of
      such points in `int_list` is not recovered in the computation, the statement
      "The following integral point was not detected:..." is printed.

    (3) A list of lists. The first two entries of the lists represent points in
      `E(\QQ_p)\times E(\QQ_p)` (modulo a `p`-adic precision dependent on `n` and
      `double_root_prec`):
      the points in the `p`-adic quadratic Chabauty output that were not recognised
      as points in `E(\ZZ)` but which are of the form `(P, P)` for some `P` in `E(\QQ_p)`.
      The third entry of a list gives information on the value of the cyclotomic local
      heights away from `p` for which the given point was recovered. This information is given
      as an integer: the index in the set `W` of possible sums of heights away from `p`
      (The set `W` is printed in the computation.)

    (4) A list of lists. points in `E(\QQ_p)\times E(\QQ_p)` (modulo a `p`-adic precision
      dependent on `n` and `double_root_prec`): all the points in the `p`-adic
      quadratic Chabauty output that are not in the previous three lists.
      As in the previous output item, the index of the corresponding cyclotomic height value
      at bad primes is returned. Note: if a point is recognised as algebraic, it is
      represented as a tuple of minimal polynomials/rational numbers, rather than
      as a point in `E(\QQ_p)\times E(\QQ_p)`.

    (5) An integer: the number of residue pairs for which the computation could not
      establish if the recovered points lift to solutions over `\QQ_p` or if they
      lift uniquely. Note that if this occurs in a disk containing a point in
      `int_list`, the statement "A double root in a disc with the known integral points..."
      is printed during the computation.

   .. NOTE::

      If the `p`-adic precision is too low, some integral points may not be recognised
      as such and will appear in (3) or (4).
    """
    print("This is Quadratic Chabauty for elliptic curves over imaginary quadratic fields")
    L=E.base_field()
    h=L.class_number()
    OL=L.maximal_order()
    (prime1,p1,psi1,Fp1),(prime2,p2,psi2,Fp2)=compatible_primes_and_embeddings_and_residue_fields(L,p)
    try:
        assert not E.rank()>2 and not E.rank()<2, "The rank of the elliptic curve over the imaginary quadratic field should be 2"
    except:
        print("Sage couldn't determine the rank of this curve")
    assert E.conductor().norm()%p!=0, "The chosen prime divides the conductor of the elliptic curve!"

    EFp1,EFp2,EQp1,EQp2=find_base_change(E,p1,psi1,p2,psi2)
    assert E.has_good_reduction(prime1)  and E.has_good_reduction(prime2), "The elliptic curve does not have good reduction above given prime."
    assert EFp1.is_ordinary() and EFp2.is_ordinary(), "The elliptic curve is not ordinary above given prime."

    if up_to_auto == True:
        print ("Note that you have chosen to consider residue disks up to automorphisms and reversing")
        sys.stdout.flush()

    #K = pAdicField(p, n) #probably need idetifcations of Qp1 and Qp2 with this.
    Zpn = Zp(p, prec = n, type = 'fixed-mod', print_mode = 'series')
    _.<x> = PolynomialRing(L)
    Eshort = E.short_weierstrass_model()
    psi = E.isomorphism_to(Eshort)
    psi_inv=Eshort.isomorphism_to(E)
    a4 = Eshort.a4()
    a6 = Eshort.a6()
    [u, rr, s, tt] = psi.tuple()
    print(u,rr,s,tt)
    #embedding is chosen so that p1 is 'pi'

    H = HyperellipticCurve(x^3 + a4*x + a6)

    sigma1 =p1adic_sigma_imquad(E, p1, N=20, E2=None, check=False, check_hypotheses=True)
    sigma2= p1adic_sigma_imquad(E, p2, N=20, E2=None, check=False, check_hypotheses=True)
    val_sigma1 = 0
    val_sigma2 = 0
    #else:
    #    bernardi = True
    #    sigma = bernardi_sigma_function(E, prec=n)
    #    sigma = sigma(E.formal().log(n))
    #    val_sigma = max(sigma[i].denominator().valuation(p) for i in range(sigma.precision_absolute()))
    EshortFp1,EshortFp2,EshortQp1,EshortQp2=find_base_change(Eshort,prime1,psi1,prime2,psi2)

    #Write all the differnt hyperellipitc methods AJ
    HFp1=H.change_ring(Fp1)
    HFp2=H.change_ring(Fp2)
    HQp1=H.change_ring(psi1)
    HQp2=H.change_ring(psi2)
    a4Zp1=Zp(p,n)(psi1(a4)); a6Zp1=Zp(p,n)(psi1(a6))
    a4Zp2=Zp(p,n)(psi2(a4)); a6Zp2=Zp(p,n)(psi2(a6))
    _.<y>=PolynomialRing(Zp(p,n))
    HZp1=HyperellipticCurve(y^3+a4Zp1*y+a6Zp1)
    HZp2=HyperellipticCurve(y^3+a4Zp2*y+a6Zp2)

    EshortFp1,EshortFp2,EshortQp1,EshortQp2=find_base_change(Eshort,p1,psi1,p2,psi2)
    #def p_adic_isomorphism(E,isom,F):
    psiQp1=WeierstrassIsomorphism(EQp1, (psi1(u),psi1(rr),psi1(s),psi1(tt)))
    psiQp2=WeierstrassIsomorphism(EQp2, (psi2(u),psi2(rr),psi2(s),psi2(tt)))

    """#cyclotomic height of P1 (anticyc is 0). Not true, try and incorporate
    h = E.padic_height(p, n)
        hP1 = h(E(P1min))
    else:
        hP1 = height_bernardi(E(P1min), p, n)

    mP = E.Np(p) #replace with number of points on EFp1, EFp2
    #AJ just find cyclotmic and anticyclotomic heights
    fmP = E.division_polynomial(mP, two_torsion_multiplicity=1)
    mPP2 = mP*P2min
    P3min = P2min+P1min
    mPP12 = mP*P3min
    fmPP2 = fmP(P2min[0], P2min[1])
    fmPP12 = fmP(P3min[0], P3min[1])
    sigmamPP2_1 = pAdicField(p,n-val_sigma-2)(sigma(-pAdicField(p,n+5)(embd1(mPP2[0]/mPP2[1]))))
    sigmamPP2_2 = pAdicField(p,n-val_sigma-2)(sigma(-pAdicField(p,n+5)(embd2(mPP2[0]/mPP2[1]))))
    sigmamPP12_1 = pAdicField(p,n-val_sigma-2)(sigma(-pAdicField(p,n+5)(embd1(mPP12[0]/mPP12[1]))))
    sigmamPP12_2 = pAdicField(p,n-val_sigma-2)(sigma(-pAdicField(p,n+5)(embd2(mPP12[0]/mPP12[1]))))
    fmPP2_1 = pAdicField(p,n-val_sigma-2)(embd1(fmPP2))
    fmPP2_2 = pAdicField(p,n-val_sigma-2)(embd2(fmPP2))
    fmPP12_1 = pAdicField(p,n-val_sigma-2)(embd1(fmPP12))
    fmPP12_2 = pAdicField(p,n-val_sigma-2)(embd2(fmPP12))
    try:
        hP2 =  -(log(sigmamPP2_1/fmPP2_1) + log(sigmamPP2_2/fmPP2_2))/mP^2 + non_archimedean_local_height(P2min, None, p, n)
        hP12 =  -(log(sigmamPP12_1/fmPP12_1) + log(sigmamPP12_2/fmPP12_2))/mP^2 +  non_archimedean_local_height(P3min, None, p, n)
    except ValueError:
        print "Sorry, We are currently assuming that the generators of E(L) and their sum are integral at p; minor modifications needed to remove the assumption"
        return "Unknown"
    hP12_anti = anticyc_padic_height(E, P3min, L.discriminant(), p, prec=n, multi=1, bernardi=bernardi)


    #Compute Frobenius data only once:
    M_frob, forms = monsky_washnitzer.matrix_of_frobenius_hyperelliptic(HK)
    forms = [form.change_ring(K) for form in forms]
    M_sys = matrix(K, M_frob).transpose() - 1
    inverse_frob = M_sys**(-1)"""

    #Compute constants alpha_cyc and alpha_anti:



    #P1,P2=generators_over_quadratic_field(E)
    if gens==[]:
        P1,P2=lin_indep_generators(E)
    else:
        P1=gens[0]
        P2=gens[1]
    R1=psi(P1)
    R2=psi(P2)

    #Check reductions make sense
    #assert OL(R1[0].denominator()).valuation(p1) >=0 and OL(R2.denominator()).valuation(p1)>=0 and OL(R1.denominator()).valuation(p2) >=0 and OL(R2.denominator()).valuation(p2)>=0, "The generators have denominators which have bad reduction with respect to primes chosen"
    #print("This is R2",R2)
#print(R1,R2)

    R1Fp1=HFp1(R1)
    R2Fp1=HFp1(R2)

    K1=psi1.codomain()
    K2=psi2.codomain()

    hcycR1=cyc_quad_ht1(E,P1,p)
    hcycR2=cyc_quad_ht1(E,P2,p)

    hcycR1plusR2=cyc_quad_ht1(E,P1+P2,p)
    hcyc=Matrix(3,1,[hcycR1,1/2*(hcycR1plusR2-hcycR1-hcycR2),hcycR2]) #Our normalization is -1 times Francescas
    hcycminus=-1*hcyc
    hanticycR1=anticyc_padic_height(Eshort, R1, p, prec=25, bernardi=False, multi=1,M=25)
    hanticycR2=anticyc_padic_height(Eshort, R2, p, prec=25, bernardi=False, multi=1,M=25)
    hanticycR1plusR2=anticyc_padic_height(Eshort, R1+R2, p, prec=25, bernardi=False, multi=1,M=25)

    hanticyc=Matrix(3,1,[hanticycR1,1/2*(hanticycR1plusR2-hanticycR1-hanticycR2),hanticycR2])

    P11=HQp1(psi1(R1[0]),psi1(R1[1]))
    P21=HQp1(psi1(R2[0]),psi1(R2[1]))

    P12=HQp2(psi2(R1[0]),psi2(R1[1]))
    P22=HQp2(psi2(R2[0]),psi2(R2[1]))

    M1_frob, forms1 = monsky_washnitzer.matrix_of_frobenius_hyperelliptic(HQp1)
    forms1 = [form.change_ring(K1) for form in forms1]
    M1_sys = matrix(K1, M1_frob).transpose() - 1
    inverse_frob1 = M1_sys^(-1)

    M2_frob, forms2 = monsky_washnitzer.matrix_of_frobenius_hyperelliptic(HQp2)
    forms2 = [form.change_ring(K1) for form in forms2]
    M2_sys = matrix(K1, M2_frob).transpose() - 1
    inverse_frob2 = M2_sys^(-1)


    C11 = coleman_integrals_on_basis(HQp1, HQp1(0,1,0), P11, inverse_frob1,forms1)[0] #weird bug here which requires the defining polynomial must have variable x
    C12 = coleman_integrals_on_basis(HQp2, HQp2(0,1,0), P12, inverse_frob2, forms2)[0]#this is not working for E4? #also funny business with Weierstrass points

    C21 = coleman_integrals_on_basis(HQp1, HQp1(0,1,0), P21, inverse_frob1,forms1)[0]
    C22 = coleman_integrals_on_basis(HQp2, HQp2(0,1,0), P22, inverse_frob2, forms2)[0]

    M= Matrix(3,3,[[C11^2,C11*C12,C12^2],[C11*C21,1/2*(C12*C21+C11*C22), C12*C22],[C21^2,C21*C22,C22^2]])

    cycalphas= M^(-1)*hcyc
    antialphas= M^(-1)*hanticyc

    alphas_cyc= [-cycalphas[i][0] for i in range(3)]  #Normalising right now to match Francesca's code
    alphas_anti=[antialphas[i][0] for i in range(3)]  #had the same normalisation for anti
    print("Found alphas")
    #print(alphas_cyc,alphas_anti)


    #print("found alphas")
    #the residue pairs we need to consider:
    PointsModp1 = list(HFp1.points())
    PointsModp2 = list(HFp2.points())
    classes_to_consider = [Q for Q in itertools.product(PointsModp1, PointsModp2)]
    #print(classes_to_consider)
    #if up_to_auto == False:
    #    classes_to_consider = classes_to_consider_0
    #else:
    #    classes_to_consider = []
    #    for Q in classes_to_consider_0:
    #        Qaut = (Hp(Q[0][0], -Q[0][1], Q[0][2]), Hp(Q[1][0], -Q[1][1], Q[1][2]))
    #        Qrev = (Q[1], Q[0])
    #        if Qaut in classes_to_consider or Qrev in classes_to_consider:
    #            continue
    #        classes_to_consider.append(Q)
    #Finding the orders of points mod p on both reductions.
    #Classes to consider are the same
    OrderPointsPairs = []
    OrderPoints2 = []
    for Q in classes_to_consider:
        Q1 = Q[0]
        Q2 = Q[1]
        mQ1 = EshortFp1(Q1).order()
        mQ2 = EshortFp2(Q2).order()
        OrderPointsPairs.append([mQ1,mQ2])
        OrderPoints2.append(mQ1)
        OrderPoints2.append(mQ2)
    OrderPoints = list(Set(OrderPoints2))

    #making a list of division polynomials to multilpy later to get the points in the right neighbourhood to use the Coleman-Gross sigma functions for heights.

    OrderDivPoly = [[0, 0] for i in range(len(OrderPointsPairs))]
    for mQ in OrderPoints:
        if mQ%2 != 0:
            fmQ = E.division_polynomial(mQ)
        else:
            fmQ = E.division_polynomial(mQ, two_torsion_multiplicity=1)
        for i in range(len(OrderPointsPairs)):
            if OrderPointsPairs[i][0] == mQ:
                OrderDivPoly[i][0] = fmQ
            if OrderPointsPairs[i][1] == mQ:
                OrderDivPoly[i][1] = fmQ

    number_Fp1_points = len(HFp1.points())
    number_Fp2_points = len(HFp2.points())

    W = local_heights_at_bad_primes_number_field(E, L, p)
    print ("W is", W)

    int_list_new = []
    int_list_new_embedded = []
    base_points = []
    #int_pts are the same but when it appends to base points here it changes sign??

    for int_pt in int_list:
        int_pt = E(int_pt[0], int_pt[1])
        bad_height_int_pt,bad_height_int_pt_anti = non_archimedean_local_height(int_pt, None, p, n)
        ind_W=W.index([2*bad_height_int_pt,2*bad_height_int_pt_anti])
        ind_W_anti=ind_W
        int_pt_1 = EQp1(psi1(int_pt[0]), psi1(int_pt[1]))
        int_pt_2 = EQp2(psi2(int_pt[0]), psi2(int_pt[1]))
        int_pt_1_short = psiQp1(int_pt_1)
        int_pt_2_short = psiQp2(int_pt_2)
        int_mod_p = (HFp1(int_pt_1_short[0]%p, int_pt_1_short[1]%p), HFp2(int_pt_2_short[0]%p, int_pt_2_short[1]%p))

        if int_mod_p in base_points:
            int_list_new[base_points.index(int_mod_p)].append(int_pt)
            int_list_new_embedded[base_points.index(int_mod_p)].append([int_pt_1, int_pt_2, ind_W])
        else:
            int_list_new.append([int_pt])
            int_list_new_embedded.append([[int_pt_1, int_pt_2, ind_W]])
            base_points.append(int_mod_p)
        #base_points picks up all the known points and finds their mod p rperesentations.
    points = []
    integral_points_L = []
    extra_points_Q = []
    extra_points_non_Q = []
    points_new = []
    integral_points_Q = []
    integral_points_L = []
    extra_points_Q = []
    extra_points_non_Q = []
    double_root_count = 0
    actual_double_root_count = 0

    S1.<t1> = PowerSeriesRing(K1,default_prec=n+2)
    S2.<t2> = PowerSeriesRing(K2,default_prec=n+2)
    coeff1=K1.gen()/(S1.gen().coefficients()[0])
    coeff2=K2.gen()/(S2.gen().coefficients()[0])
    psit1=K1.hom(coeff1,FractionField(S1))
    psit2=K2.hom(coeff2,FractionField(S2))
    psit1=psit1*psi1
    psit2=psit2*psi2
    print("Total classes to consider is",len(classes_to_consider))

    for Q in classes_to_consider:
        #print(classes_to_consider.index(Q))
        x+=1
        Q1 = Q[0]
        Q2 = Q[1]
        if Q1[2] == 0 or Q2[2] == 0:
                continue
        par_rat = 0
        new_points_disc = []
        if Q in base_points:
            par_rat = 1
            ind_bp = base_points.index(Q)


        indexQ = classes_to_consider.index(Q)
        if indexQ%20==0:
            print("done with ",indexQ, " classes")
        m1 = OrderPointsPairs[indexQ][0]
        m2 = OrderPointsPairs[indexQ][1]
        fm1 = OrderDivPoly[indexQ][0]
        fm2 = OrderDivPoly[indexQ][1]
        R1 = Q_lift(HQp1, Q1, p)
        R2 = Q_lift(HQp2, Q2, p)
        R1Zp = HZp1(R1)
        R2Zp = HZp2(R2)

        xR1, yR1 =  HZp1.local_coord(R1Zp, prec=n+2)
        xR1 = S1(xR1)
        yR1 = S1(yR1)
        dx1 = xR1.derivative()
        const_term1 = coleman_integrals_on_basis(HQp1, HQp1(0,1,0), R1, inverse_frob1, forms1)[0]
        log_nearR1 = S1((dx1/(2*yR1)).integral() + const_term1)
        log_nearR1 = S1(log_nearR1(p*t1))
        xR1new = S1(xR1(p*t1))
        yR1new = S1(yR1(p*t1))
        Eloc1=E.change_ring(psit1)
        Elocshort1 = Eshort.change_ring(psit1)
        xR1E = psi1(u^2)*xR1new + psi1(rr)
        yR1E = psi1(u^3)*yR1new + psi1(s*u^2)*xR1new + psi1(tt)
        xR2, yR2 =  HZp2.local_coord(R2Zp, prec=n+2)
        xR2 = S2(xR2)
        yR2 = S2(yR2)
        dx2 = xR2.derivative()
        const_term2 = coleman_integrals_on_basis(HQp2, HQp2(0,1,0), R2, inverse_frob2, forms2)[0]
        log_nearR2 = S2((dx2/(2*yR2)).integral() + const_term2)
        log_nearR2 = S2(log_nearR2(p*t2))
        xR2new = S2(xR2(p*t2))
        yR2new = S2(yR2(p*t2))
        Eloc2 = E.change_ring(psit2) #the other elliptic curve
        Elocshort2 = Eshort.change_ring(psit2) #short weierstrass
        xR2E = psi2(u^2)*xR2new + psi2(rr)
        yR2E = psi2(u^3)*yR2new + psi2(s*u^2)*xR2new + psi2(tt)

        try:
            PointaroundR1 = Eloc1(xR1E, yR1E)
        except:
            print("problem with Q for 1", Q)
            return (xR1E,yR1E,Eloc1),(xR2E,yR2E,Eloc2)
        try:
            PointaroundR2 = Eloc2(xR2E, yR2E)
        except:
            print("problem with Q for 2", Q)
            return (xR1E,yR1E,Eloc1),(xR2E,yR2E,Eloc2)

        mxR1yR1 = m1*PointaroundR1
        mxR2yR2 = m2*PointaroundR2
        sigma_nearmR1 = sigma1.truncate(n)((-mxR1yR1[0]/mxR1yR1[1]).power_series())
        sigma_nearmR2 = sigma2.truncate(n)((-mxR2yR2[0]/mxR2yR2[1]).power_series())
        fm1=fm1.change_ring(psi1)
        fm2=fm2.change_ring(psi2)
        if m1%2 != 0:
            fm1_nearR = fm1(xR1E)
        else:
            fm1_nearR = fm1(xR1E,yR1E)
        if m2%2 != 0:
            fm2_nearR = fm2(xR2E)
        else:
            fm2_nearR = fm2(xR2E,yR2E)
        sigmaoverfm_near1 = sigma_nearmR1/fm1_nearR
        sigmaoverfm_near2 = sigma_nearmR2/fm2_nearR
        h_nearR_1 = -2*((sigmaoverfm_near1/sigmaoverfm_near1[0]).log(prec=n) + sigmaoverfm_near1[0].log())/m1^2
        h_nearR_2 = -2*((sigmaoverfm_near2/sigmaoverfm_near2[0]).log(prec=n) + sigmaoverfm_near2[0].log())/m2^2

        two_variable.<t1,t2> = PowerSeriesRing(h_nearR_1[0].parent())
        h0 = (1/2)*(h_nearR_1(t1) + h_nearR_2(t2))
        f0 =  h0 - alphas_cyc[0]*log_nearR1(t1)^2 - alphas_cyc[1]*log_nearR1(t1)*log_nearR2(t2) - alphas_cyc[2]*log_nearR2(t2)^2

        h_anti = (1/2)*(h_nearR_1(t1) - h_nearR_2(t2))
        f1 = h_anti - alphas_anti[0]*log_nearR1(t1)^2  - alphas_anti[1]*log_nearR1(t1)*log_nearR2(t2)-alphas_anti[2]*log_nearR2(t2)^2

        min_deg = min(h_nearR_1.truncate().degree(), h_nearR_2.truncate().degree())
        for w in W:
            f=f0+w[0]/2
            f_anti=f1+w[1]/2
            PolRing.<T1,T2> = PolynomialRing(f[0][0].constant_coefficient().parent())
            coeffsh1 = f.coefficients()
            coeffsh2 = f_anti.coefficients()
            polh1 = PolRing(sum(T1^(k.exponents()[0][0])*T2^(k.exponents()[0][1])*v for (k,v) in coeffsh1.items()))
            polh2 = PolRing(sum(T1^(k.exponents()[0][0])*T2^(k.exponents()[0][1])*v for (k,v) in coeffsh2.items()))
            vpolh1 = min([i[0].valuation() for i in list(polh1)])
            vpolh2 = min([i[0].valuation() for i in list(polh2)])
            commonroots, doubleroots = hensel_lift_n([p^(-vpolh1)*polh1, p^(-vpolh2)*polh2], p, min(n-7, min_deg - 3))
            if doubleroots > 0:
                double_root_count += 1
                commonroots, test = two_variable_padic_system_solver(p^(-vpolh1)*polh1, p^(-vpolh2)*polh2, p, double_root_prec, min(n-7, min_deg - 3))
                if par_rat == 1 and test>0:
                    commonroots,test = two_variable_padic_system_solver(p^(-vpolh1)*polh1, p^(-vpolh2)*polh2, p, double_root_prec+2, min(n-7, min_deg - 3))
                roots = [[p*r[0],p*r[1]] for r in commonroots if r[0].valuation(p) >= 0 and r[1].valuation(p) >= 0]
                if test > 0:
                    print ("test>0 for", Q)
                    sys.stdout.flush()
                    actual_double_root_count += 1
                    if par_rat == 1:
                        print ("A double root in a disc with the known integral points", int_list_new[ind_bp])
                        sys.stdout.flush()
            else:
                roots = [[p*r[0,0], p*r[1,0]] for r in commonroots if r[0,0].valuation(p)>= 0 and r[1,0].valuation(p)>=0]
            new_points = [[HQp1(xR1(K1(sage_eval('%s'%t0[0]))),yR1(K1(sage_eval('%s'%t0[0])))), HQp2(xR2(K2(sage_eval('%s'%t0[1]))),yR2(K2(sage_eval('%s'%t0[1])))), W.index(w)] for t0 in roots]

            new_points = [[EQp1(psi1(u^2)*QP[0][0] + psi1(rr), psi1(u^3)*QP[0][1] + psi1(s*u^2)*QP[0][0] + psi1(tt)), EQp2(psi2(u^2)*QP[1][0] + psi2(rr), psi2(u^3)*QP[1][1] + psi2(s*u^2)*QP[1][0] + psi2(tt)), W.index(w)] for QP in new_points]
            new_points_disc.extend(new_points)
        if par_rat == 1:
            for QP in int_list_new_embedded[ind_bp]:
                ind_QP = int_list_new_embedded[ind_bp].index(QP)
                if QP not in new_points_disc:
                    print ("The following integral point was not detected:", int_list_new[ind_bp][ind_QP])
                    continue
                QP_rat = int_list_new[ind_bp][ind_QP]
            if QP_rat[0] in QQ and QP_rat[1] in QQ:
                integral_points_Q.append(QP_rat)
            else:
                integral_points_L.append(QP_rat)
            new_points_disc.remove(QP)
        points.extend(new_points_disc)
    for A in points:
        if QQ(A[0][0]) == QQ(A[1][0]) and QQ(A[0][1]) == QQ(A[1][1]):
            try:
                NRP = E.lift_x(QQ(A[0][0]))
                if NRP[1] - A[0][1] == 0 and NRP[1] - A[1][1] == 0:
                    integral_points_Q.append(NRP)
                else:
                    NRP = -E(NRP[0],NRP[1])
                    if NRP[1] - A[0][1] == 0 and NRP[1] - A[1][1] == 0:
                        integral_points_Q.append(NRP)
                    else:
                        extra_points_Q.append(A)
            except ValueError:
                try:
                    NRP = E.lift_x(-QQ(-A[0][0]))
                    if NRP[1] - A[0][1] == 0 and NRP[1] - A[1][1] == 0:
                        integral_points_Q.append(NRP)
                    else:
                        NRP = -E(NRP[0],NRP[1])
                        if NRP[1] - A[0][1] == 0 and NRP[1] - A[1][1] == 0:
                            integral_points_Q.append(NRP)
                        else:
                            extra_points_Q.append(A)


                except ValueError:
                    extra_points_Q.append(A)

        else:
            points_new.append(A)

    print("solved for points")
    if points_new != []:
        for A in points_new:
            p2 = algdep(A[0][1], 2)
            p1 = algdep(A[0][0], 2)
            p22 = algdep(A[1][1], 2)
            p12 = algdep(A[1][0], 2)
            if p22 == p2 and p1 == p12:
                Lf.<par> = NumberField(p2)
                if Lf.discriminant() == L.discriminant():
                    Lf = L
                if p1.degree() == 1:
                    try:
                        NPnotQ = E.change_ring(Lf).lift_x(QQ(A[0][0])) #For consistency with embeddings, enough to check that the y-coordinates are different
                        if p2(NPnotQ[1]) == 0 or p2((-NPnotQ)[1]) == 0:
                            if A[0][1] != A[1][1]:
                                if Lf.discriminant() == L.discriminant():
                                    if p2(NPnotQ[1]) == 0 and NPnotQ not in integral_points_L: #last condition to avoid cases where E:y^2=f(x) so if x_0\in Q then y_0^2\in Q so minpoly of y_0 same as of -y_0
                                        integral_points_L.append(NPnotQ)
                                    else:
                                        integral_points_L.append(-NPnotQ)
                                else:
                                    extra_points_non_Q.append([(QQ(A[0][0]), p2),  A[2]])
                            else:
                                extra_points_non_Q.append(A)
                        else:
                            extra_points_non_Q.append(A)
                    except ValueError:
                        extra_points_non_Q.append(A)
                else:
                    if A[0][0] == A[1][0]: #the x-coordinates better be different or they're the image under the same embedding
                        extra_points_non_Q.append(A)
                        continue
                    Lf.<par> = NumberField(p1)
                    if Lf.discriminant() == L.discriminant():
                        Lf = L
                        par = PolynomialRing(L,"x")(p1).roots()[0][0]
                    try:
                        ELf = E.change_ring(Lf)
                        NPnotQ = ELf.lift_x(par)
                        if p2(NPnotQ[1]) == 0 or p2((-NPnotQ)[1]) == 0:
                            if p2.degree() == 1:
                                if Lf.discriminant() == L.discriminant():
                                    if (psi1(par) - A[0][0]).valuation() < min(n, A[0][0].precision_absolute()) :
                                        par = PolynomialRing(L,"x")(p1).roots()[1][0]
                                    if p2(NPnotQ[1])== 0:
                                        integral_points_L.append(ELf(par, NPnotQ[1]))
                                    else:
                                        integral_points_L.append(ELf(par, (-NPnotQ)[1]))
                                else:
                                    extra_points_non_Q.append([(p1, QQ(A[0][1])), A[2]])
                            else:
                                embdsf = embeddings(Lf, p, n)
                                embd1f = embdsf[0]
                                embd2f = embdsf[1]
                                if (embd1f(par) - A[0][0]).valuation(p) >= min(n, A[0][0].precision_absolute()):
                                    embd = embd1f
                                    if (embd1f(NPnotQ[1]) - A[0][1]).valuation(p) >= min(n, A[0][1].precision_absolute()):
                                        if (embd2f(NPnotQ[1]) - A[1][1]).valuation(p) < min(n, A[1][1].precision_absolute()):
                                            extra_points_non_Q.append(A)
                                            continue

                                    elif (embd1f((-NPnotQ)[1]) - A[0][1]).valuation(p) >= min(n, A[0][1].precision_absolute()):
                                        if (embd2f((-NPnotQ)[1]) - A[1][1]).valuation(p) < min(n, A[1][1].precision_absolute()):
                                            extra_points_non_Q.append(A)
                                            continue
                                    else:
                                        extra_points_non_Q.append(A)
                                        continue
                                elif (embd2f(par) - A[0][0]).valuation(p) >= min(n, A[0][0].precision_absolute()):
                                    embd = embd2f
                                    if (embd2f(NPnotQ[1]) - A[0][1]).valuation(p) >= min(n, A[0][1].precision_absolute()):
                                        if (embd1f(NPnotQ[1]) - A[1][1]).valuation(p) < min(n, A[1][1].precision_absolute()):
                                            extra_points_non_Q.append(A)
                                            continue
                                    elif (embd2f((-NPnotQ)[1]) - A[0][1]).valuation(p) >= min(n, A[0][1].precision_absolute()):
                                        if (embd1f((-NPnotQ)[1]) - A[1][1]).valuation(p) < min(n, A[1][1].precision_absolute()):
                                            extra_points_non_Q.append(A)
                                            continue
                                    else:
                                        extra_points_non_Q.append(A)
                                        continue
                                else:
                                    extra_points_non_Q.append(A)
                                    continue
                                if Lf.discriminant() == L.discriminant():
                                    if embd(par) == psi2(par):
                                        par = PolynomialRing(L, "x")(p1).roots()[1][0]
                                        NPnotQ = ELf.lift_x(par)
                                    if psi1(NPnotQ[1]) == A[0][1]:
                                        integral_points_L.append(NPnotQ)
                                    else:
                                        integral_points_L.append(-NPnotQ)
                                else:
                                    extra_points_non_Q.append([(p1, p2), A[2]])
                        else:
                            extra_points_non_Q.append(A)
                    except ValueError:
                        extra_points_non_Q.append(A)
            else:
                extra_points_non_Q.append(A)

    extra_points_non_Q.sort(key=sorting_fct)

    return  integral_points_Q, integral_points_L, extra_points_Q, extra_points_non_Q, actual_double_root_count
