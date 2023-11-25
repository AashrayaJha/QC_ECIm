def find_alphas(E,p):

    K=E.base_field()
    (prime1,_,psi1,Fp1),(prime2,_,psi2,Fp2)=compatible_primes_and_embeddings_and_residue_fields(K,p)

    _.<t1>=PolynomialRing(Fp1)
    _.<t2>=PolynomialRing(Fp2)

    #P1,P2=generators_over_quadratic_field(E)
    P1,P2=lin_indep_generators(E)
    
    Eshort=E.short_weierstrass_model()
    EFp1,EFp2,EQp1,EQp2=find_base_change(Eshort,prime1,psi1,prime2,psi2)

    psi=E.isomorphism_to(Eshort); psi_inv=Eshort.isomorphism_to(E)

    a4=Eshort.a4()
    a6=Eshort.a6()
    HFp1 = HyperellipticCurve(t1^3+EFp1.a4()*t1+EFp1.a6())
    HFp2 = HyperellipticCurve(t2^3+EFp2.a4()*t2+EFp2.a6())

    H1 = HyperellipticCurve(x^3+psi1(a4)*x+psi1(a6))
    H2 = HyperellipticCurve(x^3+psi2(a4)*x+psi2(a6))

    R1=psi(P1)
    R2=psi(P2)

    #print(R1,R2)
    R1Fp1=HFp1(R1)
    R2Fp1=HFp1(R2)

    R1,R2=finding_nonWeierstrass_pts(R1,R2,EFp1,EFp2)
    R3=R1+R2

    print(R1,R2,R3)

    K1=psi1.codomain()
    K2=psi2.codomain()
    #print("computed here")
    #print(parent(P1))
    hcycR1=cyc_quad_ht1(E,P1,p)
    hcycR2=cyc_quad_ht1(E,P2,p)
    #print("computed again here")
    hcycR1plusR2=cyc_quad_ht1(E,P1+P2,p)
    #print("computed here??")
    hcyc=Matrix(3,1,[hcycR1,1/2*(hcycR1plusR2-hcycR1-hcycR2),hcycR2]) #Our normalization is -1 times Francescas
    
    hcycminus=-1*hcyc
    #print("This is the cyclotomic height",hcyc)
    #print(parent(R1))
    hanticycR1=anticyc_padic_height(Eshort, R1, p, prec=25, bernardi=False, multi=1,M=25)
    hanticycR2=anticyc_padic_height(Eshort, R2, p, prec=25, bernardi=False, multi=1,M=25)
    hanticycR1plusR2=anticyc_padic_height(Eshort, R1+R2, p, prec=25, bernardi=False, multi=1,M=25)

    hanticyc=Matrix(3,1,[hanticycR1,1/2*(hanticycR1plusR2-hanticycR1-hanticycR2),hanticycR2])
    #print("This is the anticyclotomic height",hanticyc)

    P11=H1(psi1(R1[0]),psi1(R1[1]))
    P21=H1(psi1(R2[0]),psi1(R2[1]))
    P31=H1(psi1(R3[0]),psi1(R3[1]))

    P12=H2(psi2(R1[0]),psi2(R1[1]))
    P22=H2(psi2(R2[0]),psi2(R2[1]))
    P32=H2(psi2(R3[0]),psi2(R3[1])) #why is P21 (0,0,1) mod 5... This was an error in the point I was looking at.

    M1_frob, forms1 = monsky_washnitzer.matrix_of_frobenius_hyperelliptic(H1)

    forms1 = [form.change_ring(K1) for form in forms1]
    M1_sys = matrix(K1, M1_frob).transpose() - 1
    inverse_frob1 = M1_sys^(-1)

    M2_frob, forms2 = monsky_washnitzer.matrix_of_frobenius_hyperelliptic(H2)
    forms2 = [form.change_ring(K1) for form in forms2]
    M2_sys = matrix(K1, M2_frob).transpose() - 1
    inverse_frob2 = M2_sys^(-1)
    #print(inverse_frob2,inverse_frob1)
    #print("These are the points on the completions of the curve", P21)
    #print("This is the frobenius of point 2", H1.frobenius(P12))
    #print("This is the frobenius of point 5",H2.frobenius(P22))
    #print("This is the frobenius of point 4",H2.frobenius(P21))
    #print("This is the frobenius of point 6",H2.frobenius(P23))
    #print("This is the frobenius of point 3",H1.frobenius(P13))
    #print("This is the frobenius of the first point", H1.frobenius(P11))

    C11 = coleman_integrals_on_basis(H1, H1(0,1,0), P11, inverse_frob1,forms1)[0] #weird bug here which requires the defining polynomial must have variable x
    C12 = coleman_integrals_on_basis(H2, H2(0,1,0), P12, inverse_frob2, forms2)[0]#this is not working for E4? #also funny business with Weierstrass points

    C21 = coleman_integrals_on_basis(H1, H1(0,1,0), P21, inverse_frob1,forms1)[0]
    C22 = coleman_integrals_on_basis(H2, H2(0,1,0), P22, inverse_frob2, forms2)[0]

    C31 = coleman_integrals_on_basis(H1, H1(0,1,0), P31, inverse_frob1,forms1)[0]
    C32 = coleman_integrals_on_basis(H2, H2(0,1,0), P32, inverse_frob2, forms2)[0] #precision error for E6

    M= Matrix(3,3,[[C11^2,C11*C12,C12^2],[C11*C21,1/2*(C12*C21+C11*C22), C12*C22],[C21^2,C21*C22,C22^2]])
    #print("These are the cyclotomic heights", hcyc)
    #print("these are the anticyc heights",hanticyc)
    #print("These are the points", R1,R2)
    #print("these are the coleman integrals", C11,C12,C21,C22,C31,C32)
    cycalpha= M^(-1)*hcyc
    antialpha= M^(-1)*hanticyc

    return cycalpha,antialpha
