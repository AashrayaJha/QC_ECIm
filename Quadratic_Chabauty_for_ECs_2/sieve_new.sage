r""" Generalises the sieve done for the Mordell curve y^2=x^3-4 by Francesca Bianchi at
https://github.com/bianchifrancesca/quadratic_chabauty. The novel features of this code are: 

1)It can deal with any curve E/K given two quadratic Chabauty sets and a particular condition 
on the cardinalities as described in section 4 of https://arxiv.org/pdf/2311.01691.pdf.

"""

def reduction_information_0(E,extra_points_p,q,gens=[]):
    
    """This code will work if the bigger prime for the sieve is greater than equal to 9. For smaller primes,
    one might need to do an analysis under some circumstances."""
    
    L=E.base_ring()
    p = extra_points_p[0][0].base_ring().residue_characteristic()
    (prime1,p1,psi1,Fp1),(prime2,p2,psi2,Fp2)=compatible_primes_and_embeddings_and_residue_fields(L,p)
    EFp1,EFp2,EQp1,EQp2=find_base_change(E,p1,psi1,p2,psi2)
    K1=psi1.codomain()
    K2=psi2.codomain()
    print(EFp1.abelian_group(),EFp2.abelian_group())
    if gens==[]:
        P1,P2=lin_indep_generators(E)
    else:
        P1,P2=gens

    P1Fp1 = EFp1(P1)
    P1Fp2 = EFp2(P1)
    P2Fp1 = EFp1(P2)
    P2Fp2 = EFp2(P2)
    coeffs_mod_Np = [[] for i in range(len(extra_points_p))]
    ord_1 = lcm(P1Fp1.order(), P1Fp2.order())
    ord_2 = lcm(P2Fp1.order(), P2Fp2.order())

    for i in range(len(extra_points_p)):
        P = extra_points_p[i]
        Q1 = EFp1(P[0][0], P[0][1])
        Q2 = EFp2(P[1][0], P[1][1])
        if EFp1.cardinality()==EFp2.cardinality():
            if EFp1.cardinality()==EFp2.cardinality():
                for n in range(ord_1):
                    for m in range(ord_2):
                        if n*P1Fp2 + m*P2Fp2 == Q2 and n*P1Fp1+m*P2Fp1==Q1:
                            x=[n%q,m%q]
                            if x not in coeffs_mod_Np[i] and len(coeffs_mod_Np[i])<q:
                                coeffs_mod_Np[i].append(x) #n is modulo ord_1, m is modulo ord_2
        elif EFp1.cardinality()%q==0 and EFp2.cardinality()%q==0:
            for n in range(ord_1):
                    for m in range(ord_2):
                        values_for_EFp1=[]
                        values_for_EFp2=[]
                        if n*P1Fp1 + m*P2Fp1 == Q1:
                            x=[n%q,m%q]
                            if x not in values_for_EFp2 and len(values_for_EFp2)<q:
                                values_for_EFp1.append(x)
                        if n*P1Fp2 + m*P2Fp2 == Q2:
                            x=[n%q,m%q]
                            if x not in values_for_EFp2 and len(values_for_EFp2)<q:
                                values_for_EFp2.append([n%q,m%q])
                        coeffs_mod_Np[i]=[x for x in values_for_EFp1 if x in values_for_EFp2]

        elif EFp1.cardinality()%q==0:
            for n in range(P1Fp1.order()):
                for m in range(P2Fp1.order()):
                    if n*P1Fp1+m*P2Fp1==Q1:
                            x=[n%q,m%q]
                            if x not in coeffs_mod_Np[i] and len(coeffs_mod_Np[i])<q:
                                coeffs_mod_Np[i].append(x)
        else:
            for n in range(P1Fp2.order()):
                for m in range(P2Fp2.order()):
                    if n*P1Fp2+m*P2Fp2==Q2:
                            x=[n%q,m%q]
                            if x not in coeffs_mod_Np[i] and len(coeffs_mod_Np[i])<q:
                                coeffs_mod_Np[i].append(x)
    return coeffs_mod_Np

def log_information(E,extra_points_p,gens=[],d=1):
        L=E.base_ring()
        p = extra_points_p[0][0].base_ring().residue_characteristic()
        (prime1,p1,psi1,Fp1),(prime2,p2,psi2,Fp2)=compatible_primes_and_embeddings_and_residue_fields(L,p)
        EFp1,EFp2,EQp1,EQp2=find_base_change(E,p1,psi1,p2,psi2)
        K1=psi1.codomain()
        K2=psi2.codomain()

        if gens==[]:
            P1,P2=lin_indep_generators(E)
        else:
            P1,P2=gens

        new_list_points_p = []
        new_list_coeffs_mod_Np = []

        _.<x> = PolynomialRing(L)

        Eshort = E.short_weierstrass_model()
        psi=E.isomorphism_to(Eshort)
        [u, rr, s, tt] = psi.tuple()
        a4 = Eshort.a4()
        a6 = Eshort.a6()
        H = HyperellipticCurve(x^3 + a4*x + a6)
        HQp1=H.change_ring(psi1)
        HQp2=H.change_ring(psi2)
        psiQp1=WeierstrassIsomorphism(EQp1, (psi1(u),psi1(rr),psi1(s),psi1(tt)))
        psiQp2=WeierstrassIsomorphism(EQp2, (psi2(u),psi2(rr),psi2(s),psi2(tt)))

        for i in range(len(extra_points_p)):
                P=[psiQp1(extra_points_p[i][0]),psiQp2(extra_points_p[i][1])]
                new_list_points_p.append(P)


        M1_frob, forms1 = monsky_washnitzer.matrix_of_frobenius_hyperelliptic(HQp1)
        forms1 = [form.change_ring(K1) for form in forms1]
        M1_sys = matrix(K1, M1_frob).transpose() - 1
        inverse_frob1 = M1_sys^(-1)

        M2_frob, forms2 = monsky_washnitzer.matrix_of_frobenius_hyperelliptic(HQp2)
        forms2 = [form.change_ring(K1) for form in forms2]
        M2_sys = matrix(K1, M2_frob).transpose() - 1
        inverse_frob2 = M2_sys^(-1)

        x1Qp1=psiQp1(EQp1(psi1(P1[0]),psi1(P1[1])))[0]
        y1Qp1=psiQp1(EQp1(psi1(P1[0]),psi1(P1[1])))[1]
        x1Qp2=psiQp2(EQp2(psi2(P1[0]),psi2(P1[1])))[0]
        y1Qp2=psiQp2(EQp2(psi2(P1[0]),psi2(P1[1])))[1]

        x2Qp1=psiQp1(EQp1(psi1(P2[0]),psi1(P2[1])))[0]
        y2Qp1=psiQp1(EQp1(psi1(P2[0]),psi1(P2[1])))[1]
        x2Qp2=psiQp2(EQp2(psi2(P2[0]),psi2(P2[1])))[0]
        y2Qp2=psiQp2(EQp2(psi2(P2[0]),psi2(P2[1])))[1]

        LogP1Qp1 = coleman_integrals_on_basis(HQp1, HQp1(0,1,0), HQp1(x1Qp1, y1Qp1), inverse_frob1, forms1)[0]
        LogP1Qp2 = coleman_integrals_on_basis(HQp2, HQp2(0,1,0), HQp2(x1Qp2, y1Qp2), inverse_frob2, forms2)[0]
        LogP2Qp1 = coleman_integrals_on_basis(HQp1, HQp1(0,1,0), HQp1(x2Qp1, y2Qp1), inverse_frob1, forms1)[0]
        LogP2Qp2 = coleman_integrals_on_basis(HQp2, HQp2(0,1,0), HQp2(x2Qp2, y2Qp2), inverse_frob2, forms2)[0]
        M = Matrix([[LogP1Qp1, LogP2Qp1], [LogP1Qp2, LogP2Qp2]])
        Minv = M^(-1)
        coeffs_mod_p = [[] for i in range(len(new_list_points_p))]
        bad_indices=[]

        for i in range(len(extra_points_p)):
            P = new_list_points_p[i]
            PQp11 = HQp1(P[0][0], P[0][1])
            PQp12 = HQp2(P[1][0], P[1][1])
            try:

                LogP1 = coleman_integrals_on_basis(HQp1, HQp1(0,1,0), PQp11, inverse_frob1, forms1)[0]
                LogP2 = coleman_integrals_on_basis(HQp2, HQp2(0,1,0), PQp12, inverse_frob2, forms2)[0]
                v = vector([LogP1, LogP2])
                vnm = Minv*v
                if vnm[0].valuation()<0 or vnm[1].valuation()<0:
                    coeffs_mod_p[i].append([]) #This means the point will not be integral.
                else:
                    coeffs_mod_p[i].append([ZZ(vnm[0] % p^d), ZZ(vnm[1] % p^d)])
            except :
                bad_indices.append(i)
                coeffs_mod_p[i].append([])
                print("There is an error with log")

        return coeffs_mod_p,bad_indices

def comparing_log_and_red(log_p,log_q,red_Np,red_Nq,extra_points_p,extra_points_q):
    p=extra_points_q[1][0][0].base_ring().residue_ring(1).characteristic()
    q=extra_points_p[1][0][0].base_ring().residue_ring(1).characteristic()
    remaining_points = []
    remaining_points_res = []
    print("this is the number of solutions obtained from reductions", len(red_Np[0]),len(red_Nq[0]))
    assert(len(log_p)==len(red_Nq) and len(log_q)==len(red_Np))
    for i in range(len(red_Nq)):
        for j in range(len(red_Np)):
                assert len(log_p[i]) == 1
                assert len(log_q[j]) == 1

                mod_p = log_p[i][0]
                mod_q = log_q[j][0]

                if mod_p==[] or mod_q==[]:
                    continue
#                 else:        
#                          mod_p = [x%p for x in mod_p]
#                          mod_q = [x%q for x in mod_q]
                mod_Nq=red_Nq[i]
                mod_Np=red_Np[j]
                
                if mod_Np==[] or mod_Nq==[]:
                    continue
#                 if len(mod_Np)==1:
#                     pass
#                 else:
#                     #print(j,len(mod_Np))
#                     mod_Np_new=[mod_Np[x] for x in range(0,q)]
#                     mod_Np=[[x[0]%p,x[1]%p] for x in mod_Np_new]

#                 if len(mod_Nq)==1:
#                     pass
#                 else:
#                     #print(len(mod_Nq),q)
#                     mod_Nq_new=[mod_Nq[x] for x in range(0,p)]
#                     mod_Nq=[[x[0]%q,x[1]%q] for x in mod_Nq_new]
                try:
                    if mod_q in mod_Nq and mod_p in mod_Np and extra_points_p[i][2] == extra_points_q[j][2]:
                        remaining_points.append([[i,extra_points_p[i]],[j,extra_points_q[j]]])
                except:
                     print("something went wrong with these indices")
                     print([i,j],extra_points_p[i],extra_points_q[j])

    return remaining_points


def sieve_for_ECs(E,extra_points_p,extra_points_q,gens=[]):

    if gens==[]:
        gens=lin_indep_generators(E)

    red_Nq=reduction_information(E,extra_points_p,gens=gens)
    red_Np=reduction_information(E,extra_points_q,gens=gens)

    #assertion statemnet about equality of stuff"
    log_q=log_information(E,extra_points_q,gens=gens,d=1)[0]
    log_p=log_information(E,extra_points_p,gens=gens,d=1)[0]


    remaining_points=comparing_log_and_red(log_p,log_q,red_Np,red_Nq,extra_points_p,extra_points_q)

    return remaining_points