attach("quad_chab_ell_im_quad.sage")
attach("Heights_for_im_quad.sage")
attach("p_adic_sigmafn.sage")
attach("helper_functions.sage")
attach("Findingalphas.sage")
attach("auxiliary_functions.sage")
attach("sieve_new.sage")
attach("quad_chab_ell_im_quad.sage")

R.<x> = PolynomialRing(QQ);  K.<a> = NumberField(R([1, -1, 1]))
E = EllipticCurve([K([0,0]),K([-1,-1]),K([1,1]),K([0,1]),K([0,0])]) #This is the curve at https://www.lmfdb.org/EllipticCurve/2.0.3.1/134689.3/CMa/1
gens=E([a,0]),E([1,0])
int_list=SmallIntegralPoints(E,5,gens)
print("We found", len(int_list), "small points.")
p=7;q=13;n=20;double_root_prec=5

QCset_p=quad_chab_ell_im_quad(E, p, n, double_root_prec, int_list=int_list , gens=gens, up_to_auto = False)

print("Found QC set at p=7")
print("----------------------------------------------------")
QCset_q=quad_chab_ell_im_quad(E, q, n, double_root_prec, int_list=int_list , gens=gens, up_to_auto = False)

print("Found QC set at q=13")
print("----------------------------------------------------")
extra_points_p=QCset_p[2]+QCset_p[3]
n_p=len(extra_points_p)
extra_points_q=QCset_q[2]+QCset_q[3]
n_q=len(extra_points_q)

print("----------------------------------------------------")
print("the number of extra points for ", p, "are", n_p)
print("the number of extra points for ", q, "are", n_q)

print("----------------------------------------------------")

print("We will implement the sieve in section 4 of the paper")

red_Nq=reduction_information_0(E,extra_points_p,q,gens=gens)
red_Np=reduction_information_0(E,extra_points_q,p,gens=gens)
log_p=log_information(E,extra_points_p,gens=gens,d=1)
log_q=log_information(E,extra_points_q,gens=gens,d=1)
log_p=log_p[0]
log_q=log_q[0]

remaining_points=comparing_log_and_red(log_p,log_q,red_Np,red_Nq,extra_points_p,extra_points_q)
n_remaining=len(remaining_points)

print("Number of p-adic points left from sieve are", n_remaining)
