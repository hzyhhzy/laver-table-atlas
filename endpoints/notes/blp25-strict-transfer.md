# The entire 25 line follows the standard BLP pattern, which is strictly transferred to j13(gamma16) below. · [中文版](blp25-strict-transfer.zh-CN.txt)

2026-11-09. ZFC + I3; the same as Iter(j). Paper proofs and finite algebraic audits.

Conclusion
----
The pattern referred to by the user is P25 from the previous larger-blp-seed.zh-CN.md:
Four copies of seven lines, p_init, are pieced together section by section. The first copy retains seven lines, while the subsequent three copies each add six lines.
It is not the IBLP of the 24 row that is C[6], nor the IBLP of the 28 row that is C[7].

25 rows can be moved all the way over. In fact, the complete end points are
  xi=q(J7)(kappa2)<q(J7)(mu)=Sigma=J13(gamma16)，
Among them, mu=gamma256 and q=J13(J14)(J12), the embedding operation is performed from left to right.
Retain the original ordinary BLP row addresses, step sizes, and all necessary edges. The initial linedness parameter can still be set to 8.
No rows were deleted, and there is no need to place the endpoints within the Sigma itself.

Further extracting the actual endpoint (2026-11-09): It can be written in shorter old terms
  xi=(J11(J3)(J7))(kappa2)=(J11(J3)(J7))(gamma2).
Reason: q==_Sigma J11(J3), retaining the truncation in the first parameter of the application, and
q(J7)(kappa2)=xi<Sigma, strictly speaking, the guard is established.
If xi=gamma_r, then this section actually provides a direct answer at the end.
  r>=2^f(P25, 8), and independently, there is also r>=2^(Psi^[4\](8)).
Note that the symbol used here is >=, rather than the strict > that would be given to the Sigma index due to the xi<Sigma notation.
And chi<xi<eta<Sigma, where eta=(J11(J3)(J7))(gamma3)
They are the higher BMS endpoints of the same directory lower-bms-endpoint-eta.zh-CN.txt.
In this study, the lower bounds of the six types of eta, FGH, are not proven to be moved to xi.

Therefore, writing Sigma=gamma_N, there are two independent conclusions.
  N>2^f(P25,8)，
  N>2^(Psi^[4\](8))，Psi(m)=f(p_init,m).
There is no claim that f(P25,8)=Psi^[4\](8), nor is there a direct derivation of the monotonicity of function values from the number of grammatical lines.

1. New Entrance and Lower Four-Stage Transport Operator
-------------------------------
This catalog entry-and-parametric-fgh-bound.zh-CN.txt §§1-3 has been proven
  cr q=kappa2，q(kappa2)=mu，q(kappa3)=chi，q(mu)=Sigma，
Among them, chi=J11(gamma3), mu<chi<Sigma.
Put
  g=q(j)，g2=q(J2)，b0=q(J7)，delta=q(gamma3)，xi=b0(kappa2)，
  e=b0(j)，T=e(g2)，k=T(g).
Existing actual point images
  g:kappa0 -> kappa1 -> mu -> chi，
  cr T=kappa1，T(kappa1)=mu，T(mu)=xi，k(kappa1)=chi，
  xi<Sigma.

Now let H=T(j). Because g==_kappa2 j,
  T(g)==_(T(kappa2))H.
The reader's duty is to be determined by H themselves:
  H(kappa1)<H(mu)=T(kappa2)，
So, H(kappa1)=k(kappa1)=chi.
There is also H(kappa0)=mu. Caused by the covariant H(mu)=T(kappa2),
H(T(kappa2))=T(kappa3). This is precisely the entire starting interface required by the old four-stage proof.

Important distinction: The old four-stage method used T_old=q_old(J10), T_old(mu)=Theta=J11(kappa3).
The text can be rewritten as q(J10), which can change the end point to Sigma. Here, we further use a lower value.
  T=b0(j)(q(J2)), which is its T(mu)=xi<Sigma.
Therefore, the complete 25 line results in a strict remainder.

2. Four source embeddings and legally readable congruences
-------------------------------
Let D4=J14, D16=J65534,
  R0=j，R1=D4(j)，R2=D16(j)，R3=D16(R1).
Dougherty II Theorem 7.2(c) and Lemma 7.1 provide accurate finite scaling
  D4(gamma_m)=gamma_(4m) (m<=4)，
  D16(gamma_m)=gamma_(16m) (m<=16).
From these four critical sequence prefixes in turn:
  R0: gamma0 -> gamma1  -> gamma2   -> gamma4，
  R1: gamma0 -> gamma4  -> gamma8   -> gamma16，
  R2: gamma0 -> gamma16 -> gamma32  -> gamma64，
  R3: gamma0 -> gamma64 -> gamma128 -> gamma256.

Set s_i=4^i. If h_i is a critical point index function of R_i, then
h_i(0)=s_i, h_i(s_i)=2s_i. Lemma 7.1 provides
  2s_i>=s_i+s_i(h_i(1)-s_i)，
Strictly increasing gives h_i(1)>=s_i+1, therefore R_i(kappa1)=gamma_(s_i+1).

Finite quotient projection lemma: For e, f in Iter(j) that contain ordinary composition, if
If e(gamma0)=f(gamma0)=gamma_s, then e==_(gamma_(s+1)) f.
Proof: Since cr(e(j))=gamma_s, in the finite quotient P_(s+1), the remainder of e(j) is 2^s.
The right-side generator is modulo 2^(s+1) plus one, so the remainder of e is 2^s-1; the same applies to f.
Dougherty II Theorem 2.6 explicitly includes two operations algebras P_j, so this argument allows for ordinary composition.
Therefore, for i=1,2,3,
  R_i ==_(gamma_(s_i+1)) R_(i-1)^[circ 3].

Take H_i=T(R_i). Define
  a_i=H_i(kappa0)=T(gamma_(s_i))，
  b_i=H_i(kappa1)，c_i=H_i(a_i)=T(gamma_(2s_i))，
  d_i=H_i(b_i)，e_i=H_i(c_i)=T(gamma_(4s_i)).
All are actual generation of critical points, and
  kappa0<kappa1<a_i<b_i<c_i<d_i<e_i.
Transport the above congruence along T, read the front part first
  b_i=H_i(kappa1)<H_i(mu)=T(R_i(kappa1))=T(gamma_(s_i+1)).
This provides a valid and accurate equation.
  b_i=H_(i-1)^[circ 3\](kappa1).                   (2.1)
No reading was performed at the truncation equal sign boundary.

3. Four complete p_start instances of the actual low bridge
-----------------------------
Set G0=g; for i=0, 1, 2, let C_i=H_i(H_i),
  G_(i+1)=C_i(C_i(G_i)).
Inductively derived
  G_i:kappa0 -> kappa1 -> a_i -> b_i.
Proof: If the current statement holds, then the critical point of C_i is a_i. Fixing kappa0 and kappa1,
And there are C_i(a_i)=c_i, C_i(b_i)=d_i, C_i(c_i)=e_i,
C_i(d_i)=H_i^[circ 3\](kappa1). Two applications thus send the low bridge
  kappa0 -> kappa1 -> e_i -> H_i^[circ 3\](kappa1).
And e_i=a_(i+1), the last point is determined by (2.1) being equal to b_(i+1).

Therefore, at the seven points (kappa0,kappa1,a_i,b_i,c_i,d_i,e_i)) of each segment,
  G_i,G_i,H_i,H_i,H_i(H_i)
Accurately implement the five elements p_start:
  012:1，0123:1，01234:2，012345:2，23456:2.
The actual end point of the previous paragraph is the third point of the next paragraph.

4. Construct each segment of seven lines as p_init without relying on graphical speculation.
---------------------------------------
Take any section from the previous section, omit the subscripts, and write the seven points as alpha,beta,a,b,c,d,e.
Put
  D=(H(H))(H(G))，E=D(H)，F=E(G)，L=F(H).
Actual application of covariance
  D:c -> d -> e，
  E(alpha)=a，E(beta)=b，E(a)=d，E(b)=e，
  F:a -> b -> d -> e.
F fixes alpha and beta, therefore
  L(alpha)=b，L(beta)=d，L(b)=F(c)，L(d)=e.
Taking u=L(a) and v=F(c) again, monotonicity is given to d<u<v<e.
At the nine points (alpha, beta, a, b, c, d, u, v, e)), the following seven lines are obtained:

Line                   Step Size     Actual Owner
(0,1,2)               1     G
(0,1,2,3)             1     G
(0,1,2,3,4)           2     H
(0,1,2,3,4,5)         2     H
(0,1,2,3,5,6)         3     L
(0,1,2,3,5,6,7)       3     L
(0,1,2,3,5,6,7,8)     3     L

This is all that was previously written for the same p_init, including its rows and steps. The last three rows do indeed share the owner L.
In this case, all "critical" values are actually "alpha"; each image at the corresponding step length is given by the above equation.
The first three points, the last point, and any given linedness parameters remain unchanged.

5. The unchanged 25 line
--------------------
In the i section, the address mappings for (i=0,1,2,3) are
  phi_i(0)=0，phi_i(1)=1，phi_i(t)=t+6i (t>=2).
The first paragraph is retained with seven lines; the following three paragraphs only omit their dummy first lines and are then supplemented with six lines.
Because e_i=a_(i+1), there are no additional insertion points; the new points within the segment are located in adjacent strict intervals.
The last two addresses in each line remain the global line number and the next point number, with the step size remaining unchanged.
All owners use the section corresponding to the 4 section, which is therefore the actual realization of the original P25.

Number of connection segments, Number of rows, Actual end point
1            7      T(gamma4)
2           13      T(gamma16)
3           19      T(gamma64)
4           25      T(gamma256)=xi<Sigma

The source three points (kappa0,kappa1,mu)) have a previous construction of the actual 8-line.
According to the quantitative theorem of the ordinary BLP, the implementation of P25 gives f(P25,8)-line at the endpoint xi.
And the critical counts are given as gamma_(2^f(P25, 8))<=xi<Sigma=gamma_N.
This proves that N>2^f(P25,8). By applying the same theorem to each of the four segments in turn, the result is obtained.
N>2^(Psi^[4\](8)). The two are independent lower bounds, and do not borrow the equality relationship of unproven function values.

6. The meaning of subsequent ordinary BLP operations
---------------------------
It is not just the syntax of the original static patterns that holds. It has actual BLS owners and real initial long chains.
Therefore, the M, completion, E, and column deletion operations permitted by the ordinary BLP paper can continue to be performed according to the semantic transport theorem.
The entire recursive definition of the corresponding numerical function f has been covered by quantitative theorems, and the endpoints do not exceed the initial xi.
This is not an automatic transfer of all the additional rules from the original version marked with IBLP.
There is also no proof that P25 is the largest achievable pattern under this endpoint; the current problem only requires the transplantation of the old P25.

Supplementary: The complete marking BLP is also provided in the same directory blp25-both-completions.zh-CN.txt
The initial certificate for the M_star/E version includes quantitative bridge applications, which encompass both native and marked completions.
This supplement uses natural truncation semantics and correct paper guard. Numerical functions are denoted as f_star.
It cannot be dismissed without explanation. This is a common... f Revised to f_star ， Or assert the size of both.

7. Source and Independent Review
-----------------
Public foundation:
  Dougherty II，Theorem 2.6, Lemma 7.1, Theorem 7.2(c)：
  https://arxiv.org/pdf/math/9503204
  Qi，Notes on Laver Tables，v5，Lemma 2.5, Theorem 2.25：
  https://arxiv.org/html/2501.06733v5

The original research document and the study of the old four-stage proof are named as follows. The complete argument after reorganization is presented as ../../laver_table_lower_bounds/lower_endpoints/blp.zh-CN.md.
  scratch/k11-bound-20261109/larger-blp-seed.zh-CN.md
  scratch/k11-bound-20261109/received-kappa11/proofs/kappa11_fourfold_iteration.txt
  scratch/k11-bound-20261109/received-kappa11/proofs/pinit_transfer_108.txt
This paper reworks the actual entry points, operators, and strict cap, retaining the original finite scaling theorem there.

../checks/check_blp25.py checks all rows in the four segments, all critical points, 90 steps along the edges.
Three connecting equations, all strict point orders, and the final point xi<Sigma. Records can be found at ../checks/check_blp25.json.
It runs for approximately 1.4 seconds, with 125 point names, 75 owners, and 514 point-like facts. There are no massive tables or long declines.
D16 serves as the actual J65534 compressed storage specified by the public theorem; the program does not reconstruct it into any abstract new generators.
The scaling and finite quotient lemma comes from paper proofs. The program is not a exhaustive proof of this, nor is it Lean-verified.
The shorter old terms for xi and eta, along with their strictly truncated readings, are described in section 4 of ../../laver_table_lower_bounds/lower_endpoints/endpoints.zh-CN.md.
