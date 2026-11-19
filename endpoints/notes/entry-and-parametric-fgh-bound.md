# New entrances for j13(gamma16) and the lower bound of FGH · [中文版](entry-and-parametric-fgh-bound.zh-CN.txt)

2026-11-09. A paper proof under ZFC + I3; not a new Lean proof added this time.
Fixing the same I3 to be embedded in j, all actual owners belong to the same Iter(j).

0. Conclusion and Dependencies
-----------------
Write J_a=j_(a), J_1=j, J_(a+1)=J_a(j). The brackets between two embeddings indicate application.
Ordinary compositions are written as o or with the superscript circ. gamma_n is an increasing enumeration that generates critical points.
Put
  Sigma=J13(gamma16)=gamma_N，Lambda=lim(BMS).

Following the previously organized relative BMS compilation, finite type function comparison, and the original IBLP safe class lemma.
This paper presents a new practical approach and verifies item by item that it satisfies the interfaces of those lemmas, resulting in
  N > F_(C[6])(2047)，
Among them, C=I[0][2][1]^8 and I are the original IBLP initial formulas, using the original fundamental sequences.
For a more precise conclusion, see section 6. There is also a section N>F_C(6).

Let alpha_1=Lambda, alpha_(n+1)=Lambda*omega^(alpha_n). The exact rank of C[6] is
alpha_6. When using the closure fact with omega^Lambda=Lambda, it can be simplified to
  Lambda^(Lambda^(Lambda^(Lambda^Lambda))).
It is not sufficient to simply replace F_(C[6]) with a function of the same name that uses any other fundamental sequence based on order equality.
The above describes the bounds of the finite spectrum index N, which does not compare the uncountable Sigma directly with natural numbers.

Additionally, the old 25 lines that form the ordinary BLP pattern P25 can also be fully implemented below the Sigma strictness:
  N > 2^f(P25, 8), and independently, N > 2^(Psi^[4\](8)), Psi(m)=f(p_init, m).
The full row-by-row construction is in blp25-strict-transfer.zh-CN.txt.
The two BLP function values were not arbitrarily ordered with respect to the aforementioned FGH values.

This paper is not a self-contained monograph that proves all the relative BMS basic lemmas. The reused proofs are listed in section 7.
What has been newly completed is the parametrization of the small endpoint entrance, the complete interface, and the strict cap-based fidelity replacement.

1. Original subitem data, strict truncation, and target point positions
---------------------------------
Let's denote the mathematical research manuscript as follows:
  K0=J11，A0=J12，B0=J13，E0=J14，mu=gamma256，
  chi=K0(gamma3)，Theta=K0(kappa3)=A0(mu).
Here, kappa0=gamma0, kappa1=gamma1, kappa2=gamma2, kappa3=gamma4.
In the following text, Theta is different from Sigma, and the K0(kappa3) is never rewritten as Sigma.

The required public subitem facts are:
  cr A0=kappa2，A0(kappa2)=kappa3，A0(kappa3)=mu，
  B0(kappa0)=kappa1，B0(kappa1)=kappa3，B0(kappa2)=gamma16，
  B0(kappa3)=mu，E0(kappa3)=gamma16，
  J7(kappa0)=gamma3，J7(kappa1)=kappa3，J7(kappa2)=mu，
  K0(kappa0)=kappa2，K0(kappa1)=kappa3，K0(kappa2)=mu.
Also includes membership equivalence.
  K0 ==_mu j o j，A0 ==_mu j(J2).
Source: Dougherty I §5, particularly printed p.21; Dougherty II §8.
https://arxiv.org/pdf/math/9205202
https://arxiv.org/pdf/math/9503204

Use the rules e(f) o e=e o f; cr(e(f))=e(cr f); LD;
e ==_u f can be transported along h to h(e)==_(h(u))h(f), and can also be applied with the first parameter.
Keep the same truncation. When reading ordinal image, at least one side of the output must be strictly less than the truncation.

There are already mu<chi<Sigma<Theta. To ensure that the new entry does not depend cyclically, let's review the last two comparisons:
Let s=j(<kappa1), s2=j(<kappa2). Dougherty I presents
  kappa1<s<kappa2，j(<s)<gamma3<j(s)<s2<kappa3，
  K0|V_kappa2=(j o j)|V_kappa2.
Let u=B0(s)=A0(j(s)), then u<gamma16. Furthermore
  chi=K0(gamma3)<K0(j(s))=A0(K0(s))
      =A0(j(j(s)))=B0(A0(j(s)))=B0(u)<B0(gamma16)=Sigma.
Let t=A0(s2)=B0(<kappa3). There exists gamma16<t<mu, and
  B0(<t)=A0(j(<s2))=A0(K0(<kappa2))<A0(mu)=Theta.
Therefore, Sigma=B0(gamma16)<Theta. The supremum covariance is used only at the real image.

2. New practical entrance q
-----------------
Definition
  P=B0(B0)，U=A0(A0)，X=B0(E0)，q=X(A0).
The old entrance is q_old=K0(J3). LD assigns q_old=U(A0).

Carry along A0 A0 ==_mu j(J2) to obtain
  U ==_Theta A0(j(J2))=B0(A0(J2))=B0(P)=P(P).       (2.1)

From B0=A0(j) and cr A0=kappa2, it follows that B0 ==_kappa2 j; the transport along B0 yields
  P ==_gamma16 E0.                                (2.2)
This step does not require the calculation of A_16, nor does it depend on cycles inferred from finite tests.
By application covariance, P(gamma16)=B0(B0(kappa2))=Sigma.
Transport along P (2.2)), and using P(E0)=B0(E0)=X, we obtain P(P)==_Sigma X.
Combining Sigma<Theta with (2.1), we obtain U==_Sigma X, and subsequently
  q ==_Sigma q_old.                               (2.3)

Accurately calculate the critical sequence of X:
  cr X=kappa3，X(kappa3)=mu，X(mu)=Sigma.
It fixes kappa2. Therefore, the precise image of q is
  cr q=kappa2，q(kappa2)=mu，q(mu)=Sigma.            (2.4)
The old entrance has q_old(kappa3)=chi. Because of chi<Sigma, (2.3) can be strictly read as
  q(kappa3)=chi.                                  (2.5)

Specifically, since q(mu)=Sigma<Theta=q_old(mu), it is not possible to treat (2.3) as a global equation.
This text only uses the actual new entrances for (2.4)-(2.5); no old critical points have been directly renamed.

3. Low background required and initial long chain
-----------------------
The following argument holds for any actual q that satisfies cr q=kappa2, q(kappa2)=mu;
For now, let's use Omega=q(mu) and chi=q(kappa3). The Omega that is substituted in this text is equivalent to Sigma.
Definition
  g=q(j)，g_i=q(J_i)，b0=q(J7)，
  delta=q(gamma3)，xi=b0(kappa2)，eta=b0(gamma3)，
  e=b0(j)，J=e(g_2)，k=J(g)，x=e(g).
LD gives J=x(x). The actual point order and point image are
  mu<delta<chi<xi<eta<b0(kappa3)<b0(mu)=Omega; 
  g:kappa0 -> kappa1 -> mu -> chi; 
  cr J=kappa1，J(kappa1)=mu，J(mu)=xi; 
  k(kappa0)=mu，k(kappa1)=chi，k(mu)=xi.             (3.1)

Here, the 'critical' in e is delta, so we fix kappa0, kappa1, and mu.
e(g)==_delta g, transported along J using LD:
  e(g_3)=J(e(g)) ==_(J(delta)) J(g)=k.
And e(g_3)(kappa1)=e(delta)=chi<xi=J(mu)<J(delta), so the reading of the value is valid.
The reduced truncation results in k==_delta g_3.

The same j provides the actual 8-line (kappa0;kappa1,mu). Specifically, j,J3 provide
2-line (kappa0;kappa1,kappa3); Take B0 as the image
2-line (kappa1;kappa3,mu), obtained by chain multiplication, yields 2*2^2=8-line.
This is about constructing actual owners, not deducing long chains from the indices of mu, which are marked as 256.

Crude but independent lower bounds: g magnifies this 8-line into the 2048-line of the endpoint chi.
q(B0):kappa0 -> kappa1 -> chi -> Omega, and then expand it further.
2048*2^2048=2^2059-line. Therefore, index(Omega)>=2^(2^2059).
The subsequent FGH bounds do not depend on the actual computation of this enormous long sequence.

4. Total Pattern Supremum: No use of q=q_old
---------------------------------
Let T0=q(J10) be the starting point. The source relationship J10 ==_mu J8(J2) is carried along by q for transportation.
  T0 ==_Omega b0(g)(g_2).
From g==_kappa2 j, b0(g)==_xi e, therefore T0==_xi J.
Using K0==_mu j o j, we can obtain
  k=J(g) ==_xi T0(g)=q(K0) ==_Omega g o g，
So k==_xi g o g. For t<mu, k(t)<k(mu)=xi is a strict read guard, therefore
  k(t)=g(g(t))，k(<mu)=(g o g)(<mu).               (4.1)

Let s=j(<kappa1), s2=j(<kappa2), v=k(<mu) be defined as follows.
The source background has a strict chain.
  J7(s)=J8(<kappa3)>J8(s2)=J9(<kappa2)>J9(s)
       =J10(<kappa2)>J10(s)=K0(<kappa2)>K0(s).     (4.2)
These are direct results of the covariant with respect to the supremum, as described in Dougherty I pp.22-24.

q is fixed as s, e is fixed as s, kappa1, and mu. Therefore
  g(<kappa1)=x(<kappa1)=s，x(kappa1)=J(kappa1)=mu，
  v=J(s)，J(<mu)=x(s)，k(s)<J(s)<x(s).
The last two strict relationships can also be directly derived from s<mu and the fact that mu is an ordinal limit.
The quadratic power of the ordinary composition is denoted as k^2. It is composed of k o J=J o g, J=x(x).
  k^2(v)=J(g^2(s))=J(k(s))<J(x(s))=x(x(s))=e(k(s)).
On the other hand, (4.1), (4.2), and q(s)=s give
  k(s)=g^2(s)=q(K0(s))<q(J7(s))=b0(s).
b0(s) is a limit ordinal, therefore
  e(k(s))<e(<b0(s))=b0(j(<s))<b0(gamma3)=eta.
In summary
  k^2(k(<mu))<eta<Omega.                           (4.3)

Define actual actors
  b=k(g)，c=k(b)，d=c(k)，e1=d(g)，f=e1(k)，
  A=c(d)，V=c(e1)，Q=A(k)，
And t=k(chi), a=k(xi), c_out=k(t).
There are c=(k o k)(g), c^2=(k o k)(g o g), c^2(xi)=a, A=c^2(k).
Therefore
  c^2(<a)=k^2((g o g)(<mu))=k^2(v).
The generated critical point a is a regular cardinality, xi<a=k(xi), so k(<xi)<a. Therefore
  A(<a)=c^2(k(<xi))<c^2(<a)=k^2(v)<eta.            (4.4)
This is a unified cap for all t<a; no requirement for A(a)<Omega.
This section exclusively uses the q interface from the 3 section and the unmodified source j throughout, without any use of the q=q_old.

5. The six interfaces of the original relative BMS compiler
-----------------------------
Replace (j,kappa2,kappa3,J10,J11,gamma3) in the construction of old low-open fans.
(g, mu, chi, J, k, delta). The 3 section precisely provides all the assumptions of the general front insertion lemma.
From b(b)(k): (kappa0,kappa1,mu)->(mu,xi,t), any actual m-line
It can drive m number of front-end insertions, retaining all implicit edges and spare ports. Its ends are <=t, m>=2, and <t.
Taking f again and moving down two ports 1, we obtain two real bands for the relative BMS, with seeds exactly
B_m=(0^m)(1^m), scalar real parameter exit point <=chi, output <=a.
It provides a full input and full external environment contract for S(u)(m)=K_(B_m)^(0,u)(m).

Set Tstar=J(g_3), rho=J(delta), Z=A(Tstar).
g_3==_delta g o g along J transport; accurate representation with strict guardianship
  Tstar(kappa0)=xi，Tstar(kappa1)=t，Tstar(mu)=rho，Tstar(xi)=a; 
  xi<t<rho<Tstar(chi)<Tstar(v)<a.
Additionally, A: (kappa0,kappa1,mu,chi)->(mu,chi,a,c_out),
V:mu->chi->a->c_out. The complete contract environment table is

Type Environment Auxiliary Source Initial Real Band Left Endpoint Closed Output Upper Bound
0     id         mu             chi              a
1     V          chi            a                c_out
2     Q          a              c_out            A(xi)
3     Q o V      c_out          A(xi)            A(t)
4     Z          A(xi)          A(t)             A(rho)
5     Z o V      A(t)           A(rho)           A(Tstar(chi))
6     Z o Q      A(rho)         A(Tstar(chi))    eta

The first six closed exits are given by (4.4) < eta. Only the actual closures C0<a are taken in the last row:
  Q(C0)<Q(<a)=A(v)，
  Z(Q(C0))<Z(A(v))=A(Tstar(v))<eta.               (5.1)
The ordinary composite is not unconditionally exchanged with the supremum.

Each row of auxiliary points is the same as the previous type of entries, and the first solid point is the same as the previous type of exits.
Zero replication fixes the lower domain coordinates of the owner and sends the current entry to the updated output of the entire object.
The full object induction of the original relative BMS is applied layer by layer, and it is not just comparing the function values of a fixed input.
The four-point chain of g provides a warm-up for f0(m)=m*2^m, hence the high-type effective payload is B_(m*2^m).
And m*2^m>=2 ensures the strict sealing required by (5.1)). It results in the contract of all D_i (i=1,...,6).
Full object replication and reuse [D3]; its old high cap has been independently replaced by (4.4), (5.1)).

6. Pure numerical conclusions
-------------
The negative temperature of the fast BMS K is the base object. The subsequent iteration 2^m will take the limit as the original BM4 [2^m].
Define f0(m)=m*2^m, S as above.
  D_i(u)(...)(m)=K_(B_(m*2^m))^(i,u)(...)(m)，1<=i<=6.
The following applies left conjunction:
  Tnum=D5(D4)(D3)(D2)(D1)，W=D6(D5)(D4)(D3)(D2)(D1)，
  Unum=Tnum(Tnum(S))，Qnum=Unum(Unum(f0))，
  M=Qnum(8)，Ynum=W(S)(f0)(8).
These natural number definitions completely do not involve N or Sigma.

The universal comparison of [D4] is given to W(S)>=Unum^4, Unum>=S,
Qnum>=_3 H_(C[7]), where the tail quantifies all final inputs >=3.
M>=f0(8)=2048, a strong prefix growth gives
  Ynum>=Unum^4(f0)(8)>=Unum(Qnum)(8)>=S(Qnum)(8)
      >=Qnum(Qnum(8))=Qnum(M)>=H_(C[7])(M).
In the 5 section, the actual 8-line is sent to the Ynum-line with eta as the endpoint. The critical count is given as
  gamma_(2^Ynum)<=eta<Sigma=gamma_N, therefore N>2^Ynum.

FGH uses F0(n)=n+1, F_(alpha+1)(n)=F_alpha^[n+1\](n).
The limit adopts the original syntax [n]. [D4] The full quantifier comparison given in section 6
  y>=x+1，x>=2 => H_(C[7])(y)>=F_(C[6])(x)+1.
Taking (x,y)=(M-1,M), (2047,M), (6,M)), we get
  N>F_(C[6])(M-1)+1，N>F_(C[6])(2047)，N>F_C(6).
The last formula only uses F_C(6)=F_(C[6])(6). No assumption is made regarding the monotonicity of the subscripts of any FGH.

7. Verifiable dependencies and program scope
-------------------------
[D1], [D2], [D5] retain the research manuscript's file names. The organized version of the entrance and strict endpoints can be found in ../../laver_table_lower_bounds/lower_endpoints/endpoints.zh-CN.md, while the organized version of the six types and numerical comparisons can be found in ../../laver_table_lower_bounds/lower_endpoints/bms.zh-CN.md.
[D1] scratch/k11-bound-20261109/k11-BMS-input-243.zh-CN.md，§3-7：
     8-line, general low control and sequential front-end insertion; source materials can be found in two papers by Dougherty.
[D2] scratch/k11-bound-20261109/k11-six-type-strict-cap.zh-CN.md，§2-7：
     This paper revisits the parameterized interface and the strict supremum chain.
[D3] ../../laver_table_lower_bounds/proofs/scratch/iblp030-8h-20261015/
     lift-low-open-fan-and-typed-gap.txt，§1-3; 
     hardy-root-C7-q5-single-file.txt, §3, 5 (actual relative replication and full object contracts).
     The old unresolved type gaps in the previous document §5 should not be considered theorems. This document is presented through tables and (5.1) payments.
[D4] ../../laver_table_lower_bounds/01-blp-tower.zh-CN.md，§1-4, 6-8：
     The original C includes precise fundamental sequences, safe classes, numerical comparisons of all types, and comparisons across inputs like FGH.
     This paper does not follow the old term 'critical point' from §5, but instead proves the realization of lower endpoints.
[D5] scratch/small-jn-km-100-20261109/upper-list-and-gap-order.zh-CN.txt，§3，
     b32-b64-below-theta.zh-CN.txt: The old strict point order, the necessary details have been repeated in section 1 of this article.

check_entry.py audits the finite algebras of entry and the strict outputs of guard.
check_six_types.py audits actual lows, seven-row interfaces, and finite strict order.
Audit all actual point images of the check_blp25.py rows with the 25 lines.
These procedures do not prove the supremum lemma, the open finite quotient theorem, BMS well-ordering, or total type induction.
These are derived from paper-based reasoning and explicitly dependent on the above; program execution cannot replace them.
No calculations of huge Laver tables or long downsets; no changes to old research, release repositories, commits, or pushes.
