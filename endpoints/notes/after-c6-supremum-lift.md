# After the equality 4096: Supremum lifting and J13(gamma7)=gamma16384 · [中文版](after-c6-supremum-lift.zh-CN.txt)

2026-11-09. Continue to study whether chi=J11(gamma3)=gamma_s is s=2^2048.
This document does not complete the final equal sign, nor is there any counterexample found.

New Conclusion:
  (i) R=J14(J14) and J65520 are consistent at gamma_(T+1), T=2^2048;
  (ii) J13(J15) ==_gamma65536 J_(2^256-2); 
  (iii) J13(gamma7)=gamma16384.
It has been proven by related research that the J13(gamma6)=gamma4096 is consistent with this conclusion.
All the conclusions in this document are proven in the presentation with a fixed embedding of I3; a complete translation into pure ZFC finite model is not yet completed.

### Mark and verified input
-----------------
J1=j, J_(a+1)=J_a(j), the parentheses indicate application when embedding, not function composition.
The ordinary evaluation of ordinal numbers is denoted by gamma or kappa.

  K=J11，b=J12，C=J13，E=J14; 
  mu=gamma256=C(kappa3)，chi=K(gamma3)，Theta=K(kappa3); 
  T=2^2048，z=2^256; 
  R=C(J2)=E(E)，D=C(J3)=R(E); 
  M=J65520，L=J65534，v=z-65536; 
  P=C(C)，U=b(b)，Q=K(J3)=U(b)，G=Q(j)，H=C(J15).

==_delta represents the Laver membership relation truncation, and |V_alpha represents the ordinary domain restriction, which should not be used interchangeably.

[D1] Dougherty, Critical points in an algebra of elementary embeddings,
     https://arxiv.org/pdf/math/9205202, especially section 5.
[D2] Dougherty, Critical points in an algebra of elementary embeddings, II,
     https://arxiv.org/pdf/math/9503204, Section6--8.
[Dr95] Drapal, Persistency of cyclic left distributive algebras,
       https://doi.org/10.1016/0022-4049(94)00142-1.

The inputs that have been proven and are actually used in this document are as follows:
1. (kappa0,kappa1,kappa2,kappa3)=(gamma0,gamma1,gamma2,gamma4).
   C(gamma0)=gamma1，C(gamma1)=gamma4，C(gamma2)=gamma16，
   C(gamma3)=gamma64，C(gamma4)=mu.
2. R|V_mu=M|V_mu,D|V_mu=L|V_mu, from the ordinary limit computation in section [D2], section 8.
3. b ==_mu, and thus J3(J3), therefore C(b) ==_(C(mu)), and D(D).
4. gamma_T<=chi<C(gamma16)<Theta，U ==_Theta P(P).
   See this catalog exclude-2pow2048-rigidity.zh-CN.txt and only the adjacent items are read-only.
   ../small-jn-km-100-20261109/REPORT.zh-CN.txt.
5. For 257<=d<=65536:
     65534 *_d 65534=v;                             (Square)
     65520 *_d 14=65534;                            (F4)
     v *_d y=v+y，1<=y<=65534.                     (Block)
   The paper summary of Square is as read-only adjacent.
   c4-gamma4096-even-carries.zh-CN.txt Section1--4;
   F4, see c4-filled-block-period-bridge.zh-CN.txt for Block.
   Here, no formula is extended to 65537.
6. (z-16) *_d y=z-16+y, holds for y<=12 and d<=T+1.
   This catalog contains proofs for section filled-block-and-normal-form.zh-CN.txt of the 2 chapter.

### Ordinary restrictions can be lifted along the entire supremum.
------------------------------
Lemma. Let alpha be a limit ordinal, and lete|V_alpha=f|V_alpha. If there exists abeta+2<alpha and
If delta<=e(beta)=f(beta), then e ==_delta f.
Therefore, when alpha is unreachable and delta<e(<alpha), it can also be elevated to delta.
Here, e(<alpha)=sup_{xi<alpha} e(xi).

Proof. For any x and y that belong to V_delta, let x'=x intersect V_beta.
x' belongs to V_(beta+1), therefore e(x')=f(x'). By elementarity,
  e(x) intersect V_delta
   =e(x intersect V_beta) intersect V_delta
   =f(x intersect V_beta) intersect V_delta
   =f(x) intersect V_delta.
This is precisely the required member relationship truncation equality.
The second conclusion is that by choosing a sufficiently large beta<alpha, reachability guarantees can be ensured for beta+2<alpha.

It cannot be stopped simply by setting beta to gamma255: beta can be an ordinal that is not critical below mu.
This is a more effective improvement over the finite spectrum image13107 in this round.

### The actual truncation of R exceeds the target chi.
-------------------------
Letsigma1=j(<kappa1),sigma2=j(<kappa2),S=K(sigma1).
[D1] indicates]
  sigma1<kappa2，gamma3<j(sigma1)<sigma2<kappa3，
  K|V_kappa2=(j compose j)|V_kappa2.
Therefore
  S=j(j(sigma1))=b(<kappa3).
Additionally, the co-variance with respect to the supremum is applied.
  b(sigma2)=C(<kappa3).
Therefore
  gamma16=C(kappa2)<C(gamma3)<C(<kappa3)=b(sigma2)
           <b(<kappa3)=S.
In the last step, we use sigma2<kappa3 and kappa3 as the limit ordinals.

Also from J2=j(j),
  J2(<kappa3)=j(sigma2).
Therefore
  R(<mu)=C(J2(<kappa3))=C(j(sigma2))
          >C(j(j(sigma1)))=C(S)>C(gamma16)>chi.      (1)
The ordinary restrictions R|V_mu=M|V_mu and the lifting lemma from Section 2 are now presented.
  R ==_(C(gamma16)) M.                            (2)

Because both C(gamma16) and chi are critical points, and C(gamma16)>chi>=gamma_T,
SoC(gamma16)>=gamma_(T+1). Therefore, in particular
  14 *_(T+1) 14=65520.                            (3)
This is the actual high truncation identity, not a conditional conclusion that only holds when chi=gamma_T is assumed.
Do not misinterpret (3) as 14*14, which equals 65520 in all finite tables.

### Derive the order of 65536 and read the 7 image
---------------------------
All operations are performed first in A_65536. Inputs are (2), which are far above this order.
From D=R(E) and (F4),D=65534=L; from C(b) and D(D) with known truncations and (Square),
  C(b)=v.
Using the left distributive law and (Block),
  P=C(C)=(C(b))(C(j))=v*14=v+14; 
  C(E)=P*14=(v*14)*14.
The rowv+14 is a period that divides2^16, because its lowest16 bit is14, and the highest16..255 bits are all1.
The continuous block lemma states that its gamma16 image contains at least gamma65536 elements.
Therefore, the right parameter 14 can be replaced with v+14, and then using the left distributive law:
  C(E)=(v*14)*(v*14)=v*(14*14)=v*65520=z-16.
Similarly, the period of row z-16=v+65520 is a multiple of 2^16, therefore
  H=C(J15)=(z-16)*14
    =(v*65520)*(v*14)=v*(65520*14)=v*65534=z-2.
Therefore
  H ==_gamma65536 J_(z-2).                        (4)
The above two right-hand parameter substitutions only occur in the order of this stage with periodic protection.

Also, from U ==_Theta, P(P).
  U=P(P)=(v*14)*(v*14)=v*(14*14)=z-16.
So, input 6 to give
  Q=z-4 and G=z-3 hold in A_65536.               (5)

Finally, read (4).[D2] Lemma6.2 yields J15(gamma3)=gamma7.)
Because of C(gamma3)=gamma64, covariance is given
  H(gamma64)=C(gamma7).
[ Dr95] width 256 Bit stretching homomorphism allows source order 65 (Allowing an upper bound) 65536 ），
Thus, J_(z-2)(gamma64)=gamma16384.
This output is strictly less than gamma65536, so (4) is safe to provide.
  C(gamma7)=gamma16384.                           (6)

The same argument confirms that H(gamma_r)=gamma_(256*r), 0<=r<=255.
The candidate output of r=256 only touches this section of truncation and cannot be read from (4).
This also indicates that (6) does not have an automatic proof for (C(gamma8)=gamma65536).

### Relationship to the previous 13107 bounds
----------------------
This round was earlier obtained from another general lemma: If e(gamma_n)=gamma_(f(n)),
If a is a power of 2 and 0<=b<2a, then
  f(a+b)>=f(a)+f(b)-f(0).
Proof: Using [D2] Lemma6.2, take A=J_(2^a-1), and its gamma_b image is gamma_(a+b);
e(A) sends gamma_(f(0)) to gamma_(f(a)), and then compares gamma_(f(b)) using strict increasingness.
When e is fixed with gamma0, it is the superadditivity of binary segments.

For R, use proven weights
  r1=1,r2=2,r4=16,r8=32,r16=256,r32=512,r64=4096，
We obtainr128>=8192,r255>=13107=0x3333.
The independent A10 has verified 2576 readable instances of lemmas; it does not compute any target large tables.
Recorded as check_dyadic_superadditivity.py/.json.
The proof of the supremum in Section 3 has already exceeded this specific cut-off; hence, we no longer refer to 13107 as the optimal bound.

### What is currently missing?
----------------
The ultimate goal s=T remains unproven or refuted. The current unconditional numerical lower bound is still s>=T.
We have completed the actual high truncation identification for R, and derived the equality for the 7 image of C.
However, the value of C(gamma8) has not been determined, nor has the normal shape of G been transformed from 65536 to T+1.

In particular, the Square and Block sections in section 1 only guarantee up to 65536.
Applying these formulas directly to 65537, T, or T+1 will reintroduce gaps.
The special product F4 can be proven to have a higher truncation in section 7, without relying on such extrapolations.
The next smaller threshold can be formally written as
  C(gamma8)=gamma65536 iff 13 *_65537 15=z-2; 
The complete statement of chi equals remains subject to much more complex calculations or another comprehensive proof.

No new sub-agents, automation, commit, or push have been added; the adjacent research catalog has not been changed.

### Further practical high truncation: D can also be directly upgraded.
------------------------------------
The supremum chain given on page D1] of the 23 edition contains a strict supremum.
  J3(<kappa3)=J2(sigma2)>J6(kappa3)>J7(kappa3)>mu.
The last mu-bound is also referred to in the critical point ordering on pages 21 and 24 of the same document.
These are theorems concerning the original embeddings, and not conjectures about subsequent numerical equalities.
The original chain also shows J2(<kappa3)=j(sigma2)>mu.

Apply the C to both inequalities, resulting in
  D(<mu)=C(J3(<kappa3))>C(mu)，
  R(<mu)=C(J2(<kappa3))>C(mu).
Therefore, the lifting lemma in Section 2 is also provided.
  D ==_(C(mu)) L，R ==_(C(mu)) M.                  (7)
This is even higher than the R truncation in the third section. In particular, in the A_(T+1) case, there is a strict limit.
  14*14=65520，65520*14=65534.                     (8)
Therefore, this special productF4 can indeed exceed65536.
This conclusion does not arbitrarily extend the general full-block lemma.

Another useful counter-error conclusion is:
  L(gamma256)>=C(mu)>chi>=gamma_T.                (9)
Proof: D(gamma256)=C(J3(kappa3))=C(kappa4)>C(mu)
Equation (7) rules out L(gamma256)<C(mu).
Therefore, it cannot be L(gamma_r)=gamma_(16*r) （ r<256 ）Expansion to r=256 .
In particular, [D2] Theorem7.2 yields L(gamma16)=gamma256.
It does not provide a value for L(gamma256)=gamma65536. The latter is opposite to (9).

LetA=J65533. From the first two0 positions andL=A(j),
  A(gamma0)=gamma1，A(gamma1)=gamma16，
  A(gamma2)=L(gamma16)=gamma256，
  A(gamma4)=L(gamma256)>chi>=gamma_T.              (9a)
Therefore, the exponential lower bound m^r, which states that 'the first two images are 1 and m, should not be arbitrarily regarded as a universal equality.
Here, m=16, the 4 is already much larger than the 16^4=65536.
This does not contradict the actual value of G or the equivalence of C, because A is another embedding.
And the points that are (9a)) lie above chi.

### The final goal can be transformed into three clear finite equations.
----------------------------------
Each product in this section belongs to the same A_d, d=T+1. Set
  v=2^256-2^16，u=2^256-16，q=2^256-4.
The necessary and sufficient conditions are as follows:

  chi=gamma_T
    iff
  65534*65534=v，v*65520=u，q*16=2^T.             (10)

Sufficiency. (7) and given thatC(b)==_(C(mu))D(D) implyS=C(b)=65534*65534.)
P=C(C)=S*14. If the first equation holds, then
  U=P(P)=(v*14)*(v*14)=v*(14*14)=v*65520=u.
The second equation and the input 6 yield Q=U(b)=u*12=q.
And Q(gamma4)=chi, the third equation gives chi=gamma_T.

Necessity. When chi=gamma_T, the exponential equality gives G=z-3, Q=z-4.
Due to Q=U*12, the support contains a property bits(U) subset bits(Q-1) indicates
The256th position and all subsequent positions in the sequenceU are all0.
The critical point of U is gamma4, and the first critical image is gamma256.
The continuous characterization of the first critical image's 1 position is thus given as U=u.

It is necessary to determine the value of S. Based on U==_Theta P(P) and P=b(J2),
TheP with low16 bit set to14, and theP(gamma16)=C(gamma16).
At the level of d<=index(C(gamma16)), the period of P divides 2^16, therefore
  U=P(P)=P*14=C(J14).
C(gamma4)=gamma256<gamma_d, so the period of the C row is at least 32.
Its column12 and column14 are strictly increasing. Thus
  S=C(b)=C*12<C*14=U=u<z.
Section Four has proven that S mod2^65536=v; S<2^256 forces S=v.
Using U=P(P)=S*(14*14)=v*65520 again, we obtain the second equation.
The third equation is immediately derived fromQ=q andQ(gamma4)=chi. Proof completed.

The last equation is also equivalent to
  J_(2^256-3)(gamma256)=gamma_T; 
Since the critical point of q is gamma2, the first critical image is gamma256.
Apply co-variance to q(j). This is precisely the n=2 instance of [D2] Conjecture8.1.
This document does not provide a proof for this instance, nor does it claim that it is unsolved in subsequent literature.

Due to (8) and the left distributive law, the first unresolved product in this section can also be rewritten as
  65534*65534=65520*65520=14*65520.                (11)
This is an equation that depends on high truncation input in this section, and it is not an identity of integer powers of any order.
The new bounded evaluation using (11) requires explicitly listing these inputs.

### Bounded experimental records
----------------
probe_after_supremum.py refers to the newly proven 14*14=65520, 65520*14=65534.
And add the corresponding proven upper bound to the original demand value generator. The source directory is read-only; this is allowed.
A65537, private copiespartial_backward_large.py only perform the original8192 entry checks
Change to 65537 positions. Each query still has a limit of 6 seconds, 40000 calls, and 12000 entries.
No complete large tables were constructed, nor were A_(T+1) constructed.

The independent A8 has all 13 and 14 rows passing the regression check for the total of 512 products.
Actual statistics show that they did not trigger any new high truncation branches, so it cannot be called
Independent coverage of new branches. The basis for high truncation inputs is the paper proof in this document.
Both types of equivalent evaluations, 14 *_65537 65520 and 65520 *_65537 65520, encounter resource limits.
No target value has been returned. This does not prove the equation, nor does it prove its falsity.
The complete statistics are stored in a JSON file with the same name. No budget for these queries has been increased since the failure.
