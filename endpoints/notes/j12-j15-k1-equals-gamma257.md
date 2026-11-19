# j_(12)(j_(15)(kappa_1)) = gamma_257 · [中文版](j12-j15-k1-equals-gamma257.zh-CN.txt)

2026-11-09; This document provides a proof by hand, filling in the gap left by c1-one-bit-reduction.zh-CN.txt.
No calculations using the complete A_258 notation, nor the Dougherty optimality conjecture is used.

Conclusion
----
In the context of fixing I3 to embed in j,

  j_(12)(j_(15)(kappa_1)) = j_(12)(gamma_5) = gamma_257.

The new key step is to strengthen the counting in the Dougherty II Lemma 7.1, and then to
Theorem 7.2 states that a certain block normal form can be upgraded from gamma_257 to gamma_272.
This is strictly derived from

  65534 *_258 65534 = 2^256-65536.

Here, the size of A_n is 2^n, *_n represents the ordinary Laver table operation, and 0 stands for 2^n.
The scope of paper proofs and computational verification should be distinguished: the program only verifies small-order models and bit-block indices.
Identities and sparse branching operations; the main conclusion is proven by the following lemmas, and not by extrapolating examples.

0. Notation and Literature Input
-----------------
Write J_n=j_(n), J_1=j, J_(n+1)=J_n(j). The brackets between adjacent embeddings indicate applications.
The parentheses around ordinal numbers usually indicate the value. Writing e ==_delta f represents the Laver membership relation.
Truncated equality: For x, y∈V_delta, y∈e(x), it holds if and only if y∈f(x).
In delta=gamma_d, this is equivalent to having the same remaining value as in A_d.

[D1] Randall Dougherty, Critical points in an algebra of elementary embeddings,
Section 5:
https://arxiv.org/pdf/math/9205202

[D2] Randall Dougherty, Critical points in an algebra of elementary embeddings, II：
https://arxiv.org/pdf/math/9503204

The following uses [D2] Theorem 2.1, Proposition 2.7, Lemma 2.9, and the symbols preceding them.
Properties of inclusion, Theorems 3.1 and 4.1, Lemma 5.1, Proposition 6.6, Lemma 6.7,
Lemma 7.1, Theorem 7.2, General restriction equations from section 8.

Basic Properties:

(i) cr(e(f))=e(cr f)，e(f)(e(alpha))=e(f(alpha)).

The notation (ii) e ==_delta f can be replaced in applications; after applying to g, it is truncated to g(delta).

If iii) and H=k(e), then in any finite table, each position1 ofk is the1 position ofH-1).
      For the positive residual value H≠0, it also satisfies H>k. This is a property of finite table inclusion.
      And [D2] (2.2).

(iv) If k(gamma_s)=gamma_r, Therth bit of k is0.
     k(gamma_0) and k(gamma_1) are determined by the last two0 digits of k.

Each embedding is strictly increasing on the critical spectrum, hence there exists a strictly increasing natural number mapping f_k.
Make it k(gamma_n)=gamma_(f_k(n)). In the following text, when referring to bitr, it is always taken to be higher than bitr.
Therefore, there is no ambiguity about "taking an insufficient number of bits."

1. Enhanced gap counting lemma
--------------------
Given k, write f=f_k, a=f(0), b=f(1), d=b-a.
For n>=1, Let w is k In the semi-open interval [ b , f(n)) only in 1 Number of digits. then

  f(n) >= a+n*d+w.                                      (G)

This strengthens the [D2] Lemma 7.1 of the [f(n)>=a+n*d].

Proof.
When n=1, the interval is empty, and the equation holds. For each 1<=m<n, let

  H_m=k(J_(2^m-1)).

From J_(2^m-1)(gamma_0)=gamma_m
J_(2^m-1)(gamma_1)=gamma_(m+1), there is

  H_m(gamma_a)=gamma_(f(m))，
  H_m(gamma_b)=gamma_(f(m+1))，
  cr H_m=gamma_a.

Therefore, H_m sends these gamma_a,...,gamma_(b-1)d critical points to
[ gamma_(f(m)) , gamma_(f(m+1))) within d Different critical points.
Let the index of one of the images be r. Then r>=f(m)>=b>a.
By (iv), Therth digit ofH_m is0. Due to cr H_m=gamma_a The least significant1 bit of H_m
Exactly at a, The reduction1 only affects theath bit and all bits below it. Therefore, therth position of theH_m-1) series remains0.
The position r in (iii),k must also be0.

For m=1,...,n-1, the above intervals do not intersect with each other, so [b,f(n)) contains at least
(n-1)d items of 0 bits. In addition, it also contains w items of 1 bits. Therefore)

  f(n)-b >= (n-1)d+w，

That is, (G). Proof completed.

Note: The phrase "not in the image of k" is not reversed to mean "the1 position of k".
The use of only the 1 positions cannot specify images, a one-way proposition, and the 0 positions have been constructed.

2. A strengthened lower bound with 16 bits of 1 bits
---------------------
Proposition: If

  1 <= k mod 2^16 <= 2^16-2，

and at least 16 of the bits of k in positions 16 through 255 equal 1, then

  k(gamma_16) >= gamma_272.                             (B)

Proof: For x=k mod 2^16, we make a downward induction from 65534 to 1. The inductive hypothesis holds for all...
Embeddings that satisfy the conditions for the specified low bitsx and the above1 bits are asserted simultaneously.

Basic example x=65534.
At this point, f_k(0)=0, f_k(1)>=16. If f_k(1)>=17, then [D2] Lemma 7.1
Provide f_k(16)>=16*17=272.
If f_k(1)=16, then the same lemma is given first with f_k(16)>=256; therefore, the positions from the 16th to the 255th
All fall within [f_k(1),f_k(16))]. (G) is given accordingly)

  f_k(16)>=16*16+16=272.

Inductive step 1<=x<65534.
First find alpha, beta, and an embedding e, such that

  gamma_0<k(alpha)<gamma_16<=k(beta)，
  The critical sequence of e starts with alpha -> beta -> gamma_16.          (S)

Here, the following six pairs of indices can be used explicitly: (alpha, beta)

  (0,1), (1,4), (4,8), (8,12), (12,14), (14,15).

The existence of a necessary embedding is as follows:
  (0,1): Observations before the D2] Theorem 7.2, or directly take J_65533;
  (1,4):J_14, by Theorem 7.2;
  (4,8):J_14(J_2)), based on the aforementioned point values and covariant identities;
  The last three pairs: Theorem 3.1(a), take n=4, m=2, 1, 0.

If k(gamma_1)>=gamma_16, based on the properties of the last two 0 bits and x<65534,
There must be gamma_0<k(gamma_0)<gamma_16, so we choose (0,1)).
If k(gamma_1)<gamma_16, and since x is non-zero, there are at most 15 of the type 0 in the low 16 position.
Since images can only fall on the positions 0, k(gamma_15)>=gamma_16. Along the way
This index chain consists of 1, 4, 8, 12, 14, 15. By taking the two adjacent points that cross gamma_16, we obtain (S)).

Let H=k(e). Its critical point lies between gamma_0 and gamma_16, therefore
  The index of 1<=cr is <=15.
  x'=H mod 2^16 is a non-zero even number and lies in the range of x'>x.
The lowest bit of H, which is1, is lower than16. Therefore, in the16 to255 positions, the positions ofH andH-1 are exactly the same.
The sequence (iii),H) inherits from the sequence (k) all the positions (1) within this interval, and there are still at least (16) elements.
Therefore, we can use the inductive hypothesis for H to obtain H(gamma_16)>=gamma_272.
From (S) and covariance,

  k(gamma_16)=k(e(beta))=H(k(beta))
              >=H(gamma_16)>=gamma_272.

Proof completed. The inductive argument strictly increases to the low16 positionx, and it is not an unknown length of expansion or a proven process of termination.

3. Raise the block normal form with 16 to gamma_272
-------------------------------
Definition

  h(r)=sum_i bit_i(r)*(2^(16(i+1))-2^(16i))，

That is, repeat each digit of r once, with 16. Let y=65535 and L=J_65534 be the resulting sequences.
Proof for 1<=r<=65535

  L(J_r) ==_(gamma_272) J_(h(r)).                       (N)

This step strengthens the [D2] Theorem 7.2 proof by utilizing the original [gamma_257 truncation.

First, prove 1<=r<65535

  J_(h(r+1)) ==_(gamma_272) J_(h(r))(J_65535).           (E)

Let m=v_2(r+1), s=16m, H=h(r+1-2^m), k=J_H; when H=0, take k=id.
There are
  cr k>=gamma_(s+16)，
  h(r)=H+2^s-1，h(r+1)=H+2^s*65535.

According to the [D2] Lemma 6.7, (E) holds at the minimum value of all the following protective points:

  J_(H+2^s*z-1)(gamma_16)， 2<=z<=65535.

Provide a unified lower bound gamma_272:

If m>=1, then s is at least a 16 times the 16. The corresponding embedding of the lows+16 position is
  2^s*(z-1)+2^s-1，1<=z-1<=65534.
According to the [D2] Theorem 7.2(b), this protection point is at least
  gamma_(s+256)>=gamma_272.

If m=0, then r is an even number between 2 and 65534, H=h(r). H is in the position 16 to 255.
There is at least one complete block with at least one 16 and at least one 1, and the low 16 positions are 0. In this case, the embedding of the protective point
The positionJ_(H+z-1) is low16, located betweenz-1 and1 to65534. The higher positions in this1 block remain unchanged.
Proposition (B) directly provides the required lower boundgamma_272.

Therefore, every protection point is not less than gamma_272, and E) holds true.

Finally, L(j)=J_65535=J_(h(1)), and
  L(J_(r+1))=L(J_r)(L(j)).
By making a finite induction on r, and using the compatibility of (E) and the truncation relation in the application, we obtain (N).

Take r=65534, h(r)=2^256-2^16, to obtain

  L(L) ==_(gamma_272) J_(2^256-65536).                   (K)

In particular, 258<272, thus

  65534 *_258 65534 = 2^256-65536.

This is the indeterminate product left over from the previous round, which has now been determined by paper-based reasoning.

4. Return to the original goal: truncation and low-end facts
------------------------------
Hereinafter denoted by A=J_12, B=J_13, mu=gamma_256, and D=B(J_3).
Section [D1], Section [5], and Section [D2], Section [8] are provided.

  A ==_mu j(J_2)=J_3(J_3)，
  A(gamma_3)=gamma_5，A(gamma_4)=mu，B(gamma_4)=mu，
  J_15(kappa_1)=gamma_5，
  D|V_mu=L|V_mu，L(gamma_16)=mu.

First, it should be noted that D can be replaced with L to gamma_258 and above.
If e|V_mu=f|V_mu, beta+2<mu, and e(beta)=f(beta)>=delta, then
Then e ==_delta f. Because for anyx,
  e(x) intersect V_delta=e(x intersect V_beta) intersect V_delta，
And x intersect V_beta belongs to V_(beta+1), which can be read in ordinary restrictions.
The same applies to f. This is an enhancement with clear protective conditions, and it does not confuse ordinary restrictions with member truncations.

Take beta=gamma_19, e=D, f=L. By ordinary restriction equality and strict increasingness,
  D(gamma_19)=L(gamma_19)>=gamma_259.
Therefore, D ==_(gamma_259) L.

Additionally, from A(gamma_4)=B(gamma_4)=gamma_256 and strictly increasing.
  A(mu)>=gamma_508，B(mu)>=gamma_508.

Apply A ==_mu J_3(J_3) with B, and then safely truncate to gamma_258, resulting in

  B(A) ==_(gamma_258) B(J_3(J_3))=D(D)
        ==_(gamma_258) L(L).

From (K), there is inA_258)

  v:=13*12=2^256-65536.                                 (4)

5. The final sparse operation and equality sign
----------------------
Write z=2^256, M=2^258. The asterisk symbols below are all *_258.
By row recursion,

  p:=13*13=(13*12)*14=(z-65536)*14=z-65522.              (5)

Let P=B(B), T=A(A). Apply A to A ==_mu j(J_2), and use A(mu)>gamma_258.
Obtained

  T ==_(gamma_258) A(j(J_2))
    =B(A(J_2))=B(B(B))=B(B)(B(B))=P(P).

Therefore, it remains in A_258.

  t:=12*12=p*p=z-16，                                   (6)
  t*32=2^257.                                          (7)

The following provides a compression basis for (5)--(7), so as to avoid treating them as large tables that cannot be verified.
In reverse notation, a*_n b corresponds to -((2^n-a) bar* (-b)) mod 2^n.
Its periodic generator is 2^n-a-1.

For (5), the generator is3z+65535, the lower16 positions are all1, and there are two1 at the upper level, namely256 and257.
According to the [D2] Theorem 4.1, with a block width of 16, it is the maximum period of 18 free bits.
Template. Specifically, take the x=3z, n=16, m=0, and y=65535 of this theorem.
By Lemma 5.1, the inverse period of x+1 is 4, with the period values being 0, z, 2z, 3z in sequence.
Therefore, the l=2<=16 of the theorem, as well as the divisibility conditions 2^16|x, also hold.
The right-hand side -14 is in a reverse cycle of length2^18
  2^18-14=3*65536+65522.
The reverse image is 3z+65522, which becomes the positive counterpart, i.e., z-65522.

For (6), the generator is3z+65521. Still using16 as the block width, compress it into the14th row ofA_18.
This line has a period of 32: J_14(gamma_4)=gamma_16. According to Lemma 7.1,
J_14(gamma_5)>=gamma_20. The original right-hand sidep modulo32 is14.
Small table 14*_18 14=65520; This is also described in the [D2] section number 8
  B(J_2)|V_mu=J_65520|V_mu，B(J_2)=J_14(J_14)
Directly obtained. Its reverse value is 3*65536+16, decompressed to 3z+16, and the positive value is z-16.

For (7), the generator is3z+15. Compressed with a block width of4, we obtain the largest period with6 free bits.
Template, positions are 0, 1, 2, 3, 256, 257. The right-hand term - 32 corresponds to 32 within the period 64.
Its inverse image is 2^257, and its forward image remains 2^257.
The parameters for Theorem 4.1 are x=3z, n=4, m=0, y=15, l=2.
32=16*2+0, and the inverse period of x+1 with the term 2 is 2z=2^257.

Finally, because of A(gamma_3)=gamma_5, the covariant identity is given as

  T(gamma_5)=A(A)(A(gamma_3))
            =A(A(gamma_3))=A(gamma_5).

And cr J_32=gamma_5, so cr(T(J_32))=A(gamma_5).
(7) indicates that the remainder of T(J_32) in A_258 is 2^257, and its critical point is precisely gamma_257.
Combining with J_15(kappa_1)=gamma_5, we obtain

  J_12(J_15(kappa_1))=J_12(gamma_5)=gamma_257. Proof completed.

6. Verification range and proof boundaries
--------------------
The new script c1-gap-closure-check.py includes the following finite verifications:
  * Independently constructA_8 according to the definition, verify the207 readable instances ofG);
  * Enhance the lower bound for the small model check of N=2; randomly inspect N=4 instances to find 402 qualified examples.
  * When N=2 and 4, verify the normal form input for all bit blocks individually, truncating to 6 and 20 respectively.
  * Check the bit block index identity and branching conditions used in this proof for r=1,...,65534.
The original script c1-one-bit-check.py has been rechecked for the last two sparse branches.

The verification result for this save is PASS: all index scenarios with 65534 have passed; new script
There are a total of 9810 recursive nodes and 14429 explicit table entries, taking approximately 0.38 seconds. The statistics only describe
The workload of the script is not to replace mathematical induction with sampling of large tables.

These calculations are error-checking and do not replace the general argument in section 1--3. No enumeration of A_258 is performed.
Also, Dougherty's Conjecture 8.1 is not considered a theorem. This paper presents a proof on paper.
Not a Lean formalization. The conclusion only addresses the minimal terms specified here; the other seven terms are precisely defined.
The spectrum index is not automatically determined by this document.
