# The equality in the third item: C3=gamma_1024 · [中文版](c3-gamma1024-drapal.zh-CN.txt)

2026-11-09. Fix the embeddingj withI3, and continue using the directoriesJ_a=j_(a),gamma_i, andA_d.

Conclusion
----
  C3=J_12(gamma_8)=J_13(gamma_5)=gamma_1024.

Here, the bit stretching homomorphism theorem published by Drápal 1995 is cited; no longer relying on unfinished work.
The scheme of "raising the Dougherty original truncated protection to a unified level". The precise statement of the cited theorem is as follows:
Verified in the publisher's public summary. The restrictions on the source and this verification are detailed in section 5.

1. The cited theorem of position expansion
------------------
For the integer d>=1, let r=v2(d), and define it on the binary expansion of non-negative integers.
  nu_d(sum_i a_i*2^i)
    =sum_ia_i*(2^((i+1)*2^d)-2^(i*2^d)),a_i belongs to {0,1}.
This is to repeat each element2^d times.

Drápal's theorem asserts that
  nu_d:A_k -> A_(k*2^d)
Laver homomorphism, if and only if
  k<=2^(2^(r+1)).                                      (D)

The elements here with A_k are 0,...,2^k-1, and the operation satisfies a*1=a+1 mod2^k.
0 represents the maximum/unit element in this table. Only refer to cases with d>=1 to avoid using d=0.
The convention for v2(0).

This task takesd=4,r=2,k=65. Because
  65<=2^(2^3)=256，
It is proven thath=nu_4:A_65 -> A_1040 is indeed a homomorphism, and moreover,h(1)=65535.

2. Read an entire line from the homomorphism.
------------------
Write L=J_65534. Left distributivity ensures that the left translations in A_1040
  a |-> 65534 *_1040 a
It is also a homomorphism. Its value on the generator 1 is 65535, which is the same as h.

More specifically, we induce directly from 1<=a<2^65 to a: the initial values are the same, and
  h(a+1)=h(a)*_1040 h(1)，
  65534 *_1040 (a+1)
    =(65534 *_1040 a)*_1040(65534+1).
Therefore
  65534 *_1040 a=h(a)，0<=a<2^65.
When a=0, both sides are also 0. Here, only finite induction is used, and the 2^65 items are not actually enumerated.

Takea=2^64, we get
  65534 *_1040 2^64=(2^16-1)*2^1024.
The right-side 2 is assigned the value exactly 1024, and is less than 2^1040. Therefore
  L(gamma_64)=gamma_1024.                              (1)

It is also possible to project the equation onto A_1025 to obtain the originally unresolved finite table criterion.
  65534 *_1025 2^64=2^1024.

3. Return to the original third item
------------------
Section c2-gamma260-and-c3-reduction.zh-CN.txt of the previous manuscript has been proven in the 5 section.
  J_13(J_3)|V_(gamma_256)=L|V_(gamma_256)，
  J_13(gamma_3)=gamma_64，J_3(gamma_3)=gamma_5.
Due to gamma_64<gamma_256, we can substitute gamma_64 into this ordinary restriction equation:
  L(gamma_64)
    =J_13(J_3)(J_13(gamma_3))
    =J_13(J_3(gamma_3))
    =J_13(gamma_5)=C3.
Finally, with (1). End of proof.

Note: This is a general restriction on the domain, allowing outputs that exceed gamma_256.
Do not mistakenly treat membership relationships as ordinary restrictions.

4. The available range obtained simultaneously
-------------------
Theorem (D) also allows k=256, hence h:A_256 -> A_4096 is a homomorphism.
The same derivation yields
  J_65534(gamma_m)=gamma_(16m)，0<=m<256.             (2)
Therefore, the linear spectrum mapping that could only be used at m<=16 has now been extended to all m<256.

The endpoints m=256 are not within this conclusion: 2^256 in the source table A_256 is 0.
It cannot be read as J_65534(gamma_256). If we take k=257, the condition (D) fails.
Therefore, the same bit expansion homomorphism cannot be continued to be used.

This extension can also independently shorten the proof of the constant value 14 *_21 32=2^20 used for C2:
Letd=2,k=6, and assume that the condition6<=16 holds. Thennu_2:A_6->A_24 is a homomorphism.
Therefore, 14 *_24 32=15*2^20, projecting onto A_21 yields the required constant.
The original independent finite certificates remain valid and do not need to be deleted.

5. Literature, verification scope, and matters still unresolved
--------------------------------
[Dr95] Aleš Drápal, Persistence of cyclic left distributive algebras,
Journal of Pure and Applied Algebra 105(2), 1995, pp.137-165.
DOI:10.1016/0022-4049(94)00142-1.
Publisher's page:
https://www.sciencedirect.com/science/article/pii/0022404994001421
DOI link:
https://doi.org/10.1016/0022-4049(94)00142-1

The public abstract of this paper provides a formula for nu_d and a complete necessary and sufficient condition for the parameters (D).
The original abstract retrieved from the publisher's index was checked for nested levels of the index, and compared with the author's name.
The abstract of the research paper has been cross-checked. The web page can be opened directly, and PDF access still returns 403 or
Cache miss, therefore this document does not claim to re-audit Drápal's 29 pages of proof.
This is a proof of a theorem that has been published; it does not take one's own small model conjecture as a premise.

The exact indexing of C4, C5, C6, C7, and C8 has not been resolved in this document.
The previous strict sorting and lower bounds remain valid; it is not possible to extend (2) to m=256 or larger.
