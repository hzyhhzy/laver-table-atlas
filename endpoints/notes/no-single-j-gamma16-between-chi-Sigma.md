# Small parameter single-layer J_a(gamma_b) exclusion in (chi,Sigma) · [中文版](no-single-j-gamma16-between-chi-Sigma.zh-CN.txt)

2026-11-09, fixed embedding presentation of I3.
chi=J11(gamma3)，Sigma=J13(gamma16)，Theta=J11(gamma4).

Users explicitly require the J_a(gamma_b) form. Embedding application word
(J11(J3))(gamma_n) does not conform to this form and cannot serve as an example for this problem.)

Conclusion: In the entire rectangle of 1<=a<=16 and 0<=b<=16, there is no such thing.
  chi<J_a(gamma_b)<Sigma.
Therefore, if a new example of this single-layer form is found, at least one parameter must exceed 16.
It is not claimed that there is no larger parameter range either.

Proof Source and Classification
--------------
Old document ../small-jn-km-100-20261109/research-list-gamma16.json
It is not a paper proof that exhausts the items under 272. The old classification can be directly applied to this problem:

1. The items with the symbol 95 have precise natural number spectra, with the largest being 16384, which is strictly less than
   index(chi)>=2^2048, therefore all are below chi.
2. 157 term is Theta, and the other 2 term equals Theta; due to Sigma<Theta, they are all within Theta.
   Outside this open interval.
3. The items marked with 7 are J12(gamma_b) and 9<=b<=15. The upper bound on paper is marked as gamma1792.
   Still strictly less than chi.
4. The remaining 11 items are exactly: chi itself; J12(gamma16); J13(gamma_b)
   (8<=b<=16). This catalog contains new proofs.)
   j13-gamma13-15-below-chi.zh-CN.txt indicates
     J13(gamma15)<J12(gamma16)<chi<Sigma.
   Due to strict increasing order, b<=15 All items are less than chi. b=16 stands for Sigma.

95+157+2+7+11=272, with no omissions. The proof does not require chi to be exactly equal to
gamma_(2^2048), only using its proven lower bound.

States with larger parameters
--------------
Only old nested-sup-results.json and nested-block-results.json were queried.
Nameless single-layer images; They do not record any examples where a proven point located at (chi,Sigma) exists.
These old partial orders have unresolved items, and not all images of a<=100 and b<=16 have been exhausted.
Therefore, this query can only report that 'there are no confirmed examples', and cannot prove that expanding the scope does not exist.

Previous observation (different from the current specified form)
------------------------------
LetQ=J11(J3),q=J13(J14)(J12). The old entrance proof is given as
q==_Sigma Q, q(gamma4)=chi, q(gamma256)=Sigma.
For 5<=n<=255, strict monotonicity and strict output guards are provided.
  chi<q(gamma_n)=Q(gamma_n)<Sigma.
This is a family of short application expressions, but theQ cannot be considered as a single small subscriptJ_a.
