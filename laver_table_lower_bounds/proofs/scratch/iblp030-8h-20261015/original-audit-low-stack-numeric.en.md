# Independent numerical audit of the low finite-type staircase · [中文版](original-audit-low-stack-numeric.zh-CN.md)

*The working paper was written in English. Its title links to the Chinese translation.*

> Collected reading edition. The three main papers state the results of this collection.
> This edition retains the local proofs, their hypotheses and any withdrawals. Progress reports describe the state of work at the time.
> The locations of omitted passages on preset inputs are recorded in SOURCE_MANIFEST.json.
> The main papers give the numerical derivations for the natural parameters produced by the proofs. This historical note carries no additional Lean certification.

2026-10-15, 16:10 UTC. Read hardy-root-low-stack-numeric.txt completely.
Scope: the numerical compiler, its types, source index, and tail-order
uses. The actual geometric admission/exit contracts are not re-proved.

Verdict: PASS, relative to the explicitly cited safe-D cover, BMS literal
seed paths, exact original first-root identity, and hereditary all-tail
admissibility lemmas. In particular, this does not prove the original R
target and does not turn an unchecked type level into an actual contract.

1. W>=T^4 is a whole-object inequality at the correct types. If X
dominates fourth power, X^4(Y)>=X^2(Y)=X(X(Y))>=(X(Y))^4. Extensiveness
also gives X(Y)>=Y, so the next collapsed object still dominates the next
named D_r, and therefore fourth power at that next type. This justifies
the finite descent through the left-associated chain, not merely a scalar
comparison after an argument has been selected.

2. The original source identity has top B_(n-2). Reserving one type gives
n=L+1, so its top is B_(L-1), exactly the chain bounded by U=T(T(S)).
U>=T(S^2) and the tail comparison B_0<=_3 S^2 give
  U>=_3 B_(L-1)...B_1(B_0).
Also U(f0)>=_3 h. Hence q=U(U(f0))>=_3 H_(C[L+1]). The hereditary tail
classes are essential for this mixed argument/operator substitution;
ordinary monotonicity alone would not license it.

[The three main papers give the natural inputs and their full derivation. This reading edition omits the older treatment with a preset input.]

4. W(S)>=T^4(S)>=T(U)>=U^4 gives the claimed actual-value lower bound
  Y>=U(q)(1)>=S(q)(1)>=q(q(1))=q(M)>=H_(C[L+1])(M).
The final source comparison is at M>=3. It does not substitute a source
object into a fast comparison at input 1. All inequalities before that
are whole-object inequalities over all positive inputs.

5. U and q are numerical intermediate objects in a comparison of the ONE
actual evaluation W(S)(f0). They need not themselves receive independent
physical endpoint contracts. The latter evaluation still requires all
the concrete low-stack admission contracts stated in the geometric work.

[The three main papers give the natural inputs and their full derivation. This reading edition omits the older treatment with a preset input.]

Addendum, 16:20 UTC: read hardy-root-C7-q5-single-file.txt completely.
Its sections 2 and 6--7 specialize the audited compiler correctly at
L=6. P=C[7]=J^6(A0) has seven four-row blocks, hence 28 rows; its top
source operator is B5, while Tstar=D5...D1 and W=D6...D1 reserve one
whole type. No new scalar-at-1/source substitution or change of the
original IBLP definition was found. Verdict on these sections: PASS
with the same named older dependencies. The geometric sections 3--5
remain outside this independent numerical audit's scope.

[Original manuscript](<original-audit-low-stack-numeric.txt>)
