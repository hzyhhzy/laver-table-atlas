# The quantitative recursion of P4 degenerates into a pure E closed sequence. · [中文版](P4-pure-E-collapse.zh-CN.md)

*English reading edition, translated with machine assistance. The title links to the dated Chinese manuscript.*

> Collected reading edition. The three main papers state the results of this collection.
> This edition retains the local proofs, their hypotheses and any withdrawals. Progress reports describe the state of work at the time.
> The locations of omitted passages on preset inputs are recorded in SOURCE_MANIFEST.json.
> The main papers give the numerical derivations for the natural parameters produced by the proofs. This historical note carries no additional Lean certification.

Let S be the current nine lines of pIBLP seeds, P4=S[0]^5, A=P4[2]=I[0][1], and denote f=f_PP. Although P4>A is strictly reachable, the quantitative functions of the two patterns are identical at every point; more specifically,

$$
\boxed{f(P4,m)=f(A,m)=u_{\omega^\omega}(m)\quad(m\ge1).}
\tag{1}
$$

Here, u is a purely E recursive sequence explicitly given later in the text, and it is not part of the entire pIBLP notation, which consists of FGH. ω^ω is the control subscript of this recursion, and it does not claim that P4 or A have an ordinal equal to ω^ω in the full pIBLP notation order. This equation indicates that ordinal embedding does not automatically yield numerical FGH comparisons; it does not deny the additional structure of the complete S, nor does it change the explicit lower bound of the previous q(5).

## 1 Four-step process independent of parameters

The four M_PP in [P4 Prefix Calculation](<../piblp-q5-enhancement-20261014/baseline-piblp-Cline-prefix.en.md>) are all transient, and the guard is fully replicated. The four steps do not read the numerical parameter m, so for each m, it is an equation of f. The resulting pattern R is

```text
01:1 012:1 0123:2 01234:3 01245:3
```

Its first two lines are fixed, and the next three lines correspond to the parent pointers 0, 1, 2, respectively, which is p_(ω^ω). Therefore, f(P4, m)=f(A, m)=f(R, m). The following directly proves that the entire recursive closure of R, f, has only the E branch, with no parent package scanning or failed cuts.

## 2 canonical parent pointer encoding

For the Cantor normal form of α<ε0, define the parent pointer symbol ps(α). Let the coefficient expansion of each individual term ω^γ be composed of several repeated terms:

- ps(0) is empty;
- ps(β+1)=ps(β) is followed by 0;
- When γ>0, let A=ps(β), a=|A|+1, then after ps(β+ω^γ)=A comes 0, followed by ps(γ), with each item adding a to the words after it.

The pointer positions start from 1, where 0 represents an external root. This notation is the preorder code of Cantor's normal form tree, and all pointers satisfy 0≤u_i<i.

If ps(α)=(u_1, …, u_k), and the first two lines of p_α are fixed; then the position i corresponds to the i+2th line: if u_i=0, it is (0, 1, 2, i+2):2; otherwise, it is (0, 1, 2, u_i+2, i+2):3. There are no marks. Therefore, p_(ω^ω) is exactly the R used in the formula (1).

If α is the successor, the last pointer is 0. Therefore, p_α is the successor of E, and cut(p_α)=p_(α−1). If α is a non-zero limit, the last pointer is t=u_k>0; the true replication threshold of E is

$$
a_{\rm E}=t+2,
\tag{2}
$$

Not an arbitrary selected outer single root. Especially when α=ω^ω, ps=(0, 1, 2), thus a_E=4, while the row address of the outer single root is 3, which is different.

## 3 Proof by coordinate E The accurate identity

The usual basic columns are used: ε0 If α=β+ω^(δ+1), Then α[n]=β+ω^δ·n; If the last index γ is a limit, Then (β+ω^γ)[n]=β+ω^(γ[n]). Here, n≥1.

Given the limit α, let the ps letters be (u_1,…,u_k)), and let t=u_k>0, ℓ=k−t. Remove the last pointer to separate

$$
A=(u_1,\ldots,u_{t-1}),\qquad B=(u_t,\ldots,u_{k-1}).
$$

For the jth copy of the character B, only increase the pointers that are at least t by jℓ. The smaller pointers remain unchanged, denoted as B^(j). There is an accurate formula for the parent pointer.

$$
ps(\alpha[n])=A\frown B^{(0)}\frown\cdots\frown B^{(n-1)}.
\tag{3}
$$

Proof by induction on the last exponent. If α=β+ω^(δ+1), the last pointer t is the root position of the last term; after deleting the last leaf, B is the complete root tree of ω^δ. Copying n times is exactly β+ω^δ·n. If the last exponent γ is a limit, let the last pointer of its ps be v. The outer translation amount is a, and the actual last pointer is t=a+v, not a. Apply induction to γ, and then translate the entire exponent code by a, translating the thresholds of the interval, external pointers, and internal pointers together, exactly giving the expression (3). This also covers any nested limit of γ.

Now, let's examine the actual raw E. E(0) is cut(p_α), and its ps is exactly A followed by B. Let the ps of E(m) be A followed by 2^m copies of B, with its word length being d=t−1+2^mℓ. The next E adds an auxiliary row (t+2,d+3):1), and another raw short copy is performed. The actual coordinate mapping fixes x<t+2, and x≥t+2 is added.

$$
(d+3)-(t+2)=2^m\ell.
$$

The source line ranges from t+2 to d+2, corresponding to exactly the entire existing 2^m copies of B. The 0, 1, and 2 in the core are all fixed; the internal parent pointers are shifted according to the definition of B^(j); the external parent pointers are fixed. Therefore, this round doubles the number of copies of B from 2^m to 2^(m+1), and the step size is maintained line by line. Inductive conclusion

$$
\boxed{E_{p_\alpha}(m)=p_{\alpha[2^m]}.}
\tag{4}
$$

All replicated coordinates lie within the domain of "fixed low zones or complete translation high zones". The first complete replication of f on p_α also passes the guard: the last line contains 0, 1, 2, with the replication starting point being 1. The only low address 0 has a specified image, while the rest of the addresses belong to translation zones. The entire family has no marks, and the branch of E is not subject to PP scanning, so these properties are retained throughout the evaluation closure.

## 4 Pure E Function Equality

Definition

$$
u_0(m)=m2^m,\qquad
u_{\alpha+1}(m)=u_\alpha^{\circ2^m}(m),\qquad
u_\lambda(m)=u_{\lambda[2^m]}(m).
\tag{5}
$$

The precise cut formulas for formulas (4) and the successors of E are given by α<ε0, and are recursively derived as f(p_α, m)=u_α(m). A full definition of these pure grammatical calls is provided. The induction for α is used here to independently illustrate the control subscript of the pure E recursion; the actual quantitative bridges for q(5) still use the same I3 algebra and finite current linedness evidence.

α=ω^ω and the fourth-parameter invariant M in the first section yield the formula (1). Especially in m=1,

$$
(\omega^\omega)[2]=\omega^2,\quad
(\omega^2)[2]=\omega\cdot2,\quad
(\omega\cdot2)[2]=\omega+2,
$$

So f(P4, 1)=u_(ω+2)(1)=C_line, restore the existing long-chain constants. For the general m, the formula (1) is stronger than this single-point identity.

It is also possible to accurately eliminate the outer exponents using a common form of hierarchy. Definition

$$
\mathcal M_0(n)=n^n,\qquad
\mathcal M_{\alpha+1}(n)=\mathcal M_\alpha^{\circ n}(n),\qquad
\mathcal M_\lambda(n)=\mathcal M_{\lambda[n]}(n).
\tag{6}
$$

By induction on α, we obtain

$$
\boxed{2^{u_\alpha(m)}=\mathcal M_\alpha(2^m).}
\tag{7}
$$

The zero term is because it is 2^(m2^m)=(2^m)^(2^m). The successor terms undergo n iterations at n=2^m; every intermediate input is always a power of 2, as the lower-level inductions have already written the function output as a power of 2. The index of the limit branch is precisely 2^m. Therefore, there are specifically 2^f(P4, m)=M_(ω^ω)(2^m), which are accurate, and only use the exponential conjugate formulas for ordinal numbers below ε0.

This conclusion does not strictly follow the classical FGH pattern of sandwiching by F_0(n)=n+1 and the subsequent iteration by n+1, where M_α is used instead. The base functions and the number of iterations for the two conventions differ, and it is not possible to directly rewrite the formula (7) as the previous F_α. However, this already illustrates that f can completely avoid a strict decrease along a full index sequence, and that an internal pattern with a large order can degenerate into a simple E control family in this numerical recursion. The next step of external embedding must retain quantitative ports, rather than just preserving order.

## 5 Minor Scale Verification

The verification process (historical reference: `canonical-E-family-audit.py`) directly invokes the existing raw copy and PP implementation to complete 99 subsequent cuts or E checks for core, step-size, and marks identities, including ω^ω, nested limits, mixed Cantor monoms, and m=0 to 4. Additionally, it accurately verifies P4 four transient paths. The peak execution time is 54 lines, 302 storage entries, and it exits in approximately 0.02 seconds. The full formula (3), (4) is based on the above coordinate induction, not on this finite set of examples.
