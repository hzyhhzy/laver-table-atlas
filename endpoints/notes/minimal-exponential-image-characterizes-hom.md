# Equivalence between minimal index images and homomorphisms of the third level blocks · [中文版](minimal-exponential-image-characterizes-hom.zh-CN.md)

2026-11-09. Fixing I3 into the context. The main equality is not determined. This document strengthens the sufficient condition in third-level-certificate-needed.zh-CN.md to a necessary and sufficient condition, but does not prove the condition itself.

## 1. Universal Propositions

Let $k(\gamma_0)=\gamma_1$, $k(\gamma_1)=\gamma_m$ be two sets, where $m\ge2$ is a fixed set, and let $n\ge2$ be another fixed set. Denote

$$
 D=m^n,\quad d=D+1,\quad q_r=m^r\ (0\le r\le n).
$$

Define the column deletion map $\Phi_{m,n}:A_{n+1}\to A_d$:

$$
 \Phi_{m,n}\left(\sum_{r=0}^{n}a_r2^r\right)
 =\sum_{r=0}^{n}a_r(2^{m^{r+1}}-2^{m^r})\pmod{2^d}.
\tag{1}
$$

The last bit has only the $D$th bit modulo $2^d$.

**Proposition.** If $f_k(n)=D$, then in $A_d$, the entire row multiplied by $k$ satisfies the condition.

$$
 \boxed{k*a=\Phi_{m,n}(a)\qquad(0\le a<2^{n+1}).}\tag{2}
$$

Therefore, $\Phi_{m,n}$ is a bijection homomorphism.

Here, the left multiplication by $k$ refers to its representation by $A_d$, and it is not the ordinary natural number multiplication. All outputs of the "read image" are clearly located below the truncation.

## 2. First, find all the right-hand parameters $2^r-1$

Exponential bounds and equicontinuousness

$$
 f_k(r)=q_r\quad(0\le r\le n).
\tag{3}
$$

In the current table, the period of the $k$ row is exactly $2^{n+1}$: $f_k(n)=D<d$, and the strict increasing property ensures that $f_k(n+1)\ge d$. Therefore, within the parameter $1,\ldots,2^{n+1}$, this row is strictly increasing, with the final 0 serving as the top of the table.

For $1\le r\le n$, let

$$
 E_r=J_{2^r-1},\qquad H_r=k(E_r).
$$

The first two symbols of $E_r$ are $r,r+1$, and the critical point is $\gamma_0$. Therefore

$$
 \operatorname{cr}H_r=\gamma_1,\quad f_{H_r}(1)=q_r,
 \quad f_{H_r}(m)=q_{r+1}\quad(r<n).
\tag{4}
$$

When $r=n$, the continuous block rule of the first critical image is directly given

$$
 H_n\bmod2^d=2^D-2.\tag{5}
$$

For $r<n$, the last value of 4) is $m q_r$. The linear equipartition part of the Dougherty II Lemma 7.1 gives

$$
 H_r\bmod2^{q_{r+1}+1}=2^{q_r}-2.\tag{6}
$$

Now we will make a downward induction from $r=n-1$. If $H_{r+1}\bmod2^d=2^{q_{r+1}}-2$ already exists, then the strict increasing order of parameters within the same row gives

$$
 0<H_r\bmod2^d<H_{r+1}\bmod2^d<2^{q_{r+1}}.
$$

Combining (6), excluding all higher bits, thereby)

$$
 \boxed{k*(2^r-1)=2^{q_r}-2\quad(1\le r\le n)}\tag{7}
$$

The complete target table $A_d$ holds true. This downward induction is necessary: merely based on (6) alone, it cannot assert that higher bits are 0.

## Find a single square right parameter for 3.

For $0\le r<n$, applying $k(J_{2^r})$ to its critical points gives the first critical image, which is $q_r,q_{r+1}$. Therefore, its configuration below $q_{r+1}+1$ is
$2^{q_{r+1}}-2^{q_r}$.
Also, due to the increasing property within the row, and (7),

$$
 k*2^r\le k*(2^{r+1}-1)=2^{q_{r+1}}-2<2^{q_{r+1}},
$$

Therefore, high positions are also excluded, resulting in

$$
 \boxed{k*2^r=2^{q_{r+1}}-2^{q_r}\quad(0\le r<n).}\tag{8}
$$

For $r=n$, the critical point index is $D$, and the table order is $D+1$. Therefore,

$$
 \boxed{k*2^n=2^D.}\tag{9}
$$

## 4. Binary induction with arbitrary right parameters

Let $a=2^r+b$, $0<b<2^r$, and $r<n$ be defined. In the source $A_{r+1}$, there exists a semi-upper bound identity.

$$
 J_{2^r}(J_b)\equiv_{\gamma_{r+1}}J_{2^r+b}.
$$

Applying $k$, there is a truncation by the members of $\gamma_{q_{r+1}}$

$$
 k*(2^r+b)\equiv (k*2^r)*(k*b).
\tag{10}
$$

From (7),$0<k*b<2^{q_r}$. In $A_{q_{r+1}}$, the interval row $2^{q_{r+1}}-2^{q_r}$ operates on this right parameter exactly like ordinary addition, so the right end of (8)(10)) is

$$
 2^{q_{r+1}}-2^{q_r}+k*b.
$$

Both ends are strictly less than $2^{q_{r+1}}$: The left end is still guaranteed by the inner upper bound of (7). Therefore, this lower truncation equation is sufficient to read the complete integer equations in the current table. By induction on the number of binary digits, it follows that (2) holds for $0<a<2^n$.

Finally, let $a=2^n+b$ and $0<b<2^n$ be defined. The same source identity holds under $\gamma_{n+1}$; its image truncated at $k(\gamma_{n+1})\ge\gamma_{D+1}$ is high enough, so it can be used directly at $A_d$. From (9) and the upper half table formula,

$$
 k*(2^n+b)=2^D+k*b.
$$

Add $b=0$ to the cases where (9) with the right parameter being 0, to complete all (2). Since the left multiplication is a homomorphism, and the period is exactly $2^{n+1}$, (2) is the described injection homomorphism.

## 5. Necessary and Sufficient Conditions for the Main Problem

Let $m=n=256$, $D=T=2^{2048}$, $g=2^{256}-3$. target-boundary-normal-form.zh-CN.md has been materialized into $J_g$. Combining this proposition with the sufficientness proofs in old documents, we obtain

$$
\boxed{
 J_{11}(\gamma_3)=\gamma_T
 \quad\Longleftrightarrow\quad
 \Phi_{256,256}:A_{257}\longrightarrow A_{T+1}
 \text{ preserves the Laver operation}.
}\tag{11}
$$

Therefore, finding any strict failure product for the**Specific truncation** $\Phi$ now is sufficient to disprove the main equality; there is no need to restrict the failure product to the previous fourth image test. However, the stronger $G_3[256]:A_{257}\to A_{256^{257}}$ is still only a sufficient condition, and this paper does not prove that it is equivalent to the main equality.

This document does not provide proof that either side of the inequality 11) is true or false. The precise parameter range for three-layer homomorphisms has not yet been determined, and thus the applicable upper bound based on speculation cannot be cited.

## 6. originates from and is verified within the scope of...

- [Dougherty II](https://arxiv.org/pdf/math/9503204): Finite table period,
Application to member truncation, the linear equilibrium part of Lemma 7.1.
- exclude-2pow2048-rigidity.zh-CN.txt: Indexed bounds and equality.
- target-boundary-normal-form.zh-CN.md: The principal truncation identification of the actual object and the first critical image position rule.

finite_exponential_hom_audit.py independently checks several sets of equivalent instances in the small table according to the definition, including both success and failure cases. It only examines finite scales and does not prove the homomorphism for the target scale. This paper still does not provide a translation or formalization in the general pure ZFC or Lean form.
