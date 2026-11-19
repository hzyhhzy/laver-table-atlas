# In the 13th row, the 15th item: The high position is determined entirely by the fourth image threshold. · [中文版](c15-terminal-block-normal-form.zh-CN.md)

Fix the embedding of I3 and its critical spectrum. This lemma for 2026-11-09 provides a normal shape without the need to assume the main equality or the fourth image equality. The exact values for the 11 row are subsequently given in a complete proof. [Proof of equality](../proof.md)

## 1. Symbols and Conclusions

Continue to use

$$
 C=J_{13},\quad b=J_{12},\quad
 G(\gamma_{256})=J_{11}(\gamma_3)=\gamma_s,\quad T=2^{2048},
$$

$$
 N=256,\quad F=N^4=2^{32},\quad
 \ell=2^N-2,\quad g=\ell-1,
 \quad u=2^N-16,\quad q=2^N-4.
$$

Define the actual spectrum index $a$ as

$$
 G(\gamma_4)=b(\gamma_{16})=\gamma_a.
$$

There are already $F\le a<s$ and $s\ge T$. Note that $C*15$ represents the application of the product $J_{13}(J_{15})$, not the critical point image $C(\gamma_{15})$.

**Theorem.** for all integers $F+1\le d\le T+1$.

$$
\boxed{13*_d15
 =\ell+2^d-2^{\min(a,d)}.}
\tag{1}
$$

That is, the lower positions are continuous blocks $[1,N)$; if it is $a<d$, then a continuous block $[a,d)$ is added; there are no 1 positions other than this. If it is $a\ge d$, the second block is empty.

In particular

$$
\boxed{a=F\quad\Longleftrightarrow\quad
13*_{F+1}15=2^F+\ell.}
\tag{2}
$$

The value of the other branch $a>F$ is exactly $\ell$. This is another interpretation of the old fourth image square junction, and it does not determine which branch occurs.

## 2. is a general row-end formula

Let the actual embedding $A$ in the rows of $A_d$ have a period of $2^k$, $f_A(r)=v<d$, where $r<k$.

$$
 A*_d(2^k-2^r)=2^d-2^v.
\tag{3}
$$

Proof: The critical point representing $c=2^k-2^r$ is $\gamma_r$, and the first critical image is $\gamma_k$. Therefore, the critical point representing $A(J_c)$ is $\gamma_v$, and the first critical image is $A(\gamma_k)\ge\gamma_d$. The continuous block rule of the first critical image forces the entire $A_d$ to represent precisely $2^d-2^v$. Here, only the critical points below the truncation are considered; the threshold $\ge\gamma_d$ is used only for the first image.

Furthermore, for $0<t<2^r$, the source terminal blocks satisfy $c*t=c+t$. Multiplying by $A$ is a homomorphism, therefore

$$
 A*_d(2^k-2^r+t)
 =(2^d-2^v)*_d(A*_d t).
\tag{4}
$$

On the right side, read its right parameters in cycles of $2^v$. If the remainder is $z\ne0$, the result is $2^d-2^v+z$. It is not possible to simply replace the remainder here with the complete $A*_d t$.

This problem only uses $r=4,t=1,A=G$. When $a=f_G(4)<d$, $G*_d1=\ell<2^a$, therefore

$$
\boxed{g*_d(-15)=2^d-2^a+\ell.}
\tag{5}
$$

The negative right parameter indicates the remainder of the modulo row period. If $a\ge d$, the $g$th row period is divisible by 16, and for $-15\equiv1\pmod{16}$, the same product is $\ell$.

## 3. The actual product is reduced to $u*14$

It has been proven that the high truncated input is: among all $d\le T+1$.

$$
 G\equiv_{\gamma_d}J_g,\quad
 U=b(b)\equiv_{\gamma_d}J_u,\quad u*_d12=q.
\tag{6}
$$

Where $U\equiv P(P)$, $P=C(C)$, and $P\bmod2^{16}=14$. Also

$$
 P(\gamma_{16})=C(\gamma_{16})>J_{11}(\gamma_3)\ge\gamma_T.
$$

So in $d\le T+1$, the row period of $P$ is a multiple of $2^{16}$. Therefore,

$$
 C(J_{14})=P(J_{14})\equiv P(P)\equiv J_u.
$$

The first equation is $C(J_{14})=C(C(j))=C(C)(C(j))=P(J_{14})$. Therefore

$$
\boxed{13*_d15=u*_d14.}
\tag{7}
$$

## The truncation is strictly below $s+1$ when 4.

If $d\le s$, denote the predecessor of the actual $G$ application as $Q$, that is, $G=Q(j)$. Its finite representation is $q$, and it satisfies $Q(\gamma_4)=\gamma_s$, so the $q$th row is a period that divides 16. By the (6) and finite table recurrence,

$$
 u*_d13=q*_d(u+1)=q*_d1=g,
\qquad u*_d14=g*_d(u+1).
\tag{8}
$$

On the other hand, $G(\gamma_{256})=\gamma_s\ge\gamma_d$ indicates that the period of the $g$ row is a multiple of the $2^{256}$. Since $u+1=2^{256}-15$, the last term of 8) is $g*_d(-15)$. Now, directly using (5) and its $a\ge d$ branches, we obtain (1).

This covers all cases of $d\le T$, as well as $d=T+1,s>T$.

## 5. Only remaining boundary $d=T+1,s=T$

At this moment, $B=2^T$. The $q$th row has a period of 32, and $q*_{T+1}16=B$, so the recurrence is given as

$$
 q*_{T+1}17=B+g.
$$

Because $u+1\equiv17\pmod{32}$, there is

$$
 u*_{T+1}13=B+g,
 \qquad u*_{T+1}14=(B+g)*_{T+1}(u+1).
\tag{9}
$$

In the lower table $A_T$, $a<s=T$, and the $g$th row has a period that divides $2^{256}$. The 2th section formula gives

$$
 g*_T(u+1)=2^T-2^a+\ell\ne0.
$$

The upper half formula transforms (9) into

$$
 B+(2^T-2^a+\ell)=2^{T+1}-2^a+\ell,
$$

That is, (1). The output equal to $\gamma_T$ is not truncated from $\gamma_T$; this step reads $q(\gamma_4)=\gamma_T$ from $\gamma_{T+1}$.

## The result 6. excludes which types of repetitive work

If the fourth image takes the equal value $a=F$, then even without knowing the main equal value $s=T$, there is already

$$
 13*_{T+1}15=2^{T+1}-2^F+\ell.
$$

So, by checking each term of this product at $F,\ldots,T$, we can independently test the 256 terms that cannot be solved by the main equality. They are actually controlled by the same fourth threshold.

This document does not determine whether $a=F$ or $a>F$ holds, nor does it improve the unconditional bound of $s\ge T$. However, it is an unconditional complete product shape, not just a necessary condition for "if the main equality holds...".

The test checks for terminal_row_formula_audit.py in all non-zero rows that are exact $A_{12}$, in all applicable indices where (3) and $t=1$ are present in the (4), for a total of 20,472 items passed. The array load is approximately 0.30 MB, and the time taken is 0.015 seconds. This test only verifies small tables and does not replace the general paper proofs mentioned above.

Dependence: target-boundary-normal-form.zh-CN.md
after-c6-supremum-lift.zh-CN.txt, exclude-2pow2048-rigidity.zh-CN.txt，
As well as the periodicity, covariance, and finite table recurrence of [Dougherty II](https://arxiv.org/pdf/math/9503204). No new proofs or Lean proofs have been provided for the pure ZFC context.
