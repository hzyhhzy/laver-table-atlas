# The order at which the period first reaches 32: a lower bound of a BMS limit layer FGH · [中文版](laver-period-32-BMS-bound.zh-CN.md)

*English reading edition, translated with machine assistance. The title links to the dated Chinese manuscript.*

> Collected reading edition. The three main papers state the results of this collection.
> This edition retains the local proofs, their hypotheses and any withdrawals. Progress reports describe the state of work at the time.
> The locations of omitted passages on preset inputs are recorded in SOURCE_MANIFEST.json.
> The main papers give the numerical derivations for the natural parameters produced by the proofs. This historical note carries no additional Lean certification.

2026-10-14. This paper continues the unified lemmas of this catalog to the final numerical comparison. The axiomatic condition is **ZFC + I3**; this is a paper proof, which has not yet been formalized in Lean. The initialization directly uses the published conclusions on linedness of Qi, without relying on the marked completions earlier in this catalog, the steps starting from 32, or the proofs of preserving endpoint repositioning. No row number feedback from another research catalog is used either.

The BMS directly invokes the established theorems from the [Summary of fixed index decline and FGH docking](<BMS-fixed-index-to-FGH-summary.md>) specified by the user. This summary only proves the BMS side, while this article is responsible for completing the Laver side and the final numerical comparison. What is accomplished here is the **A strict lower bound of the BMS hierarchy**, not the delivery of the structural super-BMS notation required by the main line. Adding a successor to the BMS limit, adding the $\omega$, or multiplying by the $\omega$ is not considered as achieving the main line's goal.

**The following stronger conclusion follows by combining the constructions.**[Two-round feedback three-layer BMS FGH lower bound](<../iblp-030-laver-20261014/nested-bms-FGH-bound.md>) yields $q(5)>F_{\mathrm{BMS}}(F_{\mathrm{BMS}}(F_{\mathrm{BMS}}(F_3(257))))$. It also checks the overhead of transitioning to the next round of lines for each output. This paper retains a proof that does not rely on feedback. The dependency chain between the two papers is the long-chain initialization and integer budget that this paper calls upon the other paper.

## Conclusions and Conventions

Put

$$
q(5)=\min\{m:\text{size }2^m\text{ in the ordinary binary Laver table has first-row period at least }32\}.
$$

Using the original BM4 fundamental sequence, let

$$
B_r=(0^r)(1^r),\qquad R_h=(0^h)(1^h)(1^h),\qquad
D(h)=\text{from }R_h\text{ repeatedly applying the original }[1]\text{ steps to the empty matrix}.
$$

The original `[1]` is equivalent to the new representation `[2]` of the parent table in this directory, so it is also denoted as $D_2(R_h)$. The convention for FGH is

$$
F_\varnothing(x)=x+1,\quad
F_{MZ}(x)=F_M^{\circ(x+1)}(x),\quad
F_M(x)=F_{M[x]}(x)\quad(M\text{ has a nonzero last column}),
$$

Among them, $Z$ represents the all-zero column. The outer topmost elements are denoted as $\mathrm{BMS}[x]=B_{x+1}$, that is, $F_{\mathrm{BMS}}(x)=F_{B_{x+1}}(x)$. The finite index $F_3$ follows the same convention.

**Theorem.** Under the above agreements and I3 assumptions, $q(5)$ exists. Moreover

$$
\boxed{q(5)>F_{\mathrm{BMS}}\bigl(F_3(257)\bigr).}
\tag{1}
$$

More generally, let $C=f(p_{\omega+2},1)$, its exact finite recursive definition that does not use ordinal notation is given by the formula (5). For any positive integer $r,x$, there is

$$
\boxed{r+\lceil\log_2(x+2)\rceil\le C
\quad\Longrightarrow\quad q(5)>F_{B_r}(x).}
\tag{1a}
$$

The following presents a fixed lower bound for the descent, as well as independent inferences from the original target $q(5)>F_{B_{11}}(10)=F_{\mathrm{BMS}[10]}(10)$. The comparison is made with the order parameter of the table, $m$, not the number of elements, $2^m$.

## Number of lines required for 1.: A uniform theorem of arbitrary height

Let $\ell(x)=\lceil\log_2(x+2)\rceil$ be denoted as such. The uniform theorem for [BMS Docking Summary](<BMS-fixed-index-to-FGH-summary.md>) is given as follows

$$
\boxed{D(h)\ge F_{B_r}(x)
\quad(r,x\ge1,\ h\ge r+2+\ell(x)).}
\tag{2}
$$

It is a universal proof concerning any $r,x,h$, not limited to the 17 row: first precisely compile FGH into $H_{W(B_r)}$, then add a row of forest control parameters to grow, and finally use ancestor coverage and row width exchange to carry this $r+1$ row and $x+4$ column auxiliary matrix. The complete local proofs are in the order of [FGH to Hardy](<fixed-index-growth-interface.en.md>), [Forest controller](<diagonal-forest-hardy-proof.md>), [Counting coverage and row width exchange](<ancestor-cover-growth.md>). The input used is a specific seed $R_h$, not any matrix with $h$ rows.

In particular, for each $h\ge7$,

$$
D(h)\ge F_{B_{h-6}}(10).
\tag{3}
$$

The six lines of loss correspond to a fixed input 10; the general loss for the input is $2+\ell(x)$. It is not possible to change the input in (3) while maintaining the same number of lines.

## Published long chains and their lengths marked with 2.

Fix the I3 embedding in $j$, and all embeddings and critical points come from the same $\operatorname{Iter}(j)$. Continue using [Low point initialization](<short-terminal-initialization.md>) as
$K=j_{(11)}$, $\theta_5=K(\kappa_3)$, $\theta_6=j_{(10)}(\kappa_3)$, 
$\theta_7=K(\theta_5)$. Given
$\theta_5<\theta_6<\theta_7<\kappa_4$.

[Proof of Proposition 1.3(1) in Section 3 of "Notes on Laver Tables" by Qi](https://arxiv.org/html/2501.06733v5#S3) is directly given.

$$
(\kappa_0,\kappa_1,\theta_5)\text{ is }C\text{-lined},
\qquad C=f(p_{\omega+2},1),\qquad 2^C=m_{\omega+2}(2).
\tag{4}
$$

Here, the actual chain used in the proof is used, rather than guessing the existence of a chain with a large number of critical points in reverse order. Its length can be completely written as a finite integer recursive sequence:

$$
\begin{aligned}
g(x)&=x2^x,& u_0(x)&=g(x),\\
u_{k+1}(x)&=u_k^{\circ2^x}(x),&v(x)&=u_{2^x}(x),\\
w(x)&=v^{\circ2^x}(x),&C&=w(w(1)).
\end{aligned}
\tag{5}
$$

The preciseness is derived by the induction of $m_k(2^x)=2^{u_k(x)}$; $m_\omega,m_{\omega+1}$ becomes $v,w$ through this conjugation, and thus $m_{\omega+2}(2)=2^{w(w(1))}$. There is no need to calculate the decimal representations of the aforementioned integers.

## 3. converts long chains into the number of BMS rows that maintain small periods

The existing embedding $L_3$ has a finite initialization, which satisfies

$$
\operatorname{crit}(L_3)=\kappa_3,\qquad
L_3(\kappa_3)=\theta_6,\qquad L_3(\theta_6)=\theta_7.
$$

Let $E=L_3(K)$, the parentheses indicate the application. From the application point identity,

$$
E(\kappa_0)=\kappa_2,\quad E(\kappa_1)=\theta_6,\quad
E(\theta_6)=L_3(\theta_5)<\theta_7.
\tag{6}
$$

Each point and each embedding of (4) are uniformly taken as the image of $E$, resulting in a chain of $C$ segments of $(\kappa_2,\theta_6,E(\theta_5))$, and
$E(\theta_5)<E(\theta_6)<\theta_7<\kappa_4$.

[Unified Front-End Insertion Lemma](<lined-front-insertion.md>) thus provides a closed and compatible set with a high degree of $H=C+2$, with the closure strictly below $\kappa_4$. This lemma holds for any specified finite chain length, and it also recursively maintains common truncation and closure bounds; it does not count mutually incompatible witnesses directly as BMS rows.

The compatible group provides [Implementation](<ribbon-initialization.md>) for $R_H$. The one-time fixed point `[1]` is achieved by several column deletion points and one-time preservation of the end point. [Finite Counting Lemma](<balanced-ribbon-bridge.md>) states that: when $H\ge3$, the total number of descent steps is strictly less than the actual number of column deletion points; the latter does not exceed the critical point index of the initial end point.

If $\kappa_4=\gamma_s$, Then $q(5)=s+1$: Because $\kappa_3=\gamma_4$ And $j(\gamma_t)=\gamma_a$ holds if and only if the first row period does not exceed $2^t$ at the $a$ order parameter, but exceeds it at the $a+1$ order. This uses [Dougherty, Article 2, Section 2 Finite Table Correspondence](https://arxiv.org/pdf/math/9503204). I3 Ensures that these critical points have a finite index; The cycle will only remain the same or double at each step. Therefore, the first period that is reached here is 32. So

$$
\boxed{q(5)>D(C+2).}
\tag{7}
$$

All descending operations use the standard BMS descendants, and termination can also be handled using the existing [BMS Well-Order Theorem](https://arxiv.org/html/2307.04606v2). The termination and counting of auxiliary non-standard matrices are separately proven by their ancestors, and their numerical ordinal order is not confused with ordinal numbers.

## Input with a number of lines exceeding four times the budget for 4.

Let $t=F_3(257)$. According to the convention of FGH,

$$
F_2(x)=(x+1)2^{x+1}-1,\qquad t=F_2^{\circ258}(257).
$$

For $x\ge1$, $g(x)\ge2x$, and

$$
g^2(x)\ge g(2x)=2x2^{2x}\ge(x+1)2^{x+1}>F_2(x).
$$

The functions are strictly increasing, and there is also $g^3(1)=2048>257$, so

$$
t<g^{\circ516}(257)<g^{\circ519}(1).
\tag{8}
$$

Write $b=g^{\circ258}(1)$. Note

$$
v(1)=u_2(1)=u_1(u_1(1))=u_1(8)=g^{\circ256}(8)=b.
$$

Each $u_k$ is strictly increasing with respect to the input and is greater than the identity function, and it does not decrease as $k$ increases. These properties are generalized for $k$: $u_{k+1}(x)$ is increasing and greater than the identity function for the $u_k$ iteration $2^x$ times, hence it is at least $u_k(x)$; increasing the input also increases the initial value and the number of iterations. Therefore, $v,w$ is also increasing and greater than the identity function. Thus

$$
\begin{aligned}
C&>w(1)=v(b)=u_{2^b}(b)\\
 &\ge u_1(b)=g^{\circ2^b}(b)
 =g^{\circ(2^b+258)}(1)\\
 &\ge g^{\circ521}(1)>g^2(t)\ge4t.
\end{aligned}
\tag{9}
$$

Here, $b\ge2048$, so the number of intermediate iterations is more than sufficient. The old parameter $b+2$ cannot be used directly to make the same conclusion: in fact, $F_2(x)>g(x)$ and $257>1$, therefore $t>b$. This paper uses the literature to supplement this with a longer chain $C$, rather than assuming that the two are already close enough.

## 5. merged

First, prove the unified formula (1a). If $r+\ell(x)\le C$, then $r+2+\ell(x)\le C+2$. Substitute $h=C+2$ into (2), and using (7), we obtain

$$
\boxed{q(5)>D(C+2)\ge F_{B_r}(x).}
\tag{10}
$$

The rigor comes from the first step on Laver's side; the non-strict inequalities in the BMS summary were not rewritten as strict inequalities.

For $t\ge2$, $\ell(t)\le t$. The formula (9) is thus derived

$$
C+2>t+3+\ell(t).
$$

Substitute $r=t+1,x=t,h=C+2$ for (2), and then use (7):

$$
q(5)>D(C+2)\ge F_{B_{t+1}}(t)
=F_{\mathrm{BMS}}(t)=F_{\mathrm{BMS}}(F_3(257)).
$$

This proof is (1). It does not use the general rule that "the larger the ordinal subscript, the larger the FGH value". The sufficient number is directly converted into a counting comparison through ancestor coverage and structural simulation.

The original target is also directly obtained as: $C+2\ge17$. Substituting $r=11,x=10$ gives $q(5)>F_{B_{11}}(10)$. Similarly, the old parameter boundary $q(5)>D(b+2)$ is restored from $C>b$ and the fixed counting monotonicity covered by the ancestors, eliminating the need for a marked completion proof.

The unified formula can also directly provide two explicit examples:

$$
q(5)>F_{B_{C-4}}(10),\qquad
q(5)>F_{\mathrm{BMS}}\!\left(\left\lfloor\frac{C-1}{2}\right\rfloor\right).
\tag{11}
$$

The first equation uses $\ell(10)=4$. The second equation is set to $z=\lfloor(C-1)/2\rfloor\ge2$, and since there is $z+1+\ell(z)\le2z+1\le C$, $r=z+1,x=z$ can be chosen. Each conclusion independently meets the row budget, and there is no need to prove that $F_{\mathrm{BMS}}$ is monotonic for all natural number inputs.

## 6. proofs depend on and are not used to strengthen

The entire proof uses only the following three sets of interfaces:

1. In the BMS summary, $D(h)\ge F_{B_r}(x)$ refers to the coverage processing of non-standard auxiliary matrices.
2. The proposition 1.3(1) proves the actual $C$-lined chain, as well as the finite initialization.
$L_3$, $E=L_3(K)$. Here, the linedness is not deduced from the fact that "the critical points of endpoints have large subscripts".
3. Unified front-end insertion, non-completion balance preservation, and deletion endpoint counting.
They transform a given chain of a finite length into an implementation of a specific $R_{C+2}$.

All actual embeddings always belong to the same $\operatorname{Iter}(j)$. The construction of general $C$ uses finite induction, and there is no requirement to generate $C$ witnesses with a program. This is a numerical theorem under the condition of I3; the assumption of a large cardinality is not eliminated here.

The well-ordering, the identity with the original IBLP `[2]` and short copies, the monotonicity with any ordinal size for a fixed number of indices, or the statement "any extra row dominates all matrices with fewer rows." Also, no two-row feedback is used, so this conclusion can be independently verified from subsequent ultra-BMS designs.

## Verification scope

This article introduces the selection, transportation, and integer comparison of published chains. General constructions and proofs of combinatorial counting are found in the local links mentioned above. Finite checks do not replace these universal inductions.

This round is being rerun:

- `three_row_certificate.py`: All 17 derived application items have passed the initialization for both two-layer and three-layer configurations.
- `diagonal_forest_compiler.py`: 1, 608 complete forest trajectories, 14, 070 steps, and additionally 180 items from the original BM4 cross-verification.
- `ancestor_cover_growth.py`: Simulation of 559 degree coverage, transformation of 130 row width, preparation of a maximum limit for 22 path contact, still considered unfinished.
- `fgh_hardy_compiler.py`: 5, 600 local identities; 88 instances are equal in value, 74 instances exceed the resource budget, the latter is not counted as a pass.

The `...proved: false` fields retained in these scripts indicate that the script itself does not prove the final universal theorem; it does not elevate finite tests to a formalized level. There is no computation of massive complete reductions, no modification of notation definitions, and no pushing of repositories.
