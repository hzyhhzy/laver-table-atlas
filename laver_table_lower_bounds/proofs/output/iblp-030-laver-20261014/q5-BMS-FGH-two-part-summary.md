# The rapid growth lower bound of a thirty-two-period triple BMS · [中文版](q5-BMS-FGH-two-part-summary.zh-CN.md)

*English reading edition, translated with machine assistance. The title links to the dated Chinese manuscript.*

> Collected reading edition. The three main papers state the results of this collection.
> This edition retains the local proofs, their hypotheses and any withdrawals. Progress reports describe the state of work at the time.
> The locations of omitted passages on preset inputs are recorded in SOURCE_MANIFEST.json.
> The main papers give the numerical derivations for the natural parameters produced by the proofs. This historical note carries no additional Lean certification.

2026-10-14. Under **ZFC + I3**, let $q(5)$ be the order parameter for the first occurrence of a period under the ordinary binary Laver table head, which reaches $32$. That is, the table has $2^{q(5)}$ elements. Let $\Lambda$ denote the BMS limit, using the fundamental sequence and FGH conventions described below.

$$
\boxed{\displaystyle
q(5)>F_\Lambda\!\left(F_\Lambda\!\left(F_\Lambda\!
\left(F_3(256)\right)\right)\right).}
\tag{A}
$$

This is a triple function composition of the same $F_\Lambda$: two rounds of row feedback, plus the innermost one-time BMS calculation. The main formula conservatively takes the inner input $256$, without retaining logarithms, additive constants, or auxiliary functions. The proof is divided into two parts: first, fixing the number of reductions by the BMS, and then handling the FGH and paying all the costs. This is a paper proof, and it has not yet been formalized in Lean.

## Part One: The Laver Table and the Docking of BMS Fixed Downcomings

### Counting and endpoint interfaces with 1.

Parentheses indicate a column of the BMS. Definitions

$$
B_r=(0^r)(1^r),\qquad R_h=(0^h)(1^h)(1^h),
$$

$$
D(h)=\text{from }R_h\text{ repeatedly applying original BM4 index }[1]\text{ steps to the empty matrix},
\qquad T(h)=D(h)+2.
\tag{1}
$$

The original BM4 `[1]` is now represented as `[2]` in this directory, not as the newly represented `[1]`. $D$ is counted with each expansion, not just in the step of deleting the last column. Here, $T$ is always an integer function (1); it does not refer to the embedded elements temporarily named $T$ in other documents.

Fixing I3 and embedding $j$, all observations take place in the same $\operatorname{Iter}(j)$. $\gamma_n$ enumerates its critical points, $\kappa_i=j^i(\gamma_0)$. Given $\kappa_3=\gamma_4$; if $\kappa_4=\gamma_s$, the corresponding finite Laver table is provided.

$$
q(5)=s+1.
\tag{2}
$$

A closed compatible group of heights $h$ has points that are strictly increasing $U_0<\cdots<U_h<V_0<\cdots<V_{h+1}<c$, as well as actual embeddings that satisfy

$$
\operatorname{crit}(K_i)=U_0,\quad K_i(U_t)=V_t\ (t\le i),
\quad K_i(V_0)=V_{i+1},
$$

$$
\operatorname{crit}(L)=V_0,\quad L(V_0)=V_{h+1},\quad L(V_{h+1})=c.
\tag{3}
$$

Place three columns with $U,V,L(V)$, use $L(K_i)$ for the second positive column, and then the specific seed $R_h$ can be achieved. Here, $L$ fixes the common source point, so the two positive columns indeed have the same parent column. [Implementation preservation](<../iblp-laver-bms-20261013/ribbon-initialization.md>) and [Balanced band counting](<../iblp-laver-bms-20261013/balanced-ribbon-bridge.md>) prove that the original BM4 can be achieved by several deletion endpoints and a short replication, completing the inactivation; replication does not increase the endpoints. When $h\ge3$, the total number of steps of the BMS is strictly less than the actual number of deletion endpoints. Therefore, when $c=\gamma_a$ is sealed...

$$
D(h)<a.
\tag{4}
$$

Therefore, $c<\kappa_4$ implies $q(5)>D(h)$. What is controlled is the order parameter of the table, not the weaker table size $2^{q(5)}$ lower bound.

### Initialize the long chain with 2.

Following the conventions used in [Finite initialization](<../iblp-laver-bms-20261013/short-terminal-initialization.md>), we introduce $K=j_{(11)}$ and $\theta_5<\theta_6<\theta_7<\theta_8<\kappa_4$. [Proof and Lemma for the Proposition Qi 1.3(1) 3.3](https://arxiv.org/html/2501.06733v5#S3) provides the actual $C$-lined chains.

$$
(\kappa_0,\kappa_1,\theta_5),\qquad
C=f(p_{\omega+2},1),\qquad 2^C=m_{\omega+2}(2).
\tag{5}
$$

Here, chain witnesses are used directly, without inferring linedness from the fact that 'critical points have a large subscript'. The definition of pure finite integers and the lower bounds for $C$ are presented in the second part.

Finite initialization also has $L_3:\kappa_3\mapsto\theta_6\mapsto\theta_7$. Let $E=L_3(K)$, $\tau=L_3(\theta_5)$, then

$$
E(\kappa_0)=\kappa_2,\quad E(\kappa_1)=\theta_6,
\quad E(\theta_6)=\tau,\quad \theta_6<\tau<\theta_7.
\tag{6}
$$

Take the entire (5) as the image of $E$. At its end, it is marked as $E(\theta_5)<\tau$.   [Unify the front-end insertion](<../iblp-laver-bms-20261013/lined-front-insertion.md>) Only the root is included. $\kappa_2$ , starting point not lower than $\theta_6$ of $m$ The segment chain has been changed to a height. $m+2$ The closed compatible group The seal is strictly below the end of the chain. Groups with a height of $C+2$ and a seal below $\tau$; The original chain prefix also provides the group for each $3\le h\le C+2$. This does not rely on the earlier marker-based startup history.

### 3. has two rounds of feedback to check the endpoints.

[First round of root reduction feedback](<root-lowered-bms-feedback.md>) constructed an actual embedding into $P$, which satisfies

$$
P(\gamma_0)=\theta_6,\quad P(\gamma_1)=\tau,
\quad P(\tau)=\theta_7,
\quad (\kappa_2,\theta_6,\tau)\text{ is 2-lined}.
\tag{7}
$$

The input has a height of $h$ and is sealed with $c<\tau$. Let $N=D(h)$, $m=\lfloor\log_2N\rfloor$. The formula (4) yields $\gamma_N<c$. Dougherty's standard $m$ segment chain $(\gamma_0,\gamma_1,\gamma_{2^m})$ takes $P$-image, then multiplies it by (7) to obtain a $2^{m+1}>N$ segment chain, with the end point lower than $P(c)<\theta_7$. The endpoints are contracted to the segment $N$ and inserted at the front end, resulting in a group with a height of $T(h)=N+2$ and a seal that is lower than $\theta_7$.

The next round cannot directly repeat the same window, because of $\theta_7>\tau$. [Second-round transport](<promoted-bms-feedback.md>) uses $S=j_{(9)}(j_{(4)})$ to prove.

$$
S(\kappa_2)=\kappa_2,\quad
\theta_7<S(\tau),\quad S(\theta_7)<\theta_8<\kappa_4.
\tag{8}
$$

Taking the (7) to the ($S$-image, the first-round output is legally allowed to enter the second round, resulting in a group with a height of ($T(T(h))$ and a seal that is lower than ($S(\theta_7)<\kappa_4$. From (2), (4), the interface of the first part is

$$
\boxed{q(5)>D\!\left(T(T(C+2))\right).}
\tag{9}
$$

Only the first round can also result in $q(5)>D(T(C+2))$. It is not asserted that any number of rounds of feedback can still result in a value below $\kappa_4$. A more complete chain of evidence and sources can be found at [Itemized proof of nested lower bound](<nested-bms-FGH-bound.md>).

## Part Two D and the Connection with FGH and All Substitutions

### 1. FGH convention and exponential tower surplus

$Z$ represents a zero column. The original BM4 fundamental sequence is used to define...

$$
F_\varnothing(x)=x+1,\quad
F_{MZ}(x)=F_M^{\circ(x+1)}(x),\quad
F_M(x)=F_{M[x]}(x)\quad(M\text{ has a nonzero last column}),
$$

$$
\Lambda[x]=B_{x+1},\qquad F_\Lambda(x)=F_{B_{x+1}}(x).
\tag{10}
$$

Define $e_0=1,e_{n+1}=2^{e_n}$, and let
$\ell(x)=\lceil\log_2(x+2)\rceil$.
The user-provided [Summary from BMS terminal](<../iblp-laver-bms-20261013/BMS-fixed-index-to-FGH-summary.md>) proves $D(h)\ge F_{B_r}(x)$ when $h\ge r+2+\ell(x)$. Its [Forest proof](<../iblp-laver-bms-20261013/diagonal-forest-hardy-proof.md>) formula (9) actually retains a stronger endpoint count $e_y$, thus the same proof is given

$$
\boxed{D(h)\ge e_{F_{B_r}(x)}
\quad(r,x\ge1,\ h\ge r+2+\ell(x)).}
\tag{11}
$$

The specific chain is as follows:

$$
D(h)\ge s_{R_h}(1)
\ge s_{\Sigma(W(B_r)Z^x)}(1)
\ge e_{H_{W(B_r)}(x)}=e_{F_{B_r}(x)}.
$$

Here, $s$ only counts zero column deletions, $W$ precisely compiles FGH into Hardy, and $\Sigma$ adds a row of forest; ancestor coverage and row width exchange provide a clear size budget. The auxiliary non-standard matrix is terminated by standard diagonal chains covering. This part does not use I3, but instead relies on the standard BMS well-ordering and the linked finite structure proofs.

### 2. outputs the number of rows for the next layer at each level

Set $\rho(x)=x+3+\ell(x)$. When (11) takes $r=x+1$, there is

$$
h\ge\rho(x)\quad\Longrightarrow\quad D(h)\ge e_{F_\Lambda(x)}.
\tag{12}
$$

By performing a well-founded induction on the standard subscripts, (10) yields $F_M(x)\ge x+1$. Therefore, when $x\ge2$, $y=F_\Lambda(x)\ge3$ follows. From $2^y\ge y+2$, we obtain $\ell(y)\le y$, and thus $\rho(y)\le2y+3$. At the same time, for all $y\ge3$,

$$
e_y\ge2y+3>y.
\tag{13}
$$

The foundation is $e_3=16\ge9$; inductive steps are denoted with $e_{y+1}=2^{e_y}\ge2e_y\ge4y+6\ge2(y+1)+3$.

$$
\boxed{h\ge\rho(x),\ x\ge2
\quad\Longrightarrow\quad T(h)\ge\rho(F_\Lambda(x)).}
\tag{14}
$$

The total logarithmic costs and additive constants of the next layer are paid by (13). It is not possible to simply replace each nested $D$ with $F_\Lambda$ using the weaker $D(h)\ge F_\Lambda(x)$; retaining the exponential tower surplus is precisely to fix this step.

### The exact constants for the inner input of 3.

Finite subscripts are calculated by (10):

$$
F_1(x)=2x+1,\quad F_2(x)=(x+1)2^{x+1}-1,
\quad \boxed{t=F_3(256)=F_2^{\circ257}(256).}
\tag{15}
$$

The superscript $\circ n$ of a function indicates that it is composed of $n$ operations. The innermost layer is neither $F_2^{\circ256}(256)$ nor the $T(3)$ of the feedback function.

The $C$ of (5) can be precisely defined by a purely finite integer recursive sequence:

$$
\begin{aligned}
g(x)&=x2^x,&u_0(x)&=g(x),\\
u_{k+1}(x)&=u_k^{\circ2^x}(x),&v(x)&=u_{2^x}(x),\\
w(x)&=v^{\circ2^x}(x),&C&=w(w(1)).
\end{aligned}
\tag{16}
$$

In the literature, $m_0(n)=n^n$, $m_{k+1}(n)=m_k^{\circ n}(n)$, and $m_\omega(n)=m_n(n)$ represent the exponential conjugates of $m_k(2^x)=2^{u_k(x)}$. By taking $\omega,\omega+1,\omega+2$ three steps further, we obtain $m_{\omega+2}(2)=2^{w(w(1))}$. Therefore, the original constants for (16) remain unchanged.

For $x\ge1$, $g(x)\ge2x$, and so on.

$$
g^{\circ2}(x)\ge g(2x)=2x2^{2x}
\ge(x+1)2^{x+1}>F_2(x).
$$

These functions are strictly increasing, and $g^3(1)=2048>256$, therefore

$$
t<g^{\circ514}(256)<g^{\circ517}(1).
\tag{17}
$$

Write $b=g^{\circ258}(1)$. Check directly.
$u_1(1)=8$, $v(1)=u_2(1)=u_1(8)=g^{\circ256}(8)=b$.
By induction on $k$, each $u_k$ is strictly increasing, greater than the identity function, and non-decreasing with respect to $k$. By increasing the input, the initial values and the number of iterations are also increased, so $v,w$ also possesses these properties. Therefore

$$
\begin{aligned}
C&>w(1)=v(b)=u_{2^b}(b)\\
&\ge u_1(b)=g^{\circ2^b}(b)
=g^{\circ(2^b+258)}(1)\\
&\ge g^{\circ519}(1)>g^{\circ2}(t)\ge4t.
\end{aligned}
\tag{18}
$$

The number of iterations only needs to be denoted by $b\ge2048$. Starting from $t\ge2$, $\ell(t)\le t$,

$$
\boxed{C+2\ge t+3+\ell(t)=\rho(t).}
\tag{19}
$$

If we retain the strong $257$, then change the $514,517$ of (17) to $516,519$, and change the $519$ of (18) to $521$. The proof still holds. Let $256$ be a conservative simplification, which does not hide unverified overhead in the constant.

### 4. merged into the main formula

Set $h_0=C+2,h_1=T(h_0),h_2=T(h_1)$ and $x_0=t,x_{i+1}=F_\Lambda(x_i)$. From (19), (14), we can successively obtain

$$
h_0\ge\rho(x_0),\qquad h_1\ge\rho(x_1),\qquad h_2\ge\rho(x_2).
$$

Part one (9), followed by (12), (13), that is

$$
q(5)>D(h_2)\ge e_{x_3}>x_3
=F_\Lambda\!\left(F_\Lambda\!\left(F_\Lambda(F_3(256))\right)\right).
$$

This proof is (A). The same principle applies to obtaining two-layer versions during the first round of feedback. Throughout the process, the general concept of "using larger ordinal subscripts to determine larger FGH values" is not used, nor is it necessary to prove the input monotonicity of $F_\Lambda$ first. Instead, the required number of rows is directly checked each time.

### The minimum values of 5. T and the conclusion boundary

According to (1),$D(1)=7,D(2)=22$), therefore $T(1)=9,T(2)=24$. These small values can be proven directly, without needing to use finite tests as numerical definitions: Let $A=(00)(11)(10)$, then the original `[1]` has

$$
\begin{aligned}
R_2&\longrightarrow(00)(11)(10)(21)
\longrightarrow(00)(11)(10)(20)\\
&\longrightarrow(00)(11)(10)(10)
\longrightarrow AA.
\end{aligned}
$$

Also, $A[1]=B_2B_2$, $B_2[1]=B_1$ (ignoring the all-zero rows), $d_1(B_1)=3$. The zeroth column of a block cuts off the parent edge, so the blocks descend independently in series, resulting in $D(2)=4+2(1+2\cdot4)=22$. Similarly, $R_1[1]=B_1B_1$, and thus $D(1)=7$.

And $T(3)$ precisely refers to

$$
T(3)=d_1\bigl((000)(111)(111)\bigr)+2.
$$

It is not another way of writing the forest tower $e_3$ or $g^3(1)$. A simple and precise numerical value has not been given at this time. A strict but conservative lower bound is $T(3)\ge28$: $R_3$ progresses to $(000)(111)(110)(200)(311)(310)$ in four steps, with its last three columns directly covering $R_2$ in the first two rows, and the count theorem by ancestry covers at least 22 steps, hence $D(3)\ge26$. This proof starts from a high level of $C+2$ in the literature chain, and does not use $T(3)$ as a constant to hide overhead, therefore there is no need to calculate its decimal expansion first.

The formula (A)) represents a numerical lower bound under the condition of I3. There is no actual construction of a new notation that fundamentally surpasses the BMS, nor is there any proof that the specified Hardy or FGH values of the original IBLP 030 are controlled by $q(5)$. It is not possible to rename the composite of cubic functions and declare the goal of surpassing the BMS structurally. The finite program verification only checks the local algebra and coding interfaces and does not replace the aforementioned comprehensive proofs.

Subsequent additions: The structure of three-row seed counting with upper and lower bounds (historical reference: `T3-fixed-BMS-count-bounds.zh-CN.md`) improves the conservative estimate of $T(3)$ mentioned above, but still does not claim to obtain its exact value. [Feedback segment by segment along the long chain](<lined-feedback-corridor.md>) further allows the feedback rounds to be generated by the BMS, resulting in a stronger $F_{\Lambda+1}(F_\Lambda(F_\Lambda(F_3(256))))$ numerical lower bound. The formula in this paper (A)) remains unchanged as an independent summary of the original two rounds of feedback.
