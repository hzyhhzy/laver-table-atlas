# The lower bound of the three-layer BMS FGH given by two-round row feedback · [中文版](nested-bms-FGH-bound.zh-CN.md)

*English reading edition, translated with machine assistance. The title links to the dated Chinese manuscript.*

> Collected reading edition. The three main papers state the results of this collection.
> This edition retains the local proofs, their hypotheses and any withdrawals. Progress reports describe the state of work at the time.
> The locations of omitted passages on preset inputs are recorded in SOURCE_MANIFEST.json.
> The main papers give the numerical derivations for the natural parameters produced by the proofs. This historical note carries no additional Lean certification.

For a concise entry divided into two parts, "Laver and BMS docking" and "D and FGH and all contractions", see [Summary of the two-part proof](<q5-BMS-FGH-two-part-summary.md>). The innermost input is conservatively taken as 256, and $F_3(256)=F_2^{\circ257}(256)$ is checked; this article retains the more robust 257 version.

2026-10-14. Under **ZFC + I3**, there have been two instances of BMS row feedback that can be strictly connected with [FGH estimate of BMS fixed index decline](<../iblp-laver-bms-20261013/BMS-fixed-index-to-FGH-summary.md>). The conclusion is not just a single-layer BMS: if $\Lambda$ represents the BMS limit, and $t=F_3(257)$, then

$$
\boxed{q(5)>F_\Lambda\bigl(F_\Lambda(F_\Lambda(t))\bigr).}
\tag{1}
$$

The first round of feedback provides two versions of $q(5)>F_\Lambda(F_\Lambda(t))$ separately. The second round adds another layer. This is the numerical lower bound of the nested FGH, not treating the BMS limit with its successors as a new structural enhancement marker. The proof is as follows; it has not yet been formalized in Lean.

## The notation 1. is used for functions and subscripts.

$q(5)$ is the order parameter for the first occurrence of a period of 32 in the first row of a regular binary Laver table.

$$
q(5)=\min\{m:\text{we have }2^m\text{ elements whose first row has period at least }32\}.
$$

Let's denote the mathematical research manuscript as follows:

$$
B_r=(0^r)(1^r),\quad R_h=(0^h)(1^h)(1^h),\quad
D(h)=\text{from }R_h\text{ repeatedly applying original BM4 index }[1]\text{ steps to the empty matrix},
\quad T(h)=D(h)+2.
$$

The original BM4 `[1]` is equivalent to the new index `[2]` of the parent table. FGH uses the original BM4 fundamental sequence:

$$
F_\varnothing(x)=x+1,\qquad
F_{MZ}(x)=F_M^{\circ(x+1)}(x),\qquad
F_M(x)=F_{M[x]}(x)\quad(M\text{ has a nonzero last column}),
$$

Among them, $Z$ represents a zero column, $\Lambda[x]=B_{x+1}$, so $F_\Lambda(x)=F_{B_{x+1}}(x)$. The "three layers" mentioned in this text refer to the composition of a cubic function with the same $F_\Lambda$, not three rows of BMS.

## 2. uses published chain length to expand the range of inputs for feedback.

Let $C=f(p_{\omega+2},1)$. To avoid relying on undeveloped BLP recursion, it can be equivalently defined using the following pure finite integer recursion:

$$
\begin{aligned}
g(x)&=x2^x, & u_0(x)&=g(x),\\
u_{k+1}(x)&=u_k^{\circ 2^x}(x), & v(x)&=u_{2^x}(x),\\
w(x)&=v^{\circ 2^x}(x), & C&=w(w(1)).
\end{aligned}
\tag{2}
$$

The [Single-layer BMS FGH proof](<../iblp-laver-bms-20261013/laver-period-32-BMS-bound.md>) sections 2 and 4 have been verified: The proof of the Qi proposition 1.3(1) is provided with the actual $C$-lined chain $(\kappa_0,\kappa_1,\theta_5)$ in the same $\operatorname{Iter}(j)$, and

$$
C>4t,\qquad t=F_3(257).
\tag{3}
$$

Here, the chain witness used in this proof is not used to deduce linedness from a large number of critical points. The formula (2) comes from the exponential conjugate of $2^C=m_{\omega+2}(2)$.

Initializations have been provided

$$
E=L_3(K),\quad K=j_{(11)},\quad
E(\kappa_0)=\kappa_2,\quad E(\kappa_1)=\theta_6,\quad
E(\theta_6)=\tau=L_3(\theta_5),\quad \theta_5<\theta_6.
$$

Take the entire segment of $C$ as the image of $E$-, with the end being
$E(\theta_5)<\tau$.
[Unify the front-end insertion](<../iblp-laver-bms-20261013/lined-front-insertion.md>) yields a closed compatible set with a height of $C+2$, and the closure is strictly below $\tau$. For any $3\le h\le C+2$, taking the first $h-2$ segments of the original chain also yields a set with a height of $h$ that satisfies the same closure conditions.

This is a broader range than the early use of upper bounds with $g^{\circ258}(1)+2$, and it does not depend on the history of marker activation.

### Both rounds of feedback remain below the same periodic endpoint.

The local lemma for [First round of feedback](<root-lowered-bms-feedback.md>) states that when the input consists of groups with a height of $h$ and a closure lower than $\tau$, the output has a height of $T(h)$ and a closure lower than $\theta_7$.

It has been proven that when [Second-round transport proof](<promoted-bms-feedback.md>) takes $S=j_{(9)}(j_{(4)})$,

$$
S(\kappa_2)=\kappa_2,\qquad
\theta_7<S(\tau),\qquad S(\theta_7)<\theta_8<\kappa_4.
$$

The first round of output allows for the input of feedback conditions after transportation, resulting in groups with a high degree of $T(T(h))$ and seals below $S(\theta_7)<\kappa_4$. Implementation and deletion endpoint counts are provided for these groups respectively.

$$
\boxed{q(5)>D(T(h)),\qquad q(5)>D(T(T(h)))
\quad(3\le h\le C+2).}
\tag{4}
$$

The newly introduced elements do not alter the local proofs for the two rounds. After the second round, there is no further transportation of results; the expression (4) does not imply that any number of rounds of feedback can be placed below $\kappa_4$.

## The remaining amount retained by the3. forest estimation

The mathematical research manuscript as written cannot be directly iterated with just $D(h)\ge F_{B_r}(x)$: The next round requires not only the $F_{B_r}(x)$ rows, but also the cost of row count. It is necessary to return the proof, rather than ignoring this cost.

Definition

$$
e_0=1,\qquad e_{y+1}=2^{e_y},\qquad
\ell(x)=\lceil\log_2(x+2)\rceil.
$$

[Forest Controller Proof](<../iblp-laver-bms-20261013/diagonal-forest-hardy-proof.md>) The formula (9) actually provides a stronger endpoint estimate: if Hardy's calculation yields $y$, the number of subsequent deletions in the control forest should be at least $e_y$, rather than just $y$. Keep it, and use the same line-width budget to obtain

$$
\boxed{D(h)\ge e_{F_{B_r}(x)}
\quad(r,x\ge1,\ h\ge r+2+\ell(x)).}
\tag{5}
$$

The specific chain is as follows:

$$
D(h)\ge s_{R_h}(1)
\ge s_{\Sigma(W(B_r)Z^x)}(1)
\ge e_{H_{W(B_r)}(x)}
=e_{F_{B_r}(x)}.
$$

All inequalities and dimension conditions are the same as those provided by the user in the summary, except that the $e_y$ is not relaxed to $y$ at the end. The termination and coverage of the auxiliary matrix also follow the original proof, without adding any new well-foundedness assumptions.

## 4. outputs one round of data, covering all rows for the next round.

Put

$$
\rho(x)=x+3+\ell(x).
$$

Take $r=x+1$, the formula (5) becomes

$$
h\ge\rho(x)\quad\Longrightarrow\quad
D(h)\ge e_{F_\Lambda(x)}.
\tag{6}
$$

For any standard index, the well-founded induction gives $F_M(x)\ge x+1$: The zero term is directly established, the successor is an iteration that increases strictly at least once, and the limit uses the induction hypothesis of its smallest fundamental term. Therefore, when $x\ge2$, $y=F_\Lambda(x)\ge3$.

For $y\ge2$, it can be derived from $2^y\ge y+2$ to $\ell(y)\le y$, hence $\rho(y)\le2y+3$. Similarly, for $y\ge3$,

$$
e_y\ge2y+3>y.
\tag{7}
$$

The basis of the subsequent formula is $e_3=16\ge9$; inductive step is used
$2^{e_y}\ge2e_y\ge4y+6\ge2(y+1)+3$.

Therefore, (6) yields the desired cost-fulfilling conclusion.

$$
\boxed{h\ge\rho(x),\ x\ge2
\quad\Longrightarrow\quad
T(h)=D(h)+2\ge\rho(F_\Lambda(x)).}
\tag{8}
$$

The mathematical research paper does not use the general FGH ordinal monotonicity, nor does it identify $D$ with $F_\Lambda$.

## 5. two feedbacks and three FGH calculations

More generally, take any $x\ge2$ that satisfies

$$
x+1+\ell(x)\le C.
\tag{9}
$$

Set $h_0=C+2$, $h_1=T(h_0)$, $h_2=T(h_1)$, and let $x_0=x$, $x_{i+1}=F_\Lambda(x_i)$. The equation (9) precisely ensures $h_0\ge\rho(x_0)$. Applying it twice with (8), we obtain

$$
h_1\ge\rho(x_1),\qquad h_2\ge\rho(x_2).
$$

Therefore, (4), (6) are given respectively

$$
\boxed{q(5)>D(h_1)\ge e_{x_2}>x_2
=F_\Lambda(F_\Lambda(x)),}
\tag{10}
$$

$$
\boxed{q(5)>D(h_2)\ge e_{x_3}>x_3
=F_\Lambda(F_\Lambda(F_\Lambda(x))).}
\tag{11}
$$

Take $x=t=F_3(257)$. By (3) and $\ell(t)\le t$, $t+1+\ell(t)\le2t+1<C$, it follows that (9) holds. Prove that (1) is also true. Similarly, we can take $x=\lfloor(C-1)/2\rfloor$; it also directly satisfies the budget, without the need to prove the input monotonicity first.

## 6. This conclusion differs from the continuation of the research

The two- or three-layer nested numerical lower bounds have been derived from the above paper. The single-layer $F_\Lambda(F_3(257))$ that has been organized so far are basic conclusions without feedback, and they are not the complete lower bounds that can be given at present.

This conclusion still does not provide a super BMS notation that substantially enhances through internal replication or completion. It also fails to prove that the specified Hardy or FGH values of the original IBLP 030 are controlled by $q(5)$. It is not possible to rename the triple function composition of (11) as a new notation, thereby declaring the main line complete.

Finite verification is only used to check local implementations: on the BMS side, the forest controller is rerun in the current round, and checks from FGH to Hardy and ancestral coverage; the finite certificates transported by Laver can be found in the two-round feedback documents. No actual evaluation of $D(h_i)$, $F_\Lambda(x_i)$, or construction of these large arrays is performed. The general formulas come from the aforementioned integer induction, structural simulation, and embedding implementation proofs, and do not come from finite experiments.
