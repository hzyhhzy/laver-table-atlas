# The dynamic depth template raises the lower bound of q5 to Lambda plus omega plus one. · [中文版](dynamic-depth-Lambda-omega-successor.zh-CN.md)

*English reading edition, translated with machine assistance. The title links to the dated Chinese manuscript.*

> Collected reading edition. The three main papers state the results of this collection.
> This edition retains the local proofs, their hypotheses and any withdrawals. Progress reports describe the state of work at the time.
> The locations of omitted passages on preset inputs are recorded in SOURCE_MANIFEST.json.
> The main papers give the numerical derivations for the natural parameters produced by the proofs. This historical note carries no additional Lean certification.

2026-10-14. Under the assumption of ZFC + I3, which has the same lower bound as before, fix the same $\operatorname{Iter}(j)$. Let $\Lambda=\lim(\mathrm{BMS})$, $g=F_\Lambda$. Using $(\Lambda+\omega)[x]=\Lambda+(x+1)$, it can be proven that

$$
\boxed{q(5)>F_{\Lambda+\omega+1}\!\left(
F_{\Lambda+\omega}\bigl(g(g(2^{C_{\rm line}}))\bigr)\right).}
\tag{A}
$$

This strictly improves the lower bound of $F_{\Lambda+\omega}$ on the same input as before. The new step is to make "selecting a finite template depth based on the input" itself a natural template, and then repeatedly execute this dynamic depth template along the actual long chain. It does not assume that the original IBLP 02 or complete Y sequence has been embedded into pIBLP.

## The actual endpoints and counting interface used

Following the conventions of [Short Transport Endpoint Proof](<../iblp-030-laver-20261014/small-period-endpoint-Sf.md>) and [Recursive corridor](<../iblp-030-laver-20261014/small-period-recursive-corridor.md>). To avoid confusion with the pIBLP seed $S$, this paper refers to the actual transport embedding as $H$:

$$
\begin{gathered}
k=\kappa_2<a=\theta_6<b=\tau<c=\theta_7<\kappa_4,\\
H=j_{(9)}(j_{(4)}),\qquad c<H(a)<H(b)<H(c)<\kappa_4,\\
A=H(f),\qquad r=\kappa_3,\qquad u=H(\theta_5),\\
A(\gamma_0)=r,\quad A(\gamma_1)=u,\quad
k<r<a<c<u,\quad A(u)=H(a).
\end{gathered}
\tag{1}
$$

$H$ is fixed to $\kappa_0,\kappa_1,k$. All parentheses in the formulas indicate application. Do not treat ordinary compositions as application items.

Let $D(h)$ be the total number of steps taken repeatedly by the three columns of the BMS matrix $(0^h)(1^h)(1^h)$, starting from the original BM4 and $[1]$, until it reaches zero, denoted as $T(h)=D(h)+2$. There is a natural template $T$ that changes fans whose entrance and closure are below $b$ to ones with a height of $T(h)$, and fans whose closure is below $c$.

Also using strong buffer estimation

$$
e_0=1,\quad e_{n+1}=2^{e_n},\qquad
\rho(x)=x+3+\lceil\log_2(x+2)\rceil,
$$

$$
h\ge\rho(x),\quad x\ge2
\quad\Longrightarrow\quad
D(h)\ge e_{g(x)},\qquad T(h)\ge\rho(g(x)).
\tag{2}
$$

The sources of these interfaces are initialized to $h_*=f_{\rm PP}(S,1)+2\ge\rho(2^{C_{\rm line}})$, as described in sections 1 to 4 of [Previous complete derivation](<../piblp-q5-enhancement-20261014/q5-piblp-enhanced-bound.md>). The following proof is based on the height $h$ of any existing actual entrance fan, and is concluded with the selection.
$h=h_*$.

## Dynamic finite depth has a unified lower exit point

Define an integer function

$$
U_0=T,\qquad
U_{i+1}(h)=U_i^{\circ(D(U_i(h))+1)}(h),
\qquad m(h)=\lfloor\log_2D(T(h))\rfloor,
$$

$$
V(h)=U_{m(h)}(h).
\tag{3}
$$

The key reinforcement is not the old numerical bounds, but rather the following **Unified Exit**: $V$ is the entrance, $b$ is the exit.

$$
d=A(c)<A(u)=H(a)
\tag{4}
$$

Natural template.

The proof is as follows. Given an actual entrance fan with a height of $h$, create a copy and perform a $T$ operation, marking it with $C<c$. Let $N=D(T(h))$ and $m=\lfloor\log_2N\rfloor$ be the results of this operation. Assign a count to $\gamma_{2^m}\le\gamma_N<C$. The global Dougherty's $m$-lined $(\gamma_0;\gamma_1,\ldots,\gamma_{2^m})$ chain takes $A$-images point by point and owner by owner, resulting in

$$
(r;u,\ldots,A(\gamma_{2^m})),\qquad
A(\gamma_{2^m})<A(C)<A(c)=d.
\tag{5}
$$

By progressively upgrading its segments to $U_0$, we obtain $U_m$. Each new outlet is lower than the end of the current segment, so the final outlet is still strictly below $d$. If it reaches $m=0$, it can be directly upgraded to $U_0=T$, as $c<u<A(c)=d$ is not required. The entire process only uses a finite chain that has been constructed, with no requirement to fix endpoints to ensure the existence of chains of any length.

The naturalness holds as well. For any fixed environment with $\gamma_0,\gamma_1$, the environment embedding with $Q$ results in the background using $Q(A),Q(r),Q(u),Q(c)$ after the transport. The input fan can be any fan that satisfies the guard condition in the global $\operatorname{Iter}(j)$, and does not need to be the inverse image of some old fan. The global counting is still given as $\gamma_N<C<Q(c)$, so the end point of the chain is below $Q(A)(Q(c))=Q(d)$. The numerical function $m(h)$ remains unchanged, as the fan height is constant. Therefore, (4) is a natural template for the whole background, rather than just an accidental input-output witness.

## Upgrade the dynamic template once more

The existing corridor upgrade lemma states: If the entrance of the natural template $F$ is $b$, the exit is $d'\ge c$, and the actual embedding $R$ fixes $\kappa_0,\kappa_1,k$, satisfying $d'<R(a)$, then

$$
\mathcal U(F)(h)=F^{\circ(D(F(h))+1)}(h)
\tag{6}
$$

A natural implementation with an entrance $b$ and an exit $R(c)$.

Here, we take $F=V$, $R=H$. From (4), there is $d<H(a)$, and $H(c)<\kappa_4$. Therefore

$$
W(h)=V^{\circ(D(V(h))+1)}(h)
\quad\Longrightarrow\quad q(5)>D(W(h)).
\tag{7}
$$

Note that $W$ selects the depth based on the current height each time it calls $V$. This is different from the old template $U_{m(h)+1}(h)$, which always calls a fixed $U_{m(h)}$ after determining the $m(h)$ once. This difference is precisely the new source of growth.

## Step-by-step buffer simulation

Let's denote the mathematical research manuscript as follows:

$$
J_i(x)=F_{\Lambda+i}(x),\qquad
K(x)=F_{\Lambda+\omega}(x)=J_{x+1}(x).
$$

There are already finite layer inductions given

$$
h\ge\rho(x),\quad x\ge2
\quad\Longrightarrow\quad U_i(h)\ge\rho(J_i(x)).
\tag{8}
$$

This induction only repeatedly uses (2) and $J_{i+1}(x)=J_i^{\circ(x+1)}(x)$. Each function increases strictly; at the same input, $J_{i+1}(x)>J_i(x)$ ($x\ge1$). There is no need to assume that these functions are monotonic with respect to the input.

If $h\ge\rho(x)$, twice (2)

$$
D(T(h))\ge e_{g(g(x))},\qquad
m(h)\ge e_{g(g(x))-1}\ge g(g(x))+1\ge x+1.
\tag{9}
$$

Here, $g(g(x))\ge4$. Therefore, by (8), finite layer comparison on the same input,

$$
\boxed{h\ge\rho(x),\ x\ge2
\quad\Longrightarrow\quad V(h)\ge\rho(K(x)).}
\tag{10}
$$

This dynamic depth template is truly connected to $F_{\Lambda+\omega}$, rather than directly guessing the FGH level from the symbolic "variable finite layers".

## Retain a limit layer preheating within the dynamic template

Fix the $h\ge\rho(x)$, $x\ge2$, set

$$
x_2=g(g(x)),\qquad m=m(h).
$$

From $x_2\ge4$ and the elementary tower estimate $e_{x_2-1}\ge x_2+2$, 9) is actually given.

$$
m-1\ge x_2+1.
\tag{11}
$$

Expand $V(h)=U_m(h)=U_{m-1}^{\circ M}(h)$, where $M=D(U_{m-1}(h))+1$. The first round is given by (8)

$$
U_{m-1}(h)\ge\rho(J_{m-1}(x))
\ge\rho(J_1(x))\ge\rho(x_2).
\tag{12}
$$

The last step comes from the same strict increment track of $J_1(x)=g^{\circ(x+1)}(x)$. From (2),$M\ge2$. In the second round, (8) is reused to fix the input $x_2$, resulting in

$$
U_{m-1}^{\circ2}(h)\ge\rho(J_{m-1}(x_2))
\ge\rho(J_{x_2+1}(x_2))=\rho(K(x_2)).
\tag{13}
$$

In subsequent rounds, the fixed input $x_2$ can still be used (8), because the right-hand side of (13) is at least $\rho(x_2)$. Therefore, let $y=K(x_2)$, then there is

$$
V(h)\ge\rho(y),\qquad N=D(V(h))+1\ge e_{g(y)}+1\ge y+2.
\tag{14}
$$

In $W(h)=V^{\circ N}(h)$, there are at least $y+1$ rounds remaining after the first round. By repeatedly using the fundamental buffer (10) and tracking the $K$ orbits with the same strict increment, we obtain

$$
W(h)\ge\rho\bigl(K^{\circ(N-1)}(y)\bigr)
\ge\rho\bigl(K^{\circ(y+1)}(y)\bigr).
\tag{15}
$$

Set $Y=K^{\circ(y+1)}(y)=F_{\Lambda+\omega+1}(y)$, from (2), (7) we get

$$
\boxed{q(5)>D(W(h))\ge e_{g(Y)}>Y
=F_{\Lambda+\omega+1}\!\left(F_{\Lambda+\omega}(g(g(x)))\right).}
\tag{16}
$$

Taking the $h=h_*$ and $x=2^{C_{\rm line}}$ that pIBLP has already initialized, we obtain (A). If we continue to use the audited BMS diagonal input property that the inputs are strictly increasing, we can also relax the $2^{C_{\rm line}}$ into $2^{F_3(256)}$.

On the same input $z\ge1$

$$
F_{\Lambda+\omega+1}(z)=K^{\circ(z+1)}(z)>K(z),
$$

And $F_{\Lambda+\omega+1}(z)>z$. Therefore, the right-hand side of (A)) strictly exceeds that of the previous $F_{\Lambda+\omega}(g(g(2^{C_{\rm line}})))$; this comparison does not even require comparing the values of FGH at different input points.

## Further upgraded endpoint gaps

The unified exit of the new template $W$ is $H(c)$, not below $H(a)$. The same $H$ cannot be used directly again. A sufficient new resource is the actual application item $R\in\operatorname{Iter}(j)$, fixed $\kappa_0,\kappa_1,k$, which satisfies

$$
H(c)<R(a),\qquad R(c)<\kappa_4.
\tag{17}
$$

The known strict image identities do not imply (17). The candidate endpoint $H(H(c))$ for ordinary composition $H\circ H$ is only known to lie between $\theta_8$ and $H(\theta_8)$. The latter is at least $\kappa_4$, so this does not justify the proposed exit. One must also show that its owner belongs to the required algebra and distinguish embedding application $H(H)$ from ordinary composition.

This paper does not declare any FGH lower bounds of the level $F_{\Lambda+\omega\cdot2}$ or Y; (A) only uses actual finite endpoints that have been closed and natural template lemmas.
