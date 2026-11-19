# Dynamic BMS depth feedback up to Λ + ω + 1 · [中文版](02-bms-feedback.zh-CN.md)

Work in a single $\operatorname{Iter}(j)$ in ZFC + I3, using the original BM4 fundamental sequences and $(\Lambda+\omega)[x]=\Lambda+(x+1)$. The BMS count and feedback construction use finite configurations of embeddings directly. The stronger initialization also uses the quantitative parent-packet lemma for pIBLP.

## 1. Three bounds with their original natural parameters

Write $\Lambda=\lim(\mathrm{BMS})$, $g=F_\Lambda$ and $K=F_{\Lambda+\omega}$, and put

$$
\rho(x)=x+3+\lceil\log_2(x+2)\rceil.
$$

The length $C_{\rm line}$ comes from Qi's concrete chain and also has a definition by finite recursion.

$$
u_0(x)=x2^x,\quad u_{r+1}(x)=u_r^{\circ2^x}(x),\quad
v(x)=u_{2^x}(x),\quad w(x)=v^{\circ2^x}(x),\quad C_{\rm line}=w(w(1)).
\tag{1}
$$

**A. The direct long chain.** The direct initialization supplies an entrance fan of height $h=C_{\rm line}+2$. Put

$$
z_{\rm dir}=\max\{z\ge2:\rho(z)\le C_{\rm line}+2\},
$$

Then

$$
\boxed{q(5)>F_{\Lambda+\omega+1}\!\left(K(g(g(z_{\rm dir})))\right).}
\tag{2}
$$

The set is nonempty and finite because $\rho$ is strictly increasing. Equation (1) immediately gives $\rho(2)\le C_{\rm line}+2$. This entrance is independent of pIBLP. Compiling the BMS computation uses the same operations on actual embeddings as the BLP ribbon construction.

**B. A simpler strengthened input.** Put

$$
X=F_{\,2^{C_{\rm line}}+1}(C_{\rm line}),
$$

The subscript is a natural number, so only the ordinary finite levels of the FGH occur here. Parent-packet initialization gives

$$
\boxed{q(5)>F_{\Lambda+\omega+1}\!\left(K(g(g(X)))\right).}
\tag{3}
$$

This retains the actual chain-length constant.

**C. An input retaining more of the original recursion.** Put $H_0=u_{\omega^\omega}$, using the usual Cantor fundamental sequences below $\varepsilon_0$.

$$
u_0(m)=m2^m,\quad u_{\alpha+1}(m)=u_\alpha^{\circ2^m}(m),\quad
u_\lambda(m)=u_{\lambda[2^m]}(m).
\tag{4}
$$

We have $H_0(1)=C_{\rm line}$. With base $H_0$ define

$$
U_0^{H_0}=H_0,\quad
U_{\alpha+1}^{H_0}(m)=(U_\alpha^{H_0})^{\circ2^m}(m),\quad
U_\lambda^{H_0}(m)=U_{\lambda[2^m]}^{H_0}(m),
$$

$$
\widehat J=U_{\omega+1}^{H_0}(1),\qquad X_*=2^{\widehat J}.
$$

Initialization with shared ports gives the stronger bound

$$
\boxed{q(5)>F_{\Lambda+\omega+1}\!\left(K(g(g(X_*)))\right).}
\tag{5}
$$

These auxiliary indices describe particular recursions. We do not identify them with the order type of pIBLP. The main argument applies to any realized entrance meeting its hypotheses. Equations (2), (3) and (5) use three different established entrances.

## 2. The BMS count and its realization by feedback

Let $D(h)$ count all steps taken by $(0^h)(1^h)(1^h)$ to reach the empty matrix under repeated application of the original BM4 index $[1]$. Put $T(h)=D(h)+2$ and $e_0=1,e_{n+1}=2^{e_n}$. By [Shared fixed-index lemma](common/bms-fixed-index.md),

$$
h\ge\rho(x),\ x\ge2\Longrightarrow
D(h)\ge e_{g(x)},\qquad T(h)\ge\rho(g(x)).
\tag{6}
$$

The proof follows the fixed-index path, covers it by ancestors, compiles the resulting forest, and keeps an explicit budget of rows.

Fixed finite background

$$
k=\kappa_2<a=\theta_6<b=\tau<c=\theta_7<\kappa_4.
$$

A closed compatible fan of height $h$ has two increasing rows of ports with their owners, a common lower source and a cap. It realizes a three-column BMS seed. Following the fixed descent gives a budget of critical-point indices for endpoint deletions strictly larger than $D(h)$.

The specific term $P=L_3(f)$ satisfies

$$
P(\gamma_0)=a,\quad P(\gamma_1)=b,\quad P(b)=c,
$$

There are actually two instances of $L(k,a,b;2)$. By calculating the BMS, we obtain $\gamma_{D(h)}$ located beneath the seal. By transporting the standard finite chain to the required length and then inserting it uniformly at the front end, a natural template is obtained.

$$
T:(h,\ \text{cap}<b)\longmapsto(D(h)+2,\ \text{cap}<c).
\tag{7}
$$

Here naturality means that after applying an allowed environmental embedding to the whole finite background, the construction works for every valid entrance fan in its image environment. The entrance need not itself be an image of the old fan. This quantifier allows repeated use.

The initial long chain is taken as $L_3(K)$, and then an insertion is made at the front end to provide an entrance for $3\le h\le C_{\rm line}+2$. All implicit edges, membership truncations, and closed owners are located in the [Self-contained base proof](proofs/output/iblp-030-laver-20261014/q5-BMS-successor-single-file-proof.md) section on the 3–8 side; the [Recursive corridor](proofs/output/iblp-030-laver-20261014/small-period-recursive-corridor.md) provides the naturalness of the overall background.

## 3. Choosing a finite depth dynamically under a common cap

Definition

$$
U_0=T,\qquad U_{i+1}(h)=U_i^{\circ(D(U_i(h))+1)}(h),
$$

$$
m(h)=\lfloor\log_2D(T(h))\rfloor,\qquad V(h)=U_{m(h)}(h).
\tag{8}
$$

The actual terms $H=j_{(9)}(j_{(4)})$ and $A_*=H(f)$ satisfy

$$
c<H(a)<H(b)<H(c)<\kappa_4,\quad
A_*(\gamma_0)=r=\kappa_3,\quad A_*(\gamma_1)=u,
$$

$$
c<u,\quad A_*(u)=H(a),\qquad d=A_*(c)<H(a).
\tag{9}
$$

Save another copy, execute the $T$ operation once, and seal it with $C'<c$. Set $N=D(T(h))$ and $m=\lfloor\log_2N\rfloor$, then $\gamma_{2^m}\le\gamma_N<C'$. Take the entire standard $m$-line and image it with $A_*$, resulting in a real chain that starts from $u$ and has its final endpoint below $A_*(C')<d$. Upgrade the $U_0,\ldots,U_m$ along this chain step by step; each new exit point is below the end of the current segment, so all dynamic finite-depth seals are unified below $d$.

A separate, already terminated BMS computation supplies the depth. When transporting the environment, one moves all actors, roots and endpoints together. The numerical function $m(h)$ stays the same.

From (9), it is possible to upgrade the entire dynamic template:

$$
W(h)=V^{\circ(D(V(h))+1)}(h),\qquad q(5)>D(W(h)).
\tag{10}
$$

Each call to $V$ chooses the depth afresh from the current height. The final realized output is $H(c)<\kappa_4$. The endpoints, guards and naturality are checked in [Proof of the dynamic depth bound](proofs/output/q5-further-bound-20261014/dynamic-depth-Lambda-omega-successor.md).

## 4. Comparing successive rounds with the FGH

Write $J_i=F_{\Lambda+i}$, so $K(x)=J_{x+1}(x)$. Induction using (6) gives

$$
h\ge\rho(x)\Longrightarrow U_i(h)\ge\rho(J_i(x)).
\tag{11}
$$

Put $x_2=g(g(x))$. Two buffer rounds also give

$$
D(T(h))\ge e_{x_2},\qquad m(h)-1\ge x_2+1.
\tag{12}
$$

Retain the first two rounds within $V(h)=U_{m-1}^{\circ(D(U_{m-1}(h))+1)}(h)$: The first round is at least up to $\rho(x_2)$, and the second round reaches

$$
\rho(J_{m-1}(x_2))\ge\rho(J_{x_2+1}(x_2))=\rho(K(x_2)).
$$

Let $y=K(x_2)$ be defined. The outer call budget is $D(V(h))+1\ge y+2$. In the first round, $V$ arrives $\rho(y)$, and there are at least $y+1$ rounds left to simulate along the same $K$ trajectory, hence

$$
W(h)\ge\rho(K^{\circ(y+1)}(y))
=\rho(F_{\Lambda+\omega+1}(y)).
$$

Finally, (6) and (10) yield the general entrance theorem

$$
\boxed{h\ge\rho(x),\ x\ge2
\Longrightarrow q(5)>F_{\Lambda+\omega+1}\!\left(K(g(g(x)))\right).}
\tag{13}
$$

The proof follows a specific increasing trajectory throughout and requires no global monotonicity in the input of $U_i,V$ or pIBLP.

## 5. The stronger initialization

The sealing of the nine actual seeds $S$ is $\theta_6<\kappa_4$. Let

$$
G(m)=f_{\rm PP}(S,m),\quad
H_0(m)=f_{\rm PP}(S[0]^5,m),\quad L=G(1).
$$

The parent package has a finite number of parameters, which are used in this actual realization and the parameters involved. It also proves the recursive definiteness and $L$-linedness. The actual chain is fed into the front end for insertion, resulting in the actual entry height $h_*=L+2$.

The pure E identity gives $H_0=u_{\omega^\omega}$. Finite transient paths, auxiliary E, and prefix extraction give

$$
L\ge H_0(C_{\rm line}),\qquad
L\ge H_0(\widehat J)\ge\widehat J\,2^{\widehat J}.
\tag{14}
$$

The first equation is given as $h_*\ge\rho(X)$ after two rounds of purely E finite FGH comparisons, with the proof (3); the second equation is given as $h_*\ge\rho(2^{\widehat J})$, with the proof (5). The result $\widehat J$ comes from the line-by-line parametric substitution from the grafts at the shared 0, 1, and 2 ports.

In order, the inputs are [Nine-row seed](proofs/output/iblp-030-laver-20261014/same-owner-L3-sat-closure.md), [Quantitative parent-packet lemma](proofs/output/iblp-030-laver-20261014/parent-packet-quantitative-transfer.md), [Pure E reduction](proofs/output/piblp-external-FGH-20261014/P4-pure-E-collapse.md), [Finite-level FGH initialization](proofs/output/q5-further-bound-20261014/P5-uniform-and-large-input.md) and [Strengthening through shared ports](proofs/output/q5-further-bound-20261014/active-port-stronger-initialization.md).

## 6. Dependencies

The direct-chain version (2) is independent of pIBLP. The larger inputs (3) and (5) use a parent-packet recursion at finite parameters. They do not assume a well-order for the whole notation or an order isomorphism with the original IBLP.

This argument does not establish a large-input Hardy or FGH bound for the whole of the original $I[0][2]$ or $R$. Comparing this numerical estimate with the first paper's estimate requires more than comparing the names of their ordinal indices. [Dependencies by statement](PROOF_DEPENDENCIES.md)
