# The P5 recursion of pIBLP and the larger FGH initialization · [中文版](P5-uniform-and-large-input.zh-CN.md)

*English reading edition, translated with machine assistance. The title links to the dated Chinese manuscript.*

> Collected reading edition. The three main papers state the results of this collection.
> This edition retains the local proofs, their hypotheses and any withdrawals. Progress reports describe the state of work at the time.
> The locations of omitted passages on preset inputs are recorded in SOURCE_MANIFEST.json.
> The main papers give the numerical derivations for the natural parameters produced by the proofs. This historical note carries no additional Lean certification.

2026-10-14. Assume ZFC + I3, using the same actual embedding algebra and the proven pIBLP finite parameter quantitative bridge. Denote as

$$
G(m)=f_{\rm PP}(S,m),\qquad H(m)=f_{\rm PP}(P_4,m),\qquad C=H(1),
$$

Among them, $P_i$ are the first $i$ rows of the nine actual seeds $S$. The following provides a new explicit lower bound that does not depend on any unknown external notation: Let

$$
\Lambda=\lim(\mathrm{BMS}),\quad g=F_\Lambda,\quad
X=F_{2^C+1}(C),
$$

Then

$$
\boxed{q(5)>F_{\Lambda+\omega}\bigl(g(g(X))\bigr).}\tag{1}
$$

Here, $(\Lambda+\omega)[x]=\Lambda+(x+1)$. This is a strict enhancement of the original explicit numerical bounds that initialize with $2^C$. It is not a proof of embedding a notation for an order type that is strictly greater than BMS into pIBLP.

## 1 already has interfaces

[Strict P5 prefix calculation](<../piblp-q5-enhancement-20261014/audit-piblp-strict-Cline.md>) represents actual definitions and calls.

$$
L=G(1)\ge H(H(1))=H(C).\tag{2}
$$

[Pure E closed set](<../piblp-external-FGH-20261014/P4-pure-E-collapse.md>) provides the exact identity

$$
H(m)=u_{\omega^\omega}(m),\tag{3}
$$

amongst

$$
u_0(m)=a(m)=m2^m,\quad
u_{\alpha+1}(m)=u_\alpha^{\circ2^m}(m),\quad
u_\lambda(m)=u_{\lambda[2^m]}(m).
\tag{4}
$$

The subscript is less than $\varepsilon_0$, using the usual Cantor normal form fundamental sequence. The formula (3) is a syntactically recursive full-parameter identity; the actual call definitiveness in (2) is also guaranteed by a finite-parameter bridge.

[Compilation of the recursive corridor](<../piblp-q5-enhancement-20261014/q5-piblp-enhanced-bound.md>) has been proven to provide a legal entrance fan for the actual output length $L$ and the supply height $h_*=L+2$.

$$
\rho(x)=x+3+\lceil\log_2(x+2)\rceil
$$

There are

$$
h_*\ge\rho(x),\quad x\ge2
\quad\Longrightarrow\quad
q(5)>F_{\Lambda+\omega}\bigl(g(g(x))\bigr).
\tag{5}
$$

Therefore, the new proof task is simply to establish $H(C)\ge\rho(X)$ rigorously.

## The fundamental sequence with fixed parameters2 decreases comparably

For all $\alpha<\varepsilon_0$, by induction from the subscript, $u_\alpha(m)\ge a(m)\ge m$. For a fixed $m\ge1$, set it as $n=2^m$. If

$$
\beta=\alpha[n]\quad(\alpha\text{ is a limit}),
\qquad\text{or}\qquad
\beta=\alpha-1\quad(\alpha\text{ is a successor}),
$$

Then $u_\alpha(m)\ge u_\beta(m)$. The limit case is defined; the successor case, because each iteration of $u_\beta$ does not decrease the current value, the result of iterating $n$ times is at least the result of the first iteration. This argument does not assume that $u_\beta$ is monotonous with respect to the input.

When $m\ge1$, $n\ge2$, from $\omega^\omega$ along the aforementioned fixed $n$ operation, one can reach $\omega+1$: The first step is $\omega^n$, followed by $\omega^{n-1},\ldots,\omega^2$, then $\omega n$, removing the trailing $n-2$ blocks of $\omega$ to reach $\omega\cdot2$, then $\omega+n$, and finally deleting $n-1$ successors.

The process of "removing a block at the tail" is a finite fixed-point descent process: only that tail block is operated on, while the preceding Cantor prefix remains unchanged. The ordinal numbers below $\varepsilon_0$ decrease, ensuring that the tail block eventually becomes zero. This process does not require calculating its enormous actual length.

Therefore

$$
H(m)=u_{\omega^\omega}(m)\ge u_{\omega+1}(m)
=u_\omega^{\circ2^m}(m).
\tag{6}
$$

## 3 is used for the classical FGH comparison only on finite levels.

Here, the classical finite layer convention is $F_0(x)=x+1$, $F_{r+1}(x)=F_r^{\circ(x+1)}(x)$. For $x\ge2$,

$$
a(x)=x2^x\ge2x+1=F_1(x).
$$

The usual induction on finite natural number subscripts gives $F_r$ as a monotonous function of the input. By applying the induction to $r$ and using $2^x\ge x+1$, we obtain

$$
u_r(x)\ge F_{r+1}(x),\qquad r<\omega,\ x\ge2.
\tag{7}
$$

Inductive steps indeed require comparison iteration, but here we only use the finite layer $F_{r+1}$ that has been proven to be monotonic: if the current $u_r$ trajectory input is not less than the corresponding $F_{r+1}$ trajectory input, then the pointwise lower bound (7) and the monotonicity of the latter maintain this relationship. Here, the monotonicity of the unknown global inputs of $u_r$, $H$, or $G$ is not used.

At $x=C\ge2$, let $n=2^C$. From $\omega[n]=n$,

$$
y_1=u_\omega(C)=u_n(C)\ge F_{n+1}(C)=X.
\tag{8}
$$

Also, since $u_\omega(y)\ge a(y)$, and $a$ is strictly increasing with respect to the input, the second iteration satisfies

$$
y_2=u_\omega(y_1)\ge a(y_1)\ge a(X)\ge\rho(X).
\tag{9}
$$

The last inequality holds for the integer $X\ge2$: $\lceil\log_2(X+2)\rceil\le X$, hence $\rho(X)\le2X+3\le X2^X$. The iteration number of the formula (6) is at least 2, and the remaining iterations do not reduce the current value. Therefore

$$
\boxed{L\ge H(C)\ge\rho\bigl(F_{2^C+1}(C)\bigr).}\tag{10}
$$

Substituting (10) for (5) gives (1).

Due to the monotonicity of the finite layer subscripts, it is proven that for $X\ge F_2(C)>2^C$, [The input strict monotonicity of the BMS diagonal sum and finite successor layer](<../piblp-q5-enhancement-20261014/audit-BMS-diagonal-input-monotonicity.md>) proves that the right endpoint of 1) strictly exceeds the original $F_{\Lambda+\omega}(g(g(2^C)))$.

If you wish to remove the literature constant $C$, there are already $C>4t$, $t=F_3(256)$, so it can also be conservatively written as such.

$$
\boxed{q(5)>F_{\Lambda+\omega}\bigl(g(g(F_{2^t}(t)))\bigr),
\qquad t=F_3(256).}\tag{11}
$$

Here, we still use the monotonicity of finite FGH layers to compare two initialized integers.

## The fully parametric block structure for 4 P5

Another accurate structure that can be reused is to let $Q_l$ be the pattern composed of $l$ and the following two lines, with the first two lines fixed as $01:1$ and $012:1$:

$$
(0,1,2,2i+1):2,\quad
(0,1,2,2i+1,2i+2):2\ \text{and mark }2i+1,
\qquad1\le i\le l.
$$

Therefore, $Q_1=P_4$. The threshold of P5 for E is 3; its $m$th auxiliary raw copy simply doubles the number of existing blocks, so for all $m\ge0$,

$$
\boxed{E_{P_5}(m)=Q_{2^m}.}\tag{12}
$$

Looking at each coordinate, each round of source blocks starts from address 3, with a total of $2l$ rows. The shared 0, 1, and 2 remain fixed, while all other addresses are uniformly increased by $2l$. The marks are preserved with the same translation. No PP or native scanning is performed here.

The deletion prefix $R_{l+1}$ of $Q_{l+1}$ is followed by a $Q_l$ and then a E-successor, resulting in a complete pass of the guard. The actual defined parameters are located at

$$
f_{\rm PP}(Q_{l+1},m)
\ge f_{\rm PP}(R_{l+1},m)
=[x\mapsto f_{\rm PP}(Q_l,x)]^{\circ2^m}(m).
\tag{13}
$$

It is safe to extract a fully parameterized monotonic lower envelope. Definition

$$
B_0(m)=m2^m,\qquad B_{r+1}(m)=B_r^{\circ2^m}(m).
$$

Each $B_r$ is monotonic and not less than the input. It is derived by using a finite definition of certificates called (13) and the current E-successor.

$$
f_{\rm PP}(Q_l,m)\ge B_{l-1}(m),\qquad
\boxed{G(m)\ge B_{2^m-1}(m)}
\tag{14}
$$

In $G(m)$, every parameter holds true for which there is a valid certificate. The formula (14) does not claim that any handwritten $Q_l$ can take any linedness parameter under a fixed cap.

If we want to replace the $B_0$ in the expression (14) with $H$, it is also necessary to provide the monotonicity of the $H$ input or assign a different monotonic lower envelope. The point inequality is not sufficient to directly transfer multiple iterations between unknown non-monotonic functions; therefore, this substitution is not made in this paper. The main conclusion of the expression (1) does not depend on it at all.

## 5 Conclusion Range

The new conclusion is the initialization buffer for (10), the explicit FGH lower bound for (1), and the unified P5 interface from (12) to (14). There is no inference of the pIBLP as a whole being small by a purely (E) $\varepsilon_0$ control family, nor is this initialization enhancement considered to be a strictly super-BMS ordinal FGH control. The true external large notation embedding and its FGH compilation still require maintaining transient replication and global E ports.

Finite block certificates (historical reference: `P5-block-audit.py`) verify all E array identities from m=0 to 6, as well as the subsequent cuts and complete guards for 39 number of blocks, totaling 124 items. The peak value occurs at line 130, with 775 entries, taking approximately 0.02 seconds. It does not evaluate any extremely large numerical functions; the comprehensive conclusions from section 2 to 3 are given by the aforementioned paper-based induction.
