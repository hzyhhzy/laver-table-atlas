# Feedback along the long chain segment by segment: The number of feedback rounds can be a BMS calculation result · [中文版](lined-feedback-corridor.reading.zh-CN.md)

*English reading edition, translated with machine assistance. The title links to the dated Chinese manuscript.*

> Collected reading edition. The three main papers state the results of this collection.
> This edition retains the local proofs, their hypotheses and any withdrawals. Progress reports describe the state of work at the time.
> The locations of omitted passages on preset inputs are recorded in SOURCE_MANIFEST.json.
> The main papers give the numerical derivations for the natural parameters produced by the proofs. This historical note carries no additional Lean certification.

2026-10-14. Within the same `Iter(j)`, assuming still ZFC + I3, the restrictions imposed by the previous two rounds of feedback can be lifted. The key is not to repeatedly use the same sealing interval, but to follow a lined chain with a finite number of witnesses, providing a complete set of feedback backgrounds for each round of transport. The following is a new paper conclusion:

$$
\boxed{q(5)>D\!\left(T^{\circ(D(T(h))+1)}(h)\right),
\qquad 3\le h\le C_{\rm line}+2.}\tag{A}
$$

Here, $D(h)$ is the number of steps in which $R_h=(0^h)(1^h)(1^h)$ is fixed to the original BM4, `[1]` becoming empty. $T(h)=D(h)+2$ and $C_{\rm line}$ are the explicit long-chain parameters within [Two-part summary](<q5-BMS-FGH-two-part-summary.md>). The notation $T^{\circ n}$ indicates a function iteration, not exponentiation.

This goes further than the three-time BMS calculation: now the number of executions is also determined by one-time BMS calculation. But it is still a **Numerical lower bounds**; this paper does not rename it as a new super-BMS ordinal, nor has it completed the FGH lower bound of the original IBLP 030.

## 1. already has a finite background

Follow the conventions of [First round of feedback](<root-lowered-bms-feedback.md>) and [Second-round transport](<promoted-bms-feedback.md>). Let

$$
k=\kappa_2,\qquad a=\theta_6,\qquad b=\tau,
\qquad c=\theta_7,
$$

$$
P=L_3(f),\qquad P(\gamma_0)=a,\quad P(\gamma_1)=b,
\quad P(b)=c.\tag{1}
$$

There exists a real 2-lined $(k,a,b)$ witness. The unified front-end insertion lemma transforms any $m$-lined $(k,a,z)$ witness into a closed compatible group with a height of $m+2$ and a seal strictly below $z$. The lemma only requires the finite point images of that background, strict order relations, membership truncation, and application identities.

There is also actual embedding.

$$
S=j_{(9)}(j_{(4)}),\qquad \operatorname{crit}(S)=\mu>k,
$$

$$
c<S(a)<S(b)<S(c)<\theta_8<\kappa_4.\tag{2}
$$

In the first item, the proven $c<\nu=S(\mu)$ and $\mu<a$ are used. It is not only the old conclusion $c<S(b)$ that is needed here, but a stronger $c<S(a)$ is utilized.

An initial long chain has been established. For all $3\le h\le C_{\rm line}+2$, a closed and compatible set with a height of $h$ and sealed with $C_h<b$ is provided. After feedback from the original template, a set with a height of $T(h)$ and sealed with $C_1<c$ is obtained.

## 2. Background Transport Lemma

The old proof required that the transport embedding fix the $k$ in order to still use the original insertion lemma with a root of $k$. In fact, it is possible to transport the entire finite background of the insertion lemma at the same time, so this condition is not necessary.

**Lemma.** Let $Q\in\operatorname{Iter}(j)$ be fixed, and let $\gamma_0=\kappa_0$ and $\gamma_1=\kappa_1$ be other constants. Closed compatible groups with arbitrary height $x\ge3$ and sealing $C<Q(b)$ All can be grouped with a height of $T(x)$ and a sealing that is strictly lower than $Q(c)$. The owner of the input group must belong to the global $\operatorname{Iter}(j)$.

Prove by first clarifying the tools after transportation, rather than assuming that the input group also has a $Q$-image of some old group. Take the 1 section background's each named point, owner, truncation point, and application item as a $Q$-image one by one, to obtain

$$
k'=Q(k),\quad a'=Q(a),\quad b'=Q(b),\quad c'=Q(c),
\quad P'=Q(P),
$$

$$
P'(\gamma_0)=a',\qquad P'(\gamma_1)=b',\qquad P'(b')=c'.\tag{3}
$$

Actual testimonies of 2-lined $(k',a',b')$ And the following **Post-transport unified insertion lemma**: Any evidence of using $m$-lined $(k',a',z)$ can result in groups with a high $m+2$ value and a seal that is lower than $z$.

The final universal version does not state that "any new chain can be pulled back to the inverse image of $Q$". It originates from the same finite induction that reexecutes [Insert the manuscript](<../iblp-laver-bms-20261013/lined-front-insertion.md>): all background constants are replaced with the $Q$-image, and the given new chain owners participate in the construction according to the original application formula. All strict readies, common truncations, and endpoint comparisons are carried out along with the background transport. Since $Q$ fixes $\kappa_0,\kappa_1$, the bottom of the new group still consists of these two points. Any new chain owner participating does not have to come from $\operatorname{Iter}(Q(j))$; as long as they are in the same environmental algebra, the formulas and truncation rules remain valid.

Now dealing with the input group. Let $N=D(x)$, $m=\lfloor\log_2N\rfloor$. Using the critical point enumeration of **Global** $\operatorname{Iter}(j)$, with counting given

$$
\gamma_{2^m}\le\gamma_N<C<Q(b)=b'.\tag{4}
$$

The global Dougherty chain is $m$-lined $(\gamma_0,\gamma_1,\gamma_{2^m})$. Taking its $P'$-image, and multiplying it with the two segments of the chain after transportation, we obtain

$$
(k',a',Z)\text{ is }2^{m+1}\text{-lined},
\qquad Z=P'(\gamma_{2^m})<P'(C)<P'(b')=c'.\tag{5}
$$

Due to $N<2^{m+1}$, by applying the existing formula for contracting chains to preserve endpoints, it is reduced to a segment of $N$. Then, using the unified insertion after transportation, we obtain groups with a high degree of $N+2=T(x)$ and a sealing level lower than $Z<c'$. All terms still belong to the original $\operatorname{Iter}(j)$. Proof complete.

Note that the proof does not use the subalgebra $\operatorname{Iter}(Q(j))$ for enumerating critical points, nor does it assume that the input groups belong to that subalgebra; this avoids an implicit domain switch that could undermine the quantitative interface.

## A chain of 3. provides the same number of rounds of feedback.

Suppose there is a witness with a finite length of the sequence $M\ge1$

$$
(k;u_0<u_1<\cdots<u_M),\qquad c<u_0,
$$

$$
\operatorname{crit}(Q_r)=k,\quad Q_r(k)=u_r,
\quad Q_r(u_r)=u_{r+1}\quad(0\le r<M).\tag{6}
$$

Because $\gamma_0,\gamma_1<k$, every $Q_r$ satisfies the fixedness requirements of the 2 section. Furthermore, because $k<b<c<u_r$,

$$
u_r=Q_r(k)<Q_r(b),\qquad Q_r(c)<Q_r(u_r)=u_{r+1}.\tag{7}
$$

If the closure of the $r$th input group is $C_r<u_r$, then $C_r<Q_r(b)$. The overall background transport lemma provides a high degree of application once $T$, with closures satisfying

$$
C_{r+1}<Q_r(c)<u_{r+1}.\tag{8}
$$

Therefore, for any input set with height $x\ge3$ and a seal below $u_0$, the finite induction yields an output set with height $T^{\circ M}(x)$ and a seal below $u_M$.

In each round, different actual $Q_r$s and corresponding backgrounds are used. The input conditions come from strictly increasing chain endpoints. This does not involve an infinite loop within the same $(b,c)$ interval, nor is it required that a fixed endpoint support all natural length values.

### A direct corollary that does not depend on a new counting method

The chain starts with the $C_{\rm line}$-lined $(\kappa_0,\kappa_1,\theta_5)$ chain, followed by the $E=L_3(K)$-image, and then the $S$-image. Their common root is the $k$, the starting point is the $S(a)>c$, and the end point is the $S(E(\theta_5))<S(b)<\kappa_4$. In the 3 section, feedback by the $C_{\rm line}$ round is allowed, not just two rounds. The next section allows the chain length to depend on the completed BMS calculations.

## 4. is calculated using BMS to generate feedback chain length

Fix the allowed $h$. In the 1 section, a group of highly $T(h)$ and sealed $C_1<c$ is given first. Let

$$
N=D(T(h)),\qquad m=\lfloor\log_2N\rfloor.\tag{9}
$$

At this point, it is $\gamma_{2^m}\le\gamma_N<C_1<c<S(b)$. Take the $m$ segment chain of the global Dougherty and apply the $S(P)$-image, then combine it with a $S$-image segment chain while preserving the endpoint shortening. Thus, we obtain the desired result.

$$
(k,S(a),Z)\text{ is }N\text{-lined},
$$

$$
Z=S(P)(\gamma_{2^m})<S(P)(C_1)<S(P)(S(b))=S(c)<\kappa_4.\tag{10}
$$

The common root of the chains here remains $k$, because $S$ fixes $k$. The starting point satisfies $S(a)>c$. Therefore, this is the long chain that is available in the 3 section.

The input group with a height of $T(h)$ has been sealed $C_1<c<S(a)$. The $N$ round can be directly executed along this chain to obtain the height.

$$
T^{\circ N}(T(h))=T^{\circ(N+1)}(h)\tag{11}
$$

The closed compatible group is sealed below $Z<\kappa_4$. Finally, using counting again, we obtain (A).

The order of quantifiers is: First complete a group with a height of $T(h)$ and its limited BMS computation. Determine the natural number $N$; A finite chain with a reconstruction length of $N$; Finally, perform $N$ finite inductions. It does not make $N$ dependent on the final output. No termination condition has been preset for an unknown hyper-BMS system.

### A concise FGH numerical theorem

Following the conventions of [Two-part summary](<q5-BMS-FGH-two-part-summary.md>) for all FGH, tower function $e$, and buffer function $\rho$, let $t=F_3(256)$, $h=C_{\rm line}+2$, and denote $x_i=F_\Lambda^{\circ i}(t)$.

$$
\boxed{q(5)>F_{\Lambda+1}\!\left(F_\Lambda\!\left(F_\Lambda(F_3(256))\right)\right).}
\tag{12}
$$

The precise contraction only requires the existing buffer lemma and the subsequent definitions of FGH:

$$
\begin{aligned}
T^{\circ i}(h)&\ge\rho(x_i),
 &D(T^{\circ i}(h))&\ge e_{x_{i+1}};\\
N=D(T(h))&\ge e_{x_2}\ge x_2+1;\\
q(5)&>D(T^{\circ(N+1)}(h))\ge e_{x_{N+2}}
 \ge x_{x_2+3}\\
&=F_\Lambda^{\circ(x_2+1)}(x_2)=F_{\Lambda+1}(x_2).
\end{aligned}
$$

The first line is a proof by induction along the natural numbers $i$; the inequalities before the last line only use $N+2\ge x_2+3$, $F_\Lambda(x)\ge x+1$, and $e_y\ge y$. Here, $\Lambda+1$ is just a shorthand for the proven **Numerical lower bound for iteration**, and does not indicate that a new notation with a more substantial internal structure has been constructed as requested by the user.

## What is still missing from the main line of larger ordinals 5.?

The actual progress in this work is the change from a "manual two rounds" to a "computationally finite number of rounds" for the endpoint budget. It does not design a notation for internal unbounded regularization within a fundamental sequence; $D$ is merely an estimated computational function, not a step in the definition of a new fundamental sequence.

However, even if we transform (A)) into a large $F_\Lambda$ iteration, it cannot be claimed that a new internal hierarchy has been found. To proceed further, it is necessary to treat the "feedback template and its chain" itself as a structure that can be replicated and generate sub-templates, and to prove that invariants such as input/output closures and natural truncations are uniformly maintained under this higher-level structure. It is particularly important not to consider the end of (10) as a legitimate input to the second template just because the 3 section can run any specified finite chain: it only guarantees that it is lower than $S(c)$, but not necessarily lower than $S(b)$.

More precisely, the separation condition for a layer of long chains is

$$
\text{chain root }r<\text{template entrance }b<\text{template exit }c<\text{initial point of the chain }u_0.
$$

The exit of the new operator has become $S(c)$, but the starting point of the original chain is $S(a)<S(c)$. Therefore, we cannot assume that the naturalness of the entire background is a next-level closure. A sufficient new entry would be to find an actual embedding of $H$ that fixes $\kappa_0,\kappa_1,\kappa_2$, so that

$$
S(c)<H(a),\qquad H(S(c))<\kappa_4.
$$

If we relax the condition that the $\kappa_2$ is fixed, we must also consider the order of the new chain root and the old template entrance. Here, we only list the version with three fixed points as a sufficient condition. Another approach is to establish a nested structure with such separation certificates at each level, and to prove that replication and completion maintain it.

The limited probing of the next layer of transporters (historical reference: `next_corridor_promoter_probe.py`) only examines one pre-listed 82 item from the application family. It takes approximately 11.3 seconds to complete the comparison of 35 items that satisfy the known three-point fixity condition. The remaining 47 items have not proven this fixity condition, and no hits were obtained. The result is UNKNOWN, which does not prove non-existence, nor does it exhaust other items or other proof paths.

The relationship with [Short-tailed IBLP](<short-tail-cofinality.md>) still requires constructive correspondence; this paper does not assert that the entire chain of feedback occurs in the fixed `[2]` orbit of those six lines. The paper-based derivation has been independently audited and has not yet been formalized in Lean.

Finite interface verification (historical reference: `feedback_corridor_certificate.py`) reruns the old certificates of the actual transporter. It also examines the conditional algebraic consequences of two abstract segments, including the indeed movement of the template root rather than remaining fixed at $\kappa_2$. This process takes approximately 1.9 seconds; the abstract part has 18 named points, 12 owners, and 43 point-like facts. The abstract graph assumes that lined witness exists, without pretending that the pattern is contradictory. The existence of the witness required in section 4 comes from the paper-based construction, not from this test.
