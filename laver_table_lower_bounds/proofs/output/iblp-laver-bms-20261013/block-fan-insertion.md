# A sufficient condition for the BMS level to increase by a whole block from the source interval · [中文版](block-fan-insertion.reading.zh-CN.md)

*English reading edition, translated with machine assistance. The title links to the dated Chinese manuscript.*

> Collected reading edition. The three main papers state the results of this collection.
> This edition retains the local proofs, their hypotheses and any withdrawals. Progress reports describe the state of work at the time.
> The locations of omitted passages on preset inputs are recorded in SOURCE_MANIFEST.json.
> The main papers give the numerical derivations for the natural parameters produced by the proofs. This historical note carries no additional Lean certification.

The following algebraic lemma maps a set of already compatible source intervals into multiple layers of BMS compatible groups at once. The new layers are constructed directly from the same old embedding, without the need for recursive transport at each level. If the last end inequality holds, it is possible to switch to a BMS with no completion expansion.

It has not been proven that standard marked starting points can produce any finite block that meets these conditions. Therefore, this paper does not add the already completed three-layer lower bound initialization. It provides the specific structure to be extracted from the completion records, rather than interpreting the parameters of length, number of lines, or linedness directly as the number of BMS layers.

The entire text has a fixed I3 embedded in $j$, with all embeddings belonging to $\operatorname{Iter}(j)$. The application writing is performed by $a(b)$, which should be distinguished from the function composition $a\circ b$.

## Old compatible groups and source interval blocks

Let there exist a compatible set with a high $h\ge1$

$$
U_0<\cdots<U_h<V_0<\cdots<V_{h+1},
$$

$$
\operatorname{crit}(K_k)=U_0,\qquad
K_k(U_t)=V_t\quad(0\le t\le k),\qquad
K_k(V_0)=V_{k+1}\quad(1\le k\le h).
\tag{1}
$$

Let $J=K_h$, $S=V_{h+1}=J(V_0)$.

Additionally, there are integers $r\ge0$, source points, and target points.

$$
U_h<x_0<\cdots<x_r<V_0=Z_0<Z_1<\cdots<Z_{r+1},
\tag{2}
$$

And $G_0,\ldots,G_r$, satisfying

$$
\operatorname{crit}(G_i)=x_0,\qquad
G_i(x_t)=Z_t\quad(0\le t\le i),\qquad
G_i(V_0)=Z_{i+1}.
\tag{3}
$$

Here, $G_0:x_0\mapsto V_0\mapsto Z_1$ is intentionally included. It is a necessary underlying witness that cannot be omitted directly from a compatible group that contains only $G_1,\ldots,G_r$. At $r=0$, (3) only requires this one three-point witness.

Each witness of ordinary linedness has a different first critical image; however, the witnesses of 3) all send $x_0$ to the same $V_0$ and require that multiple source images are compatible. Therefore, the eight-segment linedness cannot directly serve as $G_0,\ldots,G_7$.

## Whole-block insertion lemma

For $0\le i\le r$, define

$$
H_i=J(G_i),\qquad A_i=H_i(J).
\tag{4}
$$

The following data form a compatible set with a high degree of $h+r+1$:

$$
\begin{aligned}
\text{source}&=(U_0,\ldots,U_h,x_0,\ldots,x_r),\\
\text{target}&=(V_0,\ldots,V_{h+1},J(Z_1),\ldots,J(Z_{r+1})),\\
\text{witness}&=(K_1,\ldots,K_h,A_0,\ldots,A_r).
\end{aligned}
\tag{5}
$$

**Proof.** Let $\beta=J(x_0)$. From (1), (2),

$$
V_h<\beta<S,\qquad \operatorname{crit}(H_i)=\beta.
\tag{6}
$$

Therefore, each $H_i$ fixes all the old source points, all the $x_t$, and the $V_0,\ldots,V_h$. Utilization

$$
a(b)(a(\xi))=a(b(\xi)),
\tag{7}
$$

Obtained

$$
\operatorname{crit}(A_i)=U_0,\qquad
A_i(U_t)=V_t\quad(0\le t\le h).
\tag{8}
$$

For $t\le i$, it can be derived from $H_i(x_t)=x_t$ and (3)

$$
A_i(x_t)=H_i(J(x_t))=J(G_i(x_t))=J(Z_t).
\tag{9}
$$

Specifically, $A_i(x_0)=J(V_0)=S$. In addition

$$
A_i(V_0)=H_i(J(V_0))=J(G_i(V_0))=J(Z_{i+1}).
\tag{10}
$$

These are the compatibility equations for the newly added layers. The strict order of all target points is determined by the strict increasing nature of $J$ and $Z_0=V_0$; the old $K_k$ and its point images have not been modified. Proof complete.

The key point is that (4) in $J$ is the same for every $i$. Here, $A_{i-1}$ is not substituted into the next round, so this formula should not be misinterpreted as a series of $H_r\circ\cdots\circ H_0$ effects on the end.

## The first way of sealing

If the old group already has independent terminal witnesses

$$
\operatorname{crit}(L)=V_0,\qquad L(V_0)=S,\qquad C=L(S),
\tag{11}
$$

Then take

$$
L'=H_r(L).
\tag{12}
$$

Because $V_0<\beta$, the identity is given as follows

$$
\operatorname{crit}(L')=V_0,\qquad
L'(V_0)=J(Z_{r+1}),\qquad
L'(J(Z_{r+1}))=H_r(C).
\tag{13}
$$

Therefore, it is only necessary to prove an upper bound.

$$
\boxed{J(G_r)(C)\le\Theta}
\tag{14}
$$

This can seal off the entire $h+r+1$ layer group, rather than controlling each and every $r+1$ accumulating end individually.

There is also a sufficient condition that uses inequalities on the source side. If there is a critical point $D,E$,

$$
C\le J(D),\qquad G_r(D)\le E,\qquad J(E)\le\Theta,
\tag{15}
$$

Then

$$
J(G_r)(C)
\le J(G_r)(J(D))
=J(G_r(D))
\le J(E)\le\Theta.
\tag{16}
$$

It is not necessary to assume that $C$ itself is in the image of $J$, nor is it necessary to know its exact subscript.

## The second method of sealing

The old group does not necessarily require (11). If it is possible to find another $F$ and $E$, then

$$
\operatorname{crit}(F)=U_0,\qquad
F(U_0)=Z_{r+1},\qquad F(Z_{r+1})\le E,
\tag{17}
$$

Then $L'=J(F)$ satisfies

$$
\operatorname{crit}(L')=V_0,\qquad
L'(V_0)=J(Z_{r+1}),\qquad
L'(J(Z_{r+1}))\le J(E).
\tag{18}
$$

This is directly derived from the application of identity. Therefore, $J(E)\le\Theta$ is another form of sealing certificate. It only requires three witnesses on the source side and an upper bound, without the requirement to follow the end embedding of the old group.

## Transition to Unmarked BMS Expansion

Let $d=h+r+1$. From [Repeated Initialization Lemma for a Column of Seeds](<short-terminal-initialization.md>), (5) plus any kind of seal is achieved.

$$
R_d=(0^d)(1^d)(1^d).
\tag{19}
$$

The subsequent [Balanced band expansion](<balanced-ribbon-bridge.md>) does not trigger marked completion, nor does it trigger ordinary native completion. If it is $d\ge3$

$$
\Theta\le j(\gamma_{N-1}),
$$

There is

$$
\boxed{D_2(R_d)<q(N).}
\tag{20}
$$

Here, $q(N)$ is the Laver table order parameter for the first occurrence of periodicity with $2^N$. The formula (20) still represents the boundary of the number of fixed index decreases; comparison with the specified BMS rapid growth value requires further proof and cannot be derived solely from $R_d>B_d$.

This interface allows the initialization phase to use marked completion, native completion, or other operations proven to preserve endpoints. The moment of stopping completion is determined by (1)—(3) and the sealing condition, and is not determined by some long-line step size. If it is possible to make $r$ a large function of the initialization parameters, it will be possible to add many more layers without having to manually verify only the tenth layer.

## What is missing from the current completion record to meet the condition?

Multiple rows generated by a single original completion often have the same owner. The multiple sources they represent are valid, but the same owner has only one image on $V_0$; however, (3) requires different $Z_{i+1}$. Therefore, simply renumbering these rows does not constitute a source interval block. It is also necessary to use the application item identity of replication or the actual factor words of the mark to construct $G_i$. This also explains why "large numbers of cloned rows" are not ready-made high-level certificates.

The existing preservation of endpoints involves moving parameters from 1 to 8; thereafter, the eight-segment linedness can be improved by one step to $E(8)$. The bounded diagnostic procedure (historical reference: `rebased_lining_fan_probe.py`) retains the owner identity and eight-segment linedness after the relocation, verifying this expansion and the subsequent three steps, resulting in 872 rows and the maximum step size of 5. Stopping occurs before reaching the 900 row of protection boundaries; the application of closure checks is limited to 200,000 candidate pairs. No new closed higher-order groups were found in the recorded 1,112 owners and 7,397 point images; the operation took approximately 1.1 seconds.

This diagnostic deliberately retains only the row equations guaranteed by the relocation theorem and the linedness; it discards the more detailed application structures used in constructing the eight-segment witness. Therefore, the results cannot deny the 'large parameter initiation' approach. The next step should be to retain these specific items and test whether they provide (3) and (14) or (17), rather than continuing to expand the same incomplete point-like searches.

## A finite set of fixed descent seeds

For (19), precise small examples are $D_2(R_1)=7$, $D_2(R_2)=22$. For $R_3$, at most 2,000 steps and 1,500 columns are checked at the 198 step, resulting in 1,503 columns, with no complete descent length calculated. This is a short check of the expansion formula, not a proof of growth rate. The descent of the target large number has never been brute-force expanded.

The conventions for 'application' and 'linedness' in the literature are referred to as [Qi, the 2th section](https://arxiv.org/html/2501.06733v5#S2). The conditions for insertion and both types of sealing conditions are direct consequences of these identities, and they are not the BMS lower bound that has already been given in the paper.
