# The local closure of the native full gap: a version that exempts the one-step length · [中文版](full-gap-native-local-closure.zh-CN.md)

*English reading edition, translated with machine assistance. The title links to the dated Chinese manuscript.*

> Collected reading edition. The three main papers state the results of this collection.
> This edition retains the local proofs, their hypotheses and any withdrawals. Progress reports describe the state of work at the time.
> The locations of omitted passages on preset inputs are recorded in SOURCE_MANIFEST.json.
> The main papers give the numerical derivations for the natural parameters produced by the proofs. This historical note carries no additional Lean certification.

2026-10-14. This paper only proves a clear local completion lemma, and does not claim that the new system has been fully defined, that the order type is greater than BMS, or that the original E quantitative recursion can be directly transferred.

The modification is as follows: In the regular BLP, the medium and short rows have a step length of $L\ge2$. The native node no longer extracts packets along the ancestor chain, but instead takes the entire integer source gap. The rows with $L=1$ are still not considered native. The current $+1$ guard for replication, mark filtering, and compTo, as well as the freeze of old marks from left to right, remain unchanged.

## The precise definition of 1. and the indispensable boundary of $L=1$

The $r$ behavior is core $A_r$, the step size is $L_r$, the final term is $r$, and an implicit endpoint is $r+1$. It adopts a regular row type, where the complete length and step size satisfy Qi's Definition 2.6. Written as

$$
p(r)=A_r[-L_r-1],\qquad e(r)=A_r[-L_r].
$$

An row is called active if $|A_r|\le2L_r$ and $L_r\ge2$. For active rows...

$$
U_r=(p(r)+1,\ldots,e(r)-1).
\tag{1}
$$

If the package is empty, no action is taken; otherwise, the standard native formula for the same owner is used: between the old point $r$ and the old point $r+1$, a pair of $J_r$ is inserted (the image of all named points in 1); the new row inherits the same owner, and the step length is increased according to the original medium/short formula, and direct marks are added. Other rows are not treated as native.)

Definition of strong saturation condition

$$
\mathrm{GapSat}(P)\quad\Longleftrightarrow\quad
e(r)=p(r)+1\quad\text{for every active row }r.
\tag{2}
$$

This condition does not require that the two-point one-step core $(a,r)$ satisfy $r=a+1$. It is very important to retain this exemption: If it is also completed for non-spacetime gaps, the first steps may produce short rows with a complete length 4 and a step length 2, which no longer belong to the ordinary row type. This is not an extension covered by existing automatic proofs for ordinary closures.

GapSat implies the old Sat: the active row has $A_{e(r)}[-2]<e(r)=p(r)+1$, hence $A_{e(r)}[-2]\le p(r)$; the eligible row in one step has its predecessor exactly $p(r)$. However, the reverse does not hold.

## 2. Local semantics unrelated to ancestor chain selection

The following conclusions use the explicit formulas for the ordinary native and the paired compTo, without using the property that (1) is a ancestral chain.

### All rows with 2.1 as the native in the first column

Let the old row be active, $p=p(r),e=e(r)$, and the source package be ordered as $u_1<\cdots<u_q$. Set $u_0=p,u_{q+1}=e$. The actual row is given as

$$
J_r(\xi_p)=\xi_r,\qquad J_r(\xi_e)=\xi_{r+1}.
$$

Therefore, all $J_r(\xi_{u_h})$ are strictly contained within the old $(\xi_r,\xi_{r+1})$. Each intermediate row of the ordinary native exactly pairs the retained source points with these images; all are implemented by the original owner, with the old end points remaining unchanged. The formula for p/e is

$$
p'(r+h)=u_h,\qquad e'(r+h)=u_{h+1}\qquad(0\le h\le q).
\tag{3}
$$

The active rows satisfy $e<r$, so the new target inserted after $r$ will not renumber the aforementioned source addresses. For packages (1), $u_{h+1}=u_h+1$), the entire native family has already been GapSat. The original medium/short formulas are still given for ordinary rows; prohibited step sizes like 2 short rows will not be created, because the minimum short step size for initial active rows is 3, and the first new short row with a medium step size 2 is already a step size of 3.

### 2.2 The critical point of a non-empty native is strictly below the source threshold.

If the core has a length of $2L$, its $p$ is the $L$th item, and the core has a length of $L\ge2$. If the core has a length of $2L-1$, its $p$ is the $L-1$th item, and the ordinary row type is given as $L\ge3$. Therefore, in both cases, the core has a length of $p>\min A_r$.

$$
\operatorname{crit}(J_r)<\xi_p.
\tag{4}
$$

This replaces the same critical point inequality for "non-empty packets at the bottom" in the old argument, without requiring the packet to be part of a ancestral chain. If the threshold for the bottom-level factor $K$ is $\delta$, then the upper non-empty term $W=P\circ K$ exists.
$\operatorname{crit}(W)\le\operatorname{crit}(K)<\xi_\delta$.
The natural truncated historical boundary $\Delta_0>\xi_y=W(\xi_\delta)$ ensures that the mark owner also has the same low critical point. Therefore, the non-empty completion source $\delta$ cannot equal the smallest item of the owner.

### 2.3 pairs compTo to not contaminate the current source gap

Once the complete parallel package of a certain compTo has been verified, the original natural truncation values are proven to hold for all new edges. The general pair interval lemma is maintained for all old edges, critical points, and p/e. Its new sources are strictly below the current $p(r)$, and its new targets are at or above the current $e(r)$. Therefore, no core entries will be added to the $(p(r),e(r))$.

For long lines, the last sentence should exclude the earliest critical-image mark: The pairing source of this mark is exactly the minimal term, which has been excluded from performing non-empty completion by (4) and historical truncation. This step cannot be skipped just by checking the newly added pairs. For the conditions on pure pairing positions and the proofs derived from reading values to geometry, see [General Interval Lemma](<../../natural-mark-lemmas/marked_completion_interval_lemma.en.md>).

## A complete marked package after one legal short replication of 3.

**Theorem.** Parent mode $P$ It has a true normal implementation, proper accurate marks, natural truncation semantics, and GapSat. Using the original correct paper guard, a short copy is performed at **There is a definition.**. Then, a full gap scan is carried out from left to right, skipping the new native family, and freezing the entry marks of each old line. All local operations of this scan are legal and limited. The output still retains a true normal natural truncation implementation and GapSat. The scan after copying does not change the global cap or the final owner obtained during the copying stage.

This theorem does not guarantee that the copies of each parent pattern are defined.

### 3.1 is the old prefix for rest and replication factor positioning.

Short copies retain the 'cut' prefix of the parent. The prefixes 'GapSat' and empty entry records make each old line not native, and there are no marked records that can be read as non-empty. Therefore, it remains completely inactive during this scan.

The original full/low/high actually uses correct guard functions and accurate p chains for word recognition and dependency positioning. It also relies on the static prefix and continuous replication areas, without depending on the selection of ancestral chain packages. Therefore, whenever a mark is actually read from a non-empty native record, all of its non-terminal factors come from this continuous replication area. The underlying factors of cross-border low/high words remain in the static prefix, with no records, and non-empty calls cannot occur.

Let the parent source interval be $[a,b]$. On the row addresses of this interval, the replication mapping is a uniform translation of $\varphi(x)=x+c$; entries below $a$ can indeed have jumps, but this does not affect the following internal edges.

### The 3.2 internal active factor precisely replicates the entire lower-level package.

Consider an internal edge $v\to w$ that leads to an entrance word with a non-empty record, namely $p(v)=w$. They are all in the replication area, so $w\ge a$. If $v$ is active, the parent GapSat assigns $e(v)=w+1\le v\le b$, with both endpoints in a continuous translation area. Therefore, the entrance remains after replication.

$$
e_{\rm entry}(v)=p_{\rm entry}(v)+1.
\tag{5}
$$

Let the current base line position of the old line $w$ during scanning be $T_w$, and insert $q_w$ new targets into it. The position of the original subsequent line will then become

$$
T_w+q_w+1.
$$

There was originally no other old row between them, so when dealing with higher old rows later on, no additional native points will be inserted into this gap. The verified compTo maintains the p/e with $v$, and does not contaminate the source gap. Therefore, when $v$ performs the native operation, its complete source gap **It is exactly**

$$
T_w+1,\ldots,T_w+q_w.
\tag{6}
$$

Therefore, it is $q_v=q_w$, rather than just $q_v\le q_w$. In particular, the replication mapping of the low regions may cause the underlying factors to produce larger initial packages, but it cannot introduce additional old sources into these internal upper factors; the internal (5) has ruled out this possibility.

### 3.3 is currently excluded from the $+1$ guard, excluding non-active internal factors.

Let the lower layer be non-empty. The point $T_w+1$ is a new point in this round, and it does not belong to any old core at any entrance. If the upper layer is a long row, it does not act as a native point. The previous legal compTo cannot add this point to its $(p,e)$ source gap, as described in §2.3. Therefore, the current $+1$ guard fails.

If the upper layer is a one-step eligible row, its core contains only $(p,v)$, with no proper marks. The row's address is located after the entire lower layer, and it is not a new point $T_w+1$. Therefore, the same guard fails. If it is a one-step long row, then it already falls under the same scenario as the previous long rows.

Therefore, once the guard allows a multi-factor mark to read non-empty packets, all internal upper factors are active, and the same complete packet is transmitted layer by layer through (6). The direct mark has no internal factors, so this exclusion step is not required. The ordinary ladder formula is p, and the formula (3) provides new traces. The corresponding new rows at all layers continue to use the original factor owners.

### 3.4 has read all new edges in the historical nature, without any recursive calls.

Let the current mark's underlying owner be $K$, its old tight posterior naming point be $\Theta$, and its old word be $W=P\circ K$. The historical certificates saved at the scan entrance are

$$
F\equiv_{\Delta_0}W,\qquad \Delta_0=P(\Theta).
$$

Each new image of the native layer is $K(\xi_{u_h})<\Theta$. Based on the established correspondence, the upper target is precisely

$$
W(\xi_{u_h})=P(K(\xi_{u_h}))<\Delta_0.
$$

Therefore, the historical membership truncation indeed reads out all the newly added edges marked with $F$; §2.2 excludes the degenerate critical sources, and the ordinary interval lemma then maintains all the old edges and their complete geometry. The actual nature of the new parallel marks does not exceed the same $\Delta_0$, thus the natural semantics is preserved.

The above argument is inductive by the old owner's line numbers and the finite order in which the old marks are frozen: The current event only uses the legitimacy of earlier compTo, and the current compTo is used for subsequent events after being verified by reading values and interval lemmas. There is no assumption that the current output is legal before inferring its completeness.

### 3.5 Scan completion and output saturation

After processing an old line, if it is long or $L=1$, there is no condition to be completed; otherwise, its entire native gap either becomes empty and satisfies (2), or the entire family is transformed into GapSat by (3). Subsequent operations do not modify the earlier prefixes, hence GapSat is output.

Each scan of the old lines and their frozen marks has a limited number of items; the interval between integer sources is finite, and the new family is skipped, so the scan ends after a limited number of times. The native and compTo retain their original owners and old implicit caps, so the entire scan retains the final owner and global cap obtained from the copy of the entrance. The theorem is proven.

## 4. Original auxiliary E Does not automatically maintain new invariants

The auxiliary threshold copy mapping of E is

$$
\psi(x)=x\ (x<a),\qquad \psi(x)=x+d\ (x\ge a).
$$

If a certain active source line originally had $p=a-1,e=a$, then the original GapSat holds true. However, after duplication, it becomes $\psi(e)-\psi(p)=d+1$ and is no longer adjacent. Therefore, the rule that "no scanning is performed after E" cannot be directly applied to the old Sat proof to obtain GapSat.

A possible fix is to perform a finite scan of the text after each auxiliary replication: the auxiliary step-length row exemption native, and since there is already a prefix "GapSat" for quiescence, the proof package of this theorem is still useful. However, whether the complete E parameter implementation, the prefix family, and the quantitative recursion are retained in the original formula requires separate writing; this paper does not announce that this has been completed.

What has been proven here is merely a locally modified version with precise semantics: **Exempt from the full-length line of steps for native, allowing a valid short replication of the parent item for GapSat with a complete scan closure.** It completes a source address that may not be accurately matched by a primitive ancestor chain. But is it sufficient to uniformly repair BMS/ARD encoding, and truly enhance the sequential type? It remains an independent issue.

<a id="proof-section-13"></a>

## The eleven lines of GapSat seeds within the same $q(5)$ window as 5.

This initialization can be verified line by line directly. It is not necessary to apply the general scanning theorem to parent terms that do not satisfy GapSat. Starting from [Nine ordinary seeds $S$](<same-owner-L3-sat-closure.md>), The first eight lines already meet the requirements of this type of GapSat. In the $p=3,e=6$ line of 9, The full gap is exactly $(4,5)$. There were no empty records in this scan before. Therefore, the old marks will not be replenished again.

Define actual critical points

$$
\chi=H(\mu),\qquad \rho=H(\theta_5).
$$

Taking the image of $\kappa_3<\mu<\theta_5<\beta$ by $H$-like.

$$
\eta=H(\kappa_3)<\chi<\rho<H(\beta)=\theta_6.
\tag{7}
$$

So, we just need to insert $\chi,\rho$ between the old $\eta,\theta_6$, and the global cap remains unchanged. The new point representation is

$$
(\kappa_0,\kappa_1,\kappa_2,\kappa_3,\mu,\theta_5,
\beta,\alpha,\zeta,\eta,\chi,\rho,\theta_6),
\qquad 0,\ldots,12.
\tag{8}
$$

The first eight lines remain unchanged. The new last three lines are as follows:

| Research manuscript | core | Step size | marks | owner |
| ---: | --- | ---: | --- | --- |
| 9 | $(0,1,2,3,4,6,7,8,9)$ | 5 | $\{7,8\}$ | $H$ |
| 10 | $(0,1,2,3,4,5,6,7,8,9,10)$ | 6 | $\{7,8,9\}$ | $H$ |
| 11 | $(0,1,2,3,4,5,6,7,8,9,10,11)$ | 6 | $\{7,8,9,10\}$ | $H$ |

Their full lengths are 10, 12, 13, with step sizes of 5, 6, 6. All are ordinary row types. In the 9 row, $H$ is used for the five sides of $\kappa_0,\kappa_1,\kappa_2,\kappa_3,\mu$; in the 10 row, $H(\theta_5)=\rho$ is used again; and in the 11 row, $H(\beta)=\theta_6$ is used once more. Therefore, all new rows and their implied endpoints are realized by the same actual $H$.

The p/e in the last three lines are respectively $(3,4),(4,5),(5,6)$, which satisfy GapSat. All non-terminal words of the marks are still a globally identical $H$, corresponding to traces.

$$
(7,1),\quad(8,2),\quad(9,3),\quad(10,4).
$$

Therefore, the terms 'proper', 'accurate trace', and 'natural truncation' all hold true; the old certificates for the first eight lines are also retained. These eleven lines are marked as $G$, with the first three points still given by $j$, 1-linedness, and the final 'cap' remains $\theta_6<\kappa_4=\gamma_{q(5)-1}$.

From $G$, perform a valid short copy and add this scan. In cases where replication is not possible, perform a cut. Each step has a constant cap or a decrease. At the end of a non-cut, an application occurs once. Thus, the same finite table potential function for [Chapter 5 of the Nine-Line Counting Certificate](<same-owner-L3-sat-closure.md#proof-section-5>) is given as

$$
\#\mathrm{cut}<q(5),\qquad
\#\text{basic operation}<2^{q(5)}.
\tag{9}
$$

Here, only cuts and one-time replication with scanning are counted, and unfixed E branches are not automatically included. The initial scanning from $S$ to $G$ is also not considered as a reduction step. These bounds have not yet provided a structured upper bound for the calculation of $G$.

Finally, there is a distinction between two types of numbering: if $\kappa_d=\gamma_{F(d)}$, the general periodic interface is

$$
j(\gamma_{N-1})=\gamma_{q(N)-1},\qquad
F(d+1)=q(F(d)+1)-1.
\tag{10}
$$

Not generally $q(N)=F(N-1)+1$. The special equation in this paper, $q(5)$, only uses $F(3)=4$, that is, $\gamma_4=\kappa_3$; therefore
$j(\gamma_4)=\kappa_4=\gamma_{q(5)-1}$.
If we replace the cap with $\kappa_{d+1}$ in general dense roots, the correct window should be $q(F(d)+1)$, and it cannot be directly called $q(d+2)$ based on the number of rows.
