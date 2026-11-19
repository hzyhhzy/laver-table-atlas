# Monotonic lower bound: Ordinary BMS preserves order embeddings IBLP below [0][1] · [中文版](IBLP-01-BMS-lower-bound.zh-CN.md)

*English reading edition, translated with machine assistance. The title links to the dated Chinese manuscript.*

> Collected reading edition. The three main papers state the results of this collection.
> This edition retains the local proofs, their hypotheses and any withdrawals. Progress reports describe the state of work at the time.
> The locations of omitted passages on preset inputs are recorded in SOURCE_MANIFEST.json.
> The main papers give the numerical derivations for the natural parameters produced by the proofs. This historical note carries no additional Lean certification.

2026-09-18. Paper proof, not formalized in Lean.

**2026-09-23 Update:** The assumption of "no completion in the entire section" used in this preliminary draft can be lifted. [Positive Interface Closed Lemma and Conditional Upper Bound](<../iblp-01-equality-20260923/IBLP-01-unconditional-BMS-lower-bound.md>) Proved the security of all the major steps in this work; followed by [No supplementary proof available for the entire standard section below.](<../iblp-01-equality-20260923/IBLP-01-no-completion-proof.md>). The original macro simulation and order-preserving embedding constructions are retained below; their conditional organization is a historical version, and the upper bounds are still not completed.

## 0. Conclusions and Boundaries

Put

$$
A=\mathrm{initial}[0][1],\qquad A_n=A[n],\qquad
B_h=(0^h)(1^h).
$$

Adopting the user-permitted assumptions:

> The strictly legal descendants of A do not trigger native completion or marked completion when continuing to expand.

The completion process for A generating Aₙ continues as originally programmed, and will never be terminated.

This proof

$$
\boxed{\mathcal B_{\mathrm{std}}\hookrightarrow \mathcal I_{<A}.}\tag{0.1}
$$

On the left are all finite standard forms of the ordinary BMS; on the right are strictly descendants that can be reached from the true expansion starting from A. The lexicographical order of the original IBLP comparison keys is used. If two standard forms have the same comparison key, they can be identified. The different source forms of this construction have strictly different target comparison keys.

This is **Order-preserving embeddings are not only descending simulations.**. Therefore, the commonly referred to lower bound direction holds true:

$$
\boxed{\mathrm{BMS limit}\ \le\ \mathrm{IBLP}[0][1].}
$$

To be precise, it has been proven that without assuming the right side is well-ordered, it contains a well-ordered subset of the BMS order type. If the entire right side is strictly well-ordered, then its order type must be at least a BMS limit.

**No proof has been given for the well-ordering of the entire right-hand section, nor for the existence of an upper bound or an equality in the opposite case.**

A more specific conclusion regarding the total number of rows is: for each h≥2,

$$
[0,B_h]_{\mathrm{BMS}}
\hookrightarrow
(A_h,A_{h+1})_{\mathrm{IBLP}},
\tag{0.2}
$$

The right-hand side can be selected as

$$
\boxed{T_h=A_{h+1}[2].}\tag{0.3}
$$

Here, [2] is the subscript of the original Python program. It executes a complete copy block, and then deletes the last line of the work.

## 1. definition and origin

Using the original file:

- The fixed original iblp.py (see SOURCE_MANIFEST.json)
- Historical BMS diagnostic script (not used as a premise for external proof)

The original document remains unchanged. The SHA-256 in the first version is:

    B8FFA27818BA6104DBB8FD110581C9898930EBF29E00B2C50065B0BBF7A137A3

Previous low-level work can be found in the progress document (historical reference: `IBLP-01-BMS-progress.zh-CN.md`). This document does not rely on the upper bound proof for "low-level equals three lines of BMS seeds" mentioned in that document, nor does it depend on the anchors 01, 011, 012 preset by the old converter.

This mathematical research paper only invokes the standard well-ordering properties of the ordinary BMS, as well as its original parent table replication formula. The zero rows are conventionally accepted; when h is fixed, all descendants can be filled to the h rows.

Let the i individual actions of IBLP be denoted as Rᵢ, with a step size of Lᵢ, and the final point being i; let the auxiliary point be 0. Define

$$
q_i=|R_i|-L_i-1,\qquad p_i=R_i[q_i],\qquad
P(i)=R_i[-2].
$$

qᵢ is the number of interfaces, pᵢ is the original replication point, and P is the zero-layer parent function. These are merely notations for reading the original data, without adding parameters to the symbols or changing the rules.

The original complete copy is marked as C. A complete fundamental sequence that is non-zero and not a successor.

$$
F(X,m)=\operatorname{cut}(C^m(X)).
$$

When no completion is provided, m≥1 has F(X,m)=X[m+1]; the index 0 is the last column deleted. The additional intermediate terms of [1] can be omitted in this text.

## The full index closure of 2. Aₙ

Definition of skeleton address

$$
a_0=0,\quad a_1=1,\quad a_2=2,\qquad
a_j=3+\frac{(j-3)(j-2)}2\quad(j\ge3).
$$

that is

$$
0,1,2,3,4,6,9,13,18,24,\ldots
$$

Aₙ(n≥2) consists of the first three lines and the stages t=2,…,n. The first three lines are

$$
(0,1),L=1;\quad (0,1,2),L=1;\quad (0,1,2,3),L=2.
$$

Phase t has t rows, as defined

$$
b^{(t)}_0=a_{t+1},\qquad
b^{(t)}_k=a_{t+2}+k-1\quad(1\le k\le t).
$$

The kth line is located at address $b^{(t)}_k$, and its line set is

$$
R_{b^{(t)}_k}
=\{a_0,\ldots,a_k,a_{k+1}\}
 \cup\{b^{(t)}_0,\ldots,b^{(t)}_k\},
\tag{2.1}
$$

Arranged in ascending order. Step size:

$$
L_{b^{(t)}_k}=
\begin{cases}
k+2,&k<t,\\
t+1,&k=t.
\end{cases}\tag{2.2}
$$

When k=t, $a_{t+1}=b^{(t)}_0$, this point is counted only once. Therefore, the number of interfaces for these rows is exactly k. Total number of body rows

$$
s_n=2+\frac{n(n+1)}2.
$$

And Aₙ is a true prefix of Aₙ₊₁.

### 2.1 is derived from the original completion procedure to obtain the formula.

The original behavior of A is (2,3,4)), with a step size of 1. First, perform n−1 complete original copies, delete the working template, resulting in the first three lines and n−1 lines that are not yet completed.

$$
(0,1,r-1,r),\ L=2,\qquad r=4,\ldots,n+2.
$$

The rows that need to be processed do not have an asterisk, so their marked completion has no effect.

After processing the tth stage, the address movement caused by the previous insertion row, the row to be processed becomes

$$
(0,1,a_{t+1},a_{t+2}),\quad L=2.
$$

The original completion follows the chain along P, from aₜ to a₂, and stops upon encountering a₁=1. Therefore, t−1 points and t−1 new rows are added. The original "mid" branch is applicable, as the original length is 4=2L. The last row is...

$$
\{a_0,\ldots,a_{t+1}\}
\cup\{b^{(t)}_1,\ldots,b^{(t)}_t\},\quad L=t+1.
$$

The program first deletes the last new point to obtain the previous row; then, it deletes one end point and one specified intermediate point each time, reducing the step size by 1. Substituting each item gives us (2.1)–(2.2)).

Inserting lines will generate asterisks, but the scanning pointer directly skips them; the next raw line that is to be processed still has no asterisks. Therefore, the above derivation indeed covers the two completion entries of the original program, rather than closing another set of Aₙ after completion.

## 3. is a zero-level invariant that is sufficient to ensure that the replication is defined.

The following conditions are denoted as G₀:

1. P is a planar parent forest arranged by address: each subtree is continuous in the address sequence.
2. In each row where R appears, each point is either an ancestor of i under P, or i itself, including the auxiliary root 0.

Given (2.1), for each Aₙ, it satisfies G₀:

- $P(a_j)=a_{j-1}$; 
- The $b_0,b_1,\ldots,b_t$ at each stage is a continuous P chain.
- All the a points and b points in each row are on the same P ancestor chain of that row.
- The new phase is attached to the next sub-branch of the skeleton, maintaining the planar forest.

Consider the active data with a certain last line X

$$
\underbrace{u_0,\ldots,u_k}_{\text{first k+1 points}},
\qquad
\underbrace{v_0,\ldots,v_k}_{\text{last k+1 points}},
$$

Among them, k≥1, both strings are continuous P chains, with $u_k<v_0$ at the end point $v_k=N$. Other points are allowed in between; the number of interfaces is exactly k.

The tangent point is $c=u_k$, and the span is $d=N-c$. The original f is exactly

$$
f(x)=
\begin{cases}
x,&x<u_0,\\
v_j,&x=u_j,\ 0\le j<k,\\
x+d,&x\ge c.
\end{cases}\tag{3.1}
$$

### All points that are copied from 3.1 are within the domain of f.

c is an ancestor of the endpoint P. By the plane property, each point in the set c, …, N is a descendant of the point c under the point P. If the point in the copied row is less than c, it must be an P ancestor of c.

And $u_0,\ldots,u_k=c$ is a continuous P chain. Therefore, such a point is either less than u₀, or it is exactly equal to some uⱼ. There are no other points that would return None for f.

f is strictly increasing on the domain, so there are no merging points; the length of the line, the step size, and the number of interfaces remain unchanged. This also rules out the branch of the original program in this construction where "the first copy undefined is reduced to cut".

### 3.2 G₀ remains intact under this complete replication

The new seam is located at the old endpoint N, and its parent is

$$
f(P(c))=f(u_{k-1})=v_{k-1}=P(N).
$$

The parent of j+d (j>c) is P(j)+d, because of P(j)≥c. Therefore, the new forest is formed by grafting the subtree starting from c to the position of the old end point, maintaining planarity.

In-line citations:

- References that are less than u₀ remain ancestors of the new seams.
- uⱼ is moved to vⱼ, and still remains an ancestor of the new seams.
- At least c shall be copied along with its corresponding ancestor chains.

Thus, each new row point remains a P ancestor. The G₀ remains unchanged. The deletion of the tail also remains G₀. This is a proof for all the copied rows, not just those selected for encoding.

## 4. is represented using ancestral bands for BMS columns

Fix the h. A "band" is a continuous P chain.

$$
V_j=(v_{j,0},v_{j,1},\ldots,v_{j,h}).
$$

Here, the point marked with 0 is the starting point of the belt, while the points marked with 1, …, h are used for the 0, …, h−1 rows of the BMS. There is a strict separation required between the belts:

$$
v_{j,h}<v_{j+1,0}.
$$

There can be IBLP lines that do not belong to the belt, and these should not be deleted or considered as non-existent.

Let the parent table of the ordinary BMS matrix M be Qᵣ(j), with the parent deletion denoted as −1. The P equipped with these tags is called a representation certificate of M, which requires:

- P satisfies G₀, and its last point is the last point of the last strip.
- If Qₖ₋₁(j)=c≥0, then the number of interfaces in the row where vⱼ,ₖ is located is exactly k, and

$$
R_{v_{j,k}}[:k+1]=V_c[:k+1],\qquad
R_{v_{j,k}}[L_{v_{j,k}}:]=V_j[:k+1].
\tag{4.1}
$$

- If Qₖ₋₁(j)=−1, then two types of "zero coordinates" are allowed:
  - The number of interfaces on this line is less than k;
  - The number of interfaces is equal to k. The last k+1 points remain as k+1 points before Vⱼ, but the tangent points are strictly located before the starting point of the first band.

The second type allows inheritance of existing complex contexts. It does not mean that that IBLP line represents a zero-order number, but rather that it does not point to the k−1 row within the represented BMS column domain as a parent.

This relaxation is very important: this construction takes actual Aₙ as input, without the requirement for a new all-zero prefix to emerge out of nowhere.

## 5. One-step precise macro simulation of BMS

Let the last column of the BMS be x, and the highest non-zero behaviors be r, k=r+1, the tangent points be c=Qᵣ(x). k≥1. This is why the row numbers of the BMS are staggered by one interface position.

### 5.1 preparation

Use the real IBLP [0], truncate P to $v_{x,k}$. According to the certificate (4.1), the cut-off point of the current last line is $v_{c,k}$, and the two strings of interfaces are respectively

$$
V_c[:k+1],\qquad V_x[:k+1].
$$

Let

$$
d=v_{x,k}-v_{c,k}>0.
$$

The 3 section guarantees a complete copy of the defined elements, and the G₀ remains unchanged.

### 5.2 replication and new bands

To simulate the positive index m of BMS, perform one original IBLP [m+1], that is, after m complete copies, delete the last line of work. Then continue with [0], stopping at the last complete output.

The old version with $V_0,\ldots,V_{x-1}$ is retained. The bth copy (1≤b≤m) includes the old columns c, …, x−1. The new version formula is:

Copy of the tangent column:

$$
v^{(b)}_{c,t}=
\begin{cases}
v_{x,t}+(b-1)d,&t<k,\\
v_{c,t}+bd,&t\ge k.
\end{cases}\tag{5.1}
$$

The remaining columns j>c:

$$
v^{(b)}_{j,t}=v_{j,t}+bd.\tag{5.2}
$$

The final truncation position is $v_{x-1,h}+md$. It occurs before the final working template, so these truncations are valid [0] operations.

### 5.3 is consistent with the original BMS parent table formula item by item.

Parent of the bth first column in BMS:

- s<r: Inherits the parent row of s from the last column of the previous work.
- s≥r: The s row inherits the old tangent point c.

Non-heading copied columns are handled by maintaining them as "parent before c", otherwise they are moved to the corresponding copies.

5.1) exactly corresponds to this partition:

- The ports of t<k originate from the old last column, indicating coordinates that are lower than r;
- The ports of t≥k originate from old tangent points, indicating coordinates that are r or higher.

For non-first columns, when the parent band is before c, the entire band is located in the fixed area of f; when the parent band is at c, it is transported according to (5.1) mixed transport; when the parent band is after c, it is translated according to (5.2) translation. Therefore, the row start interface and the row end interface exactly become the two bands required by the new certificate.

The zero coordinates also remain unchanged: rows with an interface number less than k are still less than k; the external tangent points are strictly before the first band, always located within the fixed region of f. This indicates that inheriting the external context will not incorrectly result in a domain-specific BMS parent.

Each new section remains a continuous P chain: The seams are connected by the parent formula from the 3.2 section, and the rest is copied as a whole.

This proof shows that the output is a new certificate of the original BMS M[m]. The assumption of no completion is only used to confirm that the final result of the original Python positive index operation is the same as the original copied result. The completion function was not closed, nor was the actual output modified in any way.

### 5.4 indicator 0, successor, and empty formula

When the indicator 0 or the last column of the BMS is all zeros, the target can be truncated to the second-to-last column with a point. If the source is deleted, then it is truncated to the preselected protection prefix F. All operations remain as the actual IBLP [0].

Please choose F as the first true prefix with a terminal point; a clear choice will be given later in the text. The entire macro simulation includes at least one strict target reduction.

## The target macro steps of 6. indeed decrease according to the original comparison function.

It cannot be simply stated as "the expander was called, so it must be smaller"; we check this directly here.

Preparation and end truncation are true prefixes, therefore they strictly decrease in size. The positive replication that first changes is the row with the old endpoint N. The comparison key for the old row is

$$
(N,v_{k-1},\ldots,v_0,u_0).
$$

Copy the cutpoint row for the new seam. Let the number of interfaces on this row be q.

- If q=k, its parent points to an earlier containment or protection zone, so the initial point of the row is strictly less than u₀ and remains unchanged.
The tail is moved to the same v line, so the comparison keys are strictly reduced in the last item.
- If q<k, the new key length is q+2≤k+1, and all points are on the P ancestors of N.
The previous k+1 points of the old key are precisely the continuous P chains of N. Therefore, the new key is either strictly smaller than something else, or it is a true prefix of the old key.

Both scenarios involve a strict decrease. The subsequent replication does not alter this initial difference. This assertion only indicates that the steps used in this construction decrease, without presupposing that the IBLP is well-ordered throughout or that all original inputs possess certain properties.

## 7. from A Create any real basic item. h Row seeds

Let h≥2, n=h+1. Take the last stage of Aₙ, and denote it as

$$
V=(b_0,\ldots,b_h),\qquad
b_0=a_{n+1},\quad b_k=a_{n+2}+k-1.
$$

This is the ancestor band before the last line of this stage. The endpoint of Aₙ is $s_n=b_{h+1}$, and the cut points are aₙ. Let

$$
d=s_n-a_n.
$$

Perform the original [2] on Aₙ to obtain $T_h=A_n[2]$. It contains two lines.

$$
V,\qquad W=V+d.
\tag{7.1}
$$

The end point is exactly $b_h+d$, that is, the end point of W, so no further rows need to be added.

### The first line marked with 7.1 represents the zero column.

The V has k port interfaces, with the number of them being k. However, its tangent points aₖ are strictly less than b₀. Therefore, it satisfies the condition of "zero coordinates for external parents".

### The second line with 7.2 represents the entire 1 sequence.

Because k≤h<n, the copy mapping at the end of the original Aₙ satisfies

$$
f(a_k)=b_k,\qquad f(b_k)=b_k+d.
$$

Therefore, the first interface of the kth port of W becomes V[:k+1], and the last interface becomes W[:k+1]. The number of interfaces remains unchanged at k.

Therefore, (Tₕ;V,W) is

$$
B_h=(0^h)(1^h)
$$

The representation certificate. All h for the same formula, not relying on individual trial guesses.

### 7.3 are placed in intervals that are separated from each other

The protective prefix Fₕ is chosen as the prefix for the cutoff b₁. This is because h≥2 is strictly shorter than the endpoint bₕ of V.

Also, since b₁ is the first line of stage n.

$$
A_h\ \text{is a proper prefix of}\ F_h.
$$

On the other hand, this replication of Aₙ also satisfies the invariant of the 3 section. The number of tangent line interfaces is 1<n. Therefore, the comparison argument in the 6 section yields $T_h<A_n=A_{h+1}$.

Therefore, all simulation results are located within

$$
[F_h,T_h]\subset(A_h,A_{h+1}).\tag{7.2}
$$

Even when the source value is an empty formula, we only reduce it to Fₕ, without crossing this interval.

## 8. is extracted from the descent simulation to obtain a truly order-preserving embedding.

This step cannot be omitted: General descent simulations themselves do not guarantee that the target contains the same ordinal type. The established prefix compatibility is also used below.

### 8.1 simulates precise prefix compatibility

For the same certified source M, simulate the indices 0, 1, 2, … respectively, and the target results are denoted as T₀, T₁, T₂, ….

From (5.1)–(5.2):

- When M[m] is a true prefix of M[m+1], then Tₘ is also a true prefix of Tₘ₊₁.
- The result obtained by traversing from the larger output to the smaller source prefix corresponding to the end point is exactly the smaller output Tₘ.
- Any subsequent decline from the source must maintain a certain source prefix, and its target macro step must remain corresponding to the target prefix.

The data in the rows pointing to the left does not change by cutting off the right side. Additional uncoded rows are also retained in the target prefix, and the act of "deleting them" is not implicitly considered as an allowed step.

For empty source prefixes, it corresponds to Fₕ; for non-empty source prefixes, it corresponds to the end point of their last band.

### 8.2 Relative Interval Lemma

Given a source s, a target t, a prefix u for the source, and a corresponding target prefix v, it is possible to achieve order-preserving embedding.

$$
(u,s]\hookrightarrow(v,t],
$$

Translate s to t.

Proof that for a well-ordered BMS source s, an infinite induction is performed without making a well-ordering assumption for the entire domain of IBLP.

If u=s, there is nothing to do. Otherwise, u is a prefix of s[0]. For the limit s, its required interval is decomposed into

$$
(u,s[0]]\quad\text{and}\quad
(s[m-1],s[m]]\ (m\ge1),
$$

Finally, add the endpoints s. The empty intervals are omitted. The BMS fundamental sequences are tail-end and prefix-based, so these intervals do not overlap with each other in order and are exhaustive (u,s)).

For the first interval, use the inductive hypothesis for certificates s[0], T₀, and retain the boundaries u, v. For the other intervals, s[m−1] are prefix words of s[m], and the 8.1 section guarantees that the corresponding target boundaries are precisely Tₘ₋₁. Again, use the inductive hypothesis to embed them in (Tₘ₋₁, Tₘ].

The various target intervals are also strictly separated in order. Finally, s is mapped to t, and each Tₘ<t has been proven in section 6. The case of successors only requires adding an endpoint to the first interval. This completes the induction.

This construction uses non-overlapping relative intervals to handle multiple expansions of the same source formula, without mistakenly treating a path expansion tree with duplicate nodes as the source ordinal itself.

### 8.3 is a performable canonical method of extraction.

Given a fixed source root Bₕ and a certain standard target source formula M≤Bₕ:

1. If M is the current source prefix, stop at its corresponding band endpoint.
2. Otherwise, select the smallest m such that M≤ is at the current source [m], execute its target macro steps, and continue.
3. The empty source is embedded into Fₕ.

Each step is a strict decrease, and it is not less than M. Due to the well-ordering property of the ordinary BMS, this process terminates finitely for every M. The existence of the required m is guaranteed by the finiteness of the fundamental sequence. This provides a definite implementation of the interval construction from the previous section, but it does not guarantee that the computational complexity is small.

From section 7 and the interval lemma, it is obtained that (0.2).

## 9. combines all finite row numbers

Ordinary BMS has

$$
B_h=B_{h+1}[1]<B_{h+1},\qquad
\beta_{\mathrm{BMS}}=\sup_h |B_h|.
$$

The standard BMS is divided into:

- The parts that do not exceed B₂;
- (B₂,B₃]; 
- (B₃,B₄]; 
- And so on.

In the h section, the embedding of Bₕ from the 8 section is used, falling into (Aₕ,Aₕ₊₁). These target intervals are strictly arranged in order, all of which are strictly less than A. The proof for the order-preserving embedding of all finite standard BMSs is completed with (0.1).

**The conclusion does not require these finite seeds to be represented consistently across different h.** solves this compatibility issue by concatenating the true target intervals that are separated from each other.

## 10. Original code verification and evidence level

Verification procedure: check_ribbon_embedding.py (Historical reference: `check_ribbon_embedding.py`).

The program directly calls the original iblp.py and bms.py functions, and does not close any completion functions. It checks the actual output for interface conditions, zero coordinates, G₀, strict target comparison decrements, and compatibility of brother terms prefixes.

First round h=2,…,8, completed 2,093 macro steps, 3 width stops; Second round expanded to h=2,…,12:

- 11 full row seed instances;
- 7,139 are completed BMS steps;
- 4,455 are the expansions of the positive ordinal numbers of the IBLP.
- 136,468 are sub-equivalent to [0] truncation.
- 7,150 complete certificate verification;
- 189 prefix compatibility check for secondary brother terms;
- 57 is the stop at the next width, not counted as a successful macrostep.
- 736 degree of source width strategy intervention.

It will take approximately 22 seconds to complete. Additionally, for the h=2,…,6 different source-style calculations of the 182 distinct sources, a total of 177 consecutive target strict comparisons were performed in source order, all of which passed. This took approximately 0.7 seconds.

Finally, a check was conducted on the entire body of closed formulas for the original A[n]. The formulas n=2, …, 35 are exactly the same as 34. The procedure is denoted as check_seed_formula.py (historical reference: `check_seed_formula.py`). The specification image check was extended to h=2, …, 10: completing the image of 257 different source formulas, 248 adjacent strict comparisons, and checking the left and right carrying intervals of 9 seeds; additionally, 1 source formulas reached the upper limit of their target width, which is clearly marked as unknown. This stop is not a mathematical counterexample, nor is it included in the completed images.

The test includes a global budget of 25 seconds, a maximum width limit of 1 and 800 for the target bodies, the number of source steps, and a maximum number of indicators. All currently running calculations have been terminated, with no background long calculations or unbounded subscript counters.

Tests can only detect errors. Any h, any index, and any conclusions from finite subsequent expansions are derived from the closed-form and inductive proofs in sections 2–9, and not from the "measures in the 12 row".

## 11. This round has nothing proven.

- No proof has been given that every valid expression below A can be embedded reversibly into a normal BMS.
- No proof has been given for the entire original expansion relationship of A being a well-founded set.
- No proof for a complete well-ordering of IBLP.
- This argument uses the stated absence of completion as an input.
- The original notation, its expander and the notation repository were left unchanged. No changes were committed or pushed.

This round of completion is in line with the user's request: the complete standard domain embedding of the ordinary BMS into A.
