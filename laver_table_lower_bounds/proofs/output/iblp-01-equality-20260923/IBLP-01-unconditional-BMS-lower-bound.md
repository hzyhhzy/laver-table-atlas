# Remove the assumption of complete completion: All ordinary BMS embeddings into IBLP are of the form 01 · [中文版](IBLP-01-unconditional-BMS-lower-bound.reading.zh-CN.md)

*English reading edition, translated with machine assistance. The title links to the dated Chinese manuscript.*

> Collected reading edition. The three main papers state the results of this collection.
> This edition retains the local proofs, their hypotheses and any withdrawals. Progress reports describe the state of work at the time.
> The locations of omitted passages on preset inputs are recorded in SOURCE_MANIFEST.json.
> The main papers give the numerical derivations for the natural parameters produced by the proofs. This historical note carries no additional Lean certification.

2026-09-23, further research. Paper proof, not formalized in Lean.

**Subsequent updates:** After this article is completed, [Enhanced closure proof for the class D](<IBLP-01-no-completion-proof.md>) further proves that the entire 01 strictly follows the standard lower section without any supplementation. This lower bound does not depend on this step. Subsequently, [Interface bridge coverage proof](<IBLP-01-BMS-upper-bound.md>) Complete the upper bound in the reverse direction and obtain an equal sign. The list of statements "This article does not prove" only describes the scope of the lower bound argument presented in this article.

## The new conclusions of 0. and the remaining unsolved goals

Let's denote the mathematical research manuscript as follows:

$$
A=I[0][1],\qquad A_n=A[n],\qquad B_h=(0^h)(1^h).
$$

This proof:

$$
\boxed{\mathcal B_{\rm std}\hookrightarrow\mathcal I_{<A}.}
$$

This is a strictly order-preserving embedding under the original IBLP comparison key, with **No longer assume that the entire A is incomplete.**. Specifically, under the key A, there exists a well-ordering subset of all ordinary BMSs that is strictly reachable in its underlying segment; this conclusion does not presuppose that the entire IBLP segment is already well-ordered.

The key to the proof is a class that is closed under "positive interface replication + column deletion". All previous copies of [BMS Ancestor Band Construction](<../iblp-bms-20260918/IBLP-01-BMS-lower-bound.md>) belong to this operation, so there is no need to first address the zero interface replication across the entire domain.

This paper does not contain proofs.

- Any path below A does not complete.
- A The entire expansion relationship is a good base;
- The limit of A≤BMS, or the limit of A=BMS.

The original definition remains unchanged from the fixed original iblp.py (see SOURCE_MANIFEST.json). The term "positive interface" refers to the classification of the original rule's control lines in this text, and it does not constitute a change to the original rule or the closure of its completion functions.

## 1. lines, parent forests, and internal points

The incremental points of the body i are R_i, the step size is L_i≥1, and the final point is i. The auxiliary address 0 is not part of the body. Let

$$
q_i=|R_i|-L_i-1,\quad
p_i=R_i[q_i],\quad a_i=R_i[0],\quad
P(i)=R_i[-2],\quad P(0)=0,\quad q_0=0.
$$

If q_i>0, define its leading chain and trailing chain.

$$
U_i=R_i[:q_i+1],\qquad V_i=R_i[L_i:].
$$

Also retain a point used for completion after the front chain. Let

$$
J_i=R_i[1:q_i+2]\ \cup\ R_i[L_i+1:]. \tag{1.1}
$$

J_i is the set of all non-roots in the two ancestral chains that are to be preserved. The first chain is R_i[:q_i+2], which includes the points after the tangent point, and this point is removed without considering it as redundant.

Writing $x\preceq_P y$ means that x is a non-strict P ancestor of y.

## The explicit finite condition class 2. is equivalent to the class C.

Empty expressions belong to C. Non-empty expressions belong to C if and only if they satisfy the following conditions.

### C0: fundamental shape

- R_i is strictly increasing, with non-negative initial points, and the last point is i; each asterisk is marked at the actual point in that row.
- When 0≤q_i≤L_i, q_i=0 must be at two-row positions (P(i), i)), with a step size of 1.
- P is a planar forest sorted by address: each subtree is continuous in the address order.
- In each R_i, the point is either an P ancestor of an i or the i itself.
- R_i[, q_i+2], and R_i[L_i:] are all continuous P chains.

The last guarantee states that the first point after the tangent point, b_i, satisfies P(b_i)=p_i. Therefore, the original completion of each row has no effect.

### C1: Number of interfaces in the end chain

If q_i=s≥2, write

$$
V_i=(w_0,w_1,\ldots,w_s=i).
$$

Mathematical research manuscript

$$
q_{w_t}=t\qquad(1\le t\le s). \tag{2.1}
$$

The condition for the endpoint t=s is only q_i=s.

### C2: Number of interfaces at the critical point

For q_i>0, the requirements are as follows:

$$
q_{p_i}\in\{0,1,q_i\}. \tag{2.2}
$$

### C3: Front-end initial point barrier

For each q_i>0, as well as each $p_i\preceq_P j$, the requirements are as follows:

$$
a_i\notin J_j. \tag{2.3}
$$

Here, j can be earlier or later than i; this includes the point of tangency itself. It does not only check the control row or the immediately adjacent row.

### C4: Prefix barrier of the terminal starting point

For q_i=s≥2, write V_i=(w_0,w_1,…,w_s) according to C1, with the requirements being

$$
j<i,\quad w_1\preceq_P j
\quad\Longrightarrow\quad w_0\notin J_j. \tag{2.4}
$$

C4 only restricts prefixes before i; extending it arbitrarily to all future lines would be refuted by actual seeds.

These are conditions that can be checked by directly reading a finite number of lines of data. They are not implicitly defined as "this formula has been reachable from A". For verifiers, see positive_control_class.py (Historical reference: `positive_control_class.py`).

## 3. Positive Interface Copy Forest Formula

Let X∈C be the end point, N be the control interface number, and k=q_N>0 be the number of control interfaces. Write

$$
U_N=(u_0=a,u_1,\ldots,u_k=c),\qquad
V_N=(v_0,v_1,\ldots,v_k=N),\qquad d=N-c.
$$

The original complete function f is

$$
f(x)=\begin{cases}
x&x<a,\\
v_t&x=u_t,\ 0\le t<k,\\
x+d&x\ge c.
\end{cases} \tag{3.1}
$$

The other a<x<c integers are not in the domain.

c,…,N are the subtrees of c. All the elements within these rows that are less than c are part of the ancestor chain of P under c. Therefore, they are either less than a or some u_t. Thus, all the copied row points and asterisk points are within the domain of f. By q_N≤L_N, f is strictly increasing on its domain.

The original copy retains the prefix that is less than N, and places the source lines i∈[c,N] at f(i)=i+d. The new seam address is f(c)=N, and its parent is

$$
P'(N)=f(P(c))=f(u_{k-1})=v_{k-1}=P(N). \tag{3.2}
$$

The parent subtrees of the copied rows are transported. Therefore, the new tail segments remain as single subtrees, attached below the original parent of the old endpoints. The parent of the old address N remains unchanged. The references of the moved front ends also become ancestors of the new seams. Planarity and intra-row ancestry are preserved.

For the point x involved, the only possible destruction of the direct parent edge is the transport by x=a:

$$
x\ne a\quad\Longrightarrow\quad
P'(f(x))=f(P(x)), \tag{3.3}
$$

This equation is used only on the side where P appears. The fixed regions, u_t (t>0), and the tail sections are directly verified. The auxiliary root 0 does not have any parent edges that need to be transported.

The application of C3 to the control row N indicates that each replicated source row i∈[c, N] has a∉J_i. Therefore, (3.3) maintains all the direct parent edges of the front chain and the end chain. The length of the row, the step size, and the number of interfaces also remain unchanged due to the injective function of f. This proves that the result holds after replication with C0.

## Lemma on Position Classification of 4.

The following is a direct copy of the original research manuscript for the primary interface. The symbols are the same as those used in section 3.

### The cutpoint classification of the copied row with 4.1

Let the source lines be i∈[c, N], and q_i=s>0, with the tangent point being r=p_i and the starting point being z=a_i. Except for r<a and r≥c, the only possible situation is

$$
r=u_t,\quad 1\le t<k,\qquad z=a,\qquad s=t. \tag{4.1}
$$

Proof: If a≤r<c, then r must be u_t.

- If z<a, the continuous front-end chain from z to r will use a as an internal point, violating the control line N's C3.
- If z>a, then z must be some u_l, 1≤l<t. N is a descendant of r.
But z is a front-end internal point of N, violating the C3 stated in the source line i.

So, z=a. The continuous chain from a to u_t has a length of t, hence the number of interfaces is s=t; s>0 also excludes t=0.

### 4.2 The second point classification at the end of the high interface row

Let the source lines be i∈[c, N], and the q_i=s≥2. The end chains are W=(w_0, w_1, …, w_s=i). Then either w_1≥c, or

$$
k\ge2,\qquad w_0=a,\quad w_1=u_1,\quad q_c=k. \tag{4.2}
$$

Proof: If w_1<c, then w_1≤a would cause the end-of-chain to use a as an internal point, violating C3. Therefore, w_1=u_t, 1≤t<k. Continuing from w_1 to c, c is located at the k−t+1th position of W; this position is at least 2. From C1, q_c=k−t+1; from the control lines C2, q_c∈{0, 1, k}. Therefore, t=1, q_c=k, and w_0=P(u_1)=a.

This classification deals with the situation where "part of the end chain of the new copied row still falls within the old prefix."

## 5. The original copy of the positive interface is retained throughout C

### 5.1 C1 maintains

Use the 4.2 section for a replicated high-interface row.

- w_1≥c: All internal points at the ends are in the replication area, and the number of interfaces of the nodes is transported as it is.
- In another case, the beginning of W is a, u_1, …, u_k=c.
u_t (1≤t<k) becomes the old v_t, with a number of interfaces of t; copies of c are the new seams N, with the same number of interfaces as the old q_c=k. Subsequent points are copied normally. Therefore, the new end chain still has the required number of interfaces at each position.

The high interface row in the old prefix remains unchanged, so C1 is retained.

### 5.2 C2 maintains

Use the 4.1 section for the cutpoints of copied lines. The number of interfaces remains unchanged for cutpoints within the fixed or copied regions. In intermediate cases, the number of interfaces for the source line is t, the cutpoints become the old v_t, and the number of interfaces is still t, which satisfies C2. The cutpoints and the number of interfaces in the old prefix remain unchanged.

### 5.3 C3: Copies the row pair for all prefixes and tail segments

Consider the new control rows originating from the source i∈[c, N], q_i>0, the initial point z, and the tangent point r.

- **r≥c：** The new cut point and its entire new subtree are in the replication area; The barrier is obtained by the injection of C3 and f.
- **r<a：**r, z is fixed, and r is an ancestor of the old c. All rows within the r subtree in the old prefix have been protected by the source C3.
The source of the new copy row is also in the r subtree, still protected by the same conditions.
- **Intermediate situation:** is defined by (4.1), with a new starting point at v_0, and new tangents at v_t, 1≤t<k.
The offspring of the old prefix v_t is also the offspring of v_1, with the C4 that controls the line N excluding the v_0 as an internal point. The lines in the new suffix are the images of the original c subtree lines, with the original C3 excluding the a, and the injective f excluding its images v_0.

This includes the new tangent points themselves and all the old prefix lines, not just the new replicated blocks.

### 5.4 C3: The barrier of the old prefix row to the new tail section

Now fix the old lines i<N, q_i>0, the starting point z, and the tangent point r. Only consider the situation of the new tail fragment in the r subtree. Given (3.2), which is equivalent to the old N, is located within the r subtree.

If a new row contains the interior point z, trace its image under f:

- If **z<a：** and r≥c, then the old row i is also in the c subtree, and its front-end continuous chain crosses z to a and then to r.
The C3 violates the control line N. Therefore, the r<c; r is an ancestor of the c, and the source C3 has excluded the z from the tail section of the source line.
- **z≥a：** due to z<i<N, And send both f and x≥c to N and its right side. Only z=v_t and 0≤t<k need to be considered.
If t>0 and z are the terminal internal points of the old N, it directly violates the C3 of the old row i. If t=0, its only original point is a, and the C3 that controls the row N has excluded a as an internal point of any tail segment source row.

The barriers of the old lines also protect the new sections. Merge section 5.3, and keep C3.

### 5.5 C4 maintains

The C4 in the old lines only cover the prefixes that came before, and of course, they remain unchanged. For the new high-interface lines, use the 4.2 section:

- When w_1≥c, the new w_1 subtree is in the replication area, directly transporting the source C4.
- When w_1<c, 4.2) provides a new end point v_0, and the second point is v_1.
The barrier required by the old prefix is ensured by the C4 that controls the line N; the corresponding source lines in the new replication blocks are located in the c subtree, with the C3 excluding the a, thereby excluding their images v_0.

Therefore, C4 remains unchanged. This completes the proof.

$$
\boxed{X\in C,\ q_N>0\quad\Longrightarrow\quad C_{\rm raw}(X)\in C.} \tag{5.1}
$$

This is a proof of a complete original copy (including the last line of the work), and therefore can be continuously iterated any finite number of times. The original work template is not confused with the actual fundamental terms.

## 6. deletion, true fundamental sequence, completion, and comparison

### The 6.1 notation is maintained by deleting the tail, resulting in C.

C0, C1, and C2 only read the left-hand side of the data; C3 deletes some quantified descendants; C4 only reads earlier prefixes. Therefore, any true prefix remains in C.

### The completion of 6.2 has no effect.

Every original copy still has a direct parent edge with C0

$$
P(R_i[q_i+1])=R_i[q_i].
$$

This makes the original completion without insertions. Therefore, the record that is truly expanded remains empty, and the marked completion also remains unchanged. The asterisk filtering can remove the asterisk without changing the row data; it does not create completion records on its own.

Therefore:

- The indicator 0 is a column deletion.
- The index of positive interface control, 1, is the original width to which the first original copy is stretched.
- The indicator for positive interface control, m≥2, is the result of m−1 primary copies followed by the deletion of the last line.

They are all outputs of the actual original program, still belonging to C, and none of them have been effectively completed.

### 6.3 is strictly descending in each actual operation according to the original comparison key.

The deletion of the tail is a true prefix. The address that is copied for the first time is the old N. The old row key is

$$
(N,v_{k-1},\ldots,v_0,a).
$$

Copy the line with the old cut point c to a new line, setting its number of interfaces to s. From C2, s∈{0, 1, k}.

- If s=k, the end chain of the old c row is exactly U_N, and its starting point is strictly less than a.
The new end chain is V_N, with the initial point remaining in the fixed zone. Therefore, the new key decreases strictly in the last position.
- If s<k, the new key has s+2≤k+1 points, all of which decrease strictly along the new N ancestral chain.
The items with k+1 before the old key are the continuous ancestral chains of that key. Therefore, the new key is either strictly smaller than some item, or it is a true prefix of the old key.

The subsequent replication does not change this initial difference. Therefore, each of the aforementioned true positive index operations also strictly decreases.

**Range restrictions:** does not claim that C is closed for positive ordinal copies of zero interface control. It is known that it is not closed. It is allowed to perform [0] on the zero interface row at any time, as this is still a column deletion.

## All 7. belong to A_n, which in turn belong to C.

Using the closed formula from the previous progress report section 3 (Historical Reference: `IBLP-01-no-completion-and-BMS-progress.zh-CN.md`). Its ancestral structure and the front and back chains are given as C0; the asterisk is always within the same line.

The number of ports for each stage t is sequentially 1, …, t, with C1 provided. The tangent points of all positive interface rows are located at the skeleton address a_k; the number of ports for these addresses is either 0 or 1, with C2 provided. The starting points of all rows are 0, and they cannot be internal points in a strictly increasing chain, with C3 provided.

Finally, check C4. The end chain of the k≥2th row within a stage is

$$
(b_0,b_1,\ldots,b_k).
$$

In the rows that belong to the subtree of b_1, there are only b_1, …, b_{k-1} of the same stage. The front chains of these rows are strictly located before b_0, and the end chains start with b_0 as the first point; therefore, b_0 is not within their internal point set. This holds true for C4. A_0 and A_1 do not have high interface rows, and C4 does not require additional checks.

From section 5–6, we obtain the conclusions for total indices and arbitrary depths:

> Starting from any A_n, as long as the number of control interfaces that are truly copied at each step is positive, and other steps only involve tail deletion,
> All intermediate forms are in C, and all original completions and marked completions have no effect.

This is not 'just expanding to the next step', nor does it limit the size of n; however, it clearly restricts the type of operations that can be used.

## Why is 8. sufficient to achieve an unconditional upper bound for the entire BMS?

Previously, the notation indicated mapping the BMS's rth row to the IBLP's r+1th interface position. Therefore, when simulating a BMS non-successive fundamental sequence step, the number of IBLP control interfaces chosen is always

$$
k=r+1\ge1.
$$

The rest of the preparations, final touches, source successors, and source indicators 0 are all completed by the actual [0]. **The entire construction never required positive index replication of the zero interface control lines.**

### The true seeds of any finite number of rows are marked with 8.1.

Fix the h≥2, take n=h+1. Let

$$
a_j=j\ (j<3),\qquad a_j=3+(j-3)(j-2)/2\ (j\ge3).
$$

The width of A_n is s_n=2+n(n+1)/2, the last row's tangent point is a_n, and let d=s_n−a_n. In the final stage, take the ancestor band.

$$
V=(b_0,\ldots,b_h),\qquad
b_0=a_{n+1},\quad b_k=a_{n+2}+k-1\quad(1\le k\le h).
$$

Actual expansion

$$
T_h=A_{h+1}[2]
$$

Generate two columns with V and W=V+d, respectively representing the all zero column with B_h and the all 1 column.

According to section 7, A_n∈C, this time the number of control interfaces is n>0, so there is indeed no completion during this replication. All unencoded extra lines are also present in C, and it is not safe to delete or ignore them.

### Every BMS macro step of 8.2 is in C.

For the highest non-zero rows r, k=r+1 of the source end column x, control the parent column c:

1. Use [0] to reach the kth port of the last ancestor band; the number of interfaces on this row is exactly k.
2. For the original positive indicator m, perform the original IBLP [m+1], that is, a complete replication of m copies.
3. End with the last point of the complete output strip marked as [0].

In section 6, it is guaranteed that the preparatory forms, the original template of the work, and the final output are all in C, and all completions are useless. Therefore, the BMS parent table exchange formulas derived from the old text port by port can be used as they are, **The necessary security assumptions have now been independently proven.**. The source zero index, successor, and empty forms still only require tail deletion.

The parent table replication property of ordinary BMSs and the well-orderability of the standard domain are assumed to be marked with [Hunter's proof, Lemma 2.5, and the main theorem](https://arxiv.org/html/2307.04606v3). No assumptions are made regarding the well-orderability of the target domain for induction.

### 8.3 achieves order-preserving embeddings, rather than just path simulations.

A macro step preserves the target prefix corresponding to the source prefix. Different fundamental terms of the same source are ordered by actual prefix inclusion. Section 6.3 proves that each target step strictly decreases the comparison order.

Therefore, a relative interval induction can be applied to known well-ordered BMS sources: Given the source prefix u and the corresponding target prefix v, embed (u,s]) into (v,t]). Decompose the source intervals into continuous intervals between fundamental terms, use the induction hypothesis for smaller source fundamental terms, and then concatenate the non-overlapping target intervals. This construction deals with the source order type, not the expansion path tree with repeated nodes.

This is precisely the relative interval lemma from section 8 of the old text; its target major step now lies entirely within the unconditional-safe C.

The first non-head port up to the deadline V is used as the prefix F_h, as follows:

$$
A_h<F_h\le T_h<A_{h+1},
$$

Therefore

$$
[0,B_h]_{\rm BMS}\hookrightarrow(A_h,A_{h+1})_{\rm IBLP}.
$$

Segment the BMS standard domain according to B_h, and place these non-overlapping target intervals in sequence to obtain the full system embedding.

The conclusion can be simply referred to as "the BMS limit lower bound of 01", but it cannot omit the fact that the goal of proving the full well-ordering of the lower segment has not yet been established.

## 9. adds a finite verification

Verification is not a substitute for the universal conclusion of the 3–8 section; it is used only to identify errors in specific cases.

### Independent input verification for closed classes with 9.1

check_positive_control_closure.py (Historical reference: `check_positive_control_closure.py`) tests the restricted descent of true seeds, and also directly selects ancestral point sequences to generate independent inputs that satisfy C. The independent inputs are not claimed to be reachable from A, and allow arbitrary sampling of asterisks within the row.

A bounded operation that is completed in one step includes:

- There are 100 independent roots, 1, 462 independent prefixes; independent inputs with interface count 0, 5;
- With the actual seeds, there are 1, 239 positive interface control states. The actual seeds cover a total of 1, …, 10 interfaces.
- 2,478 retain the original copy of the working template; 3,717 are the true indices; 1,2,3 are their expansions.
- Every time the entire output is verified to satisfy C, to be consistent with the original copy, and to have the original comparison key strictly decrease;
- 28,143 primary completion calls have no effect, and26,878 marked completion calls also have no effect; approximately 3.8 seconds.

The earlier round of seed tests stopped at a budget of 25 seconds; this round was clearly reported as UNKNOWN, and no completed traversals were counted.

### The class 9.2 was indeed used in the old BMS macro steps.

check_positive_ribbon_macros.py (Historical reference: `check_positive_ribbon_macros.py`) Reuses the old macro to simulate the program, and additionally asserts that the number of control interfaces for each call is positive, and that each input and output belongs to C.

- h=2, …, 8, a total of 7 seeds;
- 540 completed random macro steps, with additional verification of brother fundamental item prefixes;
- 608 is a type of completion; C is a type of certificate verification; 364 is a type of original IBLP positive interface call.
- Both native and marked completions occur 15, 594 times, with no effect.
- The process of 25 branches reaches the upper limit of 350 rows in width, with a clear stop, not considered as completed; takes about 4.4 seconds.

All cycles, widths, and time have a finite upper limit; abnormal budgets will not be swallowed up by the fault-tolerant branches of the original expander. All processes have exited, with no background calculations ongoing. The original definitions and published repositories have not been modified, and there are no commits or pushes.

## 10. subsequent states

The positive interface closure of the class C has been proven in paper form. It is **Just no** closed for all zero-interface positive indices: a counterexample was given in the non-standard nine-line input D of the previous manuscript.

Subsequently, these strengthening conditions were added to form smaller classes D, and it was proven that they are closed under all operations, including zero interface replication. For details, see [No supplementary proof available for the entire standard section below.](<IBLP-01-no-completion-proof.md>).

It is still necessary to have a reverse finite row BMS upper bound in order to elevate this lower bound to an equality.
