# IBLP: All valid expressions that are strictly below 01 will not complete. · [中文版](IBLP-01-no-completion-proof.reading.zh-CN.md)

*English reading edition, translated with machine assistance. The title links to the dated Chinese manuscript.*

> Collected reading edition. The three main papers state the results of this collection.
> This edition retains the local proofs, their hypotheses and any withdrawals. Progress reports describe the state of work at the time.
> The locations of omitted passages on preset inputs are recorded in SOURCE_MANIFEST.json.
> The main papers give the numerical derivations for the natural parameters produced by the proofs. This historical note carries no additional Lean certification.

2026-09-23, further research. Regarding the original definition of paper proofs, they have not yet been formalized in Lean.

## 0. Conclusion

Let A=I[0][1], A_n=A[n]. This proof establishes:

> For any n, and any finite string of true fundamental sequences starting from A_n,
> In each step along the way, no points are inserted during the native completion process, and no rows are modified during the marked completion process.
> The original copy always has a definition and will not degenerate into a faulty branch with a deleted tail after the first copy fails.

Therefore, the standard lower segment that can be truly expanded from A is taken as the range.

$$
\boxed{\text{Further expansion of any term strictly below 01 triggers no effective completion.}}
$$

The following does not include any handwritten non-standard inputs that merely compare the smaller keys. It is true that A may be completed when it generates itself as A_n, but this theorem does not include A in its scope.

This proof is an induction on finite structure invariants and does not assume the BMS well-orderedness, the IBLP well-orderedness, or global absence of completions. It does not prove the converse upper bound of BMS; the subsequent [Interface bridge coverage proof](<IBLP-01-BMS-upper-bound.md>) separately completes the upper bound and equality, relying on this paper without being a premise of this paper in turn.

## 1. base class C and this notation

Following the class C introduced in the [Positive Interface Closed Lemma](<IBLP-01-unconditional-BMS-lower-bound.md>) section 1–6, this text provides a complete proof for each case; this article complements the zero interface replication based on this foundation.

Define a sequence of points with body movement i, with step lengths of R_i and L_i.

$$
q_i=|R_i|-L_i-1,\quad p_i=R_i[q_i],\quad
P(i)=R_i[-2],\quad h_i=R_i[L_i],
$$

and

$$
J_i=R_i[1:q_i+2]\cup R_i[L_i+1:].
$$

P(0)=q_0=0.h_i is the starting point of the end chain, hereinafter referred to as "layer head".

The conditions similar to C are briefly described as follows:

1. Ordered rows, asterisks within rows, planar P forests, all references are ancestors;
0≤q≤L, the zero interface row consists of exactly two rows; the front end has an additional point, and the end is continuous, forming a P chain.
2. At the end of the chain with the high interface line q_i=s≥2, the conditions q_(w_t)=t and 1≤t≤s are satisfied at each position, for the links w_0, …, w_s=i).
3. The tangent points of the positive interface line satisfy q_(p_i)∈{0, 1, q_i}.
4. The first point of the positive interface row is not a marked point within the J of any row in its tangent subtree.
5. For high-level interfaces, Layer head w_0 Not belonging to i Previously, located in w_1 Any row within the subtree J Volume.

C is closed to the deletion of tails and any positive interface original copies. Here, "original copy" includes the last line of the work, which has not yet undergone completion or the final deletion of tails.

## 2. strengthens the class D

D is a pattern in C that satisfies the following five additional conditions. All of these conditions are read directly from a finite number of lines, without hiding "reachability" within the definition.

### D1: The internal ports are not terminal types.

If q_i=s≥2, its end chain is (w_0,…,w_s)).

$$
L_{w_t}\ge t+2\qquad(1\le t<s). \tag{D1}
$$

The basic conditions have been provided q_(w_t)=t.

### D2: The same interface tangent point is not a terminal type.

If q_i>0 and q_(p_i)=q_i, then

$$
L_{p_i}\ge q_i+2. \tag{D2}
$$

### D3: Low interface rows cannot be connected below high interface termination nodes.

If q_i≤1, c=P(i)>0, and q_c≥2, then

$$
L_c\ge q_c+2. \tag{D3}
$$

### D4: When encountering a higher-level head, it can only be a termination type of the same-level head.

If q_i≥2, $i\preceq_P j$, and h_i∈J_j, then

$$
q_j\ge2,\qquad L_j=q_j+1,\qquad h_j=h_i. \tag{D4}
$$

This condition includes j=i. "Terminal types" are precisely defined as q≥2 and L=q+1 in this text; "non-terminal types" refer to L≥q+2, without additional semantic assumptions.

From the continuous end chain, D4 also implies $q_j=q_i+\operatorname{dist}_P(i,j)$, thus j>i implies q_j>q_i. Moreover, there cannot be L=q in the high interface row: otherwise, the layer at the head would belong to J_i, which contradicts D4.

### D5: The branch that encounters the layer head must be the last branch.

If q_i≥2, i<j, $i\preceq_P j$, h_i∈J_j, then

$$
j\le t,\quad i\preceq_P t
\quad\Longrightarrow\quad j\preceq_P t. \tag{D5}
$$

That is, in the subtree of i, after passing through j, one is not allowed to return to the brother branches of j. For a planar forest, this is equivalent to the right endpoints of the subtrees of i and j being the same.

This is the condition that was missing from the previous handwritten bad input D_old: it has a brother branch that returns to the ancestor, following the existing terminating branches. This input is not a member of the class D and cannot serve as a counterexample within the standard domain of this theorem.

## 3. Two original copies and one transport lemma

The following uses c to represent the current starting point and N to represent the current ending point. A single original copy moves the source body lines c,…,N to N,…,2N−c, retaining the prefixes before N. The positions of the lines L, q, and J are moved according to the strictly increasing function f:

$$
J'_{f(i)}=f[J_i].
$$

### 3.1 Positive Interface Control

When k=q_N>0, let the front chain be $(u_0=a,\ldots,u_k=c)$, and the end chain be
$(v_0,\ldots,v_k=N)$.
Copy function

$$
f(x)=x\ (x<a),\quad f(u_t)=v_t\ (t<k),\quad
f(x)=x+N-c\ (x\ge c).
$$

The parent of the new seam N is still the old P(N)=v_(k−1). The proof of the fundamental class C has already ensured replication of definiteness, and C0–C4 is maintained.

### 3.2 Zero interface control

The last lines of the non-successor zero interface are (c,N),c=P(N)>0,L_N=1. At this time

$$
f(x)=\begin{cases}x&x<c,\\x+N-c&x\ge c.\end{cases} \tag{3.1}
$$

The new joint N has its parent as the old P(c), rather than the old P(N)=c. The new tail subtree becomes a new sibling subtree of the old c subtree. This is the only forest difference that distinguishes it from the positive interface case.

f is defined for all integers, and it transports all source P sides along each edge; the ancestral relationships and node types within the replication area are completely preserved.

### 3.3 Old high interface nodes and layer head transport of the new tail section

Let i<N be the retained old high interface node. A certain new replicated row j'=f(j) is a descendant of i, and h_i∈J'_(j').

Therefore:

- In the positive interface case, there must be i<c and h_i<a, and h_i is fixed.
- In the zero-interface case, there must be i<c and h_i<c, and h_i is fixed.

In both cases, the source line j is also a descendant of the old i, and it is h_i∈J_j.

The zero-interface situation directly arises from new seams being attached below P(c).

The proof for the positive interface case is as follows. The new tail segment is located below the original parent term of the old N, so i is a predecessor of the old N. Since h_i<i<N, if the layer head comes from the transport area, it can only be some v_t, 0≤t<k.

- When t=0, the target point a is excluded from the frontmost point barrier of the controlled row, and cannot be an internal point of the copied row.
- When t>0, i is an ancestor of v_t, but not of N. Therefore, i=v_s, s>t.
Given the basic condition q_i=s, the end chain starting point of i is actually v_0, and cannot be v_t.

Therefore, h_i<a remains fixed. If i≥c, then the continuous end chain of the old i crosses h_i to a to i, and using a as an internal point still violates the barrier of the control line. Hence, i<c; i is an ancestor of c, and the source tail segment naturally lies within the subtree of i. The lemma is proven.

## 4. D1, D2, D3 remain unchanged upon replication

### 4.1 D1

For the replication of the positive interface, use the "second point classification at the end" from the basic proof:

- If the second point at the end of the high-interface row is ≥c, all internal ports are copied normally, and the type remains unchanged.
- Otherwise, the source end chain starts from a,u_1,…,u_k=c, and ends at q_c=k.
u_t (1≤t<k) moved to the old v_t, with the type guaranteed by the old D1; a copy of c becomes the new joint, with its number of interfaces k, guaranteed by the D2 of the control line L_c≥k+2; the subsequent internal points are copied normally.

Therefore, all internal ports of the new end chain satisfy D1.

In zero interface replication, each port either remains fixed or is replicated along with its type, with D1 being maintained directly.

### 4.2 D2

When copying the positive interface, the basic proof has been categorized and copied to the positive interface line at the critical points r:

- r<a or r≥c: The type of tangent point remains unchanged, inheriting the original D2.
- Intermediate cases r=u_t, 1≤t<k: The number of interface points of this source exactly equals t;
The new critical point is the old v_t, and its number of interfaces is also t. The old D1 yields L_(v_t)≥t+2.

At zero interfaces, all type of tangent points are only used for fixing or transporting. Therefore, D2 remains unchanged.

### 4.3 D3

Just check the copied low-interface lines, q≤1. If the source line is i>c, its parent is also in the tail section. The q and L of the parent node are copied as they are, inheriting the source D3.

The remaining line i=c is copied to a new seam, and replaced with q_c≤1.

The number of interfaces controlled by the positive interface is k:

- k=1: The new parent is the old P(N)=v_0, and the old N itself is the low interface row, with its D3 precisely providing the required conditions.
- k=2: The number of interfaces of the new parent v_1 is 1, and it does not trigger the high-parent condition of D3.
- k≥3: The number of interfaces of the new parent v_(k−1) is k−1≥2, and the old D1 ensures that it is not terminated.

In zero interface replication, the new parent is the old P(c); the source c ensures the necessary conditions for its own D3. The low interface rows in the old prefix and their parents remain unchanged. Therefore, D3 is retained.

## 5. D4 and D5 maintain their order in replication

### 5.1 D4

The high-interface nodes that need to be checked, i', and the descendants that hit their layer heads, j', can be categorized into three types:

1. The data in the **Both are old prefixes:** row remains unchanged, with no changes in ancestral relationships.
2. The ancestor relationships, internal point positions of **Both are in the new replication area:**, and those of q and L all transport with f.
Directly use the source D4. The equality holds at the head of the source layer, and the equality also holds at the head of the target layer.
3. **i' represents old nodes, and j' represents new endings:** Section 3.3 describes the fixed layer head. The source j is also a descendant of the old i'.
And it has already hit the same header. The source D4 gives q_j≥2, L_j=q_j+1, h_j=h_(i'); these facts remain true after transportation.

The old j' cannot become a descendant of the new i', thus the classification is complete. D4 remains valid for both types of replication.

### 5.2 Positive interface replication retained D5

If the new high-interface i' is in the replication area, its offspring j' is also in the replication area, and the source D5 is directly transported.

If i' is an old high interface node:

- **Old hit row j'<N:** If a new tail section enters i' The subtree, The old N is also included.
The source D5 indicates that j' is an ancestor of the old N. j'<N, therefore, is also an ancestor of the old P(N); the new suffix continues below the old P(N), thus still being within the subtree of j'.
- **New copied hit line:** is located in the old i' subtree, as indicated by the source hit line j in the 3.3 section.
The source D5 ensures that all relevant nodes after j in the source tail section are descendants of j. Replication maintains the ancestor relationships of the tail section, so the entire relevant tail section after the new hit remains within its subtree.

### 5.3 Zero interface replication retained D5

Let the subtree of the old high interface i'<N contain the new tail segment. In this case, i' is a ancestor of P(c), thus i'<c, and the old N is a direct child of c.

Let's first look at the old hit line j'<N. The source D5 indicates that j' is an ancestor of the old N, thus j'≤c.

- If j'<c, the new tail segment that follows P(c) is still a descendant of j'.
- If j'=c, the source D4 requires c to be a high interface termination type: L_c=q_c+1.
However, the old last line N is a zero interface line, with its parent being c. The requirement for D3 is that L_c≥q_c+2 must be met, which is contradictory.

Looking at the newly copied hit line, the source is j≥c. The 3.3 section and the source D5 indicate that j is an ancestor of the old N, so j can only be c or N.

- j=c: Again, it results in a contradiction between the terminal/non-terminal type determined by D4 and the D3 in the old last line.
- j=N: The source D4 requires q_N≥2, which contradicts the current zero interface control.

Therefore, this new hit row is impossible to occur. The D5 of the new interface nodes within the replication area are still directly transported by the source condition. This is proven by D5.

## 6. fills in the zero interface copy pairs for the base class C

The original positive interface lemma has proven that the positive interface replication preserves C. This text only examines the zero interface control, where c=P(N)>0, the new parent interface is P(c).

### 6.1 C0, C1, C2

The function (3.1)) is fully defined, strictly increasing, and involves a process of transporting along edges. The copied subtrees are placed after the original c subtree, resulting in a planar forest structure. The properties of front-end chains, intra-row ancestry, row length, and step length are preserved. The number of interfaces for all referenced nodes remains unchanged or is maintained by the copies, thus C1 and C2 are also preserved.

### 6.2 Front-end Initial Point Barrier C3

For copying the original interface lines, if their cut points are at or above c, the new cut point subtree is entirely within the copied area, and the source C3 is directly transported. If the cut point is before c, it is an ancestor of the old c, and the starting point of the line remains fixed. The source C3 has already protected all the old prefixes and all the tail segments of the source lines, and still protects the new copied lines.

For the old positive interface lines, the new tail section only enters the tangent point subtree when its tangent point is an ancestor of P(c). At this time, both the tangent point and the row start point are before c and fixed. The source tail section is also located within the tangent point subtree, and the original C3 directly excludes the same internal point. The other old relationships remain unchanged. Therefore, C3 remains unchanged.

### 6.3 Prefix barrier at the end of the first point C4: The last notch

Examine the replicated high-interface source line i, the end chain is

$$
(w_0,w_1,\ldots,w_s=i),\qquad s=q_i\ge2.
$$

If w_1≥c, the new w_1 and its subtree are all in the replication area, then directly transport the original C4.

If w_1<c, because i≥c, and the entire string is a continuous ancestral chain, c appears in the t≥2th position. C1 gives q_c=t, and the end chain of c itself is exactly

$$
(w_0,w_1,\ldots,w_t=c).
$$

Therefore, h_c=w_0, and both w_0 and w_1 are fixed by f.

It is necessary to exclude the internal points w_0 from the subtree of w_1 in the old prefixes. Located in position:

- **j<c：** is excluded by the C4 of the source node c.
- **j=c：** The old last line N is the zero interface line, with the parent being c. D3 provides L_c≥q_c+2.
The layer head R_c[L_c] does not belong to the internal segments at the front end, nor is it the first point of the end chain, therefore it is w_0∉J_c.
- These points **c<j<N：** are all within the subtree of c. If w_0∈J_j, D5 is applied to c, j.
The offspring of forcing the old N to j should be possible; however, P(N)=c and N are direct children of c, which is impossible, leading to a contradiction.

In the new replication area, the corresponding source lines before the new i are still protected by the C4 of the original i. Therefore, C4 remains unchanged, and the basic class gap is filled in the case of zero interfaces.

## 7. has a full closure of operations and no completion.

Section 4–6 jointly proves:

> If X∈D, and X is non-zero and not a successor, then the original complete copy is defined, and the output (including the working template) still belongs to D.

All D conditions hold for prefix truncation:

- Type conditions and left-hand side citations remain unchanged;
- The barrier only reduces the descendants being examined.
- D5 only reduces the later nodes, without increasing any returning branches.

Therefore, it can be repeatedly copied any finite number of times, and then the tail can be deleted. The special operation for the indicator 1 is to cut the first original copy to its original width, still belonging to D.

D contains C0, so each new row satisfies

$$
P(R_i[q_i+1])=R_i[q_i].
$$

The original completion process involves reaching the tangent point by taking the parent node for the first time, without inserting any points. The record of the first expansion is always empty, and the marked completion does not modify the lines either. The asterisk filtering only deletes the asterisk, without changing the body lines.

Therefore, the true fundamental sequence of the original program is completely consistent with the above original replication result:

- Zero form, successor, index 0: Remove the tail according to the original rule;
- Other indicators 1: Copy the critical point row and retain the original width;
- Other indicators m≥2: m−1 refers to the operation of deleting the last row after a primary complete copy has been made.

These are all steps allowed by the original definition. The completion is not closed, and intermediate points are not omitted.

## Initial verification for all 8. that are A_n

All A_n∈C have been proven by a full index closed proof in section 7 of the main interface manuscript. The following sections D1–D5 are supplementary. A_0 and A_1 do not have high interface lines; they can be checked directly.

For n≥2, the ports at each stage t are sequentially b_1, …, b_t. The number of interfaces is 1, …, t. The end chains all start from b_0. The step size is

$$
L_{b_k}=\begin{cases}k+2&k<t,\\t+1&k=t.\end{cases}
$$

- The step length between the internal port **D1：** and the port k<t is k+2.
- All positive interface tangencies of **D2：** are skeletons of a_k; their number of interfaces is either 0 or 1.
All rows with an interface number of 1 are cut to the leftmost root of the interface number 0, so the interface condition is not triggered.
- **D3：** Zero, single interface rows whose parents are auxiliary roots or skeleton single interface rows, are not high interface nodes.
- The **D4：** phase has a high interface within the fixed stage. The i=b_k phase is the next stage. Its high-interface subtrees only contain the remaining ports at the same stage.
The subsequent stages are attached to a single interface skeleton and are not descendants of these high-interface ports. For b_l at the same stage, the layer head b_0 does not belong to the end internal points; it only appears in the front-end internal points at l=t. At this time, it is L_(b_t)=t+1, and the layer head is still b_0, which is precisely the termination type required by D4.
- The only possible hit line marked with **D5：** that is b_t is the last leaf of this high-interface subtree.
Therefore, there is no subsequent return to the sibling branch.

Therefore, all n have A_n∈D. Combining with the 7 section, by ordinary induction on any finite expansion history, the non-deletion theorem of the 0 section is obtained.

## The comparative properties that are incidental to 9., as well as the uncompleted upper bounds

The strict comparison reduction of the positive interface expansion has been proven in the basic manuscript. The old last-line keys that control X are (N,c); the second item of the new keys after copying the tangent point row is P(c)<c, so it also has a strict reduction. The deletion of the tail of the interface is of course also a reduction.

Additionally, due to the original block-by-block replication and truncation formulas, the actual fundamental terms follow the prefix chain for ordinal indices. The indices 1 and 2 are the same for spans that exceed 1.

These properties do not prove the fundamental property individually. In particular, the upper bound on BMS cannot be directly derived from a finite width or a finite number of interfaces. Currently, there are already:

$$
\mathcal B_{\rm std}\hookrightarrow\mathcal I_{<01},
$$

See [Unconditional BMS lower bound](<IBLP-01-unconditional-BMS-lower-bound.md>).

A finite number of BMS hosts or other strongly anti-ordered embeddings must be provided for the entire closure of each A_n, in order to obtain a situation where 01 is exactly equal to the BMS limit.

## 10. is a reviewable procedure and audit boundary.

The original definition remains unchanged. Complete condition verifier: complete_safe_class.py (Historical reference: `complete_safe_class.py`).

check_complete_safe_closure.py (Historical reference: `check_complete_safe_closure.py`) Directly calls the original IBLP, testing all control types, including zero interfaces that were unresolved in the previous round. It also independently generates patterns that satisfy D, not just sampling from known seed paths.

A bounded operation that is completed in one step:

- 2, 158 states; contains 251 non-successor zero interface control states;
- 3,894 retain the original copy of the working template;
- 5,841 are non-successive real expansions,627 are successor checks.
- 51,333 primary completion calls have no effect, and49,321 marked completion calls also have no effect.
- There are 120 independent roots, 1, 667 independent prefixes.
- The actual seed interface numbers cover 1, …, 11; independent inputs include interface numbers 0, …, 4;
- In approximately 9.1 seconds, all cycles have a finite upper limit and there is a 25-second global budget.

The test checks that the entire output still satisfies D, that it is identical to the result of repeated truncation, and that the original comparison keys have strictly decreased. Finite verification is only used for error detection; all indicators and conclusions at the full depth come from the closed proofs in sections 3–8.

Also use check_small_safe_exhaustive.py (historical reference: `check_small_safe_exhaustive.py`) List all members that have no asterisk and no more than six lines: D There are a total of 4,855 patterns. Completed 8 , 422 Single Original Replication Verification 8 , 422 Only true expansion verification is performed; Native and tagged completions were called respectively 41 times and 151 times. None of them have any effect. approximately 2.1 Seconds. This exhaustive enumeration method covers all subsets of the ancestral path and all allowed step sizes. Does not rely on standard-generated history. The seven-line version was stopped at the 20 second budget. Clearly marked as UNKNOWN. Does not claim to have completed all seven lines of exhaustive listing.

The SHA-256 of the original iblp.py is once again confirmed to be `B8FFA27818BA6104DBB8FD110581C9898930EBF29E00B2C50065B0BBF7A137A3`. Same as at the beginning.

The previous two exploration scripts examined terminal barriers and type constraints in bounded states at 68, 776, and 67, 636, namely probe_terminal_barrier.py (historical reference: `probe_terminal_barrier.py`), probe_typed_barriers.py (historical reference: `probe_typed_barriers.py`). These observations guided the selection of conditions in this paper, but they are not intended as a universal proof.

The mathematical research paper has not been formalized in Lean, and no claim has been made to have it independently verified by machine. The original notation has not been modified, and there is no published repository. No submissions or pushes have been made; all computational processes in this round have been terminated.
