# Finite-row upper bounds of non-standard BMS: Ancestor coverage simulation · [中文版](BMS-nonstandard-row-bound.zh-CN.md)

*English reading edition, translated with machine assistance. The title links to the dated Chinese manuscript.*

> Collected reading edition. The three main papers state the results of this collection.
> This edition retains the local proofs, their hypotheses and any withdrawals. Progress reports describe the state of work at the time.
> The locations of omitted passages on preset inputs are recorded in SOURCE_MANIFEST.json.
> The main papers give the numerical derivations for the natural parameters produced by the proofs. This historical note carries no additional Lean certification.

2026-09-18. This paper supplements a BMS lemma required in the reverse comparison with ACD `123595`. This is a paper-based argument, not formalized in Lean; finite program checking is discussed in another section, and does not serve as a universal proof.

The ACD closure gap recorded in Section 7 of **Subsequent updates:**. Subsequently, it has been proven in writing by K=BMS (Historical reference: Completing the piecewise invariant of (`ACD-123595-equals-BMS.zh-CN.md`). This article also extends the argument covered in this article to any finite number of colors on the left side of the figure. The pending status in the following text is retained as a historical record.

## 1. Conclusions and the Meaning of "Non-Standard"

Let the ordinary BMS seeds be denoted as

$$
B_h=(0^h)(1^h),\qquad h\ge1,
$$

Use the original rule for short fundamental sequences (indices 0 with column deletion). Let

$$
D_{h,m}=(0^h)(1^h)\cdots((m-1)^h).
$$

For m≥1, the original formula is directly given.

$$
\boxed{D_{h,m}=B_{h+1}[m-1]<B_{h+1}.} \tag{1}
$$

The conclusions required and proven in this article are: one h Line, m column **The parent table is valid.** Finite BMS Matrix M ， Even if not reached from the standard seed point, There are also strict criteria for the values of BMS in the original expansion relationship. and

$$
\boxed{\rho(M)\le |D_{h,m}|<|B_{h+1}|.} \tag{2}
$$

Here, $\rho$ represents the well-founded rank of the original expansion, which does not refer to the arrangement of all non-standard matrices in their original numerical lexicographical order. It specifically covers the standard parent table domain used in this paper: each row entry represents the depth of the corresponding parent chain, with positive entries having parent items. The parent table is recovered through row-by-row parent searches using a standard BMS. The standard expansion maintains this domain. Zero rows can be deleted or filled in; empty matrices are assigned the value 0.

Do not include the missing parent items in the "arbitrary numerical matrix". For example, the first column is non-zero, or there are positive numbers in a certain row, but no parent can be found in the lower row below. Therefore, it cannot be directly fed into the NER expansion formula that depends on that parent item. Nor is it necessary to demonstrate all possible non-standard/fault-tolerant expansion versions here.

The candidate projection for ACD is precisely the parent chain depth matrix, and thus this range is sufficient.

## 2. adopts the normal BMS parent table formula

Let $P_q(j)$ denote the parent item of the qth row, and $p\prec_q j$ denote the non-empty parent chain ancestor relationship. Each row represents a forest, where the ancestors of higher rows are also ancestors of lower rows.

Let the highest parent of the last column x be r, whose parent is c=Pᵣ(x),L=x−c, and

$$
\phi_b(i)=\begin{cases}i&i<c,\\i+bL&i\ge c.\end{cases}
$$

The ordinary BMS expansion satisfies the following parent table formula:

- The old prefix j<x remains unchanged.
- The parent of the bth non-first replication column j+bL(c<j<x) is the $\phi_b(P_q(j))$.
- The bth first column c+bL in q<r is the parent of
$\phi_{b-1}(P_q(x))$ becomes $P_q(c)$ when q≥r.

The text continues as follows: The parent item is missing and is still read as missing. This is a lemma for the original parent table replication of BMS, not a new definition of expansion. The original mathematical source is marked as [Hunter's BMS well-ordering paper, Lemma 2.5](https://arxiv.org/abs/2307.04606). The local original `BM.ts` and the existing parent table Lean module also use this set of formulas.

These formulas also illustrate that the parent chain depth normativity is preserved in the expansion: non-leading column transports the same parent chains; the leading column in the lower row continues with the old last column parent chains, while the higher rows inherit the critical point parent chains, with numerical updates exactly corresponding to the chain length.

## 3. does not require isomorphism, only ancestor coverage is required.

For the source matrix M and the standard target matrix N, a strictly increasing column mapping f is called a coverage if:

1. When M is not empty, f maps the source end column to the target end column.
2. Every source ancestor relationship holds in the same row of the target.

$$
p\prec_q^M j\ \Longrightarrow\ f(p)\prec_q^N f(j). \tag{3}
$$

The target allows for additional columns, additional ancestors, and higher rows. It is not required that "no target edges exist if there are no source edges." It is sufficient to check the direct source parents, as the target ancestor relationships are transitive.

Any h row and m column that are of type M are covered by the standard Dₕ,ₘ: let f(j)=j be taken. Any earlier column of the diagonal chain is a ancestor of any later column in each q<h row. Therefore, the initial coverage does not depend at all on the M itself and its standard.

## 4. Local Preparation: Remove redundant ancestor targets that hinder control

For non-empty targets N, denote T(N) as first taking `[1]`, then using `[0]` to truncate back to the original width. When the target control line R and the control parent p are performed, the new last column satisfies

$$
T(N)_x(q)=\begin{cases}
N_x(q),&q<R,\\
N_p(q),&q\ge R.
\end{cases} \tag{4}
$$

It is a non-empty, real, finite, decreasing sequence. The original prefix remains unchanged; the last column decreases strictly in the Rth coordinate, while the lower coordinates remain unchanged. All coordinates are constrained by the finite maximum value of the initial prefix and the last column, hence the same width T cannot be executed indefinitely. It is not necessary to make a well-ordering assumption for the global lexicographical order of non-standard matrices here.

Now, the control behavior of M is governed by x, which in turn is controlled by r. The parent is c, and N covers M through f. Because of $f(c)\prec_r^N f(x)$, the control lines of N are R≥r.

- If R>r and T maintain all the ancestors of the last column of q≤r, then they maintain all the relationships required by the source.
- If R=r and the target direct parent is p>f(c), then f(c) is the rth ancestor of p.
T inherits from the r row the ancestor of p, thus retaining f(c) as well as the earlier source ancestors it covers. The relationship of q<r remains unchanged, and there are no requirements for the source columns in q>r.

The coverage of all non-terminal columns remains constant. Therefore, as long as the target control is not `(r,f(c))`, the aforementioned T can continue and maintain coverage. The target cannot become an empty terminal column, as this would result in the loss of the r ancestor f(c) that still needs to be retained. Given the finiteness of T, it is certain that a finite number of steps will be required to achieve this.

$$
\boxed{R=r,\qquad p=f(c).} \tag{5}
$$

This preparation is the missing step from the previous "target excess edge blocking control".

## 5. synchronous replication maintains coverage

First, handle the index 0 or the source empty final column: the target iterates `[0]`, stopping at the end of the second-to-last source column in the image. It strictly descends and covers the source after deletion. When the source is deleted to empty, the target also stops at empty.

In other cases, first perform the preparations in section 4, and then proceed as follows:

$$
L_M=x-c,\qquad L_N=f(x)-f(c).
$$

The source and target both take the same positive index n. The unreplicated source prefix is retained as f; each replicated block is defined as follows.

$$
f_n(j+bL_M)=f(j)+bL_N
\qquad(c\le j<x,\ 1\le b\le n). \tag{6}
$$

This is a strictly increasing column mapping. The following sections will verify (3) block by block.

The chain starting from **Non-leading replication columns.** is transported along with the covering chain in the target. If the parent chain stops within a block, its target chain stops within the corresponding target block; if it passes through a tangent point to enter a shared prefix, it continues to be connected to the same shared prefix in the new first column. The continuation of the tangent point at each step is guaranteed by the following first column formula.

**First copy column, q<r.** both sides inherit the q row parent chain from the previous column template. The old columns cover all the source q ancestors, and c is the lower ancestor on both sides. Therefore, the existing coverage chain still covers each source ancestor after being spliced with the previous block column.

**First copy column, q≥r.** inherits the old cut points from the q row ancestors on both sides, without retaining the r row control edges of the old last columns. The old cut points are covered by f(c), so the same holds true.

Using the three cases described from left to right, block by block, we obtain a complete coverage of the entire output. If there are additional columns that do not belong to the fₙ image at the end, we can use `[0]` to truncate to the last point of fₙ; the ancestors only point to the left, so truncation does not disrupt the coverage.

In summary, **Any cover can simulate every step of the source.**:

$$
(M,N,f),\ M\to M[n]
\quad\Longrightarrow\quad
N\to^+N',\quad N'\text{ covers }M[n]. \tag{7}
$$

All target steps are actual implementations of the original standard BMS, hence the target standardness remains intact. The arbitrary coverage proposition is not replaced by the statement that "the source/target happens to come from a selected common history."

## 6. takes the minimal standard cover, resulting in a rank upper bound.

The standard BMS is known to have a well-order. For each M, let e(M) be the smallest of all standard covers of the target. The 3 section provides a cover, hence the set is non-empty; e does not depend on the source generation history or any arbitrary choice.

If M→M[n], starting from e(M) and one covering map, using (7) we obtain N':

$$
e(M[n])\le N'<e(M). \tag{8}
$$

Therefore, $|e(M)|$ is the strict ordinal metric of the original expansion, where the original expansion is well-founded, and its rank satisfies

$$
\rho(M)\le |e(M)|\le|D_{h,m}|<|B_{h+1}|.
$$

This proof is (2). It does not claim that e maintains **The numerical ordinal order of any two non-standard matrices**. If the source domain itself is a finite descending comparable initial segment, then (8) further provides an order-preserving embedding of that source domain.

## The actual assistance and remaining gaps of 7. to ACD `123595`

Let K=ACD(1, 2, 3, 5, 9, 5). The candidate projections for K[n] are

```text
(0)(1)(2)(3,1)(4,2,1)
(3)(4,1)(5,2,1,1)
(4)(5,1)(6,2,1,1,1)
...
```

The first five columns are fixed, followed by n three-column blocks. Its non-standard nature does not hinder the use of the upper bound described in this text. For n≥1, the number of rows is n+3 (three rows are sufficient for n=0), so if the projection remains the original expansion on all descendants, a standard BMS upper bound Bₙ₊₄ for the entire K[n] descendants is obtained.

**What has not yet been proven is not the finite number of lemmas in this paper, but the full descendant closure of the ACD projection.** needs to be proven as follows: Every actually used head is always a certain pure zero complete ancestor graph Qᵣ₊₁; it does not insert other ancestor graphs during reduction; replication does not transform it into a higher or different type of head; each threshold ancestor still corresponds to the parent search of the ordinary BMS, and the seams are completely consistent.

`probe_acd_bms_upper.cjs` This round of finite inspection has covered 4, 094 states, and 1, 934 actual pairing expansions. These candidate properties have not failed in the matrix level exchange; there were 437 interventions using width strategies, but not full depth searches. It cannot replace the above inductive reasoning. Therefore, here it is **No announcement of K=BMS, K well-order or ACD global well-order**.

If this projection lemma is completed later, then any standard G below K can be mapped to its projection's smallest standard cover e: Due to the real descent comparability and (8), a strict order-preserving mapping is obtained for all standard BMSs below K; Merge with existing reverse embeddings, which can prove that K is precisely a BMS limit.

## 8. originally involves verification and resource constraints

`check_bms_raw_cover.cjs` loads the original NER `BM.ts` without writing a separate BMS expander. It checks the preparation steps for any given coverage and the ancestor relationships of all rows after index replication. It includes a random parent table depth matrix, as well as instances of the candidate projections mentioned above by K[n].

The current round has completed 3, 586 source steps of simulation, 122, 783 preparations for reduction, 129, 985 coverage checks, with no failures. 30 paths stopped at single preparations 1, 200 steps, and 4 paths stopped at width limits; the program reports these stop counts, but does not consider stops as completion of paths, nor does it use them to prove universal theorems. The remaining 179 paths have completed the scheduled bounded path checks. Approximately 2.7 seconds have passed, with RSS 101 MiB. Global limits are 20 seconds, 2, 000 tens of thousands of computational resources, 384 MiB Node heap, 640 MiB RSS.

A batch of tasks that did not have upper limits prepared for each path was returned at a workload of 2,000, and the status is unknown. Only 631 source steps have been completed; these tasks are not mixed with completed batches. All processes have exited.

```text
node --max-old-space-size=384 check_bms_raw_cover.cjs
node --max-old-space-size=384 probe_acd_bms_upper.cjs
```

The mathematical research paper is presented as it is, without any modifications. No submissions or pushes have been made.
