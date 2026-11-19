# Counting upper bounds of ancestor coverage and the number of rows to columns in BMS · [中文版](ancestor-cover-growth.zh-CN.md)

*English reading edition, translated with machine assistance. The title links to the dated Chinese manuscript.*

> Collected reading edition. The three main papers state the results of this collection.
> This edition retains the local proofs, their hypotheses and any withdrawals. Progress reports describe the state of work at the time.
> The locations of omitted passages on preset inputs are recorded in SOURCE_MANIFEST.json.
> The main papers give the numerical derivations for the natural parameters produced by the proofs. This historical note carries no additional Lean certification.

2026-10-14. This paper strengthens the existing ancestor coverage simulation with a fixed metric counting inequality, and proves a clear capacity bound that can be used in a Hardy compiler. All the $[n]$ here refer to the original BM4 metric. The new version of the parent table fixes the $[2]$ to be equal to the fixed $[1]$ here.

Let $d_n(M)$ denote the total number of steps taken to fix the value from $[n]$ to the empty formula, and let $s_M(n)$ denote the number of times the entire zero column is deleted. Therefore, we have $d_1(R_h)=D_2(R_h)$, $s_M(n)\le d_n(M)$. This paper does not assume that the fixed index counts of any two matrices are also arranged in the same direction when arranged in order of ordinal size.

## Ancestor coverage with fixed indices

Using [Ancestral coverage of non-standard parent matrix](<../new-notation-20260918/BMS-nonstandard-row-bound.md>): A strictly increasing column mapping $f:M\to N$ maps the last column to the last column, and maps each source row of the $r$th row to a non-empty ancestor chain of the $r$th row. The target allows for multiple columns and extra rows. The source can be non-standard, but it must belong to the standard parent table domain of the original BM4.

The steps of the old simulation have an important limitation: when simulating the source with $[n]$, the target only uses $[0]$, $[1]$, $[n]$. Specifically, it is as follows.

When the source and target columns are non-zero, and the control behavior is $r$, with the cut-off point being $c$, first repeatedly set the target to $[1]$ and then truncate it back to the original width. Each time, only the last column of the target is reduced, while retaining the ancestors required by the source, until the target's control line is $r$ and the direct controller is $f(c)$. The coordinates of the last column are constrained by a fixed prefix and the maximum value of the old last columns. Each time, they are strictly reduced in column lexicorder, so the preparation is finite. Then, both sides are synchronized to take $[n]$, transporting and covering the mapping block by block, and finally, the tail columns that are not mapped are truncated.

The reason for keeping the coverage is as follows: The new first columns below the control row follow the parent chain of the old last columns, while the control row and above follow the parent chain of the old cut points. The parent chains of non-first columns follow the transport of the copies. Cut points are ancestors of the lower rows, so when crossing the seams between new and old copies, the ancestor chains on both sides continue at the same cut point. When deleting the source end, the target directly intersects with the image of the second-to-last source column. Each source step corresponds to a non-empty target descent.

### Filling the trailing steps with fixed positive indicators

Fix the $n\ge1$. If $P$ is a column prefix of matrix $Q$, and the fixed $[n]$ of $Q$ terminates downward, then this downward process must pass through $P$: Each step retains the prefix obtained by deleting the last column, with the width decreasing by at most 1 at each step. Therefore, it is impossible to skip the width of $P$.

Also, since both $Q[0]$ and $Q[1]$ are prefixes of $Q[n]$, any index that takes the downward value of $0,1,n$ is a subsequence of the fixed $[n]$ trajectory. Each true step occupies at least one fixed $[n]$ step.

**Theorem.** If the canonical parent matrix $M$ is ancestor-covered by the canonical matrix $N$, and the fixation of $N$ terminates in the orbit of $[n]$, then for this $n\ge1$,

$$
\boxed{d_n(M)\le d_n(N),\qquad s_M(n)\le s_N(n).}
\tag{1}
$$

Prove that embedding the above macro steps into the fixed orbits of $N$. The target orbit is finite, therefore the source orbit is also finite. Each source step occupies a non-empty interval, resulting in the first equation. Each source successor step cuts off at least one column in the target; The non-successor steps of the positive index do not reduce the number of columns, so there must be a target deletion within this interval. The intervals from different sources do not overlap, resulting in the second equation. In particular, the standard time for $N$ can be used for all positive indicators. Standard BMS well-foundedness can be used as existing results, see [Proof of Vargovčík](https://arxiv.org/html/2307.04606v2).

In particular, for $H\ge h$, the column-by-column identity mapping gives a coverage of $R_h\to R_H$, hence

$$
d_1(R_h)\le d_1(R_H),\qquad s_{R_h}(1)\le s_{R_H}(1).
\tag{2}
$$

This is a proof of monotonicity for fixed counting, not a direct inference from ordinal sizes.

## One line replaced with a diagonally wide chain nearly twice the length

Write

$$
D_{k,m}=(0^k)(1^k)\cdots((m-1)^k),\qquad k\ge1,m\ge2.
$$

This is the standard matrix $B_{k+1}[m-1]$. If $k\ge2,m\ge3$, starting from $D_{k,m}$, perform the $m-2$ operations of "taking the $[1]$ part and then truncating back to the width $m$" on the last column. The prefix remains unchanged, and the last column is transformed in sequence.

$$
((m-1)^{k-1},m-2),\ldots,((m-1)^{k-1},1).
$$

At this point, the direct parent of the highest row is the first column. Taking another $[1]$, we obtain a matrix with a width of $2m-2$, where exactly $k-1$ rows of it are

$$
0,1,\ldots,2m-3.
$$

It covers $D_{k-1,2m-2}$ with column-by-column identity mappings. All actual steps are marked as 0 or 1, hence they are supplemented by fixed orbits and (1),

$$
\boxed{s_{D_{k,m}}(1)\ge s_{D_{k-1,2m-2}}(1).}
\tag{3}
$$

The total number of steps also has an inequality in the same direction.

On the other hand, there are four columns for $R_H[1]$.

$$
(0^H)(1^H)(1^{H-1},0)(2^{H-1},1).
$$

Take the 0, 2, 3 columns, which form a ancestral chain in the preceding $H-1$ row and cover the $D_{H-1,3}$. Iterate starting from a width of 3 (3), with the width being recursively increased by $m_{t+1}=2m_t-2$, thus $m_t=2+2^t$. The result is obtained.

$$
\boxed{s_{R_H}(1)\ge s_{D_{H-1-t,\,2+2^t}}(1)
\quad(0\le t\le H-2).}
\tag{4}
$$

If the canonical matrix $P$ has a height of at most $k$ and a width of at most $m$, then the diagonal chain $D_{k,m}$ covers $P$: Any strictly increasing column mapping is acceptable, as long as the last column is aligned. This is because any earlier column in each row is a ancestor of the later column. Therefore, (4) not only controls the standard matrix, but also includes non-standard auxiliary matrices that satisfy these finite size conditions.

## The current Hardy candidate only requires a capacity of seventeen lines.

Define $\Sigma(M)$ for the matrix $M$: Add a full of zeros first column, and assign a new first coordinate to each of the remaining columns, denoted as $1,2,\ldots,|M|$. The original coordinates are moved up. In the parent table, the $j$th old column $C$ becomes

$$
(j)\,\mathbin{{}^\frown}\,(p+1:p\in C).
\tag{5}
$$

This adds a new row; the 0th row is a complete ancestor chain. The new parent table is still restored from the original BM4 parent search. Let $W$ be the [Exact transformation from FGH to Hardy](<fixed-index-growth-interface.en.md>). One specific candidate for the target is

$$
P_* = \Sigma\bigl(W(B_{11})Z^{10}\bigr),
\tag{6}
$$

Here, $Z$ represents a all-zero column. $P_*$ has a 12 row and a 14 column. Taking the point (4), $H=17,t=4$), we obtain a diagonal chain $D_{12,18}$, which covers $P_*$. Thus, a strict result is obtained.

$$
\boxed{D_2(R_{17})\ge s_{R_{17}}(1)\ge s_{P_*}(1).}
\tag{7}
$$

The existing lower bounds for large row numbers are given by (2)

$$
q(5)>D_2(R_H)\ge D_2(R_{17})\ge s_{P_*}(1)
\tag{8}
$$

Among them, $H=g^{\circ258}(1)+2$, the axiomatic assumptions remain as I3. This step no longer lacks the interface regarding whether the "auxiliary matrix is standard" or "how to reach below the specified starting point".

The following formula originally constitutes the remaining gaps in this article, and is now filled in by [A unified proof for forest controllers](<diagonal-forest-hardy-proof.md>):

$$
s_{P_*}(1)\ge\mathcal H_{W(B_{11})}(10)
=F^{\mathrm{BMS}}_{B_{11}}(10).
\tag{9}
$$

The complete dependency chain used by Laver is shown in [Lower bound of the 32-period BMS](<laver-period-32-BMS-bound.md>). The use of published linedness input is avoided in marker initialization. The general number of lines and the version with general input are shown in [Forest Controller Proof Formula (13)](<diagonal-forest-hardy-proof.md>). The early local derivations of $\Sigma$ are preserved in [Diagonal row Hardy candidate](<diagonal-hardy-compiler.md>).

## Verification scope

ancestor_cover_growth.py (Historical reference: `ancestor_cover_growth.py`) independently checks coverage relationships, identical simulation, and explicit formulas for row-to-column transformations. This task involves 559 simulations, including 68,572 preparations for reduction; 22 paths have reached the upper limit for single preparations, marked as incomplete. Additionally, 130 row-width transformations, 90 cross-verifications with the original values BM4, as well as the (6) in the 12 row 14 column size and diagonal chain coverage are checked. The process exits in approximately 6 seconds; large complete reductions are not calculated. The conclusions based on the full count are derived from previous simulations and finite counting proofs, not from these samples.
