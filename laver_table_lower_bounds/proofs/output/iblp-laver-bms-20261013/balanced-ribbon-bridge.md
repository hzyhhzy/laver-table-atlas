# Direct expansion of BMS parent tables and ordinary BLP one-step simulations · [中文版](balanced-ribbon-bridge.zh-CN.md)

*English reading edition, translated with machine assistance. The title links to the dated Chinese manuscript.*

> Collected reading edition. The three main papers state the results of this collection.
> This edition retains the local proofs, their hypotheses and any withdrawals. Progress reports describe the state of work at the time.
> The locations of omitted passages on preset inputs are recorded in SOURCE_MANIFEST.json.
> The main papers give the numerical derivations for the natural parameters produced by the proofs. This historical note carries no additional Lean certification.

The one-time fixation of a regular BMS [1] expansion can be precisely encoded as several deletions plus one-time fixation of a regular BLP's M. And all are completely inactivated. After replacing the basic column indicators with the following IBLP-style conventions, This is the new representation of [2]. Therefore, there is no need to perform "iterate M until normal" in the basic column definition.

The new representation is merely a parent table representation of BMS, and does not claim to be superior. The top item at position 10 is strictly greater than the original BMS[10], corresponding to an explicit 38 row of BLP pattern. For this encoding, the general finite table size count is enhanced to a direct critical point subscript count: as long as the seed is implemented below j(γₖ₋₁), then there is a D₂(A[10])<q(K). It has not yet been proven that this pattern can be implemented below the endpoints of a smaller K, nor has the length of the descent been compared with the specified FGH values.

The independent implementation is denoted as anchored_parent_bms.py (historical reference: `anchored_parent_bms.py`), and the bounded verification is denoted as balanced_ribbon_probe.py (historical reference: `balanced_ribbon_probe.py`). The step-by-step identities in this paper are unified combinatorial proofs, and they do not replace universal conclusions with finite experiments.

## Direct Parent Table Notation

A formula is a finite sequence of terms P=(P₀,…,Pₓ. The j term is the parent sequence number list.

$$
P_j=(p_{j,0},\ldots,p_{j,h_j-1}),\qquad 0\le p_{j,r}<j.
$$

Write [] for an all-zero column. The empty sequence of columns denotes zero. Entry r of the list corresponds to row r of BMS. All higher rows omitted from the list are zero. We use the rules on the standard domain. A hand-written parent table can satisfy the structural constraints without being a standard term.

Recover the numerical matrix from the depths of the parent chains. For a missing entry put a_{j,r}=0,. For a listed entry put

$$
a_{j,r}=1+a_{p_{j,r},r}.
\tag{1}
$$

The column numbers are always referenced in the forward direction, so a finite scan from left to right is sufficient for calculation, without the need for ordinal descent searches. During comparison, the columns after restoration are subjected to the usual two-level lexicographical order, with the zero terms at the end of the columns being ignored.

### Fundamental sequence rules

The fundamental terms of zero remain zero, but zero's self-loop is not counted as a descent. For non-zero P:

- P[0] removes the last column.
- When the last column is empty, all indicators delete the last column.
- We set r=|Pₓ|−1, c=p_{x,r}, , d=x−c. First, we keep the first x columns. The positive indices are copied according to the following rules: the source columns c,…,x−1.

The bth copy is numbered starting from b=1, and its first column is divided into two parts:

$$
\begin{cases}
p_{x,t}+(b-1)d,&t<r\text{ and }p_{x,t}\ge c,\\
p_{x,t},&t<r\text{ and }p_{x,t}<c,\\
p_{c,t},&t\ge r\text{ and column }c\text{ contains this entry}.
\end{cases}
\tag{2}
$$

For each parent number p of the source sequence c<j<x, change it to

$$
p\quad(p<c),\qquad p+bd\quad(p\ge c).
\tag{3}
$$

When the index is n=1, only the first column of the first document is output. When it is n≥2, complete copies of n−1 are output. Therefore, each fundamental sequence has a clear finite cycle boundary. P[0] represents the column deletion, P[n] is the literal column prefix of P[n+1], and all positive indices yield the same replacement column at the position of the old deletion column.

The formula (2)–(3) is a parent table replication rule of BMS, as described in the previous [Ancestral simulation of parent table correspondence](<../iblp-bms-20260918/IBLP-01-BMS-lower-bound.md>). The first column that is not the head column inherits the old last column below the active row, and inherits the tangent point column above the active row. The parents that are not the head columns remain before the tangent points; otherwise, they are moved along with the copy.

The recursive parent function for BM4 can be verified directly: the low coordinates of the first column are the same as those of the old last column, so the parent remains unchanged; in the active row, the candidate values between the old last column and the critical point are all non-negative, and after decreasing to the critical point value, the search just continues as the parent search of the critical point. Higher rows are recursively induced by the parent chain. Non-first columns are induced by the row and the column number within the copy; the values within the same critical point subtree are added with a common offset, and the values outside the parent chain remain unchanged, giving (3). Starting from the seed and simultaneously inducing, the depth of the parent chain in the formula (1) is the original BM4 value. The entire zero high row is identical and will not change the parent table.

Therefore, if B(P) represents the original BMS value, then when n≥2

$$
B(P[n])=B(P)[n-1]_{\rm BM4}.
\tag{4}
$$

P[1] is a prefix that continues as the first new column after B(P)[1], which can be obtained through a finite number of operations using the original [0]. The convention of indices here does not indicate growth or progression; it simply aligns the fixed [2] with the next M below.

### The starting form above the top and BMS[10]

Define the n term of the outer top vertex A as

$$
A[n]=\bigl([],\underbrace{[0,\ldots,0]}_{n+1},
                 \underbrace{[1,\ldots,1]}_{n+1}\bigr).
\tag{5}
$$

Let B_h=(0^h)(1^h), S_h=(0^h)(1^h)(2^h). The original BM4 satisfies

$$
B_h=S_h[0],\qquad S_h=B_{h+1}[2].
$$

Therefore, B_h<S_h<B_{h+1}. The formula (5) represents S_{n+1}, which ultimately lead to BMS limits. The original seed B_h can also be obtained by deleting the last column from S_h, along with (4), the new standard domain is consistent, and the order type is precisely the BMS limit.

In particular

$$
\boxed{|A[10]|=|S_{11}|>|B_{11}|=|\mathrm{BMS}[10]|.}
\tag{6}
$$

This initial form is written out directly, without undergoing a massive M reduction to calculate it.

## BLP encoding for balanced port bands

Fix the height of the input matrix h, and fill in zeros for the rows that disappear in the offspring. Let it be w=h+1. The jth matrix column corresponds to a strip, with a base point.

$$
b_j=3+jw,
$$

The ports are b_j, …, b_j+h. First, keep the two fixed first lines of the ordinary BLP: (0,1,2):1 and (0,1,2,3):1.

For the port i=b_j+k:

1. k=0, or when the k−1 behavior of the column of the matrix is zero, release (0,i,i+1)), with a step size of 1.
2. Otherwise, assume that the parent sequence of that coordinate is c, and let it pass.

$$
(b_c,b_c+1,\ldots,b_c+k,
  b_j,b_j+1,\ldots,b_j+k,b_j+k+1),
\qquad L=k+1.
\tag{7}
$$

Denote the result as R_h(P). The formula (7) is of length 2k+3, with the last two points being i,i+1, which conform to the standard BLP definition. The entire encoding has 2+w·|P| rows.

In BLP, the Copied and M operations are implemented using [Qi, Chapter 2 of the fifth edition of the paper](https://arxiv.org/html/2501.06733v5). This section introduces the aforementioned encoding and the following single-step identities.

### The completion is always empty.

The only thing that needs to be considered is the odd-length rows of (7). The upper bound of fullcomp is b_j, and the lower bound is b_c+k. The rows located at b_j are fixed anchor rows (0, b_j, b_j+1)), with the item just before the third from the end being 0. Therefore, the first step of the ancestor scan reaches 0, which does not exceed the lower bound, and no points are inserted.

All the lines starting with 3.0 do not belong to the long lines that need to be completed. Therefore, each fullcomp of R_h(P) is an identity operation.

## One step of expansion corresponds exactly to one occurrence of M.

When the last column of **Proposition.** P is non-empty, let r be the highest non-zero row, and let k=r+1 be the next row. Delete the last h−k row from R_h(P), and then perform another ordinary M operation. The result will be exactly R_h(P[2]).

If the last column is empty, then delete the last row with w, leaving only R_h(P[2]). All the deleted rows are non-replicable three-zero rows.

**Proof.** only needs to be proven for non-empty cases. Let x be the last column number, and c be its r parent column. After deleting the tail, the last row is located at

$$
n=b_x+k.
$$

Given (7), the starting and ending points of the ordinary short replication are

$$
p=b_c+k,\qquad e=b_x,
$$

That is, copy the lines p, …, e−1. Note that e is the starting point of the current band, not the next port immediately adjacent to p; this is a key difference from the original IBLP ancestor band encoding.

Address transport is

$$
\phi(t)=
\begin{cases}
t,&t<b_c,\\
t+(b_x-b_c),&b_c\le t<p,\\
t+(b_x-b_c),&t\ge p.
\end{cases}
\tag{8}
$$

The middle section consists of all the continuous source ports listed in the last column, so there are no missing addresses; the two segments are exactly identical in translation. The maximum point of all the copied rows does not exceed e, therefore Copied is always defined.

The old end with ports 0,…,k−1, along with copies starting from the parent band at k, forms the first new band. This new band inherits the old end columns below the coordinate r, and inherits the parent columns above the coordinate r, which is exactly the case of (2) at b=1. The remaining intact bands of the source block are shifted accordingly; the addresses of the parent band before c remain fixed, while the other addresses are shifted, which is exactly the case of (3).

The copy ends at e−1, precisely the last port of the old penultimate ribbon. No half-ribbon remains to reduce. The output row count is

$$
n+e-p-1=2+(2x-c)w,
$$

The number of columns after a bad block copy of BMS is 2x−c. The output still has the same encoding, so all fullcomps remain empty. Thus, for M=Copied, the aforementioned equation is obtained. The zero-column case can be deleted line by line. Proof complete.

This macro performs the M operation at most once after deleting the h lines, without containing loops of unknown length that "terminate upon encountering a certain type." To execute the new marking [2], it is also possible to directly use (2)–(3), without running the M at all.

## The number of descent steps and the number of M occurrences

Let it be that from P, we repeatedly create new [2] up to zero, requiring a total of D steps, where the number of steps for non-zero final columns is C, and the number of initially all-zero columns is z. According to the simulation in the previous section, the BLP has exactly M instances of C; the rest are simply column deletions, never entering the E branch.

**Zero-column counting lemma.** Once positive BMS [1] expands to at most one new zero column.

**Proof.** The active cutpoint c is the zero-level ancestor of the last column x. The subtrees of the zero-level parent forest are contiguous in column order, so the bad blocks [c,x)] contain no columns with zero at the zero level, except for the column itself c. In a standard matrix, having zero at the zero level is equivalent to having zero in the entire column. In a single replication, only the first column can be all zero. The other replicated columns remain non-zero, with a non-negative numerical offset. Proof complete.

Each zero-end column step consumes one zero-column, so the total number of such steps does not exceed z+C. Therefore

$$
\boxed{C\le D\le 2C+z.}
\tag{9}
$$

For the seed z=1 of the formula (5), it follows that (D−1)/2≤C≤D). Therefore, the number of times of M differs from the required fixed [2] descent length by at most a constant multiple and an additive term, and there is no longer an unknown huge conversion factor.

The total number of steps in the complete actual process of BLP, T, also satisfies D≤T≤(h+1)D. Each counting step of both is explicitly listed.

## The column deletion count directly provides the lower bound of the order parameter.

The finite quotient potential function of the general BLP only controls the table size 2^{q(K)}. However, for this encoding, another method of row conservation can be used to directly control q(K), without any unproven cyclic threshold amplification lemma.

Take a fixed strip with height h≥3, and initially have a column with m>0. Divide the complete fixed [2] descending macro steps into four categories:

- u: Last column non-zero, active port k=h, bad block width d=1;
- v: Last column non-zero, d≥2;
- s: Last column non-zero, d=1 and k<h;
- z: Deletion of a completely zero final column.

Therefore, it is D=u+v+s+z. Here, z represents the number of column deletions in the process, not the initial number of zero columns from the previous section. Let the total number of row deletions in the actual BLP be δ.

### Three finite counting facts

**1. Conservation of the number of columns.** The net increase in the number of columns in the positive direction is d−1 ， The number of columns in the zero step has been reduced to 1. The final number of rows is zero. therefore

$$
z=m+\sum_{\text{positive step}}(d-1)\ge m+v.
\tag{10}
$$

**II. Number of rows deleted.** Deletes rows starting from h−k in each positive step, and deletes rows starting from h+1 in each zero step.

$$
\delta=\sum_{\text{positive step}}(h-k)+(h+1)z
       \ge s+(h+1)z.
\tag{11}
$$

In the class **III. u≤v+z** u, the M exactly duplicates one row without adding any more rows. Between two such steps, there must be a v or z step.

To prove the third point, it is necessary to examine the positive steps of the continuous d=1. During this process, the number of columns remains unchanged, the penultimate column Q remains unchanged, and the tangent point is always Q. If the u step occurs at the current moment:

1. If the height of Q is equal to that of h, the highest parent number at the top level of the last column after expansion inherits the highest parent number of Q, which is strictly earlier than Q. Therefore, the next step, d≥2, no longer belongs to this segment.
2. If the height of Q is less than that of h, the height of the last column after expansion is h−1. Subsequently, the height of the last column in each d=1 step is max(k−1, |Q|, which is still less than h. Therefore, u will not occur again until the next v or z step.

The entire descent must ultimately be completed through the z steps, and cannot end with the u. Each u is assigned to the first v or z that follows it. This ensures that no duplicate assignments are made, hence the use of u≤v+z.

Combining three facts:

$$
\begin{aligned}
D&=u+v+s+z\\
 &\le s+2v+2z\\
 &\le s+4z-2m\\
 &\le\delta-(h-3)z-2m.
\end{aligned}
\tag{12}
$$

Specifically, when h≥3, then D<δ. This argument uses only clear macro steps and finite integer counts, without treating the number of executions of M as an internal step in calculating a fundamental sequence.

### From the number of column deletions to the subscript of critical points

Assume there is an initial BLS realization with a fixed Iter(j) within it, and its end is γᵣ. All M maintain the end state; each del operation replaces the end with a strictly smaller named critical point. Therefore, after these δ deletions, the subscript of the end state strictly decreases, and

$$
\delta\le r-r_3,
\tag{13}
$$

Among them, γᵣ₃ are two fixed rows that start at the end of θ₃. M does not change θ₃; at the end, only these two fixed rows remain. All named points belong to the same set of critical points in the same Iter(j), which is a direct corollary of the general BLS transport lemma.

As long as the initial end conditions satisfy γᵣ≤j(γₖ₋₁)=γ_{q(K)−1}, then there is

$$
\boxed{D_2(P)<q(K).}
\tag{14}
$$

Here, the parameter that controls the order of the table is q(K), not the number of elements 2^{q(K)}. The formula (14) is a theorem with a clear initialization assumption; it does not require the small K initialization that is necessary for proof. The completeness of the reduction can be guaranteed by the known BMS well-ordering property, or by the ordinary M/del good basis relation after a given BLS implementation.

### Do not confuse the BLP rank in the paper with the BLP rank mentioned here.

The first term of the non-zero port rows must be at least 3, and it cannot be the successor or limit type of the paper; the zero rows cannot be copied. Therefore, in the complete reduction, only M and del exist. The f function of the paper does not increase parameters in either of these branches, hence

$$
f(R_h(P),m)=m2^m.
$$

The BLP rank defined in the paper is also zero. Here, the BMS order type refers to all the fundamental columns of the parent table notation, not the rank assigned to these BLP patterns by the paper. We are using the actual number of M steps; this explains why we need [Independent Stepwise Counting Lemma](<direct-step-bridge.md>) instead of directly using the original f value.

## The problem of small cycles is reduced to a clear finite implementation problem.

Take P=A[10], h=11, and the bases of the three bands are 3, 15, 27. Corresponding to BLP, there is

$$
2+3\cdot12=38
$$

Rows: All ports in the first band are zero rows; the positive ports in the second band have the first band as their parent; the positive ports in the third band have the second band as their parent. The last row is...

$$
(15,16,\ldots,26,27,28,\ldots,39),\qquad L=12.
\tag{15}
$$

If it is possible to construct a finite pattern in an algebra with fixed j, such that the endpoints do not exceed j(γₖ₋₁), where K is explicit and small, then the entire [2] decline has been preserved by the above M/del operation, and there is no need to provide a separate budget for the entire tail replication. The new column deletion theorem is then presented.

$$
\boxed{D_2(A[10])<q(K).}
\tag{16}
$$

Any finite BLP's universal κ subsequence implementation only assigns the κ₃₉ endpoints of this pattern, thus the corresponding K=F(38)+1 is maximal, which does not satisfy the original objective. This universal existence cannot be considered as a small cycle implementation.

Therefore, there are two independent gaps remaining in the current main line: the initialization of 38 within the small cycle endpoints, and the FGH comparison that is placed afterward as required by the user. The exponential loss in the size of the table to the order parameter has been eliminated by the special coding in this paper, but this does not mean that the initialization can be omitted.

The initial conditions have been weakened to [A highly 11 compatible mapping group and the upper bound on the third critical image](<ribbon-initialization.md>): It does not require the zero row to have BLS witness, and the witness of the second higher layer is automatically generated by the first. This is a simplification of the initialization requirements, and it is not a proof of the existence of small cycle initializations.

## Verification scope

The bounded test covers standard matrix random expansions with heights 1,…,13. A total of 1,796 inputs were verified, of which 1,633 were positive expansions. For each input, the test checks the correspondence between new representation indices 0,…,4 and BM4, the depth of the parent chain, prefix properties, the fullcomp identity for all original elements, the exact output of the one-time original M, as well as the zero column count lemma. The maximum number of inputs is 692 BLP rows, and 58 branches stop upon encountering resource protection, which is not considered a pass.

The completed code has not been tested. It has been verified that there are 14 counting trajectories that can end within a small bound, as well as 12 trajectories whose prefixes are truncated within 60 steps or 350 columns. The separation properties of zero-growing steps and the formula (12) have been examined. The truncated trajectory should not be considered as verification of a complete descent.

The total program time limit is 20 seconds, with single lines being 2, 500 lines, 100, or 000 storage entries. The current round should exit normally in about 8 seconds, without retaining background processes. The test is not evidence for small-cycle implementations, FGH comparisons, or global formalizations.
