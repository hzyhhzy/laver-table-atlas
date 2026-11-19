# Compile Hardy parameter growth into a fixed BM4 decline using a single-line forest · [中文版](diagonal-forest-hardy-proof.zh-CN.md)

*English reading edition, translated with machine assistance. The title links to the dated Chinese manuscript.*

> Collected reading edition. The three main papers state the results of this collection.
> This edition retains the local proofs, their hypotheses and any withdrawals. Progress reports describe the state of work at the time.
> The locations of omitted passages on preset inputs are recorded in SOURCE_MANIFEST.json.
> The main papers give the numerical derivations for the natural parameters produced by the proofs. This historical note carries no additional Lean certification.

The independent entry for the BMS endpoint delivery is found at [General formulas and proofs summary](<BMS-fixed-index-to-FGH-summary.md>). There, a complete proof chain is summarized for any row number, any positive input quantity, and for quantities that do not depend on the Laver table.

2026-10-14. This paper proves the full lemma missing from the previous version of the diagonal row candidates: For any canonical parent matrix $M$ and positive integer $x$, if the last column of $M$ is non-zero, then

$$
s_{\Sigma(MZ^x)}(1)\ge s_{\Sigma(M[x]Z^x)}(1).
\tag{1}
$$

Combining the literal equality at the successor, this will terminate the Hardy computation into a fixed original BM4 $[1]$ successor count. Here, it is not about finding separate experimental paths for each parameter, but rather using any finite row forest to provide a unified step-by-step simulation.

The notation and indices follow [Quantitative Ancestor Coverage](<ancestor-cover-growth.md>): $[n]$ is the original BM4 index, $s$ only counts deletions of all zero columns; the new version of the parent table, $[2]$, is here represented by $[1]$. $\Sigma$ adds a column of all zeros and a row of consecutive column numbers; $Z$ represents the zero column.

## Purpose of canonical parent tables and ancestor coverage

The positive coordinates of the matrix correspond to the depth of the corresponding parent chain. The parent search is performed row by row, with the parent being to the left and the higher row ancestors also being lower row ancestors. The original BM4 expansion maintains this domain, as does $\Sigma$. Any such finite matrix has a standard diagonal chain coverage, and therefore its expansion is well-ordered.

The quantitative covering lemma used in the following text is as follows: If $U$ is covered by the ancestors of $V$, and the fixed $[1]$ of $V$ terminates with a decrease, then $s_U(1)\le s_V(1)$. The target does not have to be standard itself; the standard diagonal chain covering has already provided the required termination. The proof still involves embedding the steps of $[0]$ and $[1]$ in the target's fixed $[1]$ orbits, as in the covering simulation.

## Active bad blocks and root templates

Fix the $M$ with non-zero last column, make its highest parent $r$, and control parent as $p$. Write

$$
\Sigma(M)=A B_0 C_0,
\qquad |B_0|=d=|M|-1-p\ge1,
\tag{2}
$$

Where $B_0$ starts from the image of the original controlling parent, and continues until $C_0$ in the previous column. The new active behavior is $R=r+1\ge1$. $C_0$ satisfies:

- In the 0 row, the parent is the last column of the $B_0$.
- In the $R$ row, the parent is the first column of the $B_0$.
- Every parent line is within $B_0$;
- There are no parents above $R$.

The third point comes from ancestral nesting: the original controlling parent is the ancestor of all lower rows, so the direct parents of these rows do not precede the controlling parent. The newly added direct parent of the 0 row is adjacent to the preceding rows and also within the bad block.

A "root template" $C_b$ preserves the same internal parent number, only moving the block from $B_0$ to the block $B_b$ of the current length $d$.

## Decorate the root template with a finite row of forests

Let $F$ be any finite row of standard parent forests. Define $E_b(F)$:

- Replace each forest root with the complete $C_b$;
- For each non-root, only the parent at the 0th row is retained, along with the image to its forest parent. All other rows have no parents.

The $E_b(F)$ is immediately followed by the $B_b$. The forest roots are directly attached to the end of the $B_b$ row at the 0 position. Non-roots continue along the forest. The target is currently in the form of

$$
\text{frozen prefix}\ B_b E_b(F).
\tag{3}
$$

The freeze prefix can include previous bad blocks, roots, and counting sequences; it does not belong to the current active forest. There are no other $B$ blocks within the current active forest.

### The end point of a forest is not a root.

At this point, the target's last column only has the 0th row as its parent. Its bad root is the parent at that point in the forest, which will not enter the $B_b$th row. The target takes a single $[1]$, which happens to be...

$$
E_b(F)\quad\text{becomes}\quad E_b(F[1]).
\tag{4}
$$

If the first point to be copied is the root of the forest, then the original target remains at $C_b$, and after copying, it remains at $C_b$. The parent points that are all outside the bad blocks, namely $B_b$, remain unchanged. If the first point is not the root, then it is copied according to the rules for one-row parents. The parents of other forest columns move with the copies within the copied area, and remain fixed outside the area. This verifies item by item that (4), $B_b$), and the freezing prefix remains completely unchanged.

### A forest endpoint is a root.

The target last column is $C_b$, the active behavior is $R$, and the bad root is $B_b$ in the first column. Let $F^-$ delete this last root. The target is once $[1]$ retained with the old prefix $B_bE_b(F^-)$, and the entire block is copied.

$$
B_bE_b(F^-).
$$

The copied head $d$ becomes $B_{b+1}$, followed by exactly $E_{b+1}(F^-)$. All parents of the copied roots are originally within $B_b$, so they are moved to $B_{b+1}$ along with the block. Non-roots are still transported according to their forest parents. This results in a new active state.

$$
\text{longer frozen prefix}\ B_{b+1}E_{b+1}(F^-).
\tag{5}
$$

Therefore, a single forest deletion generates a new bad block, and the remaining forest is moved onto it. This is a goal BM4 step, not a massive reduction cycle hidden within the fundamental sequence rules.

## Every bad block that is born is exactly the next copy of the original fundamental sequence.

After generating the $b$th bad block, select the original $A$ and $B_0,B_1,\ldots,B_b$ from the target, skipping the frozen forest columns. These selected columns have a mapping that preserves the direct parent relationship with $\Sigma(M[b])$.

Prove by induction on $b$. When $b=0$, both sides are the deleted original prefix of $C_0$. The new block's first column inherits from the parent at $C_b$, which is below $R$. Therefore, it is placed in the corresponding position in $B_b$. In $R$ and above, the parent that inherits the old bad block's first column always points to the original shared prefix $A$. The parent of the new block that is not the first column is moved to the new block, while the ones originally in $B_b$ are fixed in $A$. This is the parent formula of the BM4, the $b+1$th copy. The new line at position 0 also conforms to this formula: the first column of the new block is connected to the last column of the previous bad block, and the remaining columns continue as a chain. The forest step never changes these selected columns. Therefore, the induction holds.

Run the activity forest until it is empty. Each target step corresponds strictly to one fixed $[1]$ in the forest, so the process is finite. At the end, the last column of the current $B_b$ becomes the final column of the entire goal. Maintaining the mapping to the direct parent also results in a ancestor coverage that aligns with the last column.

$$
\boxed{b=s_F(1).}
\tag{6}
$$

This conclusion applies to any finite row forest, not just an initial chain.

## The parameter tail chain provides a sufficient number of copies.

Take the forest $F_x$ as a depth sequence $0,1,\ldots,x$. The initial decoration matrix is exactly $\Sigma(MZ^x)$. Denote

$$
e_0=1,\qquad e_{x+1}=2^{e_x}.
$$

From a single line of forest evaluation, $s_{F_x}(1)=e_x$. Therefore, the previous section results in a fixed $[1]$ decline, which ends with coverage

$$
\Sigma(M[e_x]).
\tag{7}
$$

For each $x\ge1$, $e_x\ge2x$: $e_1=2$, the inductive step uses $2^{2x}\ge2(x+1)$. Therefore, after the prefix in $M[x]$, $M[e_x]$ still has at least more

$$
(e_x-x)d\ge x
$$

Column. The 0th row of $\Sigma(M[e_x])$ is a complete chain, so it covers the $\Sigma(M[x]Z^x)$th column. The first $|\Sigma(M[x])|$ columns are mapped to the identity, and the last $x$th column is mapped to the target's last $x$th column. The parameter columns have no parent edge requirements in higher rows, and the parent edge across the gap in the 0th row is covered by the target's ancestral chain. The same applies to the alignment of the last column.

By the Quantitative Cover Lemma,

$$
s_{\Sigma(MZ^x)}(1)
\ge s_{\Sigma(M[e_x])}(1)
\ge s_{\Sigma(M[x]Z^x)}(1).
\tag{8}
$$

The first segment of the activity forest simulation actually does not delete the target zero-length columns, so the counting within this segment remains equal; only weaker inequalities are used here. The formula (8) proves the universal formula (1) that is to be proven.

## The conclusions of Hardy and FGH

Let $K(M,x)=s_{\Sigma(MZ^x)}(1)$. The Hardy successor step satisfies the literal identity $K(MZ,x)=K(M,x+1)$, and the limit step is made by (8) so that $K$ does not increase. If Hardy calculates from $(M,x)$ to $(\varnothing,y)$, then

$$
\boxed{s_{\Sigma(MZ^x)}(1)\ge s_{\Sigma(Z^y)}(1)=e_y\ge y
=\mathcal H_M(x).}
\tag{9}
$$

No preset standard Hardy computation termination is assumed. For applications, the proven termination of $M=W(B_{11}),x=10$ is used, and the results are given by [Exact identity from FGH to Hardy](<fixed-index-growth-interface.en.md>) as $F^{\mathrm{BMS}}_{B_{11}}(10)$.

$$
\boxed{s_{P_*}(1)\ge F^{\mathrm{BMS}}_{B_{11}}(10),
\qquad P_* =\Sigma(W(B_{11})Z^{10}).}
\tag{10}
$$

Using [Seventeen-row capacity bounds](<ancestor-cover-growth.md>) again, we obtain a pure BMS conclusion.

$$
\boxed{D_2(R_{17})\ge F^{\mathrm{BMS}}_{B_{11}}(10).}
\tag{11}
$$

Here, it is $B_{11}=\mathrm{BMS}[10]$. Combined with I3 under $q(5)>D_2(R_{18})$, and the $D_2(R_{18})\ge D_2(R_{17})$ given by the ancestor coverage, the required chain is formally established.

$$
q(5)>D_2(R_{18})\ge D_2(R_{17})
\ge F^{\mathrm{BMS}}_{B_{11}}(10).
\tag{12}
$$

The final application of the Laver table is described in [Lower bound of the 32-period BMS](<laver-period-32-BMS-bound.md>). This proof uses the readily available linedness from the literature, without relying on the earlier marked completion initialization.

## Any number of rows and explicit losses for the input

The preceding argument does not depend on 11 or 10. For any integer $r,x\ge1$, let

$$
\ell(x)=\min\{t\in\mathbb N:2^t\ge x+2\}
=\lceil\log_2(x+2)\rceil.
$$

$P_{r,x}=\Sigma(W(B_r)Z^x)$ has $r+1$ rows and $x+4$ columns. Taking $h=r+2+\ell(x)$, the row widths are exchanged to give $D_{h-1-\ell(x),\,2+2^{\ell(x)}}$ which has exactly $r+1$ rows, with a width of at least $x+4$, thus covering $P_{r,x}$.

$$
\boxed{D_2(R_h)\ge F^{\mathrm{BMS}}_{B_r}(x)
\quad\text{provided that }h\ge r+2+\ell(x).}
\tag{13}
$$

When there is a surplus of height, use the monotonicity of fixed counting covered by ancestors, rather than the ordinal monotonicity of any FGH. In particular, for $\ell(10)=4$, this holds true for all $h\ge7$.

$$
\boxed{D_2(R_h)\ge F^{\mathrm{BMS}}_{B_{h-6}}(10).}
\tag{14}
$$

Here, 10 represents the numerical input for FGH, and $h$ can be any specified finite number. Fixing the input only results in a constant number of lines being lost; if the input also changes, the current apparent loss is $2+\ell(x)$, and there is no claim that the same number of lines are lost for all inputs uniformly.

## Independent verification and resources

diagonal_forest_compiler.py (Historical reference: `diagonal_forest_compiler.py`) checks at each step: the literal encoding of the current active forest, the internal parent of the root template, the correspondence between each birth block and the direct parent of $\Sigma(M[b])$, as well as the end coverage. This completes the complete trajectory of 1, 608 small control forests, for a total of 14, 070 steps, with a maximum width of 184, without any truncation. Additionally, there are 180 items that are consistent with the original value of BM4. Exit takes approximately 2 seconds. The full conclusion comes from the two types of local calculations and forest induction mentioned above; these limited checks only verify consistency of implementation.
