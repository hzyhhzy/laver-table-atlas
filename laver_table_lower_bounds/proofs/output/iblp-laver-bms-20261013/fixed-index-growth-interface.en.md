# Comparison interface between fixed index BMS decline and FGH · [中文版](fixed-index-growth-interface.md)

*English reading edition, translated with machine assistance. The title links to the dated Chinese manuscript.*

> Collected reading edition. The three main papers state the results of this collection.
> This edition retains the local proofs, their hypotheses and any withdrawals. Progress reports describe the state of work at the time.
> The locations of omitted passages on preset inputs are recorded in SOURCE_MANIFEST.json.
> The main papers give the numerical derivations for the natural parameters produced by the proofs. This historical note carries no additional Lean certification.

Update: The following columns in this text are the final numerical interfaces to be proven, which have been supplemented by [Quantification of ancestral coverage](<ancestor-cover-growth.md>) and [Diagonal Row Forest Controller](<diagonal-forest-hardy-proof.md>). The initial reduction, the lemma on row-duplication columns, and the exact identity from FGH to Hardy are retained in this text. The complete proof applied by Laver can be found in [Lower bound of the 32-period BMS](<laver-period-32-BMS-bound.md>), and the historical gaps below are no longer considered as the current state.

2026-10-14. The current lower bound for the Laver table that has been obtained is

$$
q(5)>D_2(R_H),\qquad
R_h=(0^h)(1^h)(1^h),\qquad
H=g^{\circ258}(1)+2,\quad g(t)=t2^t.
\tag{1}
$$

The formula (1) uses the same generation embedding as in I3, as seen in [Construction of the number of lines to BMS](<lined-front-insertion.md>). $D_2$ adopts the new fundamental sequence convention from the parent table, which equals the original BM4, fixing to $[1]$ until the total number of steps of the empty formula. It differs from the slow-growing function that only calculates the number of subsequent deletions.

The remaining task is to compare the right side with $F^{\mathrm{BMS}}_{B_{11}}(10)$, where $B_h=(0^h)(1^h)$ is used. It is allowed to sacrifice the number of rows, parameters, and constants, and a tight bound is not required.

## An inequality sufficient to achieve the goal

A sufficient condition that is hoped to hold is the existence of a clear small constant $c$, such that within an appropriate range

$$
D_2(R_{h+c})\ge F^{\mathrm{BMS}}_{B_h}(10).
\tag{2}
$$

It should be noted that how the $R_H$ of the formula (1) governs the decrease in the number of rows used cannot solely rely on their ordinal size. It is also possible to directly prove the formula for the number of rows lost with respect to the $H$, avoiding this interface. A linear or even more relaxed explicit number of rows overhead is acceptable, as long as the final result is indeed obtained.

$$
D_2(R_H)\ge F^{\mathrm{BMS}}_{B_{11}}(10).
\tag{3}
$$

The formulas (2), (3) are currently targets to be proven, not theorems that have already been established. In particular, the results in the following row do not prove them.

## A theorem stating that a row with fixed indicators is determined by repeated column compensations

Let $M$ be a standard row BM4 matrix. Define $s_M(n)$ as the total number of times the original BM4 $[n]$ is deleted by taking the original $M$ and removing all zero columns when it reaches an empty form. Let $E_d(M)$ be the operation of repeating each digit column continuously for $d$ times.

**Theorem.** For each integer $d\ge2$,

$$
\boxed{s_{E_d(M)}(1)\ge d\,s_M(d-1).}
\tag{4}
$$

The expansion index does not increase as the process progresses. The theorem merely reduces the successor count of any given fixed index $d-1$ to the successor count of the index 1 by changing the initial structure.

### Forest evaluation of a row matrix

A standard row matrix is a preorder depth list of a finite ordered forest. The root of each tree is denoted as 0, and the depth of the forest formed by its children is uniformly increased by 1. Denote $q=n+1$, and define the evaluation of natural numbers.

$$
V_q(\varnothing)=0,\qquad
V_q(T_1\cdots T_r)=\sum_{i=1}^r V_q(T_i),\qquad
V_q(\operatorname{node}(A))=q^{V_q(A)}.
\tag{5}
$$

Then $s_M(n)=V_{n+1}(M)$. It can be directly verified along BM4: deleting a terminal column of depth 0 reduces $V_q$ by 1; the positive terminal expansion remains $V_q$. The latter equation is $q^{u+1}=q\,q^u$ at the parent node of the last leaf: the original bad block plus $n$ copies, making a total of $q$ pieces. This equation holds when substituted with the ancestors' indices and the addition of the forest. Due to the termination of a row of BM4, the final value is zero, so the total number of subsequent deletions is exactly the initial evaluation.

### The tree structure of repeated columns

If $T=\operatorname{node}(A)$, repeat each item of the prefix order list $d$ times, so that the first $d-1$ roots become single-node trees; all children are connected to the last root. Therefore

$$
V_2(E_d(T))=(d-1)+2^{V_2(E_d(A))}.
\tag{6}
$$

This is a literal forest identity, and there is no need to guess whether the function values for different ordinals are monotonic.

### Structural Induction

Make a structural induction on the forest to prove $V_2(E_d(M))\ge dV_d(M)$. An empty forest and concatenation are obtained by addition. For a tree, set $a=V_d(A)$, and make the induction hypothesis and (6) given.

$$
V_2(E_d(T))\ge d-1+2^{da}\ge d^{a+1}=dV_d(T).
\tag{7}
$$

The last integer inequality holds for all $d\ge2,a\ge0$:

- When $a=0$, both sides are $d$.
- When $d=2,a\ge1$, $2^{2a}\ge2^{a+1}$.
- When $d=3,a=1$, $2+8\ge9$; when $a\ge2$
  $8^a\ge3^{a+1}$.
- When $d\ge4,a\ge1$, $2^d\ge d^2$, therefore
  $2^{da}\ge d^{2a}\ge d^{a+1}$.

This proves that (4). In the parent table representation, when there are duplicate columns, each parent number $p$ is changed to $d(p+1)-1$, indicating the last copy pointing to the parent column.

## Any row number FGH to Hardy exact transformation

The auxiliary matrix **Not required to be a standard BMS format** is still expanded according to the original BM4 numerical rules. For a $h$ row matrix $M$, the $W(M)$ is defined as follows: first add a full zero first column, then add 1 to the first coordinate of each column of $M$, while the rest of the coordinates remain unchanged. Therefore, $W$ does not increase the number of rows. In the parent table, first add empty columns, and then...

$$
[]\longmapsto[0],\qquad
[p_0,\ldots,p_r]\longmapsto[p_0+1,\ldots,p_r+1]
\tag{8}
$$

Transform the original columns. The new parent number points all forward, and the positive coordinates of the numerical matrix have no supporting holes.

**One-step identity.** Let $Z$ be the all-zero column, and $n\ge0$, the power on the right side represents independent concatenation:

$$
\begin{aligned}
W(\varnothing)&=Z,\\
W(MZ)[n]&=W(M)^{\frown(n+1)},\\
W(M)[n]&=W(M[n])&&\text{when }M\text{ has a nonzero last column}.
\end{aligned}
\tag{9}
$$

The last column of the second equation has the first coordinate as 1, and its bad root is a newly added all-zero first column. The original block is added with $n$ copies, which is exactly $n+1$ times $W(M)$. In the third equation, the original last column is non-zero, and the active row remains unchanged. Its bad root is still the original bad root, and the column number is overall added with 1. The overall first coordinate is added with 1, which does not change the parent search of the original non-zero coordinates. The parent chain of the higher rows also remains unchanged. The new 0- parent of the old all-zero columns is the additional first column, but it will not be inserted between the old non-zero coordinates and the old parent. Therefore, the determination of the numerical difference of each bad block and whether the rows have increased remains unchanged. The index 0 only deletes the last column and also satisfies the third equation. This proves that (9) does not invoke non-standard well-ordering properties.

Define the auxiliary Hardy computation

$$
\mathcal H_{\varnothing}(x)=x,\qquad
\mathcal H_{PZ}(x)=\mathcal H_P(x+1),\qquad
\mathcal H_P(x)=\mathcal H_{P[x]}(x)\quad(P\text{ has a nonzero last column}).
\tag{10}
$$

**Theorem.** For each standard BMS type $M$ and natural number $x$, the auxiliary calculation terminates, and

$$
\boxed{F^{\mathrm{BMS}}_M(x)=\mathcal H_{W(M)}(x).}
\tag{11}
$$

Prove a well-ordering for the standard $M$. The empty formula is given by $W(\varnothing)=Z$, and $x+1$. The limit formula directly uses the third formula of (9) and the induction hypothesis. If $M=AZ$, then the second formula of (9) produces $x+1$ parts of $W(A)$; each part starts with a full zero sequence, and the active bad blocks do not cross this first sequence, so they execute independently one after another. Each part transforms the current input $y$ into $F_A(y)$, and the final value is exactly $F_A^{\circ(x+1)}(x)$. The induction also provides a termination condition.

The above non-standard notation warnings should not be removed. For example:

$$
W((00)(11))=(00)(10)(21)
$$

Not a standard BMS format: Starting from the standard seed, before the second column becomes $(10)$, all subsequent columns must be cleared first; after the second column itself is reduced to one row, the subsequent expansion cannot regenerate the second row. Therefore, it is impossible for a third column $(21)$ to appear. Consequently, it cannot be claimed that (11) is a Hardy lower bound for standard BMSs with the same height, simply by maintaining the number of rows with $W$. Nor has $W(M)$ been identified as a standard ordinal power in the proof.

## Multiple lines of repetition and variable parameters are still two different issues.

A proof line depends on the finite forest evaluation formula for (5). This formula cannot be used for more than two lines, so any version with a certain number of lines for (4) has not yet been proven. Bounded multi-line checks can only be used to rule out error candidates.

Even if multiple lines of proof are presented, it only addresses the comparison between two **Fixed** expansion indices. The successor rule for FGH is to iterate the lower-level functions $x+1$ times, with each output serving as the input for the next iteration; the subsequent limit expansions will use the increased parameters. A structural transformation is also needed to generate sufficient subsequent replication budgets in these successor steps. Encoding the initial input 10 does not solve this problem.

The formula (11) reduces this gap into a specific problem: starting from a fixed standard BMS formula of $[1]$, governing $\mathcal H_{W(B_{11})}(10)$. The target auxiliary matrix is now completely clear: its three columns are $0^{11}$, $(1,0^{10})$, $(2,1^{10})$. Here, a simulation still needs to be constructed; one cannot simply assert the governing relationship based on a larger number of rows.

It should not be required that the entire $[n]$ subexpression after the repetition must appear verbatim on a fixed $[1]$ track. For example, take two rows $M=(00)(11)$, $d=3$: $E_3(M[2])=(00)^3(10)^3(20)^3$. Starting from $E_3(M)$ and fixing it to $[1]$, when the first $(11)$ has not been processed, the track is still greater than the target in that column. By the time it is processed, the subsequent columns have been cleared, and its one expansion results in only a $(10)$, so it is directly dropped below the target. Therefore, it cannot be proven that "the fixed track passes verbatim through the target." This does not refute the subsequent counting inequality, which allows for larger counts to occur on earlier branches.

## Bounded verification

forest_growth.py (Historical reference: `forest_growth.py`) uses (5) to directly calculate the count of one row beyond, and for small examples, it implements cross-verification step by step with (BM4. All large integers and time have an upper limit; instances that exceed this limit are recorded as unknown and not considered as inequalities being satisfied. The universal formula (4) is based on the above structural induction, not on these samples.

This enumeration covers all the 626 rows of the forest that do not exceed the 7 columns. It verified 1 and 709 duplicate column inequalities. Additionally, 1 and 421 items were not determined due to protection by large integers. The 100 small instances are consistent with the subsequent counts of the incremental implementation. All tests were completed normally, with no background degradation tasks occurring.

fgh_hardy_compiler.py (Historical reference: `fgh_hardy_compiler.py`) performs bounded verification on (9), and compares the FGH stack machine with auxiliary Hardy computation on small inputs. These checks verify the local consistency of implementations and identities; the universal conclusion of equation (11) is given by the above induction. This coverage covers the local identities from 1 to 14 lines, with 5,600 local identities, where 112 terms are implemented with the original value BM4 for cross-verification; 88 numerical calculations yield equal results, and 74 terms are not determined within the resource limit.
