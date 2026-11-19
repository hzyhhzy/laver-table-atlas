# Diagonal row Hardy compilation candidate · [中文版](diagonal-hardy-compiler.zh-CN.md)

*English reading edition, translated with machine assistance. The title links to the dated Chinese manuscript.*

> Collected reading edition. The three main papers state the results of this collection.
> This edition retains the local proofs, their hypotheses and any withdrawals. Progress reports describe the state of work at the time.
> The locations of omitted passages on preset inputs are recorded in SOURCE_MANIFEST.json.
> The main papers give the numerical derivations for the natural parameters produced by the proofs. This historical note carries no additional Lean certification.

Update: This list contains the universal formula (3), which has now been uniformly proven as [Any row of forest controllers](<diagonal-forest-hardy-proof.md>). The following text remains a partial derivation at the time of candidacy, and no longer represents the latest gap.

2026-10-14. By assigning a column number to each row of a matrix, the successor parameter of Hardy can be increased to an exact equality. The remaining full-term limits have not been proven. This paper provides a local coverage of its exact propositions, the parameters 1 and 2, as well as bounded checks; it does not declare any dominance over the specified FGH values.

All indices are the original BM4 indices. $Z$ represents the all-zero column, $s_P(1)$ represents the number of subsequent deletions of the fixed $[1]$, and the definition of $\Sigma$ is provided in [Counting upper bounds of ancestral coverage](<ancestor-cover-growth.md>).

## Candidate potential function

Definition

$$
K(M,x)=s_{\Sigma(MZ^x)}(1),\qquad x\ge1.
\tag{1}
$$

Here, only a single explicit transformation of finite matrices is used, without performing a descent of an unknown length in advance. All inputs are standard parent table matrices; the finite-size standard diagonal chain coverage ensures that the descent terminates in a fixed manner.

The Hardy successor step $(MZ,x)\mapsto(M,x+1)$ satisfies

$$
\boxed{K(MZ,x)=K(M,x+1),}
\tag{2}
$$

Since the underlying matrices on both sides are identical. The endpoint $K(\varnothing,y)$ is a fixed indicator count of a row-depth sequence $0,1,\ldots,y$, which requires at least $y$ to evaluate according to a row forest.

Therefore, to prove $K(M,x)\ge\mathcal H_M(x)$ along a finite Hardy computation, it is only necessary to complete the missing parts.

$$
\boxed{K(M,x)\ge K(M[x],x)
\quad\text{when }M\text{ has a nonzero last column and}x\ge1.}
\tag{3}
$$

A stronger and sufficient combinatorial proposition is: from $\Sigma(MZ^x)$, through a finite number of $[0]$, $[1]$ steps, one can obtain a matrix that covers $\Sigma(M[x]Z^x)$. Here, coverage refers to ancestral coverage, without the requirement of literal equality or the original trajectory passing through the latter word-for-word.

If (3) holds for all normative matrices and all positive parameters, then by calculating and applying (2), (3) along the known termination of $\mathcal H_{W(B_{11})}(10)$, the endpoint is given by $s_{P_*}(1)\ge F_{B_{11}}(10)$. Combining this with the seventeen-row capacity bounds already proven in another paper, $q(5)>F_{B_{11}}(10)$ can be completed. The premise of this corollary, (3), has not yet been completed.

## Swap the diagonal rows with the positive last columns

When the last column of $M$ is non-zero, there is a direct

$$
\Sigma(M)[n]=\Sigma(M[n]).
\tag{4}
$$

Move the original activity line up one row; add 1 to the entire parent number, and the new 0 line has a parent pointer that points to the adjacent rows ahead. If the original bad block width is $d$, the replication offset for the 0 line is also $d$, so the column numbers remain continuous after replication. The remaining lines are transported according to the original rules, resulting in (4). The indicator 0 also clearly satisfies the conditions.

If $M$ has zero last column, then (4) does not hold: the last column of $\Sigma(M)$ still has a new parent at the 0 row. This is precisely why (2) uses a zero-column tail to store parameters, and cannot simply use $\Sigma$ as an order-preserving embedding.

## Unified Local Coverage of Parameters One and Two

Let $m=|M|$ be the original terminal column, with the parent columns being $p$, $d=m-1-p$. The following assertion holds for the norm matrix of any non-zero terminal column, not only for the two seed columns.

**Parameter 1.** continuously takes twice $[1]$ after $\Sigma(MZ)$, covering $\Sigma(M[1]Z)$. The covering map is

$$
f(j)=\begin{cases}j&j<m,\\j+1&j\ge m.\end{cases}
\tag{5}
$$

**Parameter 2.** continuously takes five times $[1]$ from $\Sigma(MZ^2)$, covering $\Sigma(M[2]Z^2)$. Covering map is

$$
f(j)=\begin{cases}
j&j<m,\\
j+3&m\le j<m+d,\\
j+5&j\ge m+d.
\end{cases}
\tag{6}
$$

### Verification by replication block

Write $\Sigma(M)=ABC$, where $B$ is the bad block from the controlling parent to the previous column of the last column, $|B|=d$, $C$ is the last column. $X,Y$ are the consecutive two children of the new row 0, and they have no other rows. The subscript indicates the corresponding block after replication according to the active row, not just changing the numerical label.

The two steps of the parameter 1 are:

$$
ABCX\longrightarrow ABCC\longrightarrow ABCB_1C_1.
\tag{7}
$$

Skip the intermediate retained $C$, $AB B_1$ exactly cover the required original expansion; the 0th row of the final $C_1$ has a parent link at the end of the new block, and its excess height will not hinder its use as a parameter zero column. This results in (5).

The five steps of the parameter 2 are:

$$
\begin{aligned}
ABCXY&\longrightarrow ABCXX\\
&\longrightarrow ABCXCX\\
&\longrightarrow ABCXCC\\
&\longrightarrow ABCXC B_1C_1X_1C_1\\
&\longrightarrow ABCXC B_1C_1X_1 B_2C_2X_2.
\end{aligned}
\tag{8}
$$

Retaining the symbols $AB$, the first one being $B_1$, and the last one $B_2C_2X_2$, we obtain (6). For the parent of the active row below, the second block continues with the old last column template from the first part; the active row and above inherit the parent of the original critical point. The parents of the remaining copied columns are moved within the block and fixed outside the block. Therefore, the two $B_i$ correspond to the two copies of the original $M[2]$ side by side. The $C_2,X_2$ row at the 0 position constitutes the two required consecutive children; the source has no parent edge requirements in the remaining rows. This verifies the coverage, not just the equality of the number of columns.

According to the counting coverage theorem, (3) has been proven for parameters 1 and 2. It still cannot complete the Hardy comparison, as a Hardy calculation starting with 10 would continue to increase the number of parameters.

## Bounded evidence and the subsequent universal question

Test the parameters for 189 different short specification matrices (including standard descendants and $W$ images).
1. 2, 3, 4: Fix the steps $[1]$ to cover the corresponding ones in steps 2, 5, 13, 48
$\Sigma(M[x]Z^x)$, with a total of 756 items, no failures or resource interruptions have occurred. The results of parameters 3 and 4 are currently only based on limited evidence, and no generalizations can be made for any $x$ based on these findings.

Another direct comparison of the early diagnosis of the huge successor count only completes 2 items, while the remaining 390 items remain undetermined. This indicates that it is advisable to prioritize the proof of the covering template for finite structures, rather than continuing to brute-force calculate the huge decrease values.

The next step requires a unified combinatorial induction on the length of the parameter tail chain $x$: to explain how zero-layer replication and active row replication generate sufficient original bad blocks, and to retain zero-layer ancestor chains that cover the number of parameter columns required to be $x$ at the end. The statements "there are already many copies" or "the number in the 0th row of the last column is already very large" should not be considered as proof of coverage alone.
