# Single-file lower bound proof: Minimum dependency audit at the FGH endpoint · [中文版](FGH-standalone-dependency-audit.zh-CN.md)

*English reading edition, translated with machine assistance. The title links to the dated Chinese manuscript.*

> Collected reading edition. The three main papers state the results of this collection.
> This edition retains the local proofs, their hypotheses and any withdrawals. Progress reports describe the state of work at the time.
> The locations of omitted passages on preset inputs are recorded in SOURCE_MANIFEST.json.
> The main papers give the numerical derivations for the natural parameters produced by the proofs. This historical note carries no additional Lean certification.

2026-10-14. Used for merging single-file proofs. This paper is not a new lower bound theorem; it specifies which local proofs must be included in the main text or appendices, and which external results can be cited with attribution. The following four substantial proofs and the BMS-side summary have been reread section by section.

## The strongest interface required for 1.

Adopt the original BM4 indicator, let $R_h=(0^h)(1^h)(1^h)$,
$D(h)=d_1(R_h)$, $B_r=(0^r)(1^r)$, 
$e_0=1,e_{u+1}=2^{e_u}$, $\ell(x)=\lceil\log_2(x+2)\rceil$.
The interfaces that need to be retained are:

$$
\boxed{h\ge r+2+\ell(x),\ r,x\ge1
\quad\Longrightarrow\quad D(h)\ge e_{F_{B_r}(x)}.}
\tag{1}
$$

The old formula summary only writes the weaker $D(h)\ge F_{B_r}(x)$ in the prominent box, but the forest proof actually retains $e_y$ at the Hardy endpoint. It cannot be discarded in the transcription, and the tower function residues used for feedback should not be regarded as unproven new enhancements.

## 2. Minimum list of documents to be transported

### A. specifies the standard parent table, coverage, and finite control preparation.

Source: `output/new-notation-20260918/BMS-nonstandard-row-bound.zh-CN.md`, Section 2–5. It is necessary to provide at least the complete information:

- The original BM4 parent table's one-step formula includes the first copy of the lower row connected to the old last column, and the higher row inherits the tangent point.
- A strict increasing ancestor coverage definition with aligned last columns;
- $T(N)$: Take the original `[1]` and then truncate back to the original width.
- Its finiteness: the prefix is fixed, each row of coordinates has a fixed finite upper bound, and the last column decreases strictly in lexicographical order.
- When the control line is too high or the direct parent is later than the required parent, $T$ retains all ancestors of the source requirements.
- After reaching the same control line and corresponding tangent point, the column mapping of identical indicators and the proof of cross-seam coverage are carried out.

**It is not sufficient to simply say "just prepare the control items" or to quote a relative path.** This is precisely the key lemma that allows auxiliary non-standard matrices to be legally compared numerically.

Premise: The matrix belongs to a specified parent chain depth domain. The original parent search restores its parent table, and the higher row ancestor is also a lower row ancestor. It is not an arbitrary bare numerical matrix, nor is it an arbitrary left-oriented diagram. The domain of the auxiliary matrix used must be specified.

Status: There is a complete written argument available locally; no formalization using Lean. No remaining additional conjectures. The historical ACD projection closure problem at the end of this document is not involved in this proof.

### B. covers counting and row width exchange

Source: `output/iblp-laver-bms-20261013/ancestor-cover-growth.zh-CN.md`, the top two sections.

Please provide two items:

1. Fixed positive index orbits must pass through any of their column prefixes: retain the prefix at each step, with a length that does not decrease by more than 1.
The trajectory ends. Therefore, in A, only the macros `[0]`, `[1]`, and `[n]` can embed into fixed `[n]` trajectories, and each source column deletion step occupies at least one target column deletion step.
2. Explicit row width exchange: $R_h[1]$ covers $D_{h-1,3}$, and
$D_{k,m}$ is covered by a finite number of equally wide descending columns and a single `[1]` covering $D_{k-1,2m-2}$. Therefore, $R_h$ controls the fixed count of $D_{h-1-t,2+2^t}$.

Here, $D_{k,m}=(0^k)(1^k)\cdots((m-1)^k)$, do not confuse with the integer function $D(h)$. In the merged manuscript, the diagonal matrices can be referred to as $\Delta_{k,m}$.

State: Complete written argument, no new unproven premises. When proving non-standard source termination, only one terminated standard coverage of the target is required; the reverse assumption of source termination cannot be made first.

### C. A line of forest evaluation and precise FGH-Hardy transformation

Source: `output/iblp-laver-bms-20261013/fixed-index-growth-interface.md`. Only requires "forest evaluation of one-row matrices" and "FGH to Hardy exact transformations for any number of rows", without the need for repeated column inequalities and other historical issues.

Forest value: The concatenation of fetch operations, with node values being $2^{\text{value of the forest of children}}$. The limit step of `[1]` remains this value. The zero-column deletion reduces it to 1, so it is precisely the successor of the deleted number.

Transform $W$ by adding a zero first column and adding 1 to the original 0 row, without increasing the number of rows. It is necessary to list each item individually.

$$
W(0)=Z,\quad W(MZ)[n]=W(M)^{\frown(n+1)},\quad
W(M)[n]=W(M[n])\quad(M\text{ has a nonzero last column}).
$$

The independent zero initial block is executed from right to left, yielding $H_{W(M)}(x)=F_M(x)$, and it proves the computation is finite along the well-founded induction of **Standard source $M$**.

Premise: Standard BMS well-ordering. The $W(M)$ may be non-standard, and cannot be identified as a standard ordinal power without explicit specification. The inductive and subsequent normative coverage are sufficient to handle it, leaving no hidden fundamental assumptions.

### Complete local compilation of the Forest Controller with D.

Source: `output/iblp-laver-bms-20261013/diagonal-forest-hardy-proof.zh-CN.md`. Requires a substantial content from "Active Bad Blocks and Root Templates" to "Harding's Conclusion and FGH's Findings".

It is necessary to clearly distinguish between $\Sigma$ and the $E_b(F)$ with a root template, rather than simply stating "add one row of compensation parameters".

- Non-root Forest Endpoint: The target one `[1]` is strictly exchangeable with the forest one step away;
- Root Forest Endpoint: The target one-dimensional `[1]` creates a bad block and moves the remaining forest behind the new block.
- Each birth block has a point-to-point direct parent correspondence with the next copy of the original BM4.
- The frozen forest columns are skipped to obtain column-aligned coverage, rather than literal equality.
- The chain forest generates $e_x$ copies, with $e_x\ge2x$ being the ones that retain $x$ parameter columns.
Provide capacity;
- Hardy successor step is a literal identity, while limit step makes
$K(M,x)=s_{\Sigma(MZ^x)}(1)$ does not increase; the endpoint is $K(0,y)=e_y$, thus retaining the strong bound $K(M,x)\ge e_{H_M(x)}$.

Note that $\Sigma(W(B_r)Z^x)$ has exactly $r+1$ rows and $x+4$ columns. In B, taking $t=\ell(x)$ allows us to deduce (1).

State: Complete written argument, no experiments substituted for universal steps. The forest decoration and $\Sigma$ maintain the standard parent domain; the termination of the fixed orbits is obtained by the standard diagonal coverage of A, B.

## 3. refers to standard external facts that can be explicitly cited.

- Samuel Vargovčík's BMS Good Order Theorem: It applies only to the good order properties of standard BM4 domains.
<https://arxiv.org/html/2307.04606v2>.
- The formulas from the parent table of the same text can be cited as existing lemmas. However, the single-file manuscript should still include the formulas that are actually used.
List all items, indicating that the indicators used are from BM4 `[n]` (the old blocks are retained and supplemented with $n$ copies).

"Non-standard ancestor coverage", "counting preservation", "forest compilation", and the $W$ computational identities are newly proven chains locally, and they cannot be claimed to be fully included in the external BMS well-order theorem.

## 4. is written from (1) to the arithmetic that must still be explicitly stated in the feedback FGH formula.

Let $\Lambda[x]=B_{x+1}$, $\rho(x)=x+3+\ell(x)$, $T=D+2$ be given. For $x\ge2$, $h\ge\rho(x)$, 1) is given as follows:

$$
D(h)\ge e_{F_\Lambda(x)},\qquad T(h)\ge\rho(F_\Lambda(x)).
$$

The latter formula uses only $y=F_\Lambda(x)\ge3$, $\ell(y)\le y$, and $e_y\ge2y+3$. In addition, it is necessary to provide a clear finite recursive estimate for the long-chain parameters that satisfy $C_{\rm line}+2\ge\rho(F_3(256))$, and this cannot be stated as "a constant is sufficiently large." This estimate has been fully developed in the second part of the summary.

Finally, if it has been independently proved by Laver's side
$q(5)>D(T^{\circ(N+1)}(h))$, $N=D(T(h))$，
Set $x_i=F_\Lambda^{\circ i}(F_3(256))$. Then $T^{\circ i}(h)\ge\rho(x_i)$, $N\ge e_{x_2}\ge x_2+1$, so

$$
q(5)>e_{x_{N+2}}\ge x_{x_2+3}
=F_\Lambda^{\circ(x_2+1)}(x_2)=F_{\Lambda+1}(x_2).
$$

This is a lower bound for numerical iteration, not the construction of a new marker for structural hyper-BMS.

## 5. This round of audit conclusions

Within the aforementioned clear scope, no local unproven interfaces that are still considered as assumptions have been found. The single-file manuscript should contain the key proofs for A—D, rather than simply replicating the arrow chains summarized at the BMS end. It is particularly necessary to prevent three types of misunderstandings: using non-standard auxiliaries as standard forms, treating general ordinal sizes as fixed index counting monotonicity, and failing to retrieve the tower function residual without a valid basis after discarding $e_y$.

This audit does not replace the independent verification of Laver initialization, background transport, enumeration of the same global critical points, and witness of the feedback chain; these do not fall under the scope of FGH. No new long descent was executed, and there were no remaining computational processes.
