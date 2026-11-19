# BMS Fixed Index Downward Movement and the Docking of FGH: Summary of Conclusions and Proofs · [中文版](BMS-fixed-index-to-FGH-summary.zh-CN.md)

*English reading edition, translated with machine assistance. The title links to the dated Chinese manuscript.*

> Collected reading edition. The three main papers state the results of this collection.
> This edition retains the local proofs, their hypotheses and any withdrawals. Progress reports describe the state of work at the time.
> The locations of omitted passages on preset inputs are recorded in SOURCE_MANIFEST.json.
> The main papers give the numerical derivations for the natural parameters produced by the proofs. This historical note carries no additional Lean certification.

2026-10-14. Based on the scope of tasks after this iteration, only the following is summarized for **BMS terminal**: determining the length of the descending sequence that is fixed at one time, and how to control the specified rapid growth of function values. The following does not use Laver tables, linedness, or I3, nor does it assume any subsequent connection with these concepts.

The conclusion has been proven in written form, but has not yet been formalized in Lean. The standard BMS well-ordering property is used as a known theorem; the rest consists of one-step identities of the parent table, coverage simulations, well-founded induction, and finite integer counts.

## 1. Accurate Theorem

Let the brackets represent a column of the matrix, and denote as follows:

$$
B_r=(0^r)(1^r),\qquad R_h=(0^h)(1^h)(1^h).
$$

All fundamental sequence indicators use **The original BM4**: `[0]` for column deletion, positive indicators `[n]` retain the old prefix, followed by a $n$ copy of the bad block. Let

$$
D(h)=d_1(R_h)
$$

It starts from $R_h$, always taking the original `[1]`, until it reaches the empty formula **Total number of steps**. It equals the number of times the new representation of the parent table in this directory is fixed at `[2]`. Do not confuse it with the new representation `[1]`.

FGH has the following conventions, where $Z$ represents a zero column:

$$
F_\varnothing(x)=x+1,\qquad
F_{MZ}(x)=F_M^{\circ(x+1)}(x),\qquad
F_M(x)=F_{M[x]}(x)\quad(M\text{ has a nonzero last column}).
\tag{1}
$$

The superscript $\circ k$ of a function indicates a composite iteration of $k$ times. Let's denote by $\ell(x)=\lceil\log_2(x+2)\rceil$ the smallest natural number that satisfies $2^{\ell(x)}\ge x+2$.

**Uniformity Theorem.** for all integers $r,x\ge1$.

$$
\boxed{D\bigl(r+2+\ell(x)\bigr)\ge F_{B_r}(x).}
\tag{2}
$$

More generally, any $h\ge r+2+\ell(x)$ satisfies $D(h)\ge F_{B_r}(x)$. Equivalently, as long as $h-2-\ell(x)\ge1$, then there is

$$
\boxed{D(h)\ge F_{B_{h-2-\ell(x)}}(x).}
\tag{3}
$$

Therefore:

- When the input is $x=10$, for $\ell(10)=4$, and for **Any** $h\ge7$,
$D(h)\ge F_{B_{h-6}}(10)$. The rows with 17 are just examples of $r=11$.
- The explicit line loss when inputting $x$ is $2+\lceil\log_2(x+2)\rceil$.
- (2) is not a strict lower bound. If a strict upper bound is required, 1 can be added on the left; the notation $\ge$ is not written as $>$.)

The "arbitrary row number" refers to the parameter of the seed family $R_h$ which can be taken arbitrarily large, such as **Not every matrix that has a row with $h$ has this calculated length.**. For example, the valid seed $B_h$ itself is fixed to the original `[1]`, requiring only $h+2$ steps; it is not advisable to rely solely on the high-level inference count.

## II. Proof Structure

Let $s_M(1)$ denote the number of times the entire zero column is deleted when $M$ is fixed at the original `[1]`. It does not count the expansion of positive columns, so it is $s_M(1)\le d_1(M)$. The proof chain is

$$
\begin{aligned}
D(h)&\ge s_{R_h}(1)\\
&\ge s_{\Sigma(W(B_r)Z^x)}(1)\\
&\ge H_{W(B_r)}(x)\\
&=F_{B_r}(x),
\end{aligned}
\tag{4}
$$

The second inequality precisely requires that $h\ge r+2+\ell(x)$. The following explains each interface separately.

### 1. FGH is precisely transformed into Hardy computation, without increasing the number of lines.

For the matrix $M$, define $W(M)$: add a full zero first column, and add 1 to the value in the 0th row of each original column, while keeping the other rows unchanged. Let the independent concatenation represent that there are no parent edges between the blocks. The original rules are as follows:

$$
W(\varnothing)=Z,\quad
W(MZ)[n]=W(M)^{\frown(n+1)},\quad
W(M)[n]=W(M[n])\quad(M\text{ has a nonzero last column}).
\tag{5}
$$

Definition of Hardy computation

$$
H_\varnothing(x)=x,\quad H_{MZ}(x)=H_M(x+1),\quad
H_M(x)=H_{M[x]}(x)\quad(M\text{ has a nonzero last column}).
$$

Perform a well-founded induction on the standard $M$, and prove the computational termination for (5) at the same time.

$$
H_{W(M)}(x)=F_M(x).
\tag{6}
$$

In the subsequent scenario, the $x+1$ independent blocks operate in sequence, with each block transforming the current parameter $y$ into $F_{M^-}(y)$. Therefore, what is actually implemented is a variable-parameter iteration, rather than a fixed-parameter repetition. For a complete proof, see [FGH—Hardy exact transformation](<fixed-index-growth-interface.en.md>).

### 2. Add one more row of forests, fixing the variable parameter Hardy calculation to a fixed value `[1]`

Define $\Sigma(M)$: Add a full zero first column, and create a new row $1,2,\ldots,|M|$ below each original column. The original rows are shifted up as a whole. The newly created 0 row is a continuous parent chain. Set

$$
K(M,x)=s_{\Sigma(MZ^x)}(1).
$$

The Hardy successor step has a literal identity $K(MZ,x)=K(M,x+1)$. For $M$ where the last column is non-zero, the forest control lemma provides the result.

$$
K(M,x)\ge K(M[x],x)\qquad(x\ge1).
\tag{7}
$$

The key point is to treat the last column of $M$ as a root template, and the subsequent $x$ sequence of counting columns as a single row forest. The non-root steps of the forest are simulated by the target fixing the `[1]` original state; as the forest deletes a root, the target generates a new original bad block, and simultaneously moves the remaining forest behind this block.

Let $e_0=1,e_{x+1}=2^{e_x}$ be the initial forest. The number of subsequent deletions for this forest is $e_x$, so the fixed descending end covers $\Sigma(M[e_x])$. Due to $e_x\ge2x$, there are enough additional copies to cover $\Sigma(M[x]Z^x)$, resulting in (7). This can be generalized for any finite control forest's two types of local steps, without relying on finite test extrapolation.

Along a finite Hardy computation, $K$ does not increase. When the termination parameter is $y$,

$$
K(\varnothing,y)=s_{\Sigma(Z^y)}(1)=e_y\ge y.
$$

Therefore, $K(M,x)\ge H_M(x)$. For the detailed template, parent numbers, and copy verification, see [Complete proof of the forest controller](<diagonal-forest-hardy-proof.md>).

### The ancestor coverage of 3. indeed maintains a count.

The coverage here refers to a column mapping that is strictly increasing and with aligned last columns; each source parent edge is mapped to a non-empty ancestor chain in the same row of the target. It allows for additional rows and additional ancestors, but does not assume any monotonicity in the ordinal of FGH.

If $M$ is covered by $N$, the target's last column is reduced a finite number of times, the control row and cutpoint are adjusted, then synchronized with the source for replication, and any excess tail columns are removed. The simulation of the original `[n]` only uses the target's `[0]`, `[1]`, `[n]`.

When $n\ge1$ is fixed, these macro steps are embedded in the target fixed `[n]` trajectory: each fundamental sequence retains the prefix obtained from the column deletion, with the width decreasing by at most 1 at each step. Therefore, the terminating trajectory must pass through each required prefix. Each source successor deletion occupies at least one target successor deletion, thus

$$
d_n(M)\le d_n(N),\qquad s_M(n)\le s_N(n).
\tag{8}
$$

The target termination is sufficient to derive the source termination. All auxiliary matrices are within the parent chain depth specification domain and are covered by standard diagonal chains. Therefore, even if it is not a standard form, $W(M)$ will not become a hidden well-founded assumption. The finiteness of the proof and preparation process is described in [Quantitative Ancestor Coverage](<ancestor-cover-growth.md>).

### 4. Changing the number of lines to the width results in logarithmic loss

Let $D_{k,m}=(0^k)(1^k)\cdots((m-1)^k)$ be denoted as such. $R_h[1]$ covers $D_{h-1,3}$. The diagonal chain also satisfies

$$
s_{D_{k,m}}(1)\ge s_{D_{k-1,2m-2}}(1)
\quad(k\ge2,m\ge3).
\tag{9}
$$

Its explicit simulation first reduces the highest row of the last column, and then performs another `[1]` operation; the lower $k-1$ rows become a complete chain with a length of $2m-2$. After iterating $t$ times, there is

$$
s_{R_h}(1)\ge s_{D_{h-1-t,\,2+2^t}}(1).
\tag{10}
$$

Any normalized parent matrix with at most $k$ rows and $m$ columns is covered by $D_{k,m}$. Meanwhile, $P_{r,x}=\Sigma(W(B_r)Z^x)$ has exactly $r+1$ rows and $x+4$ columns. Taking $t=\ell(x)$ and $h=r+2+\ell(x)$, then

$$
h-1-t=r+1,\qquad 2+2^t\ge x+4.
$$

Therefore, the diagonal chain coverage of (10) covers ($P_{r,x}$). Combining with the previous three steps, we obtain (2). If there is an excess of rows, ($R_h$ provides a monotonicity condition for the coverage of ancestors of the shorter seeds.

## III. Delivery Boundaries and Usage Instructions

This result not only provides a value for $F_{B_{11}}(10)$, but also constitutes a directly callable line budget theorem. For example, if the outer top convention is $\mathrm{BMS}[x]=B_{x+1}$, then there is an immediate...

$$
\boxed{D\bigl(x+3+\lceil\log_2(x+2)\rceil\bigr)
\ge F_{\mathrm{BMS}}(x)\qquad(x\ge1).}
\tag{11}
$$

Subsequently, for other problems, it is sufficient to provide a sufficiently high $R_h$ fixed lower bound to use (2) or (11). Whether such a lower bound has been provided, what kind of axioms are required, and whether it can be used for the Laver table are not part of this conclusion. There is no additional requirement for a uniform constant row loss, nor is it claimed to be the most optimal logarithmic overhead at present.

The rerun of the boundedness check is consistent with the detailed manuscript: FGH—Hardy has 5,600 local identities, and forest simulation has 1,608 complete trajectories; the coverage check includes 559 synchronous simulations and 130 width exchanges. The 74 numerical calculations that have reached the resource limit, along with the 22 coverage paths, are still marked as undecided. These checks do not replace the aforementioned full proofs; all processes in this run have terminated.

Within the scope of the BMS endpoint specified by the user this time, the paper proofs and summaries have been completed; Lean formalization is not included in this delivery.
