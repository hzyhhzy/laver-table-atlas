# Three-column BMS seeds and the FGH lower bound on repeated `[2]` steps · [中文版](bms-fixed-index.zh-CN.md)

Repeating index `[1]` in the original BM4 rules gives the same descent as repeating index `[2]` in the parent-table presentation. Here all indices follow the original BM4 convention. The BMS proof uses neither I3 nor Laver tables nor the well-ordering of BLP. [Conventions](conventions.md)

## 1. Statement

Put

$$
B_r=(0^r)(1^r),\quad R_h=(0^h)(1^h)(1^h),\quad
D(h)=d_1(R_h),
$$

$$
e_0=1,\quad e_{n+1}=2^{e_n},\qquad
\ell(x)=\lceil\log_2(x+2)\rceil.
$$

For all integers $r,x\ge1$ we prove

$$
\boxed{h\ge r+2+\ell(x)\quad\Longrightarrow\quad
D(h)\ge s_{R_h}(1)\ge e_{F_{B_r}(x)}.}
\tag{1}
$$

In particular $D(h)\ge F_{B_r}(x)$. Take $r=x+1$, $g=F_\Lambda$ and $\rho(x)=x+3+\ell(x)$. Then

$$
h\ge\rho(x),\quad x\ge2
\quad\Longrightarrow\quad
D(h)\ge e_{g(x)},\qquad T(h)=D(h)+2\ge\rho(g(x)).
\tag{2}
$$

The hypothesis specifies the **three-column seed** $R_h$. The number of rows alone gives no such inequality for an arbitrary matrix. For example, the two-column seed $B_h$ has a short descent at the same fixed original index $[1]$.

## 2. Parent coordinates, ancestor covers and termination

For the auxiliary matrices, recovering a parent table from its chain depths must give the specified parent table again. An ancestor in a higher row must also be an ancestor in each lower row.

A cover is a strictly increasing map of columns taking the last source column to the last target column. In each row, it sends every parent edge to a nonempty ancestor chain in the same target row. The target may have additional rows and columns. Before synchronizing an original `[n]` copy, lower the last column finitely often to prepare the control row and the cut point. All other selected ancestor relations survive. With the prefix and the coordinate bounds fixed, each preparation step strictly decreases the final column in lexicographic order. Once the control is in place, the original BM4 parent formula checks the edges crossing each copy boundary.

If $N$ covers $M$ and the target's descent at the fixed positive index terminates, then

$$
d_n(M)\le d_n(N),\qquad s_M(n)\le s_N(n)\qquad(n\ge1).
\tag{3}
$$

A terminating descent at a fixed positive index visits each prefix it needs. Every step retains the prefix obtained by deleting the final column, and the width drops by at most one. Thus every `[0]` used in preparation can be realized by following the fixed-index descent to that prefix. Each successor deletion in the source accounts for at least one successor deletion in the target.

The preparation and copy-boundary arguments are proved in Sections 2–5 of the cover proof. The quantitative version proves the fixed-count and row-for-width inequalities. [Covers of nonstandard matrices](../proofs/output/new-notation-20260918/BMS-nonstandard-row-bound.md) · [Quantitative ancestor covers](../proofs/output/iblp-laver-bms-20261013/ancestor-cover-growth.md)

## 3. An exact translation from FGH to Hardy

Let $Z$ be a zero column. Form $W(M)$ by prepending $Z$ and adding one to row zero of each original column. The original parent formulas give

$$
W(0)=Z,\quad W(MZ)[n]=W(M)^{\frown(n+1)},\quad
W(M)[n]=W(M[n])\quad(M\text{ has a nonzero last column}).
\tag{4}
$$

The copies in (4) are independent blocks. Well-founded induction on the standard source $M$ proves that the target Hardy computation terminates and that

$$
H_{W(M)}(x)=F_M(x).
\tag{5}
$$

At a successor the $x+1$ blocks are evaluated from right to left. The next block receives the actual output of its predecessor, which realizes iteration at a changing input. [Proof of the identity](../proofs/output/iblp-laver-bms-20261013/fixed-index-growth-interface.en.md)

## 4. A one-row forest simulates changing indices by a fixed index

Form $\Sigma(M)$ by prepending a zero column, shifting the old rows up one level and placing a consecutive parent chain $1,2,\ldots,|M|$ below them. Set

$$
K(M,x)=s_{\Sigma(MZ^x)}(1).
$$

If the last forest vertex is not a root, the target's fixed `[1]` step commutes with a single forest step, vertex by vertex. At a root the target produces a new copy of the original bad block and transports the remaining forest beyond it. The parent map identifies each new block with the next original BM4 copy. Skipping the frozen forest columns gives a cover aligned at the final column.

A chain forest of length $x$ produces $e_x$ bad blocks. Since $e_x\ge2x$, we can retain $x$ parameter columns again. Consequently

$$
K(MZ,x)=K(M,x+1),\qquad
K(M,x)\ge K(M[x],x)\quad(M\text{ has a nonzero last column}).
\tag{6}
$$

Follow (6) along the terminating Hardy computation. At its final parameter $y=H_M(x)$ we have

$$
K(0,y)=s_{\Sigma(Z^y)}(1)=e_y.
$$

We obtain the stronger estimate

$$
K(M,x)\ge e_{H_M(x)}.
\tag{7}
$$

The forest proof gives the root template, the two local steps and the exact parent of every copy. The tower $e_y$ used in later feedback comes from this terminal forest calculation. [Forest construction](../proofs/output/iblp-laver-bms-20261013/diagonal-forest-hardy-proof.md)

## 5. Trading rows for width

Write

$$
\Delta_{k,m}=(0^k)(1^k)\cdots((m-1)^k).
$$

The parent-table computation shows that $R_h[1]$ covers $\Delta_{h-1,3}$ and that

$$
s_{\Delta_{k,m}}(1)\ge s_{\Delta_{k-1,2m-2}}(1)
\quad(k\ge2,m\ge3).
$$

After $t$ iterations we obtain a cover of $\Delta_{h-1-t,\,2+2^t}$. The matrix

$$
P_{r,x}=\Sigma(W(B_r)Z^x)
$$

has $r+1$ rows and $x+4$ columns. Take $t=\ell(x)$. The hypothesis $h\ge r+2+\ell(x)$ supplies enough rows and $2+2^t\ge x+4$ supplies enough columns. Thus

$$
D(h)\ge s_{R_h}(1)\ge s_{P_{r,x}}(1)
\ge e_{H_{W(B_r)}(x)}=e_{F_{B_r}(x)},
$$

which proves (1). Standard diagonal matrices cover all the auxiliary expressions. Termination therefore follows from standard BMS well-ordering.

## 6. Sources for the proof

The proof first constructs the parent-table cover, then bounds the fixed-index count by ancestor coverage, establishes the exact $W$ identity and uses the forest computation. The original summary foregrounds the weaker inequality. Its stronger tower estimate comes from (7). [Original BMS summary](../proofs/output/iblp-laver-bms-20261013/BMS-fixed-index-to-FGH-summary.md) · [Dependency audit](../proofs/output/iblp-030-laver-20261014/FGH-standalone-dependency-audit.md)
