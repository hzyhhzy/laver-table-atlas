# BMS Diagonal FGH Input Strict Monotonicity · [中文版](audit-BMS-diagonal-input-monotonicity.zh-CN.md)

*English reading edition, translated with machine assistance. The title links to the dated Chinese manuscript.*

> Collected reading edition. The three main papers state the results of this collection.
> This edition retains the local proofs, their hypotheses and any withdrawals. Progress reports describe the state of work at the time.
> The locations of omitted passages on preset inputs are recorded in SOURCE_MANIFEST.json.
> The main papers give the numerical derivations for the natural parameters produced by the proofs. This historical note carries no additional Lean certification.

2026-10-14. The following uses the original BM4 fundamental sequence, as well as the FGH convention adopted in this catalog. The conclusions only involve specifying a seed family and a finite subsequent layer; it does not assume that the FGH for any two ordinal indices are monotonous in order.

Put

$$
B_r=(0^r)(1^r),\qquad
g(x)=F_\Lambda(x)=F_{B_{x+1}}(x)\quad(x\ge1),
$$

$$
G_0=g,\qquad G_{i+1}(x)=G_i^{\circ(x+1)}(x),\qquad
H(x)=G_{x+1}(x).
$$

Here, $H=F_{\Lambda+\omega}$ is adopted as $(\Lambda+\omega)[x]=\Lambda+(x+1)$. Thus, $g$, each $G_i$, and $H$ are strictly increasing on the set of positive integers. Therefore, if $X>t\ge1$, then there is

$$
\boxed{H(g(g(X)))>H(g(g(t))).}
\tag{1}
$$

In particular, for the existing $t=F_3(256)$, as long as the new pIBLP initialization yields $X=2^C>t$, replacing $t$ with $X$ will definitely increase the right-hand side of the FGH by a strict amount.

## Prefix rules with simultaneous induction

The standard BMS satisfies the following literal properties:

- Each fundamental term $P[n]$ contains $\operatorname{cut}(P)$ as a column prefix;
- When $n\le m$, $P[n]$ is the column prefix of $P[m]$.
- Both the tail and the fundamental terms are strictly below $P$, and the column prefix still belongs to the standard domain.

Using standard BMS well-foundedness, prove by induction on $P$ simultaneously

$$
F_P(x)\ge x+1,
\tag{2}
$$

$$
A\preceq P\ \Longrightarrow\ F_A(x)\le F_P(x),
\tag{3}
$$

$$
0\le x\le y\ \Longrightarrow\
F_P(y)\ge F_P(x)+(y-x).
\tag{4}
$$

Here only

$$
F_\varnothing(x)=x+1,\qquad
F_{AZ}(x)=F_A^{\circ(x+1)}(x),\qquad
F_P(x)=F_{P[x]}(x)\quad(P\text{ has a nonzero last column}).
$$

Obviously, the empty formula is vacuous. For the successor item $P=AZ$, let it be $f=F_A$. For the smaller items of (2), increasing the number of iterations does not reduce the result, so for $F_P(x)\ge f(x)$, a column deletion comparison is obtained. For the smaller items of (4), when iterating the same number of times, increasing the initial input by $y-x$ will at least increase the result by $y-x$; further increasing the number of iterations from $x+1$ to $y+1$ will not reduce the result. This proves that the successor item of (4) also yields (2).

For the $P$ where the last column is non-zero, (2) comes from the smaller term $P[x]$. It contains $\operatorname{cut}(P)$, so the (3) on the smaller term gives a column deletion comparison. By repeatedly deleting columns, we obtain all the true prefix comparisons of (3). Finally, ($P[x]\preceq P[y]$, using the (4) and (3) of the smaller term $P[y]$,

$$
\begin{aligned}
F_P(y)&=F_{P[y]}(y)\\
&\ge F_{P[y]}(x)+(y-x)\\
&\ge F_{P[x]}(x)+(y-x)
=F_P(x)+(y-x).
\end{aligned}
$$

All inductive calls occur below $P$. There is no need to extend to non-standard matrices here. This inductive process is consistent with that described by [Prelemma for the comparison of short tails FGH](<../iblp-030-laver-20261014/short-tail-cofinality.md>).

## Comparison of the number of rows with a single kind of seed in two columns

For $s\ge2$ and $n\ge1$, the original BM4 rule is directly given.

$$
B_s[n]=(0^{s-1})(1^{s-1})\cdots(n^{s-1})
=D_{s-1,n+1}.
\tag{5}
$$

The highest row with all zeros is ignored in the equation. Since $n\ge1$, the first two columns on the right are exactly $B_{s-1}$. Therefore, by (3),

$$
F_{B_s}(n)=F_{D_{s-1,n+1}}(n)\ge F_{B_{s-1}}(n).
\tag{6}
$$

Repeat along a finite number of rows (6), for $s\ge r\ge1,n\ge1$,

$$
F_{B_s}(n)\ge F_{B_r}(n).
\tag{7}
$$

This is not a general case of subindex monotonicity: it entirely stems from the prefix in front of the fundamental term.

## Diagonal function and finite successor layer

For $1\le x\le y$, first fix the input $y$ using (7), then fix the matrix $B_{x+1}$ using (4):

$$
\begin{aligned}
g(y)&=F_{B_{y+1}}(y)\\
&\ge F_{B_{x+1}}(y)\\
&\ge F_{B_{x+1}}(x)+(y-x)
=g(x)+(y-x).
\end{aligned}
\tag{8}
$$

So $g$ at least maintains the input difference, and $g(x)\ge x+1$. For $i$, a usual natural induction is applied, and the same proof for the successor iteration indicates that every $G_i$ also satisfies the condition.

$$
G_i(y)\ge G_i(x)+(y-x),\qquad G_i(x)\ge x+1.
\tag{9}
$$

Additionally, for $x\ge1$, the successor layer iterates at least twice, therefore

$$
G_{i+1}(x)>G_i(x).
\tag{10}
$$

If $1\le x<y$, first use (10) to reduce the number of layers on the same input $y$ to a finite number, and then use (9), then it will be

$$
H(y)=G_{y+1}(y)\ge G_{x+1}(y)
\ge G_{x+1}(x)+(y-x)>H(x).
\tag{11}
$$

By performing three strict comparisons with (8) and (11), one can obtain (1).

## Usage boundaries of the new q5 lower bound

This lemma allows for a strict comparison of the values of the same explicit function on two known different inputs. It does not provide a new Laver implementation, does not prove the global well-ordering of pIBLP, nor does it prove monotonicity with respect to the input for $f_{\rm PP}(S,m)$.

If it has been completed separately

$$
q(5)>H(g^2(2^C)),\qquad 2^C>F_3(256),
$$

Then, (1) immediately proves that the new explicit right-hand side is strictly greater than the old right-hand side $H(g^2(F_3(256)))$. The second condition can be derived from $C\ge F_3(256)$. There is no need to calculate any large integers involved.
