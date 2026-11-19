# Definitions, index conventions and proof scope · [中文版](conventions.zh-CN.md)

The three papers collect arguments through 2026-10-18. Their Laver-table constructions work in ZFC + I3. The separate BMS counting lemma uses standard BMS well-ordering. The papers' scope is independent of the later Lean formalizations.

## 1. The period threshold

The ordinary binary Laver table $A_m$ has $2^m$ elements, numbered $1,\ldots,2^m$. Its operation is left self-distributive and satisfies $a*1=a+1\bmod 2^m$. Write $p_m$ for the least period of its first row and put

$$
q(n)=\min\{m:p_m\ge2^n\}.
$$

The bound concerns the **order $q(5)$**. The table at that order has $2^{q(5)}$ elements. I3 guarantees that the required threshold exists.

Fix a single $j:V_\lambda\to V_\lambda$. All owners, critical points, chain witnesses and transports lie in the same $\mathcal I=\operatorname{Iter}(j)$. Write

$$
j_{(1)}=j,\quad j_{(n+1)}=j_{(n)}(j),\qquad
\kappa_0=\operatorname{crit}(j),\quad\kappa_{i+1}=j(\kappa_i).
$$

Enumerate the critical points of this algebra as $\gamma_0<\gamma_1<\cdots$. We use the standard correspondence

$$
\kappa_4=\gamma_{q(5)-1}.
\tag{1}
$$

Write $F(G)$ for embedding application and $F\circ G$ for ordinary function composition. At genuine image points we have

$$
F(G)(F(\xi))=F(G(\xi)),\quad
\operatorname{crit}(F(G))=F(\operatorname{crit}(G)).
\tag{2}
$$

In general $F(G)(\xi)$ need not equal $F(G(\xi))$.

## 2. Finite chains with witnesses

The assertion $L(a,b,c;m)$ gives a strictly increasing chain

$$
b=t_0<t_1<\cdots<t_m=c
$$

and embeddings $U_i\in\mathcal I$ satisfying

$$
\operatorname{crit}(U_i)=a,\quad U_i(a)=t_i,\quad U_i(t_i)=t_{i+1}.
$$

Such chains can be transported as a whole, concatenated, or shortened while preserving their endpoints. Given $L(a,b,c;m)$ and $L(b,c,d;n)$, successive images and concatenation yield

$$
L(a,b,d;m2^n).
\tag{3}
$$

The first $m$ segments of the original chain can be retained verbatim. [Chain calculation, Section 3](../proofs/scratch/iblp-I-to-I0-20261016/local-budget-algebra.en.md)

The critical-point count gives

$$
L(\kappa_0,\kappa_1,z;m),\ z<\kappa_4
\quad\Longrightarrow\quad
\gamma_{2^m}\le z<\kappa_4,
\quad q(5)>2^m.
\tag{4}
$$

The implication requires actual witnesses for the chain. A numerical lower bound on a critical index alone does not produce such witnesses.

## 3. The index shift in BMS

The formulas use **the original BM4 indices**.

- `[0]` deletes the final column.
- For a positive final column, `[n]` retains the prefix and appends $n$ copies of the bad block.
- An all-zero final column is deleted at every index.

Fixed index `[2]` in the parent-table presentation agrees with fixed index `[1]` in the original BM4 rules. Put

$$
B_r=(0^r)(1^r),\qquad R_h^{\rm BMS}=(0^h)(1^h)(1^h),
$$

$$
D(h)=d_1(R_h^{\rm BMS}),\qquad T(h)=D(h)+2,
$$

Here $d_1$ counts **all steps** to the empty matrix. The count $s_M(1)$ includes only deletions of zero final columns. The letter $T$ in this formula denotes the numerical feedback function.

## 4. Hardy and FGH conventions

For notation with the specified fundamental sequences, put at zero and a genuine successor

$$
H_0(x)=x,\qquad H_{P+1}(x)=H_P(x+1),
$$

$$
F_0(x)=x+1,\qquad F_{P+1}(x)=F_P^{\circ(x+1)}(x).
$$

At a nonzero nonsuccessor put

$$
H_P(x)=H_{P[x]}(x),\qquad F_P(x)=F_{P[x]}(x).
\tag{5}
$$

In the original IBLP a genuine successor has final core exactly $(0,r)$ with step size 1. Choosing a cut after a failed copy does not make the parent a genuine successor.

Let $\Lambda=\lim(\mathrm{BMS})$. The second paper uses

$$
\Lambda[x]=B_{x+1},\qquad
(\Lambda+\omega)[x]=\Lambda+(x+1).
\tag{6}
$$

The first paper's $F,H$ use the actual fundamental sequences of the pinned original IBLP. Equal descent-tree ranks alone do not justify changing these sequences.

## 5. Two guards for marks

The pinned original `iblp.py` defines full expansion and the exceptional `[1]`. Its filter for mixed marks is called the **legacy guard**. [Original code](../code/iblp_original.py) · [Source hashes](../SOURCE_MANIFEST.json)

The **paper guard** tests the next source in a mixed word, one position away from the legacy test. The initial terms in the third paper come from full original expansions. The subsequent count is for short $M_\star$ with the paper guard, the full frozen scan and cuts. The guards agree during both entrance expansions by a separate argument. Agreement for subsequent orbits remains open.

The parent-packet operation $M_{\rm PP}$ has a further rule. The native packet includes the entire new family of the current row's direct parent. The second paper uses it for the stronger initialization. Each of the three rules has its own numerical recursion.

## 6. Scope

The collection gives the arguments and dependencies for the natural inputs produced by the proofs. The local scripts check finite syntax and file consistency. The I3 semantics, inductions and bounds on growth functions are supplied by the papers. [Bibliography](../BIBLIOGRAPHY.md)
