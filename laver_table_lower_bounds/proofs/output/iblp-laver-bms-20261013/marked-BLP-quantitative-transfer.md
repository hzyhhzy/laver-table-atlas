# A finite-parameter quantitative bridge for the natural truncation marker BLP · [中文版](marked-BLP-quantitative-transfer.zh-CN.md)

*English reading edition, translated with machine assistance. The title links to the dated Chinese manuscript.*

> Collected reading edition. The three main papers state the results of this collection.
> This edition retains the local proofs, their hypotheses and any withdrawals. Progress reports describe the state of work at the time.
> The locations of omitted passages on preset inputs are recorded in SOURCE_MANIFEST.json.
> The main papers give the numerical derivations for the natural parameters produced by the proofs. This historical note carries no additional Lean certification.

2026-10-13. This paper supplements the limited parameter interface left by the previous BLP manuscript: after extracting the successor double blocks, a complete natural truncation certificate is still available, and the linedness parameter can be changed. Combined with the previous local closure lemma, a specific numerical lower bound for the original Laver table is obtained.

This is not a complete proof of the lower bound for BMS[10]. There is still a comparison missing between the final number $f_\star(P_{\rm start},1)$ and the specified BMS rapid growth value at the end of this paper. The entire text is a paper proof and has not been formalized in Lean.

## Rules and used local lemmas

The research manuscript adopts the standard BLP row format, short replication, and paper's mutually exclusive successor/limit/transient branches. $E(k)$ represents the auxiliary three-row recursion for the paper; $M_\star$ corresponds to a complete marking from left to right after a short replication, as well as the native completion scan. Replications use the correct one-base guard of PDF, and should not be replaced with the less-significant version from the old Python language.

Zero items are fixed in the first two rows. If the complete row is $s_i$, compress the core to $A_i$ and delete the implied endpoint $i+1$. Denote as

$$
p(i)=A_i[-L_i-1],\quad e(i)=A_i[-L_i],\quad B(i)=A_i[-2].
$$

The ordinary Sat condition is: for every eligible middle/short line, $B(e(i))\le p(i)$. Each actual $p$ chain with a proper mark $y$ must accurately hit its step-length source $\delta$. If the terminal factor is not $v_0=y,\ldots,v_{d-1}=t$, then

$$
W=j_{v_0}\circ\cdots\circ j_t,
\qquad
\Delta(W)=(j_{v_0}\circ\cdots\circ j_{v_{d-2}})(\theta_{t+1}).
$$

The empty composition takes the identity map. It requires $j_i\equiv_{\Delta(W)}W$, and the equivalent symbol is Laver's membership truncation, not a regular function restriction.

The local lemma used comes from the existing manuscript:

- [Naturally truncated copy closure and completion read values](<../../natural-mark-lemmas/natural_trace_cutoff_semantics.en.md>).
- [The entire package of Sat entrances and a single M closure](<../../natural-mark-lemmas/sat_endpoint_packet_theorem.en.md>).
- [Practical Replication Factor Word Recognition](<../../natural-mark-lemmas/copy_trace_word_identification.en.md>).
- [Sat maintains the scanning, prefix, and auxiliary E](<../../natural-mark-lemmas/marked_blp_order_domain.en.md>) Section 9.
- [The lower bound of the factor of the successor E and extraction](<../../natural-mark-lemmas/marked_E_transfer_work.en.md>) sections 2, 3, 7.

These lemmas only require ordinary row implementations, accurate traces, Sat, and natural cuts, without the need to restrict the input to a specific generated history. The history cut stored within the scan is re-obtained at each scan entry using the current certificate; it is not necessary to carry additional history data that follows the root node. Therefore, the following certificate classes are sufficient.

## Certificate classes

Fix a I3 to embed in $j$, and all the witnesses of embedding and linedness are in the same $\operatorname{Iter}(j)$.

Let $\mathcal C$ contain a finite marked BLS that satisfies the following conditions:

1. All ordinary rows and critical points are achieved through row embeddings. The complete sequence of the first two rows is $012$, $0123$, with a step size of 1.
2. Pattern: Sat, all marks are proper, all traces are precise.
3. The actual step size of each mark is derived from $\delta\ge1$, denoted as PosSource.
4. Each mark satisfies the natural truncation semantics of its current actual word.
5. A $(\theta_0,\theta_1,\theta_2)$ carrying a finite $m\ge1$ witnesses the endpoint $m$-linedness.

It is not required that a fixed triplet have witness of all finite parameters at the same time. There is no need for I2, nor is it necessary to mix the critical points of multiple generating elements into a single counting function.

### Prefix and witness replacement

The conditions for keeping all prefixes in at least two lines are as follows: the proper factors and their subsequent columns must not exceed the range of the retained owner. Words with marks, natural embeddings, and true embeddings remain unchanged.

If there is another finite $M$-linedness evidence for the same triplet, the 5 item can be replaced directly. The first four items do not use any $m$ or linedness evidence at all. Therefore, this is not a "more convenient row implementation"; row embedding and cardinality are fixed.

### Keeping the positive marked source

Legal replication maintains the row position and step size, with the new source being $\varphi(\delta)\ge\delta$. The non-empty package of the original completion, whose old $p\ge1$: the two-point core's one-step row has no original package, while the $p$ of the remaining ordinary eligible rows is at least the second non-negative integer entry. The new direct marks originate from this $p$ or a package source larger than it.

The correct marked completion retains the old edges, and the new marks originate from previously non-empty original packages. Thus, PosSource remains unchanged under the original operation. The accurate trace strictly descends to $\delta$, so every non-terminal factor is strictly greater than $\delta$, therefore

$$
v_0,\ldots,v_{d-1}\ge2.
\tag{Floor}
$$

Combining the aforementioned local closure lemma, the $E(m)$, $M_\star$, and cut with finite parameters all maintain the $\mathcal C$. The natural E only requires the current finite $m$-linedness; the proof does not use any arbitrarily large parameters as a common witness.

## Any implementation of new block extraction

This is the core of completing quantitative induction. Let $q$ have $d\ge2$ rows, satisfying PosSource and Sat. Define $D(q)$: add an auxiliary complete row $(2,d+1,d+2)$ after $q$, with a step size of 1, followed by a short copy. It is a doubling of the successor E, and does not add a new fundamental sequence rule for any arbitrary parent item.

Copy coordinates

$$
\psi(0)=0,\quad\psi(1)=1,\quad
\psi(x)=x+d-1\quad(x\ge2).
$$

All mark factors are at least 2, so all full-factor replication branches are used, and all marks are retained. $D(q)$ occurs in the $2d-1$ row.

For any implementation of $Q\models D(q)$ in $\mathcal C$, it is only **Extracting a lemma.**. Let $\nu=Q.\theta_{d+1}$. If there is evidence of $M$-linedness for $(Q.\theta_0,Q.\theta_1,\nu)$, Then, $R\in\mathcal C$ can be achieved through $q$. satisfies

$$
R.m=M,\qquad R.\Theta=Q.\Theta,\qquad R.J=Q.J.
\tag{7}
$$

It is not assumed that $Q$ comes from a specified semantic replication operation.

**Proof.** is defined for cardinality coordinates $2\le s\le d+1$ and row embedding coordinates $2\le s\le d$.

$$
R.\theta_s=Q.\theta_{\psi(s)},\qquad
R.j_s=Q.j_{\psi(s)},
$$

Reserve the symbols of 0 and 1, and take $R.j_1=R.j_2$ as the base. The second row of replication has a complete point sequence $(0,1,\psi(2),\psi(3))$, so its embedding of the first three points also results in a new first row. The rest of the lines are restored directly by reversing the numbering.

For any mark in $q$, the words in $Q$ are $\psi(v_0),\ldots,\psi(t)$. All these factors are in the new block, without the need for a new first line of supplementation. Due to $t\ge2$, there is

$$
\psi(t+1)=\psi(t)+1.
$$

Therefore, both the old and new natural truncations are effective, and they are the same actual ordinal:

$$
\Delta_R(W)=
(Q.j_{\psi(v_0)}\circ\cdots\circ Q.j_{\psi(v_{d'-2})})
(Q.\theta_{\psi(t)+1})
=\Delta_Q(\psi(W)).
\tag{8}
$$

In the formula, $d'$ represents the number of factors of the term. The term owner is also the same actual embedding, so it is naturally retained in the semantic interpretation. The conditions PosSource, accurate trace, and proper are restored by the inverse coordinate mapping.

Sat is a pure grammatical property of the pattern $q$, which remains unchanged after extraction; the first line also directly satisfies Sat. The given new linedness witness can be replaced without affecting other conditions. Therefore, it is $R\in\mathcal C$. The last line and the last cardinality remain unchanged, resulting in (7). Proof complete.

The history of the natural world required for scanning can be re-preserved on the new $R$, so no unlisted generative historical premises are lost here.

## Quantitative theorem

The definition of $f_\star$ follows exactly the definition in Qi's paper Definition 2.24. Only $M$ is replaced by the aforementioned $M_\star$, and the marks are retained in E:

$$
f_\star(p,m)=
\begin{cases}
m2^m,&p\text{ is the zero term},\\
f_\star(\operatorname{cut}p,m),&p\text{ cannot be copied},\\
\bigl(x\mapsto f_\star(\operatorname{cut}p,x)\bigr)^{2^m}(m),
&p\text{ is a successor},\\
f_\star(p.E(m),m),&p\text{ is a limit},\\
f_\star(p.M_\star,m),&\text{other copyable terms}.
\end{cases}
\tag{9}
$$

Use the clauses in the indicated order, with the zero term first. This initially defines a partial recursive function. Total termination remains to be shown.

**Theorem.** If $P\in\mathcal C$ is implemented as $p$, The parameter is $m$. Then $f_\star(p,m)$ is defined. Moreover

$$
(P.\theta_0,P.\theta_1,P.\Theta)
\quad\text{is}\quad f_\star(p,m)\text{-lined}.
\tag{10}
$$

**Proof.** is defined according to the BLS well-foundedness of the paper: First, compare the final cardinality $\Theta$. When they have the same endpoints, compare the final embeddings using the bounded application relation $J$. This certificate class only requires that the right factors of the application also belong to the same $\operatorname{Iter}(j)$. All natural operations satisfy this restriction. Steel's theorem ensures that this relation is well-founded.

The term 'cut' strictly reduces to $\Theta$. The term $M_\star$ does not change the final cardinality, and the final owner is $J(j_{e-1})$; a complete scan retains it. The term $E(m)$ does not change the final cardinality, and the final owner is obtained through two applications, with both intermediate critical points being lower than the common final cardinality. Therefore, these natural operations strictly decrease.

The zero terms are given by the linedness lemma in the two lines of the paper, denoted as $m2^m$. The non-replicable terms are first applied to the cut using induction, and then the end point of the last paragraph is extended to $P.\Theta$ using the critical point transport embedding. The limits and transients are directly handled using the closures and downscales of the natural E／M.

For successor, let $q=\operatorname{cut}p$, $g(x)=f_\star(q,x)$. Let $q_i=p.E(i)$, then $q_0=q$, $q_{i+1}=D(q_i)$. Prove the strengthened assertion:

> For any $Q\in\mathcal C$, if $Q<P$ and $Q\models q_i$, then its first two points and the last point are $g^{2^i}(Q.m)$-lined.

$i=0$ is an outer well-founded induction. From $i$ to $i+1$, it is first restricted to the old blocks, with the last point being $\nu<Q.\Theta$. The induction provides witness for the same endpoints at $M=g^{2^i}(Q.m)$. Using the extraction lemma, a new block $R$ is obtained for $q_i$, with parameter $M$. Finally, the cardinality and embedding are the same as $Q$, so $R<P$. Applying the same strengthening assertion again, we get

$$
g^{2^i}(M)=g^{2^{i+1}}(Q.m)
$$

The linedness of all involved function calls is proven by induction to have a definition, without presupposing that the $g$ has a full definition or monotonicity on all integers.

Finally, apply the assertion of $i=m$ to $P.E(m)<P$ in the natural order, which is the ($2^m$)-th iteration of the successor branch. Once all branches are completed, we obtain (10). Proof complete.

## A clear corollary of Laver's table

Standard notation root

```text
012:1  0123:1  01234:2  012345:2  23456:2
```

In the 4 row, the only mark is 3, and its trace is $(3,1)$. The remaining marks are empty.

The paper Qi discusses the specific implementation of ordinary $P_{\rm start}$ with owners.

$$
j,\quad j,\quad h,\quad h,\quad h(h),
\qquad h=j_{(11)}.
$$

Therefore, the mark in the 4th row is globally equal to the mark in the 3th row, and this natural semantics holds automatically. Given Sat, the only source of marks is 1; the first triplet is $\kappa_0,\kappa_1,\kappa_2$, which is 1-lined. The final cardinality is

$$
\Theta=\kappa_3^{10}<\kappa_4.
$$

Quantitative theorems and the lemma on linedness count are thus given.

$$
\Theta\ge\gamma_{2^{f_\star(P_{\rm start},1)}}.
$$

Using $q(5)=F(4)+1$ and $\kappa_4=\gamma_{F(4)}$, we obtain

$$
\boxed{q(5)>2^{f_\star(P_{\rm start},1)}.}\tag{11}
$$

This is a lower bound interface with a well-defined rule and fixed small cycle index. It does not contain "taking a sufficiently large N," nor does it invoke the common infinite linedness of all parameters. The newly added conclusion here is **The $f_\star$ notation from the complete natural truncation marking rule can be used for the quantitative lower bounds of the original Laver table.**, and it should not be called a BMS lower bound based on this.

To achieve the current goal, it is also necessary to prove, for example,

$$
2^{f_\star(P_{\rm start},1)}
\ge F^{\rm BMS}_{\mathrm{BMS}[10]}(10),
$$

Or find another pattern that is also controlled by the small $N$ and can be strictly compared.

## Bounding grammar verification

marked_quantitative_probe.py (Historical reference: `marked_quantitative_probe.py`) uses the correct PDF copy guard of the old diagnostic engine, but does not run its main program that writes files, nor does it modify any external files. The verification only involves short copies of E/M, without mixing in the original IBLP full tail rules.

The latest run checked the status of 570 queues, performed 1, 610 transfers, along with a special regression example, completed 537 double-block extractions, and accurately recovered 2, 035 marks. The special example includes true non-adjacent multi-factor traces, used to check that the extraction does not use internal adjacencies in a hidden way; it does not claim to be reachable from standard roots. The resource constraints were 20 seconds, 150 rows per state, 15, 000 entries per state, 1, 500 different states and depths of 25; 44 resource stops were not counted as completed.

These tests only verify syntax for subscripts, Sat, PosSource, accurate trace, and the recovery of marks. They do not validate the embedding semantics on infinite domains, nor do they replace the aforementioned proofs.
