# General transfer marked completion: Insertion of intervals and semantic lemmas for the whole package · [中文版](marked_completion_interval_lemma.reading.zh-CN.md)

*English reading edition, translated with machine assistance. The title links to the dated Chinese manuscript.*

> Collected reading edition. The three main papers state the results of this collection.
> This edition retains the local proofs, their hypotheses and any withdrawals. Progress reports describe the state of work at the time.
> The locations of omitted passages on preset inputs are recorded in SOURCE_MANIFEST.json.
> The main papers give the numerical derivations for the natural parameters produced by the proofs. This historical note carries no additional Lean certification.

2026-09-07. This note gives local sufficient conditions for full marked completion and permits transfers of arbitrary length. Whether clause 13 of the PDF or the standard generation history of DEN2 automatically supplies the conditions is a separate question. The argument applies to a subsystem that checks those conditions.

## The condition for the exact position of inserting two intervals 1.

Let the old sequence **Complete row** be a strictly increasing sequence

$$
A=(a_1<\cdots<a_N),\qquad 1\le L<N.
$$

All the steps in the old row are marked as $a_i\mapsto a_{i+L}$, with $1\le i\le N-L$ in between. Let $1\le s<s+L<N$ be the new step length. Insert $u_1<\cdots<u_q$ into $(a_s,a_{s+1})$, and $v_1<\cdots<v_q$ into $(a_{s+L},a_{s+L+1})$, with $q\ge1$ remaining. All points are strictly new entries located within their corresponding intervals. The new row is marked as B, and the step length is changed to $L+q$.

**Lemma 1.1.** is equivalent to the following two statements:

1. Each step edge in the old row remains a step edge of $L+q$ in B;
2. $N-2L\le s\le L$.

When these conditions are met, all the step sizes of the new row are exactly the same as all the old edges and
$u_h\mapsto v_h\ (1\le h\le q)$.

**Proof.** fixes the old edge $a_i\mapsto a_{i+L}$. Its new position difference is equal to L plus the number of insertions between the two endpoints. The first interval contributes q if and only if $s-L+1\le i\le s$; the second interval contributes q if and only if $s+1\le i\le s+L$. These two integer intervals do not intersect, and their union is $[s-L+1,s+L]$. Therefore, all $i\in[1,N-L]$ exactly receive q insertions, if and only if

$$
s-L+1\le1,\qquad s+L\ge N-L,
$$

That is, under the condition 2.

On the other hand, the new position of $u_h$ is $s+h$, and the new position of $v_h$ is $s+L+q+h$. The difference in positions is exactly $L+q$. The total number of sides in the new row is

$$
(N+2q)-(L+q)=(N-L)+q.
$$

The old edges that have been listed, along with the new edges marked with q, are distinct from each other and their number is exactly equal. Therefore, there are no other new edges that need verification. Proof completed.

With the condition that two intervals indeed exist, the allowed s are

$$
\max(1,N-2L)\le s\le \min(L,N-L-1).
\tag{G}
$$

For the complete rows of the ordinary BLP, N=2L, 2L+1, 2L+2, the requirements at the left end are s≥1, s≥1, s≥2 respectively. In particular, when N=2L+2, s=1 cannot use "inserting two packs, increasing the step size q" to ensure that all edges in the original row remain unchanged. For longer lines of the IBLP, the conditions also make sense, but there is no solution when N>3L.

**Corollary 1.2.** If the same strictly increasing function f implements an old row, and $f(u_h)=v_h$ holds for every h, then a new row is implemented under (G)) with the same f. If f is a row embedding, the smallest entry remains unchanged, therefore the requirements of critical points are also maintained.

## What new lines can be read with a weak truncation of 2.?

Using Laver membership truncation

$$
f\equiv_\Gamma g
\iff \forall x,z\in V_\Gamma\,
 (x\in f(z)\leftrightarrow x\in g(z)).
$$

If **Lemma 2.1.**, $\xi<\Gamma$, $g(\xi)=\eta<\Gamma$, and $f\equiv_\Gamma g$, then $f(\xi)=\eta$.

**Proof.**, $f(\xi)$, and $g(\xi)$ are all ordinals. If $f(\xi)>\eta$, taking $x=\eta,z=\xi$ would violate the truncation equivalence. If $f(\xi)<\eta$, taking $x=f(\xi),z=\xi$ would also lead to a contradiction. The used x and z both belong to $V_\Gamma$. Proof complete.

This allows for the reading of the new mapping for the current row from the precise new mapping of the transfer factor terms, but requires that both the input and output be below **The actually preserved truncated Γ**. After the native insertion, Γ is generally the base number of the old y+1 column, not the new adjacent column $\theta_{y+1}$.

## The sufficiency of the entire package of transfer certificates marked with 3.

The old label for the current line r is y, and the non-terminal factor of the original transfer is

$$
(v_0=y,v_1,\ldots,v_{m-1}=t),\qquad
W=j_{v_0}\circ\cdots\circ j_{v_{m-1}},
$$

And it has been saved as $j_r\equiv_\Gamma W$. Under the current scanning coordinates, assume that the original record of t is $T=(u_1<\cdots<u_q)$, and save the following **Whole package** data:

1. For each h=1, …, q and each i=0, …, m−1, perform an embedding
$j_{v_i+h}=j_{v_i}$ is globally equal.
2. For i<m−1, the complete row edge is given

$$
   j_{v_i+h}(\theta_{v_{i+1}+h})=\theta_{v_i+h};
$$

The last factor is given as
   $j_{t+h}(\theta_{u_h})=\theta_{t+h}$; 
3. All related $\theta_{u_h},\theta_{y+h}$ are less than Γ, and
   $\theta_{y+h+1}\le\Gamma$; 
4. In the current line, add sources as T, targets as
$y+1,\ldots,y+q$, two intervals and position conditions that satisfy the lemma 1.1;
5. The actual transfer of y+h after completion is
$(v_0+h,\ldots,v_{m-1}+h,u_h)$. All remaining old markings, along with still applicable factor words and truncation certificates.

**Theorem 3.1.** Under these assumptions, the original row is embedded into $j_r$ to achieve all the row edges after completion. The note semantics of each newly added marker y+h holds, and the old markers remain valid.

**Proof.** For each h, assume that 1 provides

$$
W_h:=j_{v_0+h}\circ\cdots\circ j_{v_{m-1}+h}=W.
$$

Starting from the rightmost factor, using the assumption 2, we get

$$
W(\theta_{u_h})=W_h(\theta_{u_h})=\theta_{y+h}.
$$

Assume that 3 and the lemma 2.1 together yield $j_r(\theta_{u_h})=\theta_{y+h}$. The lemma 1.1 and the corollary 1.2 prove that all new and old row edges are present.

$$
j_r\equiv_\Gamma W=W_h,
\qquad \theta_{y+h+1}\le\Gamma
$$

It is the addition of new markers that requires weak truncation equivalence in their actual transfer. The old markers are maintained by the certificates assuming 5. Proof complete.

**Truncated version.** assumes that 1 can be generalized to a word condition $W_h\equiv_\Gamma W$, without the need for global equality of each factor. In this case, use $j_r\equiv_\Gamma W_h$ and the same transport equations to read the new row boundaries, and the new markers are directly established by this truncated equivalence. Here, we use the proven truncated equivalence for words; it is not sufficient to simply omit the verification of the truncated height after combining the factors at a lower level.

This is a strict local lemma that allows for general-length transfers. Its key elements include the entire package transport, insertion intervals, and historical truncation; the mere occurrence of "+1" on each internal edge cannot be used to replace these data without demonstration. `den2_definition_work.md` provides a counter-example in pure syntax when there is no semantic assumption.

## 4. In ordinary BLP, the position condition can be derived from the packet semantics.

The following section transforms part of the pure combinatorial assumptions in the 3 section into usable semantic conditions. Let A be the ordinary BLP complete row before completion, with the embedding being F; the proper mark y<r is located at position k, and let s=k−L, $\delta=a_s$. Thus, $F(\theta_\delta)=\theta_y$. Let the old mark certificate be $F\equiv_\Gamma W$, where the last factor of W, K, is the old row embedding of a non-empty primitive package, $p(t)=\delta$. Assume that this ordinary BLP primitive row uses q>0 sources, and

$$
\operatorname{crit}(K)<\theta_\delta.
\tag{C}
$$

For the general BLP, it is actually true that (C) is established by non-empty native birth automata. The proof is as follows: the length of the eligible core is 2L or 2L−1, and its replication roots are located at the L or L−1th positions in ascending order. If the replication root equals the minimal term, the former requires L=1, while the latter requires L=2. The latter is a complete four-point step length of 2, which is excluded by the general BLP definition. The former is a two-point core of $(\delta,t)$, and its first original prehension is $q(t)=\delta=p(t)$, so the record is empty. This contradicts q>0. Therefore, the replication root is strictly greater than the minimal term, and the latter is precisely the critical point index of K, resulting in (C).

It is assumed that the entire package transport has given q mappings.

$$
W(\theta_{u_h})=\theta_{v_h},\qquad
\theta_\delta<\theta_{u_h}<\Gamma,\qquad
\theta_y<\theta_{v_h}<\Gamma,
$$

And save the truncation that does not cross the next old entry after y in A:

$$
\Gamma\le\theta_{a_{k+1}}.
\tag{H}
$$

Here, (H) does not automatically apply to any modified rows in the scan: If other marks have been inserted into the same old gaps, it must be proven anew. When using the historical gap y for the first time, without being touched by other completions, $\Gamma$ is the cardinality of the old global y+1 sequence, hence (H) holds true.

The assumptions **Corollary 4.1.** imply that all new sources and targets are fresh, that there is a single insertion interval, and that it is (G)). Therefore, there is no need for additional checks on each edge as it gets old. The same F is used to implement new rows.

Lemma **Proof.** is given as 2.1 for $F(\theta_{u_h})=\theta_{v_h}$. By (H), these are strictly located in $(\theta_y,\theta_{a_{k+1}})$. And

$$
F(\theta_{a_{s+1}})=\theta_{a_{k+1}},
$$

Therefore, the strict monotonicity of F forces $\theta_\delta<\theta_{u_h}<\theta_{a_{s+1}}$. Thus, both packages are located in the corresponding empty old gaps, and these gaps do not intersect; both freshness and pairing positions are ensured.

The critical point of a composite embedding is the minimum of the critical points of its components. Therefore
$\operatorname{crit}(W)\le\operatorname{crit}(K)<\theta_\delta<\Gamma$.
The weak truncation equivalence retains Γ for the critical points, hence $\operatorname{crit}(F)<\theta_\delta$. Since the critical point of F is the smallest entry in this row, δ is not the first item, that is, s≥2.

On the other hand, the proper mark y<r is assigned to k≤N−2, while the ordinary BLP has N≤2L+2. Therefore

$$
s=k-L\le N-L-2\le L,
\qquad N-2L\le2\le s.
$$

This is the condition for the position of the lemma 1.1; two true gaps have been proven to exist. Proof completed.

This corollary further reduces the ordinary BLP row edge maintenance gap to: entire package factor transport, and ensures that historical gaps are not incompatible and repeatedly occupied when multiple marks are processed sequentially. It does not apply to any long IBLP rows, as the last step explicitly uses N≤2L+2.

## A directed inspection on the actual standard track at 5.

`den2_completion_geometry_probe.cjs` adds a read-only audit callback to the true compTo of the source snapshot, checking for duplicate entries, old edge positions, new pairs, two inserted intervals, and (G)) for each non-empty T completion. A finite run covers 4551 different states, 8358 transfers, and 154 non-empty marked completions were observed:

- 154 occurrences occur entirely within complete rows of N=2L+2;
- A total of 616 old edges were checked, with no failures in edge positions;
- Both the source and target lie within a single corresponding interval, and all satisfy 2≤s≤L.
- No duplicate entries or new pair misalignments were observed.

The original parameters and examples are denoted by `den2_completion_geometry_checks.json`. This operation is performed based on depth, number of rows, parameters, and time truncation. The properties **No proof provided.** are maintained in the complete standard domain, and there is no proof of the theorem 3.1 with the entire embedding/owner assumption. It reduces the next-step combinatorial invariants to a clearly stated range, rather than providing global verification.
