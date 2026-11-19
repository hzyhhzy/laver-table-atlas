# The complete marked BLP E: Successor-type positive lemma and Sat limit-type counterexample · [中文版](marked_E_transfer_work.md)

*English reading edition, translated with machine assistance. The title links to the dated Chinese manuscript.*

> Collected reading edition. The three main papers state the results of this collection.
> This edition retains the local proofs, their hypotheses and any withdrawals. Progress reports describe the state of work at the time.
> The locations of omitted passages on preset inputs are recorded in SOURCE_MANIFEST.json.
> The main papers give the numerical derivations for the natural parameters produced by the proofs. This historical note carries no additional Lean certification.

2026-09-07. This paper does not assume that the semantic closure of the complete M markers has been established.

The conclusion has two parts. If all the marks of each transfer are **Non-terminal factors must have a minimum value of 2**, then the preservation of marks for the successor type E and the complete marking double-block extraction required by the theorem 2.25 are both satisfied. Conversely, Sat, this lower bound of the factor, internal adjacency, and the actual marked BLS implementation are still insufficient to ensure the preservation of marks for the limit type E. A clear I3 counterexample is given in the 4 section. The **The counterexample has not been proven to be reachable from the standard initial terms, nor has it been proven that the E output results in no other implementations.** is not provided in the original text.

## 1. first fix the actual E type

This text uses the full line s_i, with the core being A_i=s_i, omitting the last term i+1.

$$
p(i)=A_i[-L_i-1],\qquad e(i)=A_i[-L_i],\qquad q(i)=A_i[-2].
$$

The input line for the paper is:

$$
\begin{array}{c|c|c}
\text{type}&s_n&L_n\\\hline
\text{successor}&(0,1,2,n,n+1)&2\\
\text{limit}&(0,1,2,a,n,n+1),\quad 2<a<n&3
\end{array}
$$

Both provide information.

$$
j_n(\theta_0)=\theta_a,\quad
j_n(\theta_1)=\theta_n,\quad
j_n(\theta_2)=\theta_{n+1},
\tag{1}
$$

Among them, when successor a=2. Do not change the input lines to (0,a,n,n+1), step size 1; The latter is not of the E type of the original paper. The **Auxiliary** row of E is (a,N+1,N+2)), with a step size of 1. Currently, there are N rows in E(t). Auxiliary embeddings are provided by linedness evidence. The critical point is θ_a. It short copies the source a,...,N. And keep the original N line; Coordinate mapping is

$$
\psi_a(x)=\begin{cases}x&x<a,\\x+N+1-a&x\ge a.\end{cases}
\tag{2}
$$

Please verify directly using [The original paper defines 2.15 as—2.18](https://arxiv.org/html/2501.06733v5); for local word-by-word extraction, refer to `laver_v5_extracted.txt`.

The marking semantics always adopts membership truncation.

$$
f\equiv_\gamma g\iff
\forall u,v\in V_\gamma\;(u\in f(v)\leftrightarrow u\in g(v)).
$$

If tr_i(y)=(v_0=y,...,v_r=δ), its factors are W=j_{v_0}∘...∘j_{v_{r-1}}, and the last vertex δ does not contribute an embedding factor.

## 2. Subtype E The complete notation is retained

Definition of the lower bound condition for factors

$$
\mathsf{Floor}_2:\qquad
v_h\ge2\quad(0\le h<r)
\quad\text{holds for each realized transfer preserving marks.}
\tag{3}
$$

It is allowed for the endpoint δ to be 0 or 1; it is not required that all transfer vertices be at least 2.

**Lemma 2.1.** q satisfies Floor₂, and the auxiliary rows are taken as a=2. Then, the copy of the 10th item in the PDF retains every marking of q, and the original specification copied from BLS maintains the weak truncation semantics of all markings. The output still satisfies Floor₂.

**Proof.** All the vertices of the factors of each marked y fall within the source 2,...,N, so the 10(a) branch applies directly. Reading each item of the copied row p, we obtain

$$
p'(\psi_2(v))=\psi_2(p(v))\qquad(2\le v\le N).
$$

So its actual transfer is exactly

$$
(\psi_2(v_0),...,\psi_2(v_{r-1}),\psi_2(δ)).
\tag{4}
$$

Let the auxiliary embedding be K. Apply K to the original marker j_i≡_{θ_{y+1}}W. Using the homomorphic property of applications to ordinary composites, we obtain

$$
K(j_i)\equiv_{K(\theta_{y+1})}
 K(j_{v_0})\circ\cdots\circ K(j_{v_{r-1}}).
$$

Since y≥2, there exists ψ₂(y+1)=ψ₂(y)+1, and also K(θ_{y+1})=θ'_{ψ₂(y)+1}, which are exactly the heights required for the new markings. The old blocks remain unchanged. All new factor vertices are ψ₂(v_h)≥2. Proof complete.

The marked BLS successor E(m) that satisfies Floor₂ for all **Corollary 2.2.** is proven to be canonical by the linedness property in the original paper, while maintaining the complete marked semantics. E(0) is a column deletion. Replicate Lemma 2.1 for each subsequent auxiliary copy. Here, we do not invoke M or native completion.

## Extracting complete marked new blocks in arbitrary implementations of 3.

**Lemma 3.1.** q has N≥2 rows and satisfies Floor₂. Let q⁺ be the aforementioned round of auxiliary replication of a=2 by E. Q is a q⁺ with a **Any** marked BLS implementation. Let ν=Q.θ_{N+1}. If (Q.θ₀,Q.θ₁,ν)) is witnessed by M-lined, Then there exists a marked BLS implementation of q that achieves R. satisfies

$$
R.m=M,\quad R.\theta_0=Q.\theta_0,\quad
R.\theta_1=Q.\theta_1,\quad
R.\Theta=Q.\Theta,\quad R.J=Q.J.
\tag{5}
$$

**Proof.** Let ψ=ψ₂. Extract new blocks and define

$$
\begin{aligned}
R.\theta_0&=Q.\theta_0,&R.\theta_1&=Q.\theta_1,\\
R.\theta_s&=Q.\theta_{\psi(s)}&&(2\le s\le N+1),\\
R.j_s&=Q.j_{\psi(s)}&&(2\le s\le N),\\
R.j_1&=R.j_2.
\end{aligned}
\tag{6}
$$

The source 2 behavior is replicated as (0,1,ψ(2),ψ(3))), with a step size of 1. Therefore, the first three cardinalities implement the new 1 row. The rest of the complete rows and step size are restored by the inverse mapping of ψ. Let R.m=M be the given witness.

The original notation tr_i(y)=(v₀,...,v_{r-1},δ) is retained as (4) in Q. The marked equivalence of Q is

$$
Q.j_{\psi(i)}\equiv_{Q.\theta_{\psi(y)+1}}
 Q.j_{\psi(v_0)}\circ\cdots\circ Q.j_{\psi(v_{r-1})}.
$$

All factors are v_h≥2, so the original terms in R are completely extracted on the right side, without any creation of R.j₁. Similarly, y≥2 is given as

$$
Q.\theta_{\psi(y)+1}=Q.\theta_{\psi(y+1)}=R.\theta_{y+1}.
$$

This is the complete original semantic interpretation of R. The endpoints 0 or 1 only participate in the coordinates, and no replication embeddings are required for them. The original line 1 does not contain any non-empty markers that satisfy Floor₂, so this line is constructed without omission. The last line and the last cardinality are the same as those of Q, resulting in (5). Proof complete.

The old block Q|N is still fully implemented for q, and its final cardinality is ν<Q.Θ. Therefore, the original theorem 2.25, which is a double-block induction for the successor branches, can replace the "directly marked global equality" in section `marked_blp_proof.md` of 7.2 with any long factor word weak truncation condition of this lemma. There is no need to limit the marking to two vertices.

## 4. Sat + Floor₂ + Internal adjacency is still insufficient to ensure limit E

### 4.1 becomes a true I3 implementation

Take any I3 that embeds j, and the critical sequence is κ_t=j^t(crit(j)). The superscript ∘r represents a normal composition of r times, and the parentheses f(g) indicate the Laver application. Define

$$
b=j^{\circ4}(j),\qquad h=b\circ b,\qquad
g=h(j^{\circ3}).
\tag{7}
$$

The application identity f(k)∘f=f∘k is given as

$$
\begin{aligned}
\operatorname{crit}(b)&=\kappa_4,& b(\kappa_t)&=\kappa_{t+1}\quad(t\ge4),\\
\operatorname{crit}(h)&=\kappa_4,& h(\kappa_t)&=\kappa_{t+2}\quad(t\ge4),
\end{aligned}
$$

h fixes κ₀,...,κ₃. Therefore

$$
\operatorname{crit}(g)=\kappa_0,\quad
g(\kappa_0)=\kappa_3,\quad
g(\kappa_1)=\kappa_6,\quad
g(\kappa_2)=\kappa_7.
\tag{8}
$$

Take θ_i=κ_i (0≤i≤7), and the six rows of marked BLS are as follows:

| i | Complete line s_i | L_i | Embedding j_i | Mark |
| --- | --- | ---: | --- | --- |
| 1 | (0,1,2) | 1 | j | Just the translation; all original numbering symbols remain unchanged. |
| 2 | (0,1,2,3) | 1 | j | Just the translation; all original numbering symbols remain unchanged. |
| 3 | (0,1,2,3,4) | 2 | j∘j | Just the translation; all original numbering symbols remain unchanged. |
| 4 | (0,1,2,3,4,5) | 2 | j∘j | Just the translation; all original numbering symbols remain unchanged. |
| 5 | (0,1,2,3,4,5,6) | 3 | j∘j∘j | 4 |
| 6 | (0,1,2,3,6,7) | 3 | g | Just the translation; all original numbering symbols remain unchanged. |

The entire step size on the first five lines is achieved by the composite power of j; the sixth line is achieved by (8), which is indeed a=3 times **limit input**. Take m=1, and the linedness serves as evidence for j. All are embedded in Iter(j).

In the 5 row, the three predecessors marked by 4 are 1, while p(4)=2 and p(2)=1. Therefore

$$
\operatorname{tr}_5(4)=(4,2,1),\qquad j_5=j_4\circ j_2.
\tag{9}
$$

This is a global equality, stronger than the required weak truncation. Both factors with vertices 4 and 2 are ≥2. The adjacency requirement for the only internal edge 4→2 also holds for 3∈A₄.

### 4.2 Sat checks line by line.

According to `marked_blp_order_domain.md`, the eligible rows must meet q(e(i))≤p(i). In this example, the 2 and 4 rows are long rows, with no native completions. The remaining rows are as follows:

| i | p(i) | e(i) | q(e(i)) |
| --- | ---: | ---: | ---: |
| 1 | 0 | 1 | 0 |
| 3 | 1 | 2 | 1 |
| 5 | 2 | 3 | 2 |
| 6 | 1 | 2 | 1 |

Each item is equal to zero, resulting in a complete Sat. This is different from the raw short copy counterexample in the 2 section of the previous `full_marked_copy_work.md`.

### 4.3 is valid, while E(1) retains the incorrect marker.

First E(0)=del, leave five lines, then use the testimony of m=1 to add auxiliary lines with j. Its embedding and critical sequence fragments are

$$
e=g(j),\qquad
\operatorname{crit}(e)=\kappa_3,\qquad
e(\kappa_3)=\kappa_6,\quad e(\kappa_6)=\kappa_7.
\tag{10}
$$

Auxiliary complete behaviors: (3,6,7)), step size: 1, copies the source exactly as 3,4,5; mapping: ψ, fixed at 0,1,2, transforms x≥3 into x+3. The new three lines are

$$
\begin{array}{c|c|c|c}
i&s'_i&L'_i&j'_i\\\hline
6&(0,1,2,6,7)&2&e(j^{\circ2})\\
7&(0,1,2,6,7,8)&2&e(j^{\circ2})\\
8&(0,1,2,6,7,8,9)&3&e(j^{\circ3})
\end{array}
\tag{11}
$$

The old 0,...,6 columns remain as κ₀,...,κ₆, while the new columns are

$$
\theta'_7=e(\kappa_4),\quad
\theta'_8=e(\kappa_5),\quad
\theta'_9=e(\kappa_6)=\kappa_7.
\tag{12}
$$

The original mark 4 is copied to the mark 7 in the 8 row. The first vertex below a=3 in the trace is 2=a−1, which is strictly below the critical index of the auxiliary embedding, 3. Therefore, the PDF retains it in the 10(b) low branch. If the adjacent guard is also applied to the low branch, this example still passes: in the new core, 7 is at the 5 position, and A'₈[5+1−3]=A'₈[3]=2≤3.

The actual new transfer is exactly

$$
\operatorname{tr}'_8(7)=(7,2,1),
$$

Because p'(7)=2, p(2)=1, and the three-step predecessor marked 7 is still 1. The requirement is that

$$
e(j^{\circ3})\equiv_{e(\kappa_5)}e(j^{\circ2})\circ j.
\tag{13}
$$

### A direct proof of the negation of the closure of 4.4 on membership

Let H=e(j^{∘2}), β=e(κ₅). Since e is fixed with respect to κ₂,

$$
e(j^{\circ3})(\kappa_2)=e(\kappa_5)=\beta.
$$

On the other hand, from (10) and applying the identity,

$$
H(\kappa_6)=H(e(\kappa_3))=e(j^{\circ2}(\kappa_3))
=e(\kappa_5)=\beta.
$$

Therefore, ξ:=H(κ₃)<β, and

$$
(H\circ j)(\kappa_2)=H(\kappa_3)=\xi.
$$

Let u=ξ and v=κ₂ be both within V_β; the left image β contains ξ, while the right image ξ does not contain ξ. Therefore, (13) is false.

Output directly shows that the internal adjacency is lost: The new internal edge 7→2 requires 3∈A'₇. However, A'₇=(0,1,2,6,7) do not contain 3. The symbol for Sat is still maintained using the unified renumbering scheme of E.

Finite grammar cross-verification: Independently checked six input row types, all input and output Sat conditions, as well as two transfers. Then, these six rows were submitted to the E engine of `marked_blp_em_probe.py` for a fixed-point operation. The `kind` is the limit, the input is `issues=[]`, the output retains the mark 7 of the row 8. The actual trace is (7,2,1), and the only report is the aforementioned internal adjacency failure. No extensive rerun was performed, nor was the audit JSON of the engine rewritten. The embedding proof is given by the mathematical calculation of (7)—(13).

The E type, helper, and replication interval of this engine have been checked against the original paper item by item. This example helper satisfies p=c=3, thus it completely follows the low branching strategy; the deviation of the `iblp.py` high branching guard has nothing to do with this example.

The construction **Strict applicability.** refutes the claim that "every limit input that satisfies Sat, Floor₂, internal adjacency, and marked BLS semantics maintains a marked completion at E." It does not examine the birth history of P_start, and therefore cannot be used to refute the well-ordering of standard generating domains. It also does not imply that there is no other marked BLS implementation for the new grammar. A more powerful cardinality axiom would not correct the computational failure in this specified implementation, as any I3 j has indicated this failure.

## 5. Floor₂ is closed under known word operations

This section separates "numerical lower bounds preservation" from "whether the actual transfer equals the specified new term".

Let **Lemma 5.1.** denote the old transfer that satisfies Floor₂. The following verified operations on words are preserved:

1. The factor rows left by **Delete the tail and take the prefix.** and the chains by p have not been changed.
2. The new transfer that was born in the row r with **The original package was born.** is (r+h,u_h)), a unique factor.
r+h≥2. The standard first two lines have empty origins, so the non-empty origins are actually r≥3. The words that are split are unchanged; the words at the end are numbered monotonically according to ρ(t)=t (t≤r), t+q (t>r) transformation.
3. **Copy of full copy or low branching words.** has the replication factor v changed to φ(v), the non-replicating tail factor remains unchanged.
Invariant; all available copying mappings satisfy φ(v)≥v. Therefore, the lower bound remains unchanged.
4. **Copy the words with high branches.** copies the prefix, inserts a factor word with an active mark, originally not present
The end of each sequence is composed of old factors, and it may be renumbered using φ. The end point of the original active term is only used as a splicing point; if it subsequently contributes a factor, that factor is a non-end point factor that already exists in the original tail, and is still guaranteed by the old Floor₂. It is not possible to add a new factor to any end point.
5. Theorem **Whole package marking propagation.** `marked_completion_interval_lemma.md` 3.1
The verified new terms are (v₀+h,...,v_{r-1}+h,u_h),h≥1. All new factors are ≥2; the old terms are preserved and renumbered uniformly, while the lower bounds are also maintained. Versions with different non-negative displacements at different levels are also allowed.

**Proof.** operations on factors simply retain the factors, perform non-negative displacements, transfer them into other factors that already meet the lower bound, or generate factors with a number at least equal to 2. This can be checked item by item. The fact that endpoints are not considered factors is applicable to items 4 and 5, and cannot be omitted. Proof complete.

The word with the unique initial mark P_start is (3,1)), thus satisfying Floor₂; the unique factor of the standard Limit seed's marked words (y,y−2)) is y≥3, which also satisfies Floor₂.

Therefore, in the history of generating an **It has been proven that each actual transfer is produced by the operations described above.**, the rule Floor₂ holds by historical induction. This does not replace the complete word recognition theorem that is still missing from compTo: If one only knows that it returns a valid line without knowing that the actual p chain equals these words, then it is not possible to claim that the standard generating domain has completed semantic closure. On the other hand, the word recognition for the successor type E has been independently proven by (4), so the lemmas 2.1 and 3.1 do not carry this additional gap.

## 6. The exact historical information needed next.

The successor a=2 has been eliminated from the dangerous non-terminals a−1 by Floor₂. The limit a>2 does not hold: In the 4 section, (4,2,1) are precisely the dangerous chains of a=3, and they maintain these low-order invariants.

To prove the limit E in the standard domain, it is necessary to derive at least one of the following from the birth/population history:

- In the replication of E, a non-empty prefix never follows the non-terminal a−1; or
- When followed by a−1, its lower tail has additional semantics, causing H(crit(e)) to reach a new mark cutoff.
- Implementing with distinct semantic meanings with stepwise and capacity words, proving the required new markers and maintaining the original reduction budget.

Here, H is a prefix for replication factors, not an embedding of the entire owner row. Replacing the bounds of H with the adjacent guard of the entire owner row would be a mistake (the same mistake as 13)). The three strong edges of the Sat input with a common E (1) cannot individually complete this historical information.

## 7. Supplement: Floor₂ can be derived from positive marked sources without the need to first identify complete factor terms.

This section is independent of the word concatenation induction in the 5 section. For the mark y in the i row, let its actual step size be δ=A_i[pos(y)−L_i] (positive positions start from 1). Consider simpler structural conditions.

$$
\mathsf{PosSource}:\quad \delta\ge1\quad\text{for every mark}.       \tag{14}
$$

**Lemma 7.1.** If PosSource holds and the transfer of the mark is precisely defined, then every non-terminal factor is strictly greater than δ, and thus all are ≥2. That is, PosSource implies Floor₂; this deduction does not require knowledge of which proposed splicing word the actual trace equals.

**Proof.** is valid. The chain decreases strictly from p, and terminates upon reaching δ. Therefore, every non-terminal point is greater than δ. Proof complete.

**Lemma 7.2.** For ordinary BLP, The old p of non-empty native must be ≥1.

In **Proof.**, the core length is 2L. At L=1, the core is exactly (c,r),p=c), the next source is a=r, the native first-step reading is B(r)=c=p, so the source is empty. At L≥2, p is located in the Lth position in ascending order, at least in the 2th position, and the non-negative strictly increasing integers are given as p≥1. The short core length is 2L−1; the ordinary BLP rules exclude rows with a complete length of 4 and a step size of 2, so the allowed short rows are L≥3. Its p is located in the L−1th position, and also at least in the 2th position. Proof complete.

**Proposition 7.3.** Starting from P_start, Under all verified structural operations below: Keep PosSource: Legal short copy, auxiliary copy of E, native. And the edge set is a mark completion of "all old edges plus U→V". Therefore, as long as it is proven that each actual transfer is defined, Floor₂ is automatically established; There is no need to identify it with a global owner term.

**Proof.**   P_start The only source of the unique mark is 1 . No new marks are added after deletion. Legal copying maintains the within-row position and step size. Therefore, the new source that is marked is φ(δ); The copy mapping satisfies φ(x)≥x in its domain. So Xin Yuan is still ≥1. This applies to any copied branch.

The original source of the 'native' marks is retained for old marks; the source of the new marks is either the original p or the selected source u_h. When it is not empty, the lemma 7.2 is given to p≥1, and all u_h>p. The subsequent numbering is consistent without reducing the labels. The 'mark completion' retains the old edges, so the old sources remain unchanged; the source of the new marks is borrowed from the native source u_h≥1. Therefore, all source lengths remain positive. Inductive completion completed. Proof concluded.

The set of premises of the proposition only involves locally verified row structures, which is weaker than complete new mark factors and truncated semantics. It does not assume that the entire standard system is legitimate: the set of edges output by the full rules and the precise transfer still have unresolved interfaces. It also does not exclude the extreme counterexamples from the 4 section, which already have δ=1. Longer DEN2 rows need to be checked separately for the lower bounds of ordinary short rows, and the lemma 7.2 cannot be omitted and directly cited afterward.
