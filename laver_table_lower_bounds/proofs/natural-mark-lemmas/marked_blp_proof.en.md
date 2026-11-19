# Marked Completion BLP: A Proven Conservative Version with a Gap in the Complete Version · [中文版](marked_blp_proof.reading.zh-CN.md)

*English reading edition, translated with machine assistance. The title links to the dated Chinese manuscript.*

> Collected reading edition. The three main papers state the results of this collection.
> This edition retains the local proofs, their hypotheses and any withdrawals. Progress reports describe the state of work at the time.
> The locations of omitted passages on preset inputs are recorded in SOURCE_MANIFEST.json.
> The main papers give the numerical derivations for the natural parameters produced by the proofs. This historical note carries no additional Lean certification.

> Historical context note: This text retains the independent proofs from the early conservative versions. Users have subsequently expanded the continuous target.
> Complete notation: BLP well-order and IBLP / DEN2 well-order; current range, subsequent general long lemma, and unresolved
> The interface follows `wellorder_goal_state.md`. The term "target of this request" refers only to the writing of this document.
> Earlier requests for time cannot be used to narrow down the current objectives.

Verification date: 2026-09-07. The material is based on iblp.md of this catalog, the IBLP definition PDF, the old draft blp with the mark completion.md, and the [arXiv:2501.06733v5](https://arxiv.org/html/2501.06733v5) section 2. NE is verified according to the [DEN2.ts](https://github.com/SmileLee-lyx/ne-rewritten/blob/master/src/notations/DEN/DEN2.ts) obtained this time, and the local snapshot is at source_review/DEN2.ts.

The request from users with the symbol **Task object.** is to transform the infinite expansion back into a short copy of BLP, based on the marking rules of IBLP / DEN2. Design a complete BLP with marked completion, and prove that theorem 2.25 still holds. IBLP / DEN2 is its counterpart version with infinite expansion; in this case, infinite expansion allows for continued full tail copying with a finite number of parameters, and the output for each finite parameter remains of finite pattern. Proving that IBLP / DEN2 itself is well-ordered or extending the theorem to the infinite expansion version is not the goal of this request.

**The range of results.** The following construction creates a BLP system that automatically generates markers, uses markers to increase row entries and step sizes, and fully proves the corresponding conclusions of theorem 2.25. It is a conservative version of the note: it only allows two vertex transfer chains, the marker semantics is strengthened to row embedding global equality, and the completion adds finite computable edge checks.**The complete marked completion of BLP has not yet been proven; it cannot be said that the remaining work is "left with DEN2".** Even with BLP short copies, the truncation height of the complete marker rules, the block transfer, and the subsequent block recovery still need to be proven.

## 1. is an issue that needs to be corrected in the old notes/proofs.

### 1.1 complete lines, cores, and short replication endpoints

The entire text adopts the full line of a paper.

$$
s_i=(s_{i,1}<\cdots<s_{i,-2}=i<s_{i,-1}=i+1),
\quad A_i=s_i\setminus\{i+1\},
\quad d(i)=A_i[-(\ell_i+1)].
$$

The positive index starts from 1. Let the last row be numbered n, let

$$
L=\ell_n,\qquad a=A_n[-L-1],\qquad e=A_n[-L],\qquad c=A_n[1].
$$

The source line that copies 2.12 is exactly

$$
\boxed{a,a+1,\ldots,e-1.}
$$

Therefore, in **The term "core" is used under certain conventions.**, the endpoint $A_n[-L]$ written by note should be reduced by 1. The full tail replication $a,\ldots,n$ of the IBLP cannot directly replace this operation.

### The old manuscript used the wrong truncation equivalence semantics for the symbol 1.2.

The Laver truncation equivalence required here is

$$
f\equiv_\alpha g
\iff
\forall x,y\in V_\alpha\;(x\in f(y)\iff x\in g(y)).
\tag{1}
$$

It compares $f(y)\cap V_\alpha$ with $g(y)\cap V_\alpha$, different from the old draft S.3 which had a general function limit.
$f\restriction V_\alpha=g\restriction V_\alpha$.

The old manuscript S.8 has a complete counter-example under its own strong semantics. Take I3 to embed j, the critical sequence is $\kappa_0<\kappa_1<\cdots$, let

$$
\theta_i=\kappa_i\ (0\le i\le4),\qquad j_1=j_2=j,\qquad j_3=e:=j(j(j)).
$$

Complete Behavior

$$
s_1=(0,1,2),\quad s_2=(0,1,2,3),\quad s_3=(2,3,4),
\quad \ell_1=\ell_2=\ell_3=1.
$$

Only $M_2=\{1\}$ is non-empty. Since $\operatorname{tr}_2(1)=(1,0)$, $j_2=j_1$, this is a valid marked BLS under the old definition, and can be taken as $m=1$.

When copying the last line, $a=c=2$, only the source line 2 is copied. The old rule retains the marker $y=1<c$, and the new end is $(0,1,3,4)$, with the new end embedded as $e(j)$. However, $e(j)\circ e=e\circ j$ and e remain fixed as $\kappa_1$. Therefore,

$$
e(j)(\kappa_1)=e(\kappa_2)=\kappa_3
\ne\kappa_2=j(\kappa_1),\qquad \kappa_1\in V_{\kappa_2}.
$$

The output does not satisfy the strong markup semantics of the original draft. **This counterexample is directed at the semantics of the old manuscript and is not an example of the correct weak truncation version.**

### 1.3 is the factor position that crosses the replication boundary

Let the source transition chain be $(i_1,\ldots,i_{l'})$, and $i_l$ be the first vertex that is less than a. If

$$
i_l=A_n[k],\quad z=A_n[k+L],\quad
\operatorname{tr}_n(z)=(m_1,\ldots,m_s),\quad m_s=i_l,
$$

The factor chain corresponding to a valid concatenation should be

$$
\varphi(i_1),\ldots,\varphi(i_{l-1}),
m_1,\ldots,m_{s-1},i_l,\ldots,i_{l'-1}.
\tag{2}
$$

The prefix has been copied up to $l-1$, while the tail starts from $i_l$. In the old manuscript, note and $j_n(j_{i_l})$ were left on the left, with the tail starting from $i_{l+1}$, which is not a factor of this transfer. After correcting this, it is still necessary to prove that the truncation height is sufficient.

## 2. Direct Marking Pattern and Its Implementation

Let $\widehat p=(s,\ell,M)$ be referred to as **Directly marked BLP** in this paper. If the underlying $(s,\ell)$ is a BLP defined by the paper as 2.6, and every $y\in M_i$ satisfies

$$
2\le y<i,\qquad y=A_i[k],\qquad k>\ell_i,\qquad
A_i[k-\ell_i]=d(y).
\tag{3}
$$

that is

$$
\operatorname{tr}_i(y)=(y,d(y)).
$$

A**Directly marked BLS** is an ordinary BLS of the underlying pattern, plus

$$
\boxed{y\in M_i\Longrightarrow j_i=j_y.}
\tag{4}
$$

(4) represents global function equality, thus implying the local requirements for this type of transition chain. This defines a smaller but provably closed system, rather than interpreting all DEN2 as global equality.

Excluding 0 and 1 ensures that all markers can be restored during subsequent replication. Excluding i allows the markers to only reference earlier rows. There are no markers in the first and second rows. To delete the tail, simply remove the last row and its markers.

## 3. replication holds the lemma

The definition of 2.12 is based on the fundamental properties of replication and the use of copies. For the entries that are actually needed,

$$
\varphi(x)=
\begin{cases}
x,&x<c,\\
A_n[k+L],&x=A_n[k]<a,\\
n+x-a,&x\ge a.
\end{cases}
$$

This operation is performed only when all conditions for reproduction of the paper are met. For the source line $\sigma\in\{a,\ldots,e-1\}$ and the target line $\tau=n+\sigma-a$, the following definitions are established:

$$
M'_\tau=\{\varphi(y):y\in M_\sigma,\ y\ge a\}.
\tag{5}
$$

The markers in the previous $n-1$ rows are retained. The cross-border rules defined by PDF for 10(b) are not adopted here.

**Lemma.** The replication maintains direct marking implementation, m, the first two and the last base numbers; the last embedding is $j_n(j_{e-1})$.

**Proof.** uses the standard copied BLS. If y is retained, then $a\le y<\sigma\le e-1$ is also copied, and thus the referenced line y has also been copied.

$$
j'_\tau=j_n(j_\sigma)=j_n(j_y)=j'_{\varphi(y)}.
$$

A strictly increasing copy mapping preserves the row position and step size, and provides $d'(\varphi(y))=\varphi(d(y))$. From (3), a new direct transition condition is derived. Other properties are established by the ordinary copied BLS construction. Proof complete.

## 4. ordinary completion results in completed packages and new markings

Only the appropriate lines of the paper are subjected to standard completion; this model does not automatically add all the short line completions of PDF. Let the complete line length of the current line in the r position be $2L+1$, $L\ge2$, let

$$
p=s_r[L]=d(r),\quad a=s_r[L+1],\quad
T=(u_1<\cdots<u_q),\quad p<u_1<\cdots<u_q<a.
$$

The T selected using the fullcomp function in papers usually involves taking the third-to-last item of each complete row starting from a, repeating until the value is no larger than p. The internal vertices are then selected and arranged in ascending order. If T is empty, no action is taken.

For general completion, replace the original line at r with the following complete line:

$$
\begin{aligned}
s'_{r+h}
 &=\operatorname{sort}\bigl(A_r\cup\{u_1,\ldots,u_{h+1}\}
       \cup\{r+1,\ldots,r+h+1\}\bigr),&
\ell'_{r+h}&=L+h+1\quad(0\le h<q),\\
s'_{r+q}
 &=\operatorname{sort}\bigl(A_r\cup T\cup\{r+1,\ldots,r+q+1\}\bigr),&
\ell'_{r+q}&=L+q.
\end{aligned}
\tag{6}
$$

The old row numbers and columns are as follows:

$$
\rho(x)=x\ (x\le r),\qquad \rho(x)=x+q\ (x>r)
$$

Renumbering: The lines before the original line at r remain unchanged, while the lines and entries after the original line at r are transformed accordingly.

The old markers that were removed are retained in the new lines; the $r+h$th line has new markers added to it.

$$
r,r+1,\ldots,r+h-1\qquad(0\le h\le q).
\tag{7}
$$

Other old labels are renumbered according to $\rho$. The label $\operatorname{Rec}(r)=T$ is preserved, as the constructed **Complete package properties** is guaranteed by the construction.

$$
\theta_{r+h}=K(\theta_{u_h})\ (1\le h\le q),\qquad
j'_r=j'_{r+1}=\cdots=j'_{r+q}=K,
\tag{8}
$$

Among them, K represents the original embedding in the rth row. Records are only allowed to be generated from this construction, and no sequence can be arbitrarily input as a valid package.

The ordinary completion of **Lemma.** retains all the old markers, and all the new markers generated satisfy (3)–(4).

**Proof.** Ordinary BLS Completion Insertion $K(\theta_{u_h})$, And use K in all replacement lines. Therefore, the underlying implementation and (8) hold true.

Let $u_0=p$. It can be read directly from (6).

$$
d'(r+h)=u_h\qquad(0\le h\le q).
$$

In the $r+k$ row, the step-size predecessor of the entry $r+h$ (h<k) is $u_h$, so the new marker is transferred to $(r+h,u_h)$; the embeddings in the corresponding rows are all K.

For the old markers that have been removed, $y=A_r[k]$ is replaced by $k>L$, y<r. After the new source entries are added, the old step predecessors are in the L position or earlier. In the intermediate rows, both the marker positions and step lengths are increased by h+1; in the final row, both increase by q. Therefore, the old predecessors remain unchanged, as does the referenced y row. For the subsequent old rows, if the referenced row is r, then the new header row still has $d'(r)=d(r)$, with an embedding of K; other references are simply uniformly renumbered. All old markers are retained. End of proof.

## 5. uses marked completion to construct packages.

Let the current line be i, and there be a mark y, and there are already non-empty records.

$$
\operatorname{Rec}(y)=(u_1<\cdots<u_q),\qquad y+q<i.
$$

At this point, $\operatorname{tr}_i(y)[-2]=y$ is the direct transfer situation defined by PDF for 13. Let

$$
U=\{u_1,\ldots,u_q\},\quad V=\{y+1,\ldots,y+q\},\quad
s_i^+=\operatorname{sort}(s_i\cup U\cup V),\quad \ell_i^+=\ell_i+q.
\tag{9}
$$

Definition

$$
\operatorname{Edges}(s,L)=\{(s[k],s[k+L]):1\le k\le |s|-L\}.
$$

This operation is performed only if the following **Finite grammar check** all pass. (9):

1. $|U\cup V|=2q$, and $(U\cup V)\cap s_i=\varnothing$.
2. The minimum entry remains unchanged, with the last two items still being i,i+1. The new complete row and new step size satisfy the BLP row condition.
3. Every old step boundary, every pair of newly added $u_h\mapsto y+h$, is a new step boundary. It can be checked directly.

$$
\operatorname{Edges}(s_i^+,\ell_i+q)
=
\operatorname{Edges}(s_i,\ell_i)\cup\{(u_h,y+h):1\le h\le q\}.
\tag{10}
$$

Skip if there is a failure. After success, only the elements that satisfy the new (3) are retained in $M_i\cup V$; the newly added source U is not marked. Other lines remain unchanged.

This step**Do not insert global rows or columns.**:U,V are all columns that have been named through ordinary completion before this. It only adds confirmed correspondences to the current row, rather than creatingy+h a new base number out of thin air.

The rule **Lemma.** maintains direct marking of BLS implementations, all cardinality, and row embeddings.

**Proof.** consists of marked completion packages.

$$
j_i=j_y=K,\qquad
j_i(\theta_{u_h})=\theta_{y+h},\qquad j_{y+h}=j_i.
$$

Therefore, each edge on the right side of (10) is realized by the same $j_i$; the minimum entry ensures that its critical points are correct.

It is also possible to check the position difference row by row: the old edge number is $|s_i|-\ell_i$, and the new edge number is

$$
(|s_i|+2q)-(\ell_i+q)=(|s_i|-\ell_i)+q.
$$

Since the new sources are not in the old lines, the old edges and the new edges marked with q are distinct from each other, and the number of edges exactly covers all the new edges.

Retain the original global equality for the old markers. The new symbol is denoted as $j_{y+h}=j_i$. And the filtering by (3) ensures effectiveness. Also check other rows: The old boundary $(d(i),i)$ is retained in (10). i is still the second-to-last item. So the new d(i) is equal to the old d(i). The direct transfer from other lines referencing i also remains unchanged. Proof completed.

## 6. finite scan, M and E

Define finite scanning C: Initially, let Rec be empty. From left to right, only the rows that exist at the time of scanning are accessed. Upon reaching each row, freeze its existing marked set and attempt to complete it according to the order of the 5 section. If the current row is suitable, perform the 4 section fullcomp and save the record. The newly inserted rows are skipped, and the new marks are not processed again in the same step. After the scanning is completed, discard Rec, which is not part of the output pattern.

Scanning must be finite: the number of old lines is finite, the number of markers frozen at each time is finite, and the source chain is strictly decreasing. Insertions further back do not change the saved packages and their source sequences. By the first two lemmas, scanning maintains direct marker implementation, m, the first two and last cardinals, and the last embedding.

Definition

$$
\widehat p.M=C(\widehat p.\mathrm{Copied}).
\tag{11}
$$

This completion order differs from the original paper M, but it retains the endpoints and end-embedding properties necessary for induction. It does not claim that the values of the new functions are the same as those of the old functions.

For the successor/limit type, E is recursively defined as 2.16 according to the paper definition: $E(0)=del$. Subsequently, the unmarked three-row structure as defined in the original definition is added, followed by replication in section 3. The corresponding **The scan does not increase within E. C.** in BLS E is established using the original definition of 2.18 with linedness as a witness for the establishment of auxiliary lines, and then marked with the replication lemma.

Therefore, M and E are retained as m and $\theta_0,\theta_1,\theta_{-1}$, respectively. The last embedding of M is $J(P)(h)$; the last embedding of E can be written as $(J(P)(h_0))(h_1)$, with the intermediate embedding critical points being less than the original base number, as in the lemma of the original paper 2.19.

## The corresponding conclusions and complete proofs of the theorem 7. 2.25

Definition: A computable function (in a top-down order)

$$
F(\widehat p,m)=
\begin{cases}
m2^m,&p\text{ is the zero pattern},\\
F(\widehat p.del,m),&p\text{ cannot be copied},\\
g^{2^m}(m),\quad g(x)=F(\widehat p.del,x),&p\text{ is of successor type},\\
F(\widehat p.E(m),m),&p\text{ is of limit type},\\
F(\widehat p.M,m),&\text{otherwise}.
\end{cases}
\tag{12}
$$

The underlying types are judged according to the definition in the original paper, using 2.15.

**Theorem.** Under the frameworks of I3 and $\operatorname{Iter}(j)$ of the original paper, If P is a direct implementation of BLP $\widehat p$, it is a direct implementation of BLS. m=P.m， Then $F(\widehat p,m)$ is defined. and

$$
\boxed{(P.\theta_0,P.\theta_1,P.\theta_{-1})
\text{ is }F(\widehat p,m)\text{-lined}.}
$$

### 7.1 Outer well-founded induction

Let $\Theta(P)$ denote the last cardinality, and J(P) denote the last embedding. Define the well-founded relation of 2.28 from the original paper: the last cardinality decreases strictly, or when the last cardinality is equal and the last embedding becomes the original last embedding applied to another $\operatorname{Iter}(j)$ that is an embedding, then take the transitive closure. The well-foundedness comes from the lemma 2.27 of the paper. The additional markings do not change the descending parameter. It is not assumed here that the order relation of DEN2 is well-founded.

The deletion strictly reduces the final cardinality. M is composed of a single replication and a finite scan with invariant embedding, hence P.M<P. The two applications of E and the intermediate critical point bounds give P.E<P. Their direct marking implementations have been proven in the previous text.

The zero pattern uses the basic linedness of the original paper to amplify the lemma. The non-replicable branch is first applied to P.del using induction, and then the critical point is used as the column deletion base to embed it into the original base. This is applied to the last linedness witness, extending the endpoint while maintaining the number of witnesses; the required embedding exists by the lemma 2.11. The limit branch and M branch directly use strict reduction and retention of the starting base.

The following additional checks are required for the successor branch.

### 7.2 Successor expansion restores all markers

Let p be the successor type, $\widehat q=\widehat p.E(t)$, $N=\widehat q.n$. The first row of the auxiliary three-point row is 2; the source row is 2,...,N, and the replication map is...

$$
\psi(x)=x\quad(x<2),\qquad \psi(x)=x+N-1\quad(x\ge2).
\tag{13}
$$

The old block is the previous N rows, and the new block is the rows N+1,...,2N-1. Since each marker y≥2, (5) is marked in this replication as **No markers were lost.**.

Take any $Q\models\widehat p.E(t+1)$, and it does not require that Q come from a copy of a specified implementation. The old block $R^{old}=Q|N$ implements $\widehat q$, whose final cardinality

$$
\nu=Q.\theta_{N+1}<Q.\Theta.
$$

Extract new blocks, define

$$
\begin{aligned}
R^{new}.\theta_0&=Q.\theta_0,&R^{new}.\theta_1&=Q.\theta_1,\\
R^{new}.\theta_s&=Q.\theta_{s+N-1}&&(2\le s\le N+1),\\
R^{new}.j_s&=Q.j_{s+N-1}&&(2\le s\le N).
\end{aligned}
$$

The 1 row can be directly replaced with $R^{new}.j_1=R^{new}.j_2$: Copying the second row of the block to create $(0,1,\psi(2),\psi(3))$, with a step size of 1, so the first three items exactly implement the new first row. Alternatively, this row can be constructed using the base number transfer lemma from the original paper.

(The inverse renumbering of 13) restores all rows and step sizes. For any $y\in M_s$, the marked semantics of Q have been given.)

$$
Q.j_{s+N-1}=Q.j_{y+N-1},
$$

So, $R^{new}.j_s=R^{new}.j_y$. y≥2 ensures that no supplementary construction is involved in the 1 row; the relocation positions are also fully restored. Therefore, $R^{new}$ achieves the entire $\widehat q$, not just the unmarked mode.

If there are M-lined witnesses for $(Q.\theta_0,Q.\theta_1,\nu)$, they can be used as the initial witnesses for $R^{new}$, and $R^{new}.m=M$ can be set. These data do not change the row embedding and marking. At the same time

$$
\Theta(R^{new})=\Theta(Q),\qquad J(R^{new})=J(Q).
\tag{14}
$$

### A double induction for the successor branch of 7.3

Fix the successor type P, and let it be $g(x)=F(\widehat p.del,x)$. Prove for t

$$
H(t):\quad Q<P,\quad Q\models\widehat p.E(t)
\Longrightarrow
g^{2^t}(Q.m)\text{ is defined and is a lower bound on the linedness of Q}.
$$

H(t) quantifies all positive integers Q.m at the same time. H(0) directly uses the outer induction to implement $\widehat p.del$'s Q.

If H(t) has been proven, take $Q<P$ to achieve E(t+1). The base number at the end of the old block is strictly smaller, hence $R^{old}<Q<P$. From H(t),

$$
M=g^{2^t}(Q.m)
$$

There are definitions, and there are M witnesses that lead to $\nu$. Use them to establish a new block in the 7.2 section and set the parameter M. Since (14), the new block has the same decreasing parameter as Q, it follows that $R^{new}<P$. Then, using H(t), we obtain a defined...

$$
g^{2^t}(M)=g^{2^{t+1}}(Q.m)
$$

And the required witness. This also proves the definability of each iteration evaluation.

Finally, let t=m=P.m, substitute Q=P.E(m)<P, and using the first two sums and the last base number, we obtain the successor branch of (12). Once all branches are completed, the theorem is proven.

**Quantifier restrictions.** has not been proven to have a grammatical pattern for any given set of markers, therefore it cannot be directly copied from the original paper Remark 2.26. The assertion F that it is fully defined for all marked grammatical inputs cannot be accepted. The theorem here states that it is true for every direct marker BLS implementation.

## An actual example of an implementable marked completion with a trigger 8.

Take the complete row:

| Line number | Complete row | Step size | Mark |
| --- | --- | ---: | --- |
| 1 | (0,1,2) | 1 | Just the translation; all original numbering symbols remain unchanged. |
| 2 | (0,1,2,3) | 1 | Just the translation; all original numbering symbols remain unchanged. |
| 3 | (0,1,2,3,4) | 2 | Just the translation; all original numbering symbols remain unchanged. |
| 4 | (0,1,2,4,5) | 2 | Just the translation; all original numbering symbols remain unchanged. |
| 5 | (0,1,3,5,6) | 2 | Just the translation; all original numbering symbols remain unchanged. |
| 6 | (0,1,3,5,6,7) | 2 | 5 |

This pattern has a direct marking implementation: first take any ordinary implementation of the underlying BLP (as stated in the original paper Remark 2.26), and then let it be $j_5=j_6$. The requirement in the 5 line is a subset of the requirement in the 6 line, so the substitution is valid; the other lines are unmarked. d(5)=1, the entry in the 6 line with 5 as its two-step predecessor is also 1.

In the 5th row, fullcomp is chosen as T={2}: the source gaps are (1,3). In the 3th row, the third last term is 2, and then it is chained to 1 to stop. The three rows after the normal completion are...

$$
\begin{array}{c|c|c|c}
i&s_i&\ell_i&M_i\\\hline
5&(0,1,2,3,5,6)&3&\varnothing\\
6&(0,1,2,3,5,6,7)&3&\{5\}\\
7&(0,1,3,5,7,8)&2&\{5\}.
\end{array}
$$

Record Rec(5)={2}. Process the marker 5 in the 7 row, borrow the corresponding $2\mapsto6$ from the completion package, to obtain

$$
\boxed{s_7^+=(0,1,2,3,5,6,7,8),\quad \ell_7^+=3,\quad M_7^+=\{5,6\}.}
$$

The difference between the old edge $0\mapsto3,1\mapsto5,3\mapsto7,5\mapsto8$ and the new edge $2\mapsto6$ is entirely of the form 3 within the new row. This indeed increases the information about the mapping and the step size.

check_guarded_mark_completion.py has verified this example, rejecting any repeated insertions and incorrect new edges. The E of the three a=2 instances have been copied to verify all rows and marked blocks. The number of rows is 13, 25, and 49. The output is guarded_mark_completion_checks.json. The program only checks for finite syntax and edge certificates; embeddings and termination depend on the aforementioned mathematical proofs and are not replaced by finite tests.

## What remains for the goal of complete marked completion BLP with 9. distances?

**Follow-up research updates.** full_marked_copy_work.md has further provided a truly achievable input, refuting the claim that "under any bare marked BLS, the original short copy filtering preserves the correct weak truncation semantics." It is not a counterexample to the standard initial item generation domain, nor has it been proven that no other implementations exist for the output. The user has subsequently defined the well-ordering goal as being within the standard generation domain; therefore, the complete route must retain and prove additional invariants of the generation process. It cannot rely on the universal preservation lemma of any bare marked BLS as an unverified premise.

1. **A complete copy of the weakly truncated computation.** uses (1), modified by (2), to prove that each left composition and the truncation after tail replacement are at least aimed at $\theta_{x+1}$.
2. When q are inserted after **Save the entire history of bounds in a package.** y, the old $\theta_{y+1}$ becomes the new $\theta_{y+q+1}$. The current bare markings only require equivalence to the new $\theta_{y+1}$, and cannot be inferred solely to the new marking equivalence of $\theta_{y+h+1}$. The proof status during scanning should preserve the old truncated renumbering, the width of each transfer package, and the embedding copy relationship. Then prove that the PDF adjacency condition is sufficient, or add computable package-level checks. It is insufficient to simply state that "the new marking is a restriction of the old equivalence."
3. **The successor block is restored or replaced recursively.** After adding long-chain markers or additional completions to E, It is necessary to re-prove the extraction of all marked blocks. Only implementation of closure, head-tail preservation, and end-embedding descent are required. It is not sufficient to support the formula for the original successor branch $2^m$ after the specified number of iterations.

Independent verification also found a pure grammatical example that causes duplicate entries in the marked completion of the bare PDF. However, its original marking condition contradicts the row mapping, and it cannot be implemented with a marked BLS. Therefore, it only negates the unconditional statement that "every grammatical state automatically has a complete package," **It is impossible to refute the conditional theorem that the user wishes to prove.**. Replay analysis is provided in den2_definition_work.md and den2_packet_probe.py.

Another version difference: In this case, the compTo for DEN2 does not include the PDF definition of the layer-by-layer adjacency check for 13(3), nor does it have the de-duplication step; the threshold processing for seqFrom also differs. The current source code cannot be identical to the PDF word for word. The next step of the complete goal must fix the version that has been proven.

This paper completes the conservative theorem of the 2–8 section. The full version of BLP short replication, allowing general transfer chains and note truncation marking semantics has not yet been proven. The infinite expansion version of IBLP / DEN2 and its ordinal well-ordering are a different level of problem, and they are not considered as goals to be completed in this paper.

## 10. Supporting Verification Documents

- audit_draft_work.md: Old manuscript audit, containing a complete strong semantic counterexample with its S.8.
- theorem_transfer_work.md: Independent proofs for the original theorem interface and subsequent block extraction.
- den2_definition_work.md: PDF / source code differences, package transport problems, and unimplementable pure syntactic counterexamples.
- check_guarded_mark_completion.py, guarded_mark_completion_checks.json: Limited checks of the conservative rules in this document.
- source_review/DEN2.ts: This is a snapshot of the source code from this round of verification.

The original notes, PDFs, and old documentation have been retained.
