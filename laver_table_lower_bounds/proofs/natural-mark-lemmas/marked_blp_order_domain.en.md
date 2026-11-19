# Complete Marked Short Copy BLP: Generation Domain, Parameter Operations, and Comparison Bridges · [中文版](marked_blp_order_domain.md)

*English reading edition, translated with machine assistance. The title links to the dated Chinese manuscript.*

> Collected reading edition. The three main papers state the results of this collection.
> This edition retains the local proofs, their hypotheses and any withdrawals. Progress reports describe the state of work at the time.
> The locations of omitted passages on preset inputs are recorded in SOURCE_MANIFEST.json.
> The main papers give the numerical derivations for the natural parameters produced by the proofs. This historical note carries no additional Lean certification.

2026-09-07. This text only fixes the syntax and order relationship interface for the first stage of the "complete marked BLP" of "short replication". Following the general 'transfer' marker used with `iblp.md` and the rules for copying/completing markers in PDF, the notation is not condensed into two vertex markers. This text does not prove the weakly truncated semantic closure of these markers; `full_marked_copy_work.md` has demonstrated that the general replication preservation lemma for bare marked BLS is false, indicating that standard generating domains still require historical invariants.

## Two finite systems that must be distinguished in 1.

To align with the user's original theorem 2.25, **The current main design adopts the framework of the paper E/M**, the complete left-to-right marking scan and comparison bridges are provided in the sections 8–10. In the 2–5 section, the method of "shortly repeating several times, deleting the tail, and then scanning and completing" is only retained as a literal rewriting of the original note, serving as an independent audit rather than the default system.

The original paper has another set of interfaces: transient terms are done as `.M`, limit/successor terms are done as special `.E(k)` terms, and non-replicable terms are done as `.del` terms. The paper `.E(k)` adds auxiliary three-row copies each time; `.M` completes all suitable rows. This is not the same algorithm that repeatedly short-copies the last line. If it is intended to generalize the function formula of theorem 2.25, it is necessary to retain and review this E/M difference, and it cannot be automatically replaced by the same E in the cyclic system.

Short replication cyclic systems have direct prefix comparison bridges; the E part of the E/M main design also has these bridges. The standard completion saturation invariants required for the M part are proven in the 9 section.

## 2. Ordinary BLP Row Type and Short Copy

Please use a complete line.

$$
s_i=(\cdots<i<i+1),\qquad A_i=s_i\setminus\{i+1\}
$$

Representation pattern. The base line length/step size strictly follows the definition in the paper, 2.6. The first two lines are fixed as `(0,1,2)L1` and `(0,1,2,3)L1`. n=2 is the zero pattern for the first stage, and does not delete the first two lines anymore. Generally, the transfer defined by M_i \subseteq A_i) is defined as 7 in the PDF. The copying and marked completion are fixed according to the PDF definitions for 10 and 13, and are not mixed with the source code that lacks adjacency checks in the current DEN2.

For the last line of n>2, let

$$
L=\ell_n,\qquad c=A_n[1],\qquad
a=A_n[-L-1],\qquad e=A_n[-L].
$$

The source line that shortens S is:

$$
\boxed{a,a+1,\ldots,e-1},
$$

Instead of containing e. The first n−1 lines remain unchanged, and the source line σ is sent to n+σ−a. The same entry mapping φ and marking retention rules are used as in the PDF. If any required φ is undefined, the short copy is undefined. The number of output lines is

$$
n'=n+e-a-1\ge n.
$$

Here, it may be n'=n: When e=a+1, short replication only replaces the last line, without adding a new line. This is a detail that needs to be distinguished from full tail replication.

Let C_n represent the left-to-right marked/fundamental completion scan starting from **Original line number n**, with an initial state of being empty. After inserting a row, skip the newly added block according to the PDF. It does not process the original rows before n−1. No scans are inserted during each replication process.

## The parameter operation 3. cannot only check the first replication.

The most direct operations are:

$$
D_0(A)=\operatorname{cut}(A),\qquad
D_m(A)=C_n\bigl(\operatorname{cut}(S^m(A))\bigr),\quad m\ge1,
\tag{1}
$$

Among them, it is required that all the first m shortest copies are defined, and subsequent scans are also valid. The standard domain can be defined as the smallest set generated from the specified root through these valid operations.

However, for each natural number parameter to have program output, (1) is not enough. Short replication is defined only once, and it is not guaranteed to be defined again; this issue has already occurred in the actual legal generation domain of the initial terms in five lines.)

### An explicit example from the standard root

Let P represent the initial term of the working area

```text
(1,0)1(2,1,0)1(3,2,1,0)2(4,*3,2,1,0)2(5,4,3,2)2
```

Perform direct short replication twice, remove the tail. The required scanning does not result in any non-empty completion, yielding

```text
D2(P) = (1,0)1(2,1,0)1(3,2,1,0)2(4,*3,2,1,0)2(5,4)1(6,5,4)1
```

Replicate D0 to obtain

```text
A = (1,0)1(2,1,0)1(3,2,1,0)2(4,*3,2,1,0)2(5,4)1.
```

The continuous short replication of A is:

```text
S(A)   = (1,0)1(2,1,0)1(3,2,1,0)2(4,*3,2,1,0)2(5,*3,2,1,0)2
S²(A)  = (1,0)1(2,1,0)1(3,2,1,0)2(4,*3,2,1,0)2(5,3,2)1
S³(A)  = (1,0)1(2,1,0)1(3,2,1,0)2(4,*3,2,1,0)2(5,3,1,0)2(6,*5,3,1,0)2.
```

The fourth activity core is `(0,1,3,5,6)`, L=2, hence a=3, e=5. It is necessary to copy the source lines 3, 4. However, the core of the source line 3 is `(0,1,2,3)`, and the required φ(2) is undefined: `0≤2<3`. There is no entry 2 in the activity line. Therefore, **S⁴(A) is undefined.** is defined, although S(A) is undefined.

The above mathematical research manuscript has been checked item by item using the original `iblp.py`'s Pattern, entry mapping, and PDF marking screening auxiliary function. The source intervals have been copied to `[a,e)` only in memory, without modifying the original file. The counterexample does not depend on the marking semantics, nor is it an infinite descending chain. It indicates that the parameter algorithm needs to address the subsequent replication failure branches.

### A fully parametrically definable design

If it is acceptable to include failed behaviors as part of the design, it can be stipulated that for the parameter m, the process stops upon encountering the first failure within a maximum of m repetitions. Let X be the state of final success (if not achieved at all, then X=A), and return.

$$
\widehat D_m(A)=C_n(\operatorname{cut}(X)).
\tag{2}
$$

It remains to be proven whether scanning its own grammatical correctness is a necessary condition; therefore, it is not omitted. The rule (2) is merely a definition for failure in replication; it differs from the text that reverts to cut only upon the first replication failure. Each finite parameter can only undergo a finite number of replication attempts, without the need to determine whether there will be further failures. All parameters that exceed the number of successful attempts yield the same result.

If no rules are added, then the legal parameter initialization segment of (1) can be retained; the following order relations also apply to (1) and (2).

## The prefix of the short replication cycle 4. and the strict comparison descent

The premises of the following conclusions are: each performed replication and completion are valid, and the output still satisfies the ordinary BLP row type. Compare the core row keys defined using PDF for 4–5.

### Copying chain prefixes with deleted tails nested

S(X) is retained as cut(X), and the number of rows is not less than X, therefore

$$
\operatorname{cut}(X)\sqsubseteq\operatorname{cut}(S(X)).
$$

Therefore, `cut(S^m(A))` is nested with the prefix m before it. Even if some copies have the same length, this conclusion still holds, and the corresponding column deletion results may be equal.

The left-to-right scan of C_n relies only on the current row and the rows and records before it, thus maintaining the prefix at the word boundary: Two scans read the same transfer, records, and source chains on the common old row, inserting the same block of data; scans further down do not alter the earlier rows.

$$
D_0(A)\sqsubseteq D_1(A)\sqsubseteq D_2(A)\sqsubseteq\cdots
\tag{3}
$$

It holds for all valid parameters. The stop version (2) only makes the sequence a constant value after the first failure, while still having (3). All sub-items contain the prefix cut(A).

### The first copy line strictly reduces the comparison key

Let the active core be `a1<...<at=n`, the step size be L, and the minimum entry be c=a1. Their comparison keys are

$$
K=(a_t,a_{t-1},\ldots,a_{L+1},c).
$$

The first line of the research manuscript comes from the source line a, and each source entry is marked as x≤a. Valid φ(x) either is an element of the active high segment `{a_{L+1},...,a_t}`, or is less than c; whereas c itself is not in the image. Therefore, the reverse-order retention key of the first line is strictly less than K: it either is an early leakage in the high segment, or becomes a true prefix, or appears after the high segment with a value less than c. The previous n−1 lines remain unchanged, hence S(A)<A.

If a continuous short copy is always of equal length, it will repeatedly reduce the key of the nth line. Once the length increases, the subsequent copies retain the reduced nth line. Therefore, as long as there is still a nth line after the tail is deleted, its key is still strictly less than the original nth line. Otherwise, the output is the cut(A)th line.

C_n does not have a previous record in the first scanned row, so the marked completion does not affect it. In a typical BLP, the core rows that can perform non-empty native completions only need to consider two cases: rows of length 2L or 2L−1. The newly added/deleted entries in the first intermediate row are all below the retained high segment, and the step size adjustment precisely maintains the length of the high segment, so their comparison keys remain unchanged. Subsequent scans do not change this.

Therefore, for every non-zero input in (1), (2), the actual subterm is strictly less than the input.

### Standard domain comparison bridge

Select a finite root P, or a subterm nested in the form of a vertex T. Set the zero pattern as the endpoint. The cut, (3), subterm retention cut(A), strict reduction at each step, the prefix barrier theorem of `order_domain_audit.md` in the 5 section directly gives

$$
\boxed{B\le A\quad\Longleftrightarrow\quad A\longrightarrow^*B}
$$

This standard holds for the generated domain. Therefore, the comparison key is a bijection in the standard domain, and being well-ordered is equivalent to being a well-founded relation. This is a theorem that conditions the legitimacy of operations, and it does not use finite tests to replace the proof of semantic well-foundedness.

## What standard roots should be chosen for the first stage of 5.?

The most natural main domain, which does not require the creation of additional vertices, is the five rows P_start of the workspace, along with their legitimate short copies and downward domains. It satisfies the general BLP row type, with the unique label being the 3 row of the 4 row; the initial ω-rich row is implemented as seen in `standard_omega_rich_realizations.md`.

The infinite limit of DEN2 cannot be used as a regular BLP root in its entirety. DEN2 Lines only i≥3 Take the core `(0,...,i)` , Step length is constant 2 ;  When i≥5 The row-type condition for the ordinary BLP no longer allows this step size. Only short valid prefixes can be retained. It cannot be called a regular BLP just because it has a line embedding implementation.

If it is indeed desired to have another form of Limit in the first stage, one can use the family of ordinary BLP roots **Clearly defined alternative definition** to R_N:

$$
A_i=(0,1,\ldots,i),\qquad
L_i=\left\lfloor\frac{i+1}{2}\right\rfloor,
\quad 1\le i\le N,
$$

Among them, the step size of i=1 and 2 is 1. For even-indexed i≥4, take (M_i=\{i-1\); for odd-indexed rows, there are no markings. These R_N serve as prefix markers, and each row satisfies the general BLP length rules.

Take a critical sequence $\theta_j=g^j(\operatorname{crit}(g))$, and consider the embedding (j_i=g^{\circL_i}\). For even indices i, L_i=L_{i-1}, the marked transfer is `(i−1,i−1−L_i)`, hence j_i=j_{i−1}, all of which are marked with direct global realization. This yields an infinite root family that is allowed by the general BLP.

The R_N family is **Another explicitly designed root family**, not a primitive Limit fundamental sequence of DEN2. It has not been proven that P_start is generated by its short copies. It is not appropriate to place P_start and all R_N together in parallel sub-items at the same formal vertex, and to use brother prefixes nesting without further proof; their 5th lines are different. These roots can be processed separately for their generating domains.

## 6. if adhering to the original paper E/M interface

### The special E(k) itself conforms to the prefix structure.

For the lines in the original paper successor/limit, write a=s_n[-3]. Define E(0)=cut(A), and add an unmarked auxiliary three-line `(a,N+1,N+2)L1` after E(k), followed by a short copy. Copy and delete the auxiliary lines, and copy the current a,...,N lines after E(k).

$$
E(k)\sqsubseteq E(k+1).
$$

The comparison key for the core in the original parent row is `(n,a,0)` (when it is a successor, it is a=2). The first new row with E(1) comes from the a row. The auxiliary replication map sends a to n, fixing all x<a. Therefore, its key starts with n. If there is a next item, it is less than a, so strictly less than `(n,a,0)`. The subsequent E retains this new row. If we then uniformly start scanning from the original row n with another C_n scan, the prefix and strict decrease still hold as proven before.

Its difference from S^m(A) is substantial: the auxiliary three-row can always be replicated, which is why the original paper obtained a full definition of E(k). The failure examples of replicating the current last row directly repeated in the 3 section do not apply to this E.

### The original M cannot be used unconditionally with the same prefix argument.

The paper M is suitable for row completion with **All** after replication, in the order from right to left. It may change the rows within cut(A), so it is necessary to prove that the old prefixes in the standard domain have been saturated and completed, and it cannot be directly deduced from the operational definition of cut(A)⊑M(A).

An example of an unmarked ordinary BLP grammar is a complete row.

$$
\begin{array}{c|c|c}
i&s_i&L_i\\\hline
1&(0,1,2)&1\\
2&(0,1,2,3)&1\\
3&(0,1,2,3,4)&2\\
4&(0,1,2,4,5)&2\\
5&(0,1,3,5,6)&2\\
6&(0,1,3,5,6,7)&2\\
7&(6,7,8)&1.
\end{array}
$$

The last line can be copied, only the source line 6 is copied, while the first six lines remain unchanged. However, after M, a fullcomp operation is performed on the 5 line, with the source being `{2}`. The first intermediate line becomes `(0,1,2,3,5,6)L3`. As a result, the 5 line changes, and the original cut(A) is no longer a prefix of M(A). This example does not provide a proof from P_start, so only the M prefix lemma of **Unconditional** is negated, without negating possible standard saturated invariants.

If in the design, the M is explicitly changed to `C_n(S(A))`, only the newly copied suffixes are scanned, then the cut prefix and the strict descending relationship are re-established directly. However, this has already modified the original M. To generalize the theorem 2.25, it can be proven that the semantic endpoints of this new M are maintained, as well as the recovery of the successor blocks of the special E. These are semantic interface tasks that cannot be completed solely by comparison bridges.

## The scope of the conclusion for 7.

For the most direct version of 'cyclic short replication—tail deletion—suffix completion' related to note, the conditional comparison/reachability bridges have been provided in the same manner as DEN2. It has also been pointed out that there is a subsequent replication failure branch that must be completed, which actually occurs under the standard root.

If the original paper uses the notation E/M for the first stage of definition, it is necessary to maintain the distinction between the two: the prefix bridges for E can be directly proven, while the old prefixes for M are established through the standard saturation invariants described in the following section. Both types of finite systems still lack a complete marked semantic maintenance and the expansion of well-founded proofs. Therefore, it cannot be declared that the first stage of well-ordering has been completed just because the bridges are established.

## The substitution of the comparison key prefix for 8. cannot eliminate the obstacle of old row completions.

In the 6 section, there is a coincidence in the seven examples: the key in the original 6 line is `(6,5,3,0)`, and the new 6 line that results from the 5 line completion also has this key. Therefore, although this example breaks the prefix used before the word, it still retains the comparative key prefix of the original cut. This phenomenon is not common.

Let the complete behavior of the six-row pattern be denoted as follows:

$$
(0,1,2)_1, (0,1,2,3)_1, (0,1,2,3,4)_2,
(0,1,3,4,5)_2, (0,5,6)_1, (5,6,7)_1,
$$

The subscript indicates the step size, with the markers being empty. The last line simply copies the source line 5. In M, the old line 4 is inserted with the source 2, resulting in a new line 5 whose key is `(5,4,3,0)`. The old line 5 has a key of `(5,0)`. Therefore, not only does the key prefix of the original cut fail, but also M(A)>A.

Even in the case of ordinary BLP with five elements

$$
(0,1,2)_1, (0,1,2,3)_1, (0,1,2,3,4)_2,
(0,1,3,4,5)_2, (4,5,6)_1
$$

There already exists M(A)>A: The old end key `(5,4)` is a true prefix of the new key 5 in the row `(5,4,3,0)`. Here, the right-to-left fullcomp on the original M and the left-to-right scanning that only performs native completion are both yielding the same results in the crucial line 5. The ordinary BLP old prefix of n≤4 does not have a suitable row that can be non-emptyly completed: the earliest row at 3 can only be `(0,1,2,3,4)L2`, and there are no integers within its source gap. Therefore, the fifth line is the earliest line in this mechanism of 'old prefix completion that makes M larger than the parent item'.

These are still unproven examples of standard reachability. The conclusion is that if one wishes to preserve the current comparison and generalize the original E/M, it is necessary to utilize standard domain invariants, and one cannot simply replace the term "prefix" with "comparison key prefix". The following presents one such invariant that is required.

## 9. native completion saturation: P_start, cut, E, and the closed theorem of complete scanning

### The precise definition of 9.1 is related to the main design.

Write

$$
q(v)=A_v[-2],\quad p(r)=A_r[-L_r-1],\quad e(r)=A_r[-L_r].
$$

q(v)<v holds in general. Define the saturation condition for**Lines that will be called for native completion**.

$$
\operatorname{Sat}(r):\quad q(e(r))\le p(r).
\tag{S}
$$

It precisely indicates that the source package of the native completion is empty: the source chain is not greater than p(r) from the first q iteration of e(r). If strictly following the original paper, only the suitable rows are completed, then (S) quantifies only these rows; if using medium/short rows for native completion in PDF, (S) quantifies all rows of `len(A_r)≤2L_r`. The following conclusions apply to both fixed choices, and their outputs should not be mixed.

A pattern is called Sat if all the lines that need to be checked satisfy (S). The scan of C_all is defined as performing a complete marking scan in PDF style from left to right across all lines from the first line to the last line: initially, the record is empty; first process the marked completion of the current old line, then execute the selected native completion; only non-empty source packets are recorded; after inserting a block, skip that block. Newly added markers do not restart the scan from the current old line. This order is the current explicit design, **It does not claim to have the same grammatical output from right to left as the original paper M.**.

Main design selection

$$
M_\star(A)=C_{\rm all}(S(A)),
$$

E(k) retains the auxiliary triple recursion of the paper, and marked copies follow the established rules; non-copyable branches are handled using cut. Cut itself is an operation allowed for each non-zero pattern. The zero pattern consists of fixed first two lines.

The following is the translated mathematical research manuscript:

Closure Theorem: It assumes that the performed marked completion still yields a valid ordinary BLP row (with distinct entries, correct row numbers, step lengths, and valid references). The validity and weak truncation semantics remain to be proven; however, saturation does not assume these embedding semantics additionally.

### All rows of a non-empty original block that are marked with 9.2 have been saturated.

Suppose in the old step r, the native completion is performed, the old step length is L, and the source chain package is

$$
u_1<\cdots<u_t,\qquad u_0=p(r),\qquad u_{t+1}=e(r)=a,
$$

Among them, t>0. Defined by the source chain.

$$
q(u_1)\le u_0,\qquad q(u_{h+1})=u_h\quad(1\le h\le t).
\tag{4}
$$

For the completed block of rows r+h (0≤h≤t), the formula is read directly from the insertion

$$
\boxed{p'(r+h)=u_h,\qquad e'(r+h)=u_{h+1}.}
\tag{5}
$$

Specifically, when the old core has a length of 2L, the middle row core is

$$
A_r\cup\{u_1,\ldots,u_{h+1}\}\cup\{r+1,\ldots,r+h\},
\quad L'=L+h+1\qquad(h<t);
$$

When the old core length is 2L−1, the intermediate row core is

$$
(A_r\setminus\{a\})\cup\{u_1,\ldots,u_{h+1}\}
\cup\{r+1,\ldots,r+h\},
\quad L'=L+h\qquad(h<t).
$$

The final row is the same in both cases.

$$
A_r\cup\{u_1,\ldots,u_t\}\cup\{r+1,\ldots,r+t\},
\quad L'=L+t.
$$

These sets are arranged in ascending order. In native completion, sources are located between adjacent old entries p(r) and a, while targets are new row numbers, so there are no duplicates. The corresponding reverse positions yield (5).

In the general BLP model, every non-empty package must have a a<r: the two-point eligible core of L=1 always has e(r)=r and q(r)=p(r), and the source package is empty; the e(r) of the remaining eligible rows are strictly less than r. Therefore, all u_h and a are less than r, and the new row inserted after r does not change any q value in the (4) query. By (4), (5), each row in the block satisfies Sat.

This proof also examines the newly added lines, not just the final 'suitable' lines. It explains why scanning can skip over the new blocks.

### The complete left-to-right scan output of 9.3 is "Sat".

**Scanning theorem.** For any valid input, If all the local operations for C_all are legal and completed. Then its output is Sat.

**Proof.** maintains the condition that "all prefix lines that have been processed and skipped are Sat" along the scanning order. The compTo operation on the current old line r can change the p, e, and q of that line; it does not modify earlier lines. Therefore, the saturation conditions of any previous line i are not affected, because e(i)≤i<r, and the line q(e(i)) being queried is also within the earlier prefixes. Even if e(i)=i, the queried line is still the unmodified old line i.

After compTo is completed, read p and e from the line and step size starting from **current** again. If the line does not require native completion, then there are no conditions that this version should check. If the source package is empty, the current line is Sat. If the source package is not empty, the section starting at 9.2 proves that the entire newly added block is Sat, and their e values are strictly less than the original r. Therefore, there are no new lines dependencies that need to be checked.

The subsequent scanning positions are strictly after this block. The marker completion only affects the current line behind. The native insertion at the back only renumbers the lines/entries following it. Do not modify the processed prefixes. The prefix lines that are queried, q(e), also remain unchanged. Therefore, Sat will not be damaged in the past. The number of entries that can be input is limited, the number of markers that can be frozen at a time is limited, and the native q chain strictly decreases. Therefore, the scanning is limited and completed under the premise of local legality. Proof completed.

### 9.4 P_start and cut

The eligible rows for P_start are only the 1, 3, and 5 rows (if only suitable is considered, then only the 3 and 5 rows are needed).

$$
\begin{array}{c|c|c|c}
r&p(r)&e(r)&q(e(r))\\\hline
1&0&1&0\\
3&1&2&1\\
5&3&4&3.
\end{array}
$$

Therefore, P_start is Sat. The 2 and 4 rows are long rows and do not trigger native completion. The cut deletes the last row, and since all references in the i row are ≤i, the cut remains Sat.

### 9.5 The threshold replication in the original paper E maintains Sat

E is followed by an auxiliary three-row `(a,N+1,N+2)L1` after the current N row, and then the source a,...,N are copied in a short manner. The copying map is

$$
\phi(x)=x\quad(x<a),\qquad \phi(x)=x+N+1-a\quad(x\ge a).
$$

The old N lines remain intact. For each old line marked with v≤N, its corresponding line marked with φ(v) exists in the output as follows: when v<a, it is an unmoved old line; when v≥a, it is a copied line. The mapping is strictly increasing and preserves the position within the line, therefore

$$
q'(\phi(v))=\phi(q(v)).
\tag{6}
$$

Similarly, for each replicated row φ(r)

$$
p'(\phi(r))=\phi(p(r)),\qquad e'(\phi(r))=\phi(e(r)).
$$

Due to the monotonicity of (6) and φ, it follows that the same inequality holds for replicated lines as originally (q(e(r)) ≤ p(r))). The length of the line/step size and the eligible type remain unchanged. Therefore, a single auxiliary replication remains Sat; by induction from E(0)=cut(A), all E(k) remain Sat. The marked completion does not change the line entries and step sizes, and does not affect this combination proof.

### 9.6 Sat: The M_star of the parent term is completely retained with the old prefix.

**Prefix theorem.** If A is Sat, S(A) is valid. C_all Completed legally. then

$$
\operatorname{cut}(A)\sqsubseteq M_\star(A),
$$

And M_star(A) remains a Sat.

Retain the **Proof.** S lines along with the n−1 rows. All citations in these lines are denoted by ≤ their line number, and copying the end does not change their Sat.

Starting from C_all, the records are left empty. Processing the lines before n−1 one by one: Since there are no empty records, there are no packages available for marking completion, so nothing is changed. This line is already Sat, and since the source package for the original completion is empty, nothing is changed either, and no records are added. By induction, the entire old prefix remains unchanged, and the records remain empty until the first new line is processed. Finally, the output is Sat according to the scanning theorem. Proof complete.

**Standard closure theorem.** starting from P_start, Every pattern generated by legal cuts, papers E(k), M_star, and cuts that are not copyable is a Sat problem. This conclusion has excluded the raw counterexamples from section 8: Their old row 4 has q(3)=2>p(4)=1. It's not Sat.

## The comparison of well-ordering problems designed by 10. and E/M has been reduced to the expansion of well-founded sets.

For the legal standard domain of the previous section:

* The term 'cut' is allowed for each non-zero item, and it strictly reduces the comparison.
* M_star retains the prefix cut(A) before it, and is strictly less than A: The first replication row strictly reduces the key, and when scanning it, the record remains empty. Therefore, its key is only retained through native completion, and subsequent operations do not alter it.
* The special E(k) subitems are nested with the k prefix before them, retained as cut(A), and each is strictly less than A (see section 6).

It is necessary to clearly follow the original paper type hierarchy: The limit/successor type allows its E(k) to be cut; The transient copyable type allows M_star and cut. The non-replicable type can only be cut with cut. This ensures that it is comparable to parent-child items with the prefix placed before the character. **Do not add M_star unconditionally alongside all E(k) on the same parent item.**， Because this paper does not compare the prefixes of two different subfamilies.

From the prefix "barrier" and the reachability theorem, it is obtained that

$$
\boxed{B\le A\iff A\longrightarrow^*B}
$$

And the standard key injection is a bijection. Therefore, within this clear and complete framework of the marker E/M, **Current well-ordering** is equivalent to the goodness of the complete expansion relation; there is no longer any unproven conversion that claims 'the existence of rank is good order'.

This is not a final proof of well-ordering. The remaining work involves verifying the grammatical correctness of these complete marking operations, maintaining the correct weak truncation semantics/historical certificates, and ensuring a real semantic base descent that supports all parameters sufficiently. These conditions are not omitted in this paper.

If strictly only evaluating the edges that are called when the original definition 2.24 is used, and arbitrary cuts are not allowed, then it is necessary to prove that the required prefixes are reachable. The bridges mentioned above use explicitly allowed cuts. Adding cuts as a combination of descending operations is consistent with the deletion of tails in BLS, but this should still be specified in the definition.

## Independent verification of the Lemma for interval completion with 11.

Verified `marked_completion_interval_lemma.md` number 1 The necessary and sufficient conditions for a section to exist. Old borders a_i→a_{i+L} Obtained the first package q The indicator range for the new point is `[s−L+1,s]` ， The range of indicators for obtaining the second package is `[s+1,s+L]`. They do not intersect and are exactly equal to `[s−L+1,s+L]`. Cover all the old edges i=1,...,N−L. only when and only if `N−2L≤s≤L` . The two packs must intersect with the actual internal gaps. Thus obtained (G).

The new pair u_h→v_h has a position difference of `(s+L+q+h)−(s+h)=L+q`, and the number of edges `(N+2q)−(L+q)=(N−L)+q` exactly covers all the old edges plus the new pair. No errors in subscripts or necessary conditions were found.

## The same Sat invariant applies to the actual DEN2 standard domain, where 12. also holds.

This section uses the entire long line of actual DEN2 and its complete tail for reproduction, without requiring each line to meet the standard BLP numerical constraints. It is still assumed that the operations performed are legal: in particular, the eligible rows satisfy p, e are defined, and the native packages form a strictly increasing sequence between p and e.

We use the proven standard domain length invariant $m=\operatorname{len}(A_r)\ge2L-1$ in `order_domain_audit.md`. Therefore, the standard eligible rows can have a length of m=2L−1 or m=2L, which exactly corresponds to the two native formulas used in the 9.2 section, leaving $(p',e')=(u_h,u_{h+1})$. If e=r, then L=1, the eligible core has a length of 2, and the package must be empty; thus, non-empty packages are still only queried for source rows earlier than r. The entire scan proof in the 9.3 section does not depend on the long rows N≤2L+2; long rows are directly skipped by native completion, so this scan proof remains valid for this range in the actual DEN2.

The argument cannot be extended to all manual short lines in the source code: when m<2L−1, the two slices of actual compFrom will delete the central 2L−m entries, while the PDF formula (14) only deletes a single a. The two are only identical in the short line length used in the above standard domain.

In practice, every finite fundamental sequence that is `Limit` is a Sat: The 1 row contains p=0, e=1, q(e)=0; the 3 row contains p=1, e=2, q(e)=1; all rows of the 2 row and i≥4 row are long rows, and do not trigger native completion. Note that the long rows of i≥5 are specifically not considered as part of the ordinary BLP.

**Proof: DEN2.** Actual `operate` from `Limit` All generated legal finite states are SAT.

**Proof.** summarizes the operation history. Cut and any end truncation remain Sat. If the current expand operation returns to cut, the conclusion holds immediately. Otherwise, partial replication or complete tail replication followed by cut still maintain the original input of n−1 lines. These old lines remain Sat, and the actual scanning starts from the n line, with the record being empty. This is the same as the result of scanning from the first line: the full scan does not contain any non-empty original records within the old Sat prefix, so there is no record to borrow for marked completion, and nothing changes line by line. Subsequently, the complete scan theorem ensures that the output is Sat. The length truncation at `index=1` again maintains Sat. The induction is complete. Proof completed.

This conclusion is only responsible for "old prefixes no longer being natively completed" and scanning the structure. It checks for precise hits of **Proof not provided** trace, package-level tagging semantics, and local operation validity. It also does not create contradictions in the escape patterns with an infinite number of lines.
