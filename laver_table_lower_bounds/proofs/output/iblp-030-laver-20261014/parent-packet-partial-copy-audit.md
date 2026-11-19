# PP's longest valid copy prefix correction: Local audit · [中文版](parent-packet-partial-copy-audit.zh-CN.md)

*English reading edition, translated with machine assistance. The title links to the dated Chinese manuscript.*

> Collected reading edition. The three main papers state the results of this collection.
> This edition retains the local proofs, their hypotheses and any withdrawals. Progress reports describe the state of work at the time.
> The locations of omitted passages on preset inputs are recorded in SOURCE_MANIFEST.json.
> The main papers give the numerical derivations for the natural parameters produced by the proofs. This historical note carries no additional Lean certification.

2026-10-14. This document audits a proposed amendment, does not replace existing procedures, and does not claim that the new system has strictly exceeded the BMS.

## The definition of 1. that needs to be audited

Following the usual ordinary marked BLP row type, paper mark guard, and parent package scanning $\mathcal P_n$. The last row has $n$ lines, which copy the source start $p$ and the short tail end $e$, satisfying $1\le p<e\le n$. The interfaces for zero, successors, and index zero remain unchanged.

For the specified replication interval $[p,t)$, first delete the last line, and then replicate from $p$ in order. Stop before the first source line with an undefined replication address, **Do not skip bad lines.**. Each source line is an atomic unit; no half-core or half-marks should be left. The operation returns a status of "all successful" or "stopped at this source line".

- Index 2: Perform the aforementioned partial short copying on $[p,e)$, and then scan.
- Index $k\ge3$: Attempts to copy the complete interval $k-2$ times; if one attempt fails, retain the valid prefix and stop all remaining copies. If all attempts are successful, perform a partial short copy at the end. Only one scan is performed at the end, starting from the original line number $n$.
- Index 1: The 2 results are listed in the $n$ rows. If there are no new rows, then only cuts are obtained.

Let the revised version be $P^\dagger$, and the original parent package with a short tail be $P$. Here, "undefined" refers to a failure in the mathematical domain definition, excluding time/memory budgets; when resources exceed limits, it can only report unknowns.

## The prefix 2. holds for all indices.

Existing bare copy lemma: If the first complete $C(B)$ is valid, then any subsequent finite number of bare full copies and the final short copy are also valid, because during this period, the lines that are not scanned or controlled only perform copy from images. Therefore, we only need to consider two cases.

If a complete copy is valid for the first time, then $P^\dagger(B,k)=P(B,k)$ holds for all $k$, and the old prefix convergence can be continued.

If the first attempt to fully copy the first occurrence at the source line $h\in[p,n]$ fails, let

$$
W_t=\operatorname{cut}B+
       \{\varphi(\text{row }i):p\le i<\min(t,h)\},
$$

In each replicated row, the same paper mark guard is used.

$$
P^\dagger(B,2)=\mathcal P_n(W_e),\qquad
P^\dagger(B,k)=\mathcal P_n(W_{n+1})\quad(k\ge3).
$$

Because $W_e$ is a prefix of $W_{n+1}$, and since scanning depends on the past and not on the future, the scanning output maintains the prefix. Index 1 is also a prefix of index 2. Therefore

$$
P^\dagger(B,0)\sqsubseteq P^\dagger(B,1)
\sqsubseteq P^\dagger(B,2)\sqsubseteq P^\dagger(B,3)
=P^\dagger(B,4)=\cdots.
$$

The scan retains the "cut" prefix, which still requires the use of the ActiveSat parent item/reachability domain assumption used in the original text. Not unconditional for any un saturated handwritten array.

**The old descending edges are retained verbatim.** If the original $P$ is successfully fully replicated, all items with the same index are the same. If it fails, all the original items are cut, and the new index 0 still results in a cut. Therefore, each old finite descending edge has a descending edge with the same endpoint in the new system. If the roots are the same, then all the old reachable expressions are still reachable. This implies that the descending relationship is inclusive; it can only be stated as a well-ordering property without proving the corresponding fundamental property.

## The marking semantics for the partial copy 3. do not require future bad rows.

When copying a successful source line $i<h$, each copy of the core and marks at the copied addresses is within the domain of $\varphi$. The paper mark filtering only uses:

1. The original source text contains the term 'mark' and its old accurate form 'trace'.
2. Old end control core and marks;
3. The image address and its position of the current copied line are guarded.

It does not read the future lines that do not yet exist in the target. Any trace that is retained can only fall on the original cut prefix or on lines that have been copied before, because the trace always descends towards the old addresses. According to the general copy lemma that is inductive by the source lines, the retained marks still have a natural truncation interpretation; the first bad line and whether there is a grammatical copy after it do not participate in this local argumentation.

Therefore, finite success prefixes can be directly fed into the audited PP scan closure theorem. Here, a line-by-line version of the copy lemma and the parent package scan closure are referenced; no complete success copy that does not exist grammatically is taken as an object, and then truncated from it.

If the program interface is opened to non-ordinary arbitrary arrays, it is still necessary to prevent structural errors such as $p<1$ and invalid row types. The step-size array row 0 should not be considered a copyable source. This issue has been eliminated in the current ordinary domain and subsequent branches.

## The index 4. fixes the cap for the index 2, which does not increase, but is not always equal.

Let the original end owner be $J$, the old point be $\theta_i$, and the old cap be $\theta_{n+1}$. The points on the ordinary last row are like interfaces.

$$
J(\theta_p)=\theta_n,\qquad
J(\theta_e)=\theta_{n+1}.
$$

If a partial short copy is successfully created from the source line $p,\ldots,h-1$, where $p<h\le e$, its new cap is

$$
J(\theta_h)\le J(\theta_e)=\theta_{n+1}.
$$

If $h<e$, it is strictly less than the old cap; if $h=e$, it equals the old cap. If no row is copied, then it is a cut, and the cap is lowered from $\theta_{n+1}$ to $\theta_n$. The scan retains its input cap, so the revised version's fixed index 2 never increases the cap.

This requires a quantitative proof to distinguish:

- cut: The critical point subscript $r$ strictly decreases.
- The actual partial short copy: $r$ also decreases strictly, although there is no grammatical deletion of lines.
- Complete short replication: The cap remains unchanged, and the application of the last owner strictly increases the finite Laver quotient class $a$.

Therefore, the $\Phi=2^{r+1}-a$ potential function can continue to decline according to these three categories. However, it is not possible to continue writing "all non-cut steps maintain cap," nor can the strictly decreasing number of cap steps be identified with the grammatical cut steps. The grammatical cut steps still do not exceed the strictly decreasing number of cap steps, and the original cut supremum direction is retained.

Full or partial copies in high-index may lead to an increase in cap, and this section does not make any fixed small-cycle window full index assertions.

## 5. real small counterexamples with revised behavior

See parent-packet-I030-one-round-projection.zh-CN.md. Let $X=I030[1]$, $V=P(X,3)$. The old rule degenerates into a cut at $V$ due to the failure of complete replication. Here, $p=10,e=11$, the first bad source line is precisely $h=11$.

Short copies only use the original row 10, and a complete copy can only successfully replicate this same row. Therefore, the revision is as follows:

$$
P^\dagger(V,2)=P^\dagger(V,3)=P^\dagger(V,4)=\cdots,
$$

All items retain the original 20 line at the beginning, and the last line is replaced with $(19,20,21):1$. This correction indeed removes the obstruction caused by "unused high tail lines causing bad addresses" to the fixed index 2.

It does not automatically repair the entire simulation from the old IBLP to PP: subsequent control intervals, mark traces, and compTo still require dynamic projection invariants. The existing static projection can be combined with this correction, but it cannot be directly claimed that embedding has been completed.
