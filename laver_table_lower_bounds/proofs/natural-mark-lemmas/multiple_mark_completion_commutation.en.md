# Marked Completion of Exchange and Freezing Transfer: Complete Local Proof · [中文版](multiple_mark_completion_commutation.reading.zh-CN.md)

*English reading edition, translated with machine assistance. The title links to the dated Chinese manuscript.*

> Collected reading edition. The three main papers state the results of this collection.
> This edition retains the local proofs, their hypotheses and any withdrawals. Progress reports describe the state of work at the time.
> The locations of omitted passages on preset inputs are recorded in SOURCE_MANIFEST.json.
> The main papers give the numerical derivations for the natural parameters produced by the proofs. This historical note carries no additional Lean certification.

2026-09-07. This paper proves that multiple marks that have obtained correct package certificates within one row do not destroy each other. It does not assume that package propagation holds universally in the standard generation domain, nor does it claim that PDF is globally equivalent to DEN2. However, the problem of "recalculating the trace for each mark and freezing the trace for the entire row" can be eliminated under the following specific package conditions.

## The combination theorem of multiple corresponding gaps with 1.

Let the complete behavior at the start of the completion be defined as follows:

$$
A=(a_1<\cdots<a_N),\qquad \text{step size }L.
$$

Given distinct source gap positions

$$
s_1<\cdots<s_d,
\qquad \max(1,N-2L)\le s_j\le\min(L,N-L-1).
\tag{1}
$$

In the j case, there are q_j≥1 sources and the same number of targets:

$$
a_{s_j}<u_{j,1}<\cdots<u_{j,q_j}<a_{s_j+1},
$$

$$
a_{s_j+L}<v_{j,1}<\cdots<v_{j,q_j}<a_{s_j+L+1}.
\tag{2}
$$

Let Q=Σ_j q_j, and denote the sorting row after inserting all packages after A as B. The step size is L+Q.

The entire step size of **Theorem 1.1.** B is exactly equal to the entire old edges of A and the edges of $u_{j,h}\mapsto v_{j,h}$. There are no duplicate points. This holds true for any subset of packages, so the packages can be added in any order, and the above conclusions can be achieved at each step.

**Proof.**, due to s_j≤L, all source gaps lie to the left of a_{L+1}; all target gaps start from the right of a_{L+1}. Therefore, the two categories of new points do not intersect, and the same kind of gaps that are not j true gaps also do not intersect.

Fix the old edge a_i→a_{i+L}. In the j package, exactly half of the two halves are located between the two ends: this is the interval calculation of the `marked_completion_interval_lemma.md` lemma 1.1, with the condition (1) ensuring that this conclusion holds for every i=1,…,N−L. Therefore, the difference between the old and new positions increases from L to Q.

Let Q_{<j}=Σ_{i<j}q_i be the new point. The positions of the new points are as follows:

$$
\operatorname{pos}_B(u_{j,h})=s_j+Q_{<j}+h,
$$

$$
\operatorname{pos}_B(v_{j,h})=s_j+L+Q+Q_{<j}+h.
$$

The second equation includes all the source points and earlier target packages; the difference in positions is exactly L+Q. The new row has N+2Q−(L+Q)=N−L+Q) side lengths, which exactly correspond to the number of different sides listed. For any subset, the exact same proof can be applied by replacing Q and Q_{<j} with the sum within that subset.

In the process of adding elements one by one, the edge sets of any intermediate row consist of the old edges plus the edges of the packages that have been added. The edge sets of larger subsets include them, so all the established edges remain intact. The final sorted set and the step size depend only on the set of packages, not on the order. Proof completed.

## 2. previously referred to "transfer", which remains constant throughout the entire process of marked completion.

Now, A is in the r row, and a_{N−1}=r, a_N=r+1. All the proper old markers y<r are located at some k>L. Its step predecessor is a_{k−L}. Assuming that only the current row is modified, without inserting global row numbers or modifying any earlier rows; this is exactly a case of a single compTo/ marked completion within the system.

**Corollary 2.1.** In any intermediate row of theorem 1.1 Each old marker still retains its original step size predecessor. Therefore, all aspects of the transfer, final factors, whether it hits the threshold accurately, and the results of internal adjacency checks remain unchanged.

**Proof.** marks the source of a old step size edge; the theorem 1.1 retains this edge, and the new row is strictly increasing. Therefore, the source indicated by the new step size can only be the original source. The transfer operation only reads lines with line numbers ≤y<r, and these lines remain unmodified. Thus, the complete recursive queries starting from the same y and the same threshold are consistent item by item. The internal adjacency queries are also all on earlier lines. Proof complete.

Not only the unprocessed old markers are such: the source edges of the processed packages with new targets are also retained by the theorem. Therefore, if its transfer is correct at the time of birth, no other packages will change this transfer later on.

Since all new points in the source are below a_{L+1}, and every valid old marker is located after a_{L+1}, clearing the source markers does not remove the old markers. The source and target intervals do not intersect, and no new markers from other packages will be removed. The final set of markers is precisely the union of the old markers and all targets of the respective packages.

## It is sufficient for the 3. to hold term by term to complete the entire row semantic proof.

Let the embedding F implement the old row. For each package with index j, a corresponding historical truncation Γ_j and factor word W_j have been established, and there is

$$
F\equiv_{\Gamma_j}W_j,
\qquad W_j(\theta_{u_{j,h}})=\theta_{v_{j,h}}<\Gamma_j,
\qquad \theta_{u_{j,h}}<\Gamma_j.
\tag{3}
$$

The actual transfer factor terms W_{j,h}, , and W_j are equivalent at their demand cutoffs, and this demand cutoff is less than or equal to Γ_j. All of the old markings also originally had valid semantic certificates.

**Theorem 3.1.** under the conditions of (1)—(3) and these new transfer conditions, All markers in any order can be implemented by the same F; All old and new markings are retained.

**Proof.** membership leads to a weak truncation reading lemma for F(θ_{u_{j,h}})=θ_{v_{j, , h}}. Theorem 1.1 thus covers all rows in one go, with the minimum entries remaining unchanged, and the requirements of critical points are also preserved. Corollary 2.1 maintains all old factor words, old marked cutoffs, and the newly generated transfers. The new markers are guaranteed by their proven truncation certificates. No global function restrictions are used in the semantics. Proof completed.

## 4. The historical target interval is indeed empty when entering compTo.

Fix a certain scan at a certain expansion, and denote all the lines before entering the scan as "old line numbers". The scan only naturally inserts several new lines while processing the current old line, and then skips these new lines. Thus, the first occurrence of each old line y is monotonically renumbered ρ(y). Here, the renumbering by ρ refers to the old base numbers/integer labels: after the old line y is naturally unpacked, the label ρ(y) remains at the beginning of the block; it is not "the position of the original embedding final completion line at the end of the block". Before scanning a later old line r, the unprocessed line has not been modified by the local compTo, and is only subject to the unified renumbering from earlier natural insertions.

**Lemma 4.1.** If y is an old marker in the r row, when entering the compTo of that row, it will be Y=ρ(y) in the current row. The saved history cutoff is Γ_y=θ_{ρ(y+1)}. The next old entry after the current row Y must be at least ρ(y+1), and there are no entries in the current row that are strictly located at (ρ(y),ρ(y+1)).

**Proof.** In the old line, the next entry after Y was originally some integer z>y, so it became z≥y+1. Now it is ρ(z)≥ρ(y+1). All the entries in this line now come from the old integers in the ρ; there are no old integers that strictly lie between y and y+1, therefore there are no entries that fall within the current gap. The native insertion does not change the old base itself, only its index, so the listed Γ_y is indeed the original θ_{y+1}. End of proof.

This lemma applies to any number of earlier native insertions, including the case where y itself is broken down into a package. If a package to be borrowed has been proven to satisfy its targets

$$
\theta_{\rho(y)}<\theta_{v_{y,h}}<\Gamma_y,
\tag{4}
$$

They fall into the empty historical target gaps that are exclusively occupied by that marker. These gaps are not intersected by different old markers y.

For the general BLP, if this package also satisfies the native critical point condition and the transport equation from the previous document, 4.1, then all sources are also forced to their respective old source gaps by the monotonicity of F, and automatically satisfy (1). Therefore, any number of such packages can simultaneously satisfy theorem 1.1; different packages will not later occupy the historical gaps of another marked completion. Here, the same "old lines entering compTo" is used for the geometric judgment of each package.

**Unproven key quantifiers:** still needs to be derived from actual algorithms and generated history to determine the (4) and actual transfer certificates for each package borrowed. Don't assume that given there are q elements in Rec(t), there must be q correct targets after the current y. The example with the unconnected mark `marked_packet_propagation_work.md` illustrates how this kind of reasoning might fail. This paper eliminates the additional concerns regarding multi-mark order conflicts that arise after the package is correctly verified.

## When can a row completion of 5. be strictly identified with a row completion of DEN2?

In PDF page 13, it is explicitly stated that the set of markers at the start of this line is frozen. New markers are not added to this round; it processes the old markers in ascending order and recalculates the current transfer step by step. In practice, DEN2 only enumerates the old markers when entering compTo, but the transfer reads from the frozen snapshot of that input parameter, and there is no adjacency checking or deduplication in PDF.

**Corollary 5.1.** If all the actual borrowed non-empty packages in this line meet the above conditions, all old transfers accurately hit the threshold, and all the internal adjacency checks for these transfers pass, then the PDF has the same marked completion output as the current DEN2 in this line (the source records are interpreted in ascending order).

The inference from **Proof.** to 2.1 results in a transfer that is completely consistent with freezing and recalculating reads. Therefore, both processes query the same copy of Rec. In this assumption, adjacency checks do not delete any candidates. The freshness of Theorem 1.1 ensures that the results of de-duplication and non-de-duplication are the same. The set of marked items, step size, and the sorted entries are also the same in the end. Proof complete.

This is not a full scan equivalence theorem: the differences between original formulas on general manual short lines, and whether each actual package meets the target gap/transport/adjacency conditions, still need to be checked individually. It also does not consider variants with verified guards as proofs of the user's original complete rules.
