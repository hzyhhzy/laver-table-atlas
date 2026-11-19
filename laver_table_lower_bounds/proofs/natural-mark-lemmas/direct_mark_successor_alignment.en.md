# Directly aligned with the next source: a completed state invariant · [中文版](direct_mark_successor_alignment.md)

*English reading edition, translated with machine assistance. The title links to the dated Chinese manuscript.*

> Collected reading edition. The three main papers state the results of this collection.
> This edition retains the local proofs, their hypotheses and any withdrawals. Progress reports describe the state of work at the time.
> The locations of omitted passages on preset inputs are recorded in SOURCE_MANIFEST.json.
> The main papers give the numerical derivations for the natural parameters produced by the proofs. This historical note carries no additional Lean certification.

2026-09-07. This paper presents a marking birth constraint that does not rely on a fixed factor lower bound. It has been independently verified by another agent. The scope of application covers verified structures of the ordinary P_start main E/M_star: the replication is strictly legal and correct PDF filtering is used; native formulas are used in the ordinary case; compTo has correct paired gaps, old edges are maintained, and actual parallel words are present. After a legal short replication of the true BLS, Sat, and internal A parent items once, the `current_guard_full_packet_theorem.md` inference 6.1 has been provided for the latter.

This does not declare any raw scan to be correct, nor does it assume that the scan output, which contains all old marks, has closed to A. The following equation asserts that this holds true at the time of copying the scan entry and at the end of the complete scan; it should not be misused as a temporary snapshot of "native level, with the backend owner not yet processed."

## 1. Definition and Conclusions

Denote the row t

$$
p(t)=A_t[-L_t-1],\qquad e(t)=A_t[-L_t].
$$

The proper mark y is located at a base position k in the owner row R.

$$
\delta=A_R[k-L_R],\qquad d=A_R[k+1-L_R].
$$

d is the core entry that follows its source δ. A mark is called direct if the actual trace is exactly (y,δ)), thus p(y)=δ. Definition

$$
\boxed{\mathsf D:\quad d=e(y)\quad\text{holds for every direct mark}.}
                                                               \tag{D}
$$

**Theorem 1.1.** P_start satisfies D; legal PDF copying, auxiliary E, cut-preserving D; under the aforementioned correct completion interface, a complete scan sends inputs that satisfy D to outputs that still satisfy D.

This is additional historical information. Generally, weakly marked BLS only provides d≥e(y), and does not automatically provide equality: factors reach a weak bound at θ_(e(y)), while owners reach or exceed this bound at θ_d. It is not possible to misinterpret these higher images as global equality from weak truncation.

## 2. Initial, Replication, and Column Deletion

The initial unique mark3 originates from 1, the next source is 2, and the e(3)=2 of the factor row 3.

The actual word recognition indicates that full replication is used, and 'low' retains the direct word length. 'High' actually contains at least two non-terminal words that are active words and source endings. Therefore, 'high' does not produce direct words, and non-direct old words will not become direct due to replication.

The factor rows that are directly copied and the corresponding entries of the 'owner' use the same φ, hence d'=φ(d)=φ(e(y))=e'(φ(y)). The factor y<C belongs to the 'low direct', while e(y)≤y<C does not change. The entries after the source and the factor rows remain fixed, and the equations are also maintained. It is not necessary to maintain the integer spacing with φ here. The auxiliary E is a special case of the full/low branch of the same copy; the 'cut' does not change the retained rows.

## Exact local argument in the 3. scan

First, fix an entrance direct mark y. Use T=ρ(y) to represent the gene subrows that have been processed. Before processing the owner, the historical equations are saved.

$$
d_{\rm owner}=\rho(e_{\rm entry}(y)).                 \tag{1}
$$

The previous lines only numbered this entry. The source gaps for other marks on the current owner are different from those, and it is not possible to insert points into them (δ,d)). The correct (G)) also places all targets after the owner's e, preventing any proper marks from being mixed into the source gaps. Therefore, (1) can still be used when processing in multiple mark order.

If the factor y has a null native, its e is merely a renumbering of the old e. This mark does not read any non-empty Rec. The D holds as it was originally. If it has a non-empty package U=(u₁<…<u_q), then the new e(T)=u₁ of the base row is applied. The internal +1 of the direct term is checked to be empty, and the owner indeed processes this non-empty Rec. The correct compTo inserts U into the same true interval after the old source δ, so the inherited mark T has d_new=u₁, and D is restored.

The new mark T+h (1≤h≤q) for compTo is still direct. At h<q, its source u_h is immediately followed by u_(h+1), and there is also e(T+h)=u_(h+1) in the actual native factor row. At h=q, the owner's next source after u_q is the historical old d; the e(T+q) at the end of the native block is exactly the historical old e(y), as (1) are equal. This particularly checks the boundaries of the latest new marks.

If the current native creates a mark T+k, then any block row that carries it, T+h, satisfies 0≤k<h≤q. Therefore, k<q, the next source of the factor row is u_(k+1) (let u₀= be the original p), and the next item after the corresponding source in the carrying row is also u_(k+1). Thus, the direct marks that the native truly creates also satisfy D.

Finally, the owner's native does not destroy any properly marked that has been verified. Because k≤m−1 gives

$$
k+1-L\le m-L,
$$

Therefore, the next source of the mark is d≤owner, and the next source is p. The native is only added at (p,e)), the short line only removes e, and targets are added at the end. None of these will change d. Each inherited copy still uses the same direct factor and the next source. Subsequent scans will not change these already processed lines.

The theorem is given by a case-by-case induction for each owner/mark. Any number of marks and any valid non-empty scope are allowed; there is no additional condition regarding the existence of a direct carrier or Flow.

## The immediate consequences of marking 4. for H

The rows with H satisfy min=0 and p=1. Under NC and trace precision, any mark with H as the leading factor and y as the first factor can only be direct (y,1): its first p has reached 1, and the threshold must be ≥1). Therefore, the standard completion state has a source precision of source/ for each such mark.

$$
(1,e(y)).                                             \tag{2}
$$

It can be located at any height above the owner, and only the line immediately following y needs to be checked. The formula (2) is a family of constraints that can be used in the analysis of H seams. Subsequent applications and potential replication compressions are not yet excluded.
`h_anchor_history_barriers.md`.
