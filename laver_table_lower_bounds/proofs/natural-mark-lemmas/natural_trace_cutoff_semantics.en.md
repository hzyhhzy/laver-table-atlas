# End factor subsequent delivery boundary: No internal adjacency for natural mark semantics · [中文版](natural_trace_cutoff_semantics.reading.zh-CN.md)

*English reading edition, translated with machine assistance. The title links to the dated Chinese manuscript.*

> Collected reading edition. The three main papers state the results of this collection.
> This edition retains the local proofs, their hypotheses and any withdrawals. Progress reports describe the state of work at the time.
> The locations of omitted passages on preset inputs are recorded in SOURCE_MANIFEST.json.
> The main papers give the numerical derivations for the natural parameters produced by the proofs. This historical note carries no additional Lean certification.

2026-09-07. This paper only discusses the ordinary marked completion BLP. It uses a cut-off bound determined by the actual transfer to prove the semantic closure of all legal replication branches, and it is demonstrated that once the actual package transfer is established, all read values of the completion and the new mark cut-off are automatically guaranteed. No original operations are modified, marks are not deleted, the bound is not taken as 0, and the yet-to-be-verified package transfer is not considered as a completed conclusion.

This natural world is more semantic than any Γ> target in `marked_variable_cutoff_semantics.md`. In particular, the direct mark still uses the original note's complete θ_(y+1) bound, so the local counterexamples of the direct lower bound of this manuscript do not satisfy the input of this manuscript.

## The definition and precise range of 1. in nature

Let the accurate actual trace of the proper mark y of the owner F=j_r be

$$
(v_0=y,v_1,\ldots,v_{k-1}=t,\delta),\qquad
W=j_{v_0}\circ\cdots\circ j_{v_{k-1}}.
$$

Let S_0=id, S_i=j_(v_0)∘⋯∘j_(v_(i−1)). Define

$$
\boxed{\Delta(W)=S_{k-1}(\theta_{t+1}).} \tag{1}
$$

Where θ_(t+1) refers to the next column in the current BLS, which may not be the source after p(t) in the last factor row. The natural marked semantics is...

$$
\boxed{F\equiv_{\Delta(W)}W.} \tag{N}
$$

All truncations remain Laver membership truncations. The brackets E(K) indicate applications, while the circles represent ordinary composition.

**Lemma 1.1.** does not require internal +1, already exists

$$
\theta_y<\Delta(W)\le\theta_{y+1},
\qquad
\Delta(W)=\min_{0\le i<k}S_i(\theta_{v_i+1}). \tag{2}
$$

And Δ(W)=θ_(y+1) if and only if all the internal edges of that trace have a +1 adjacency.

**Proof.** if p(v_i)=v_(i+1), let e(v_i) be the next source after it. A strictly increasing integer core is given to e(v_i)≥v_(i+1)+1, while the edge is given to

$$
j_{v_i}(\theta_{e(v_i)})=\theta_{v_i+1}.
$$

So, j_(v_i)(θ_(v_(i+1)+1))≤θ_(v_i+1), and the equality holds precisely at e(v_i)=v_(i+1)+1. The left composite is strictly increasing for S_i, resulting in the terms in equation (2) decreasing along i. The exact p chain gives S_i(θ_(v_i))=θ_y, and each term is therefore strictly greater than θ_y. A finite decreasing chain has equal ends at both the beginning and the end, and this is precisely the case for the internal +1. In the direct case, the chain has no internal edges, and all conclusions hold. Proof complete.

Therefore, (N) is a clear extension of the original note semantics on non-adjacent traces, and it is completely consistent with the original semantics when it holds within adjacent traces. This boundary is determined by the actual columns and factor owners, and there is no need to guess another boundary.

If W=P∘K, and K is a non-empty tail word that starts with a non-terminal point, then it follows from the definition directly.

$$
\Delta(W)=P(\Delta(K)). \tag{3}
$$

## 2. is legal, full, and low in replication.

The activity embedding is denoted as E, the critical point as c=θ_C, and the replication root as a. It is assumed that the ordinary row and canonical cardinality replication are valid, and the marks are retained according to the rules of the original PDF. The actual new terms are denoted as `copy_trace_word_identification.md`. Each input mark requires (N), with no internal A required.)

All non-terminal factors in **Full factor replication.** are in the replication zone, hence the final factor t and its subsequent sequence are replicated synchronously:

$$
\Delta(E(W))=E(\Delta(W)). \tag{4}
$$

The original F≡_(Δ(W))W has been redefined with a new meaning through application. The endpoint δ does not need to be in the replication area.

**low.** is written as W=P∘K, where the first factor of K is u<C, which is the first time it is lower than a, a non-terminal point, H=E(P). The new term is H∘K. All factors of K and the last factor in the next column remain unchanged with the old prefix, therefore

$$
\Delta(H\circ K)=H(\Delta(K)). \tag{5}
$$

Lemma: 1.1 gives Δ(K)≤θ_(u+1)≤c. The valid bound after applying the original mark is E(Δ(W))=H(E(Δ(K))). Furthermore, E(K)≡_cK, and the ordinary left composition H replaces this into H(c). Since E does not decrease the ordinal, the formula (5) does not exceed H(EΔ(K)) nor H(c), thus obtaining a new semantics. The same holds when P is empty, including the boundaries of u=C−1, Δ(K)=c.

This step does not require that Δ(K) be fixed by E; when Δ(K)=c, it is generally not fixed.

## 3. high replication: All three boundaries automatically cover the new nature

Write W=P∘K, the prime factors of K are C≤u<a, H=E(P), z=φ(u)<n. The actual words of the referenced mark z in the active row are Q, its endpoint is u, and the input natural certificate is

$$
E\equiv_{\Delta(Q)}Q. \tag{6}
$$

New terms are marked as H∘Q∘K. The Q and K all factors and the last column remain in the old prefix, so the new natural world is

$$
D:=\Delta(H\circ Q\circ K)=H(Q(\Delta(K))). \tag{7}
$$

The three bounds guaranteed by the general transitivity method are:

$$
E(\Delta(W)),\qquad H(E(K)(c)),\qquad H(\Delta(Q)). \tag{8}
$$

Let's prove that D does not exceed these bounds, without using replication to output internal adjacency.

Let s be the last factor of Q, thus p(s)=u. From the row boundary and e(s)≥u+1,

$$
Q(\theta_{u+1})\le\Delta(Q).
$$

From Δ(K)≤θ_(u+1), we obtain

$$
Q(\Delta(K))\le\Delta(Q). \tag{9}
$$

Therefore, D≤H(Δ(Q)).

Input Δ(K)≤θ_(u+1)≤θ_z<Δ(Q), which is indeed within the bounds of (6). If (9) is strict, then the weak truncation value is given as E(Δ(K))=Q(Δ(K)); if it equals the bound, then membership is given as at least E(Δ(K))≥Δ(Q)=Q(Δ(K)). Both scenarios are unified as

$$
E(\Delta(K))\ge Q(\Delta(K)). \tag{10}
$$

So, D≤H(EΔ(K))=E(PΔ(K))=E(Δ(W)) covers the first boundary.

Final processing involves replacing 'Second' with 'boundary' to avoid it being automatically considered sufficient by default. The step size of the marks in the old source owner is set to 'δ', and the subsequent source entry is set to 'd'. The correct PDF high guard is given to 'δ<d<C'. The target of this old line of text is strictly after 'y, therefore

$$
F(\theta_d)\ge\theta_{y+1}\ge\Delta(W).
$$

Due to θ_d<θ_y<Δ(W), the old natural weak semantics is given to W(θ_d)≥Δ(W). Here, only the membership lower bound is used, and the images above the bound are not considered equal. By strictly increasing from W=P∘K, Δ(W)=PΔ(K), and P, K(θ_d)≥Δ(K) is obtained. E fixes θ_d, therefore

$$
E(K)(\theta_d)\ge E(\Delta(K))\ge Q(\Delta(K)).
$$

Also, θ_d<c, strict monotonicity gives

$$
\boxed{E(K)(c)>Q(\Delta(K)).} \tag{11}
$$

So, D<H(E(K)(c)) covers the remaining bounds.

The original source uses E, Dougherty Second's E(K)≡_(E(K)(c))E∘K, and the ordinary composite transport of (6), utilizing the three bounds of (8). The formula (9)—(11) proves that they all cover (7), thus the high new mark satisfies (N). When the empty P, the H=id remains, all arguments still hold. There is no truncation of the θ_(y+1) that is fixed to the original source, nor is the final A invoked.

**Theorem 3.1 (The complete copy closure of natural semantics).** Legal continuity preserves the natural semantics of marks retained by all original rules (N)). It does not require +1 within parents or children, Sat, RowAncestor, nor does it require that the copy reduces a certain fixed requirement boundary through scanning. The full regions, low, and high are fully covered.

## 4. inherits the old markers of cut, native, and correct from compTo.

The term "cut" does not change any words or factors that retain the "mark" and the subsequent column, thus keeping it as "(N)". The proven formulas of the ordinary native remain in their old base row "(p)" along with their original "owner"; the old marks inherited from the split row are retained as they are. When a new point is inserted after an old factor row, the original base number of that factor is preserved, and the current column can only decrease. Therefore, for each new natural world that inherits the old mark, it is not greater than the preserved old bound, which remains true for "(N))".

This statement does not mean that old certificates should be discarded: the higher historical boundaries of the entry can be preserved within a single scan, and the actual compTo that follows will use it. The current lower Δ can coexist with the higher historical certificates.

The factor "native" of the new "direct marks" is the same as the "owner" of this row. Therefore, it satisfies the natural condition θ_(y+1). The correct pairing "compTo" retains the old p, "owners", and the old column values, thus also retaining the old certificates. For the proof of the new "marks", see the next section.

## 5. Once the entire package is verified, all the completed read values and the new natural world are automatically established.

Fix the exact term W=P_t∘j_t at a certain old mark in the scan entrance, with the final factor being t. Save the historical certificate.

$$
F\equiv_{\Delta_0}W,\qquad
\Delta_0=P_t(\Theta),\qquad
\Theta=\text{the old value at this entrance }\theta_{t+1}. \tag{12}
$$

The subsequent verified operations retain the old factor owners, the old p chains, and the old columns themselves. Let the underlying actual native source be U=(u_1<⋯<u_q), q>0. The ordinary native gives

$$
j_t(\theta_{u_h})=\theta_{T_t+h}<\Theta.
$$

It is now explicitly assumed that an independent practical packet propagation lemma has been established for parallel owners at all layers, p chains, as well as

$$
W(\theta_{u_h})=\theta_{Y+h}\quad(1\le h\le q),
$$

And the targets are within the historical gaps of the original mark.

$$
\boxed{\theta_{Y+h}
=P_t(j_t(\theta_{u_h}))<P_t(\Theta)=\Delta_0.} \tag{13}
$$

Therefore, (12) can be read as all the actual new lines starting from F(θ_(u_h))=θ_(Y+h). There is no need to prove further that Γ> includes such historical inequalities; they are directly given by the definitions of nature.

The last factor of the new parallel mark is T_t+h, and the preceding factors owners still form P_t. Therefore, its nature is

$$
\Delta_h=P_t(\theta_{T_t+h+1})\le P_t(\Theta)=\Delta_0. \tag{14}
$$

When h<q, the next column is the next native packet point; when h=q, it is exactly the old next column; when Θ, the boundary h=q is also covered. The new terms are globally the same as those with W, and the formulas (12), (14) prove that all new marks satisfy (N).

The ordinary rows with source/target correspond to pairs of gaps, critical points, and geometries. (G) can be derived from (13), historical target gaps, and existing ordinary interval lemmas. Therefore, nature does not provide an independent readout interface for actual compTo: once the entire package and historical gaps are obtained from the original algorithm, all semantics hold accordingly.

The **Non-circularity.** that is not part of this package cannot be inferred as a premise from the conclusions of this section. What is preserved is the Δ_0 that was scanned at the entrance, not the current Δ that has already dropped to the first package point after the underlying native phase. The previous correctness compTo can be used for event induction; the current compTo that is to be verified does not include the previous correctness.

## The interface between 6. and the complete ordinary BLP proof

This paper proves the legitimate copy closure of the natural mark semantics, the cut/native inheritance of old marks, and the entire compTo semantics once the actual whole package is established. Compared to the fixed θ_(y+1) semantics, it no longer requires the restoration of the global internal +1 for each copy seam, and there is no need to track any bounds separately for read.

The remaining algorithmic arguments are derived from the original current guard and the standard scan entry structure to establish the integrity of the entire package, historical gaps, and the validity of ordinary rows. This requires further proof. The package theorem that only uses the entry A_rec is certainly still applicable, but this paper itself does not consider A_rec as a necessary condition, nor does it claim that it has been deleted.

The main agent is studying the Sat condition for the entrance of eligible internal upper factors, denoted as B(e(v))≤p(v), and the package dichotomy adjacent to the entrance. Section 5 of this paper can be directly combined with any correct independent package theorem of this type. The legality of the complete grammatical operations, the standard initial implementation, theorem 2.25, and the well-ordering bridging from the expansion termination to the specified order should still be verified individually in the final synthesis paper. It cannot be completed solely by the title of this paper or by a partial copy closure declaration.

**Marked completion after the current round of completion.** The description of dependencies at the upper level remains unchanged during the formation of this draft. The required independent Sat_rec theorem has been proven and finalized in `sat_endpoint_packet_theorem.md`; the legality of all ordinary operations and the good-order synthesis in I2 are also documented in `full_marked_blp_natural_cutoff_wellorder.md`, and independent final reviews have been completed. The independent final review of den2_wellorder_route for this draft covers the min formula, high three boundaries, low equality boundaries, all native inheritance markers, and h=q historical boundaries. No gaps were found. The precise numerical conclusions of the theorem 2.25 and the conclusions not belonging to this synthesis are presented in DEN2.
