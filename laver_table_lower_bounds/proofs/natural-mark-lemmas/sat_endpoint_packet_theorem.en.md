# The saturation of the entrance to the internal upper factors is sufficient to ensure the transmission of complete marked packages. · [中文版](sat_endpoint_packet_theorem.reading.zh-CN.md)

*English reading edition, translated with machine assistance. The title links to the dated Chinese manuscript.*

> Collected reading edition. The three main papers state the results of this collection.
> This edition retains the local proofs, their hypotheses and any withdrawals. Progress reports describe the state of work at the time.
> The locations of omitted passages on preset inputs are recorded in SOURCE_MANIFEST.json.
> The main papers give the numerical derivations for the natural parameters produced by the proofs. This historical note carries no additional Lean certification.

2026-09-07. This text replaces `current_guard_full_packet_theorem.md` with A_rec as a premise. The new conditions only use the B values of the row containing the source gap's right endpoint, allowing e(v)>p(v)+1. After the main agent is proposed, full_marked_proof and den2_wellorder_route respectively verify the following key inductions. This text applies to ordinary BLP and correct PDFs with the current +1 guard; it does not generalize to DEN2 without a guard.

## 1. scans the entrance and Sat_rec

Fix the legal ordinary BLP scan entry P. The actual trace of each mark precisely hits its step source. Ordinary scans first proceed to compTo and then to native, with the native new blocks being skipped. Let

$$
p_v=A_v[-L_v-1],\quad e_v=A_v[-L_v],\quad B(v)=A_v[-2].
$$

The current base row of the old line v is marked as T_v=ρ(v), and its actual native width is q_v. The old next line is D_v=ρ(v+1)=T_v+q_v+1. The ordinary native block contains

$$
B(T_v+h)=T_v+h-1,\qquad 1\le h\le q_v.
\tag{1}
$$

The previously verified compTo maintains the old step sizes, p, e, min, and sources/targets, all within their respective old intervals. The targets are all located between the historically adjacent columns marked in the mark. native maintains the block start B. These are merely assumptions based on conclusions from previous events, and the current compTo is not included in these assumptions.

It is required that for each entry word in a non-empty Rec, each internal edge v→w satisfies:

$$
\boxed{\text{if v is eligible, then }p_v=w,\quad B_P(e_v)\le w.}
\tag{Sat\_rec}
$$

"Eligible" refers to ordinary medium/short lines; long lines are not considered native. There is no requirement for e_v=w+1, nor is there a requirement that the final factor itself be Sat, nor that the entire replication entry be Sat.

## 2. First prove monotonicity in width, without using complete connectivity

**Lemma 2.1.** for the processed internal upper factor v→w, if it satisfies Sat_rec, then

$$
q_v\le q_w.
\tag{2}
$$

When q_v>0, its actual native source must be a primary segment of a new block that is w
`T_w+1,...,T_w+q_v`.

**Proof.** is a long line of q_v=0. For eligible v, denote them as s=e_v. If s=v, then the next source is the core maximum item, hence L_v=1; ordinary eligible lines can only have two core points, native first queries B(v)=p_v, and the package is empty. The legal preceeding compTo cannot change the conclusion of this degenerate line.

The following s<v, therefore the old line s is processed before v. The entrance B_P(s)≤w indicates that all of the old proper marks s are limited to the value w. Marked as y<w, its previous correct completion has targets that are strictly lower than the historical y+1 sequence, thus being lower or preceding T_w. Sources are lower. Only the old mark w could possibly cause the base row s to exceed T_w at the row B. If the mark is actually inserted into k targets, the previous geometry is given as

$$
T_w+k<D_w=T_w+q_w+1,\quad\text{hence }k\le q_w.
\tag{3}
$$

When it has this mark B_P(s)=w, it executes after B(ρ(s))=T_w+k. When it does not have this mark, it remains at B(ρ(s))≤T_w. s's native remains in the base row B; operations in higher rows do not modify it anymore.

The current v is still in historical endpoints (between T_w and ρ(s)), with the chain being B. If B(ρ(s))≤T_w, the first B query has reached the termination threshold, and the package is empty; if B(ρ(s))=T_w+k, then the package obtained by (1) is exactly `T_w+1,...,T_w+k`, thus q_v=k≤q_w. Proof complete.

It is allowed for s to be far away from w. Limiting B_P(s)≤w instead of s=w+1 is sufficient to prevent independent old sources from contaminating this package.

## The actual connection of 3. can only be empty or complete.

**Lemma 3.1.** In the lemma 2.1 in such a situation, Only after processing s

$$
B(\rho(s))\le T_w\quad\text{or}\quad
B(\rho(s))=T_w+q_w.
\tag{4}
$$

The process for dealing with **Proof.** only requires handling the situation where s's old marks are indeed completed by w and then by k>0. Its underlying old factor is denoted as t, hence k=q_t. The mark indicates the presence of non-empty records, and Sat_rec applies to each of its internal edges. All factors are strictly below the owner s, and have been processed. Along its terms, the lemma 2.1 is used to derive q_w≤q_t=k. The previous section of geometry has given k≤q_w, so they are equal. This uses the current v and previous native and verified compTo, without loop verification for the current event. Proof completed.

More specifically, when verifying the current compTo of an outer owner R, the lemma 2.1 uses each endpoint owner s<v<R that is strictly earlier. In the lemma 3.1, all factors of the carrier term are also <s. The lemma 2.1 itself does not use the lemma 3.1, but only uses the geometry of earlier compTo. Therefore, we first use monotonicity in width, and then prove dichotomy, without reborrowing the correctness of the current outer compTo.

## 4. Current +1 guard forces a complete parallel package

Fix the current outer mark, and its old non-terminal factors are recorded from bottom to top as b₀<...<b_d=y. Assume that the underlying actual native packages U=(u₁,...,u_q) are non-empty, q=q_(b₀). The current PDF detects each internal edge during inspection.

$$
T_{b_{i-1}}+1\in A_{T_{b_i}}\qquad(1\le i\le d).
\tag{5}
$$

**Theorem 4.1.** is verified to be true for Sat_rec and in the preceding sections. In each layer, the native width equals q, and the actual source of the upper layer i is exactly the entire package of the lower layer `T_(b_(i−1))+1,...,+q`. Therefore, all h=1,...,q satisfy

$$
p(T_{b_0}+h)=u_h,\qquad
p(T_{b_i}+h)=T_{b_{i-1}}+h,
\tag{6}
$$

$$
j_{T_{b_i}+h}=j_{b_i},\qquad
\theta_{T_y+h}=(j_{b_d}\circ\cdots\circ j_{b_0})(\theta_{u_h}).
\tag{7}
$$

**Proof.** Inductively from the bottom up. Assume that the lower layer is q>0. The new integer T_w+1 was not originally present in any row of the scan entry. Located within the upper-level historical gaps (T_w,ρ(e_v))). Previously, the correct sources for compTo were strictly less than p_v. Targets are at or above e_v. No points will be added to this source gap. The target position here uses the ordinary interval lemma that has been verified in previous events. Not only the bare grammar of proper mark: Non-empty underlying native is given as crit(W)<θ_δ. Historical weak certificates are provided to crit(owner)<θ_δ. Therefore, the source cannot be the smallest entry. Especially in long lines. This rules out the possibility that the earliest proper marks located below e_v actually perform non-empty completion. Therefore, (5) can only be implemented by non-empty native functions of the upper layer itself. The lemma 3.1 inevitably forces it to select the entire lower-level package. Rather than the true initial stage. degradation e_v=v Neither the single line nor the long lines can pass this check. Ordinary native line-by-line formulas are given as (6), (7). Proof completed.

This step only verifies the correspondence between packages; the actual new rows of the current outer owner still need to be verified with the marking certificate in the next section. It is not appropriate to treat the combination correspondence as semantic.

## The successor bounds of the factors 5. exactly cover all actual targets.

Let the word marked as W=P∘j_t be the entry point, where t=b₀ and P are prefixes other than the terminal factors. Save the historical boundaries of the definition of the entry base number.

$$
\Delta_0=P(\theta^{\rm entry}_{t+1}),\qquad F\equiv_{\Delta_0}W.
\tag{8}
$$

Normally, the native strictly inserts the new bottom points into their old target gaps.

$$
j_t(\theta_{u_h})<\theta^{\rm entry}_{t+1}.
$$

Theorem 4.1 thus given

$$
\boxed{\theta_{T_y+h}=W(\theta_{u_h})<\Delta_0.}
\tag{9}
$$

Therefore, the membership weak equivalence indeed reads out all the new row edges of F, and cannot be omitted solely based on Δ₀>θ_(T_y) (9). In addition, Δ₀≤ entrance θ_(y+1), so targets are located in the historical gaps of the old marks; this gap, which does not contain the owner, was not previously occupied by any other mark. `marked_completion_interval_lemma.md` §4 maintains the ordinary pairing geometry and the old edges.

The parallel factors of the new mark are globally the same; their natural new boundaries are

$$
\Delta_h=P(\theta_{T_t+h+1})\le
P(\theta^{\rm entry}_{t+1})=\Delta_0.
\tag{10}
$$

When h=q, the right side is equal to the sign, and when h, it is an inequality. Therefore, all new marks satisfy the natural semantics; the old base row factors remain unchanged, and their current immediate subsequent columns only decrease, so their natural semantics do not increase either. This completes the semantic induction for each event. For the specific natural semantics of the copy closure, see
`natural_trace_cutoff_semantics.md`.

The identification of new terms here is also determined by an algorithm: The paired geometry makes the step size of the new mark T_y+h originate from u_h. The formula (6) ensures that the actual p chain passes through each T_(b_i)+h step by step, and accurately stops at u_h. The native blocks of different layers do not intersect with each other, so they will not hit the endpoint in advance. There is no need to assume an additional +1 inside the new term; when the entrance e_v>w+1 occurs, the adjacent term at the end of the package h=q may not hold, and it is not used in this section.

The formula (8) must be retained as a historical certificate. After the underlying native stage, the current nature may have been reduced to P(θ_(T_t+1)); this lower current boundary should not be substituted into (8) when attempting to read the entire package.

## The single Sat parent item short copy marked with 6. automatically provides Sat_rec.

The parent pattern for **Theorem 6.1.** is the true ordinary BLS, Sat. The trace of all marks is precise; using natural language semantics, no internal adjacency is required. A legal short copy is executed, and a complete scan from left to right is performed. Therefore, all actual reads of non-empty Rec's old marks satisfy the entry Sat_rec.

**Proof.** Sat and empty Rec cause the original row n−1 to remain stationary. It has been proven that the actual copy word recognition and the `scan_dependency_localization.md` theorem 3.1 still apply: any mark that reads a non-empty record must have all non-terminal factors copied. The end factors of the crossing low/high are at stationary prefixes, and no records are established in this round.

For such old terms with internal edges v→w, the root is replicated as a, followed by w≥a, and then w<e_v≤v. The owner is proper, so the lines where v and e_v are located are within the same continuous replication source interval. If v is eligible, the parent Sat gives B(e_v)≤w; the unified strict mapping φ is given to

$$
B_{\rm entry}(\varphi(e_v))=
\varphi(B_{\rm parent}(e_v))\le\varphi(w).
\tag{11}
$$

Copying preserves positions within the rows and the row types, which proves Sat at the required entrance. The condition is not imposed on the lowest nonterminal factor. This factor may produce the first native packet of the round. This finishes the proof.

The formula (11) holds even when B_parent(e_v)<a: it is the core entry of the source line e_v, and the legal copy thus defines φ at that point. Moreover, φ is strictly increasing throughout the domain used. This argument applies to every actual mark that borrows from a non-empty Rec, including the carrier mark that may be read in section 3. If the carrier crosses the replication boundary, its final factor is at a static prefix, and it will never trigger a non-empty call.

Combining the copy preservation theorem in the natural world, the 4–5 section, and the general native preservation, it is possible to obtain a complete natural world marked BLS closure with a M_star. There is no need to prove the output of the old A first. The standard Sat pure combinatorial induction can then be directly applied, as the legality of each actual operation has been verified in the above event-by-event induction.

## The range of 7. and review reminders

The core Sat substitution has been verified by two agents, and the final draft has been reviewed and approved. The overall E/M synthesis can be found in the independent review record of `full_marked_blp_natural_cutoff_wellorder.md`. The general scan for the entry Sat_rec is not applicable: its endpoint row may already contain B(e_v)>p_v, creating additional old sources, which in turn causes the subsequent marks to only connect to one true initial segment. This explains why the local counterexample of `marked_cutoff_demand_analysis.md` does not refute this paper.

**Independent final review records (full_marked_proof,2026-09-07).** The full text has passed the review of the local theorem. All items have been checked. In section 2–3, only earlier events are used. In section 4, the +1 new points cannot come from compTo. In section 5, the entry history is preserved. In section Δ, and in section 6, Sat transport for all non-empty carriers is performed. Fixed the reversal of the reference to "previous/next" in section 2. And specify that it is lower than the replication root. B Similar to, new word recognition, and no need for internal new words A The boundaries. No new algorithm filters or unproven semantic premises have been added. This record is responsible for the local integralization theorem; The review of the overall E/M, termination, and well-order synthesis is noted in the global draft.
