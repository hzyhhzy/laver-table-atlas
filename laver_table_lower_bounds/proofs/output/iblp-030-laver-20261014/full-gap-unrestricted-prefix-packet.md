# Prependence theorem for full gap scanning: Semantic closure no longer requires Sat · [中文版](full-gap-unrestricted-prefix-packet.zh-CN.md)

*English reading edition, translated with machine assistance. The title links to the dated Chinese manuscript.*

> Collected reading edition. The three main papers state the results of this collection.
> This edition retains the local proofs, their hypotheses and any withdrawals. Progress reports describe the state of work at the time.
> The locations of omitted passages on preset inputs are recorded in SOURCE_MANIFEST.json.
> The main papers give the numerical derivations for the natural parameters produced by the proofs. This historical note carries no additional Lean certification.

2026-10-14. This paper strengthens the proposal [Local closure of the parent term of GapSat](<full-gap-native-local-closure.md>): For exempted $L=1$ full-gap natives, the fully scanned **Semantic Legitimacy** actually does not require GapSat, old Sat, or Sat_rec.

The reason is not that 'more supplementation makes it stronger,' but rather a definite prefix relationship: the upper-level full gap packages can be longer than the lower-level packages, but the segment preceding them must exactly be the entire new family of the lower level; transporting the underlying records only requires this segment. The order enhancement is not discussed below. GapSat is still used for the prefix properties of old prefix static and fundamental sequences.

## 1. Input and Conclusions

The input is any finite, real, ordinary marked BLS:

- Each core, after adding back the implicit endpoints, satisfies the ordinary row type; all row edges and the critical points of the minimal terms are real;
- All proper marks, whose actual p chain accurately matches the step-length pairing source;
- Each mark satisfies the natural membership truncation of its current actual word.

No input from standard roots is required, nor are any saturation conditions required. A left-to-right scan is used: each old line at that time is first frozen according to the current $+1$ guard, then processed with native. The new family of native is skipped, not re-scanned in this round. Native is only executed for ordinary and short lines with a step size of $L\ge2$. The source package covers all integer intervals with a step size of $(p,e)$.

Every actual complement scanned with **Theorem.** is legal. All new and old rows, proper traces, and natural truncations are preserved. The scanning is completed in a finite manner, and the output is GapSat. The global last-named point and the last owner remain unchanged.

This is the theorem on scanning itself; if replication is performed beforehand, it is still necessary to ensure that the original copy mapping is defined, and to invoke the natural truncation semantics of a valid copy. The theorem does not claim that all copies can be made.

## 2. old factor base row sums and untainted source gaps

Mark the old lines scanned as $v,w,\ldots$. Their current base line position is marked as $T_v,T_w,\ldots$, and the number of times they were inserted into the native state is $q_v,q_w,\ldots$. The previous insertions only renumber the old lines after this, without re-scannning the new family.

Inductive reasoning is carried out along the order of old lines and the processing of old marks that are frozen. Before verifying an event, facts that have already been verified can be used:

1. The original base row retains its p and owner, and the new tier row also uses the same owner.
2. Correctly retain the old p/e, old edge notation, and owner for compTo.
3. compTo: New sources that are strictly below the p of the owner, new targets at or above their e.
Do not add core entries to the open interval $(p,e)$.
4. The actual factor base lines of the old mark and the old terms are retained with their corresponding numbers.

The 3th item is not an assertion for any raw field. The earliest critical-image mark in a regular line may violate its literal position range; it must be proven using the §5 critical point argument that this mark will not perform non-empty completion. Only those compTo that have been verified before can use these four items, and the current event is not included in the inductive premises.

## The package containing the active factors within 3. includes the entire lower-level family as a prefix.

Suppose there is an internal edge $v\to w$ for a certain entry word, that is, the entry is $p(v)=w$. Of course, it is $e(v)>w$, but it is not required that it be $e(v)=w+1$ or the old $\delta(e(v))\le w$. Suppose a non-empty native family has been generated at the lower level, with a width of $q_w>0$.

Due to the scanning in the old row order, all the newly added global points between the old row $w$ and its immediately following old row are the native family of the old row $w$ itself. Therefore, the current addresses of these points are

$$
T_w+1,\ldots,T_w+q_w.
\tag{1}
$$

The original next line is at $T_w+q_w+1$; the native insertion points of later lines all occur after this position, and will not be reinserted into the (1) interval. compTo does not add any new global points.

When scanned to $v$, its p remains $T_w$, and its e corresponds to some old point that is strictly later than $w$, so it is at least $T_w+q_w+1$. If $v$ is active, it takes the entire current source interval, so

$$
q_v\ge q_w,\qquad
u_h^{(v)}=T_w+h\quad(1\le h\le q_w).
\tag{2}
$$

Here, the items are arranged in ascending order. The unified p formula for the ordinary native ladder is given as follows:

$$
p(T_v+h)=T_w+h\quad(1\le h\le q_w),
\qquad J_{T_v+h}=J_v.
\tag{3}
$$

The upper gaps can contain any number of old points and other previous families after these points; they only increase to $q_v$ without changing the first $q_w$ term. Therefore, there is no need for old Sat, nor is there a need for replication factors confined to the same continuous region.

## 4. current guard forces the actual passing internal factor to be active.

Fix the current mark. The old non-terminal factors are arranged from bottom to top as $b_0<\cdots<b_d=y$, and the bottom-level records are wide $q=q_{b_0}>0$. The current $+1$ guard requires that the upper core of each internal edge contains the first point after the lower fundamental row.
$T_{b_{i-1}}+1$.

This point is not a scanned entry for an old point, but rather the first new point in the underlying native. If the upper layer is a long line, it is not considered native. During its marking phase, it has been verified that the sources of compTo are below p, and the targets are either above e or at $(p,e)$. Therefore, the long line does not pass this guard.

If the upper layer is a native step-length two-core structure $(p,v)$, it has no proper marks, and only contains base points $T_w$ and row addresses that do not precede $T_w+q_w+1$. It cannot contain $T_w+1$. A step-length long row falls under the previous category.

Therefore, for an actual pass through the guard, the non-empty mark must have all its internal factors be active. It is derived by induction along (2).

$$
q_{b_0}\le q_{b_1}\le\cdots\le q_{b_d}.
\tag{4}
$$

Only take the first $q=q_{b_0}$ lines on each layer, starting from (3).

$$
p(T_{b_i}+h)=T_{b_{i-1}}+h
\qquad(1\le h\le q,\ 1\le i\le d).
\tag{5}
$$

At the bottom layer, it satisfies $p(T_{b_0}+h)=u_h$. Among them, $u_h$ is the $h$th source point in the original record. Therefore, the $q$ items actually transmitted by compTo have accurate parallel p chains and factor owners.   **Not necessary** The total width of all upper layers is equal to $q$ ;  The formula (4) is sufficient.

## 5. History of Natural Sciences, Critical Points, and Complete Pairing Geometry

Let the owner of the current mark be $F$, and its old word for entry be

$$
W=P\circ K,\qquad K=J_{b_0}.
$$

The bottom entry is marked with the sequence $\Theta$. Scanning the entry preserves the historical natural certificate.

$$
F\equiv_{\Delta_0}W,\qquad \Delta_0=P(\Theta).
\tag{6}
$$

The previous operations retain the original terms, old owners, and old naming points. All images inserted at the bottom level are lower than their old successor points, hence

$$
K(\xi_{u_h})<\Theta.
$$

Due to the prefix transport from §4, the first $q$ targets at the top level are actually

$$
\xi_{T_y+h}=W(\xi_{u_h})
           =P(K(\xi_{u_h}))<P(\Theta)=\Delta_0.
\tag{7}
$$

Therefore, the historical membership truncation reads every newly added $F$ edge, without the need to include the remaining targets that exceed $q$ in the current compTo.

The underlying non-empty native comes from the ordinary $L\ge2$ active rows. Ordinary row types exclude steps of 2 length, therefore the underlying $p$ is strictly greater than its minimal item, given by $\operatorname{crit}(K)<\xi_\delta$, where $\delta$ is the source of this mark. The combination does not improve the earliest moved point, hence

$$
\operatorname{crit}(W)\le\operatorname{crit}(K)<\xi_\delta.
$$

Also, $W(\xi_\delta)=\xi_y<\Delta_0$, the historical weak equivalence is the same as $F$, with the same low critical point. Therefore, $\delta$ cannot be the minimal term of $F$. This is precisely the argument that excludes the earliest critical-image mark from executing non-empty completion in long lines.

The formula (7) also ensures that targets are strictly located within the historical nearest gaps of the mark. Due to the real old edges, strict monotonicity, and the general pair interval lemma, the source package is located within its corresponding source gap. This holds for all old edges and new edges, and the old p/e and owner are retained. Therefore, the positional properties of §2 are also verified for the current compTo at this moment.

The actual word that adds the $h$ number of parallel marks is still composed of the same owners. The accuracy is provided by (5), and its natural form is

$$
\Delta_h=P(\xi_{T_{b_0}+h+1})\le P(\Theta)=\Delta_0.
\tag{8}
$$

The equality occurs at the bottom level $h=q$; whether there are more new lines at the upper level is irrelevant. Therefore, all new natural certificates remain intact. The current successor point of old certificates can only decrease, which still holds true.

## 6. Completion Event Inductive and Usage Boundaries

The current compTo has been fully verified, and the native operation is now executed. The latter has been directly verified for point images and ladder rows across any ascending integer gaps, without relying on ancestral chains. It applies to ordinary row types, the same owner, accurate direct marks, and the GapSat family. All new targets are strictly earlier than their mark owner, thus the proper condition is maintained.

The number of freeze marks for each old line is limited; Each gap contains a limited number of current addresses; The new family is skipped. Therefore, the aforementioned events can be summarized as limited completion and full local legitimacy. Each prefix that has been processed is marked as GapSat. Do not change the previous lines for subsequent operations. Therefore, the final output is GapSat. Do not change the old end owner and the global end point. Theorem proof completed.

This conclusion can be used after copying any finite string **Legal**: first, obtain the true input by sequentially using the original natural copy semantics, then call the scanning theorem from this article. No additional proof is required for Sat_rec. However, full tail copying may increase the cap, so this statement does not automatically provide a fixed lower bound for the reduction or number of steps of a well-founded reduction. It also cannot be interpreted as a single application reduction for any number of full tail copies.

If it is necessary to expand and retain the parent cut prefix, the parent item GapSat should still be allowed: this way, scanning the old prefix at the entrance can be stopped. Semantic closure, prefix structure, strict descending order, and quantitative strength comparison are four different interfaces. This theorem only eliminates the premise of Sat/Sat_rec within the first interface.

**Independent audit.** t3_audit independently verified the subscripts of prefix packages rather than equal-width packages, as well as the exclusion of $L=1$, historical natural phenomena, and boundaries at the end of packages $h=q_{\rm bottom}$. It was confirmed that the order of events mentioned above is not pre-allocated by the current compTo. This audit does not extend this theorem to strength comparisons or to fully fixed-capacity well-foundedness.
