# Any successor mark is sufficient to restore the scan adjacency: no compatible trace is required. · [中文版](unqualified_successor_mark_scan.reading.zh-CN.md)

*English reading edition, translated with machine assistance. The title links to the dated Chinese manuscript.*

> Collected reading edition. The three main papers state the results of this collection.
> This edition retains the local proofs, their hypotheses and any withdrawals. Progress reports describe the state of work at the time.
> The locations of omitted passages on preset inputs are recorded in SOURCE_MANIFEST.json.
> The main papers give the numerical derivations for the natural parameters produced by the proofs. This historical note carries no additional Lean certification.

2026-09-07. In this paper, the successor certificates in scanning are weakened to simply the existence of a mark. The proof does not require that this mark have the same terminal as the outer word, nor does it require that the trace be a prefix of the outer word. Additionally, it is proven that the true compTo new parallel words automatically acquire the required successor mark at the h=q point at the end of the block.

This paper presents an independent complete scanning theorem. When applied to standard single shortcopy entries, it is still necessary to verify that the corresponding old marks are adjacent to the entry after copying, and that there is a successor mark. This part of the creation/copying obligation cannot be hidden under the assumption that 'the successor is already connected'.

## 1. entry properties

The actual trace of an old mark

$$
(v_0>v_1>\cdots>v_\ell>\delta)
$$

Let v_1, …, v_ℓ be the internal lower factors. Define

$$
\mathsf R:\qquad
\text{each internal lower factor }t\text{ all satisfy }t\in M_{t+1}.
\tag{1}
$$

This rule stipulates that there must indeed be a mark t in the numerical consecutive sequence. No compatibility requirements are imposed on the trace of this mark with the original word; Different external words can use the same subsequent mark.

Consider a regular PDF that starts from an empty Rec and is scanned from left to right. The input satisfies:

* The real ordinary marked BLS, all old traces are precise;
* All old traces have internal adjacency A;
* The FactorCap of `standard_factor_cap_preservation.md`;
* Property R.

Allow any ordinary short/medium native languages, any number of marks, and their interleaved packages, without scanning isolation conditions. The following does not require input of Sat; this is a theorem of preservation for scanning itself.

## 2. with marks on R remains unchanged during local operations

**Lemma 2.1.** retains the correct compTo for the old edges and old marks, as well as the ordinary native. The R with the remaining old marks is also preserved. The cut also retains the R with the remaining old marks.

**Proof.** Correct compTo does not change any other lines, retaining all the old proper marks from the current line; the chain of p from the old trace remains intact, thus the old internal factors and their subsequent marks are also preserved.

For the native operation of inserting a new line q>0 into a line r, the old internal lower factor t is retained:

* When r<t, t and t+1 all share the same weight number, and the old successor marks are correspondingly renumbered.
* When r>t, if r=t+1, the block header retains the old mark t; if it is larger, then both rows remain unchanged.
* When r=t, the old successor is moved to t+q+1, but the new row at t+1 automatically carries a direct mark t.
The reason subidentity is still assumed by the block head t, so this is precisely the numerical successor it currently needs.

The old mark copy of the 'owner' that is split also references the same old factor word, thus it also satisfies R. It is trivial when q=0. Finally, if a mark that is retained still has an internal edge v→t, then t+1≤v<owner. It is impossible for cut to delete t+1 alone without leaving this mark behind. Proof complete.

## 3. restores all old neighbors according to the upper factor row number

**Theorem 3.1.** Under the entry conditions in the 1 section, Complete scan to restore all old marks. A. Each internal edge v→w has been restored by the time the scanning process finishes for the old row v. No changes will be made in the future.

**Proof.** implies that the entrance is fully A, and it implies `current_guard_full_packet_theorem.md` that there is a A_rec. Its event-by-event semantic theorem independently verifies all compTo that are currently being executed. This step only selects events that will be executed according to the current guard in the PDF, without presupposing any recovery from unprocessed old edges. The old FactorCap is then maintained by the proven paired geometry and native row type.

Make an incremental induction for the old label at the entrance v. Consider any internal edge v→w; the actual p of the same v is unique, so this lower factor in different old traces is still the same w. The entrance A gives

$$
p_v=w,\qquad e_v=w+1.
\tag{2}
$$

If q_w=0, the source gap remains empty; if q_v=0, the old w+1 becomes the current T_w+1, and this edge is automatically maintained. Let q_w>0 be defined as follows.

FactorCap gives a step size of at least 2 to v, so it's w+1<v. R scans the entrance and has a proper mark w for the old row γ=w+1. Examining this old mark when it is processed, let's denote its entrance trace as

$$
(w=c_0,c_1,\ldots,c_k,\varepsilon).
\tag{3}
$$

The formula (3) can be shorter than the outer word, or it can be longer. All of its non-terminal factors are ≤w<γ<v, and thus the upper factor of each of its internal edges is smaller than v. The inductive hypothesis ensures that these edges have been restored to their original state at γ under compTo: their factor-based rows remain unchanged after processing. Therefore, this marked PDF currently passes the +1 guard.

On the other hand, the formula (3), with its **Entrance** A and width monotonicity are given as

$$
0<q_w\le q_{c_1}\le\cdots\le q_{c_k}.
\tag{4}
$$

Therefore, its final factor Rec is not empty. This old proper mark has also not been correctly removed earlier, so the actual algorithm for γ indeed performs a non-empty mark w completion once.

This event has been verified by the independent event theorem. The comparison of the widths on both sides of the subsequent binary division is thus given.

$$
B(D_w)=T_w+q_w.
\tag{5}
$$

γ's native only appends to the following packages, and retains the block header B. Therefore, the condition holds when 5) reaches v. The line v is a Cap, and its actual source gap is `(T_w,D_w)`. Thus, its native selects the entire q_w package along the true continuous B chain. In particular, the addition of T_w+1 at the block header restores this internal edge.

This covers all cases where v is involved. Once the factor-based rows are processed, they will not be altered by subsequent scans, thus the incremental induction is completed. Proof complete.

Here, the term "carrier's word and foreign word compatibility" is not used. What is needed is its own entry A, the lower bound of the formula (4), and a restoration induction based on smaller upper factors. It is also not guaranteed by the current foreign term compTo (5):γ<v, where the connecting event occurs in an earlier row.

## 4. New parallel words in h=q The successor mark at

**Lemma 4.1.** Any actual compTo that has been verified by the whole package theorem satisfies R for all its new marks; this conclusion does not require assuming compatible carriers for the old traces.

The new trace for **Proof.** is

$$
(T_d+h,T_{d-1}+h,\ldots,T_0+h,u_h),\qquad1\le h\le q.
\tag{6}
$$

If d=0, there are no internal lower factors, and the conclusion is empty. Otherwise, fix the internal lower factor T_i+h of i<d.

When h<q, its numerical successor T_i+h+1 still resides in the same native block. The native birth formula is directly marked with T_i+h in that row.

When h=q, the numerical successor is the historical old row D_i=T_i+q+1, and it cannot be replaced by the q+1th new row within an existing block. The pack theorem indicates that the actual source of the upper T_(i+1) is precisely `T_i+1,…,T_i+q`. The source immediately below the entrance is the historical D_i, therefore the true B chain must satisfy

$$
B(D_i)=T_i+q.
\tag{7}
$$

Only a compTo that is non-empty, executed by the old mark T_i with D_i, can make its B exceed the old base row T_i: the historical target gaps of other old marks are strictly below T_i, while the ordinary native retained block header B. This is the same operation classification that has been used in the proof of the successor binary division.

Therefore, D_i has indeed executed the mark T_i completion before this. The correct completion assigned to it is precisely q, and T_i+q is added as a new mark. The D_i subsequent native retains this proper mark, and it is not modified by any subsequent scans.

$$
T_i+q\in M_{T_i+q+1},
$$

The R required to establish the block end. Proof completed.

This conclusion is only applicable to (6)'s **Internal lower factor** i<d. The highest prime factor T_d+q is not transported to a higher level in this old term, and there is no reason for it to automatically hold under (7); it cannot be claimed that all new marks' prime factors also have subsequent marks.

## 5. complete scan remains as A, R, and FactorCap

The ordinary complete scan output inputted in the 1 section of **Corollary 5.1.** is still correctly marked as BLS, and it satisfies all the A, R, and FactorCap criteria for both old and new marks.

**Proof.** The ordinary row boundaries, the old weak semantics, the new compTo terms, and the new mark weak semantics are given by the proven event theorem and the native formula. The old A is proven by the theorem 3.1; The A of the new compTo has been verified at birth, and its factor rows have been processed before the current owner. The subsequent scan will not change; The native new direct marks have no internal adjacency obligations.

The old R is derived from the lemma 2.1. The new native direct marks have no internal lower factors; the new compTo R is derived from the lemma 4.1. The preservation of the new FactorCap between the old and the new versions is proven for each event by the corresponding proof. Proof completed.

This provides a complete scan closure segment that does not require CC. It does not contain any new seams copied from the previous step.

## The 6. interfaces for birth and replication still need to be listed individually in a single Sat M.

After a single Sat shortcopy, only the old words with non-empty Rec must be fully factor copied, which results in A_rec. If only one internal lower factor w is known to have a successor mark at the scanning entrance, but this mark itself has undergone cross-border copying, and the entrance A is unknown, it cannot be used directly (4). Its final factor may even be located at a static old prefix, resulting in Rec=0.

Therefore, to apply the theorem 3.1 to this entry, a complete entry A is required, or it must be proven that the subsequent marks actually used in the induction have the same entry adjacency and smaller edge restoration conditions. It is not sufficient to simply substitute "exist mark" into A_rec and then skip the proof of whether it can read non-empty records.

Additionally, while word replication automatically copies the inner factors w and w+1, it does not automatically ensure that the mark w in the subsequent lines is retained. The actual word may be longer than the outer word, extending beyond the terminal of the outer word and down to below the replication root; in such cases, it is necessary to check the low/high filtering of its own word. R is weaker than CC, and cannot inherit the replication lemma that was previously only applicable to compatible end words without proof.

This manuscript has eliminated the need for compatibility with terms, the assumption of the same terminal and the assumption of successors after blocks. The standard history remains the birth and replication of actual R, as well as cross-border new adjacencies; it does not consider the existence of successors of all marked initial factors as proven invariants here.
