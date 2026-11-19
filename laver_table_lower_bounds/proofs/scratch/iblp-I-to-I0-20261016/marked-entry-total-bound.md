# Original R[x][x] with marked short M counting entries · [中文版](marked-entry-total-bound.zh-CN.txt)

*English reading edition, translated with machine assistance. The title links to the dated Chinese manuscript.*

> Collected reading edition. The three main papers state the results of this collection.
> This edition retains the local proofs, their hypotheses and any withdrawals. Progress reports describe the state of work at the time.
> The locations of omitted passages on preset inputs are recorded in SOURCE_MANIFEST.json.
> The main papers give the numerical derivations for the natural parameters produced by the proofs. This historical note carries no additional Lean certification.

2026-10-16. This round of independent entry proofs; no modifications to any original definitions or published documents are made.

This paper uses the framework with ZFC+I3 and the following explicitly listed local lemmas.
The new argument is a successor-closed extraction that maintains natural membership truncation, as well as its
Verification of total indicators in the specified forest construction for R[k] and R[k][n]. Not in Lean formalization.

[The three main papers give the natural inputs and their full derivation. This reading edition omits the older treatment with a preset input.]

To prove and provide the conclusion of the proof below:

                T_paper(S) < 2^{q(5)}.                 (A)

[The three main papers give the natural inputs and their full derivation. This reading edition omits the older treatment with a preset input.]

[The three main papers give the natural inputs and their full derivation. This reading edition omits the older treatment with a preset input.]

The above document is located in the following places: this scratch, ../iblp030-8h-20261015,
../../output/iblp-laver-bms-20261013, and
Natural Marking Lemma Directory/.
The underlying I3/BLP literature is Renrui Qi, Notes on Laver Tables v5:
https://arxiv.org/html/2501.06733v5

### The truly missing extraction lemma
----------------------
Natural semantics uses Laver membership truncation: F≡_b W indicates for x, z∈V_b.
x∈F(z) is equivalent to x∈W(z), and the function is not value-equivalent at V_b.
If the exact non-terminal word of mark y is (v_0=y,...,v_{d-1}=t), then
  W=F_(v_0) o ... o F_t，
  Δ(W)=(F_(v_0) o ... o F_(v_{d-2}))(theta_(t+1))，
Require carrier F_r≡_Δ(W) W. There are already natural lemmas given...
  theta_y < Δ(W) <= theta_(y+1).

Lemma 1 (Membership remains unchanged at critical points). If crit(G)=c, then
  G(F)≡_c F.
Proof: Both x and z∈V_c are fixed by G; Apply the compatibility rule to
G(F)(z)=G(F(z)), and by elementaryity, x∈G(F(z)) iff x∈F(z).
This does not require F(z)∈V_c.

Lemma 2 (Factor successor closure extraction). Suppose the actual marked state satisfies natural semantics.
Select the row set J, retain all core/mark/trace citations and the final row and final cap. Additionally, request the following:
  For each non-terminal factor marked with a 'v', 'v+1' also exists in 'J'.
Then, after extracting and repairing the implicit endpoints according to the original named points, it still satisfies natural semantics.
The final cap does not rise, and all owners remain at the same Iter(j).

Proof: If the next retention point of the line r changes from c=theta_(r+1) to c'>c, then use the actual
Transporter G, crit(G)=c, G(c)=c', change F_r to G(F_r). All original
The explicit edge remains intact, and the new implicit endpoints are correct. This is an existing endpoint repair.
For retaining the mark, each physical successor v+1 of the factor v is retained, hence the factor owner
Without any need for repair at all; its current successor point has also not changed. Therefore, the entire term W and Δ(W) remain unchanged.
Keep it unchanged. Do not mistake "only retaining word references" for this step.
If the carrier r is repaired, by proper y<r and the natural lemma, there is
  Δ(W)<=theta_(y+1)<=theta_r<c.
The lemma 1 yields G(F_r)≡_Δ(W) F_r≡_Δ(W) W.
The final line and 'cap' are retained, hence the final 'owner' is not repaired. Proof complete.

Therefore, the question is not whether any OPEN certificate can be upgraded, but rather the selection set of the specified forest this time.
Whether it satisfies the more stringent "reference factor and its physical successor are retained together".

### The first expansion of R[k] satisfies the strong extraction condition.
----------------------------------
The six lines of R have no marks, and the complete end package only has the last line. There is a main budget line used
m is a slightly more explicit E doubling supply of 2^m actual parallel complete packages, cap<kappa4. Take the first k of them.
According to the original forest rules, perform k-1 raw short copies, delete control lines, and complete native scans.
In the raw state, there is no inheritance of marks, so there is no semantic issue with mixed-copy.

In the first step of the forest scan, each selected original base row is considered, and its entire native family is selected as well.
Every new direct mark y is born in the later carrier r of this family; its exact word is only
Factor y, and this factor shares the same global owner with the carrier at the beginning.
Therefore, the natural relationship is initially established, and y+1<=r, y+1 are still in the same selected family.
This scan skips the new family of entities, and will not inherit and complete their new marks.

Therefore, the lemma 2 applies, yielding a precise original R[k] natural certificate, which is not just a OPEN certificate.
Ultimately, owner/cap remains unchanged. The actual endpoints and witnesses of both the main line and the backup line remain unchanged.

### Why is there no dangerous mixed mark in the second expansion?
---------------------------------------
Let A=R[k], k>=3. According to the explicit triangle family formula:
  (a) all marks are direct;
  (b), each mark's paired source δ>=3;
  The minimum address of the c) activity controller is a=2.
  (d) is the complete tail package. [e,N] are the last two complete native families.)
Within each package, the factors of the mark and their successors are within the package. The initial carrier may have been repaired.
Therefore, it is no longer assumed that the carrier is globally equal to the factor; only the natural relationships obtained in Section 4 are used.

Consider a raw short copy within the second forest, with a root of P, an address mapping of f, and an active minimum of a.
Maintenance of inductive conditions: Each paired source with a direct mark in the active source area satisfies δ>=a.
If the factor header is y<P, then:
  - The low branch requires y<a, but δ<y contradicts δ>=a.
  - The legacy high branch requires f(δ)<=a, but f(δ)>=f(a)>a, which is contradictory.
The guard for 'paper high' is stricter, and it does not retain any symbols. Therefore, all retained marks have y>=P.
Use only full-factor replication branches. Accurate terms remain single factors; natural relationships are defined by application.
Transport to new factors and successor points. The next activity source area is entirely new replication lines.
  δ'=f(δ)>=f(a)=a'，
Therefore, the induction is closed. The parallel complete tail packet also retains these conditions.

The phrase "all the next activity source areas are new replication rows" has also been specifically verified through short replication in the forest.
Applying the complete copied conclusion: All parallel live controllers share the same low pivot P.
A new line starting from the old N=f(P); the new end controller is the previous one.
The image of a parallel controller has a pivot that is precisely f(P). Therefore, the next activity source area is replicated from the new segment.
Starting from the first line, the old lines that do not meet the new δ>=a condition are not included.

This argument proves that thelegacy/paper selected in this initialization are indeed the same; it does not generalize to
Any subsequent M trajectory. The Two Chain/Sat Quiet Theorem ensures that the second freeze scan is free of...
native record, so no effective marked completion occurs and the scan acts as the identity.

### The choice set of the second forest remains closed under successor factors.
----------------------------------
The original forest selection is composed of three types of sets in rounds:
  1. Initial continuous prefix;
  2. The complete package of activities includes continuous blocks after the last 'controller' is removed.
  3. Selected source rows are mapped to their images under a raw short copy.

The 1 class obviously maintains the cited factors and their successors. The 2 class includes the y<r<= packages at the end of the 1 marks within it.
Therefore, both y and y+1 are within this continuous block. For the 3 category, only the all-high marks from the fifth section need to be processed.
If carrier r is chosen, the induction is given to y, y+1 is chosen; and since P<=y<r<e, both are chosen.
The current actual continuous replication of the source area, and
  f(y+1)=f(y)+1.
Thus, the new factor and its physical successor are also selected. The retained lines remain unaffected.
Ultimately, only the 'work controller' is deleted. The successor of the 'proper factor' does not exceed the 'carrier' remains intact.
Therefore, this closure is maintained. The entire second forest does not require effective marking scanning to avoid additional seams.
The concept of "factors within the package" in the 2 category originally comes from the last two complete native families; subsequent ones
All live packages are the actual images of complete old packages, so this internal property is also preserved by forest induction.

The lemma 2 applies again, and the extraction yields a precise natural certificate for the original A[n]=R[k][n].
It possesses ordinary practical lines, Sat, proper, and accurate marks, as well as positive mark sources.
The final lines/endpoints of the main budget and shadow construction are maintained, hence there is a finite initialization given
The same Iter(j) and cap<kappa4 are also preserved.

[The three main papers give the natural inputs and their full derivation. This reading edition omits the older treatment with a preset input.]

### Access with the marked M, and calculate the total number of steps
-------------------------------
Starting from S, a legal paper short M full scan maintains natural certificates and Sat. This local...
The theorem allows for the subsequent appearance of multiple factors of marks and effective marked completions; it is not required that the entire trajectory remain
The special shape marked with direct/quiet in Section Five. The special shape is used only to demonstrate the entrance.
Choosing 'cut' when the domain copy check fails is a permitted safe prefix operation.
Domain failure includes p=0: There is no copyable row with index 0, and Python negative indices are not allowed.
Each scan only traverses the entry old line and a limited descending ancestor chain, so the single step itself is finitely definable.
Here, only the local closure of ordinary short copy/scan is called for, without the use of I2 or all finite endpoints.
Linedness. There are no subsequent steps allowing free choice of any E(k). The existing certificates for I3 are sufficient.

Let the current be cap=gamma_r, and the final owners' Laver quotient be represented as a, 1<=a<2^r. Take
  Φ=2^(r+1)-a.
A successful M operation maintains the cap, and the last owner changes from J to J(K), so a becomes a*_r b>a;
Scanning does not change the end owner or the global cap. Therefore, Φ is at least reduced by 1.
A single cut makes r'<r; there is no need to compare the old and new owners, because
  Φ_new<=2^(r'+1)-1<=2^r-1<2^r+1<=Φ_old.
In a finite table, the definition of a*b>a can be derived recursively from the definition of a, and it is not an additional grand number conjecture.

The first two lines are the four steps of the protection base formula.
../../output/iblp-030-laver-20261014/short-tail-cofinality.zh-CN.md §6
Individual Implementation:
  (01)(012) -> (01)(12) -> (01)(02) -> (01) -> empty.
The first two steps remain as unfinished owner applications, while the last two steps are cut. The empty potential is defined as 0.
Therefore, the same integer potential strictly decreases until it becomes empty, and the entire process is finite.
  T_paper(S)<=Φ(S)<2^(r0+1).
Initialize to gamma_r0<kappa4=gamma_(q(5)-1), therefore
  r0<q(5)-1, especially T_paper(S)<2^{q(5)}.
Each cut strictly reduces the subscript of the critical point, hence D_paper(S)<q(5).

### The exact boundaries proposed by Hardy most recently
-------------------------------
This paper indeed removes the barrier that requires one to forget the marking of S before accessing the counting.
However, it does not prove that fixing the degree of M dominates the original Hardy, nor does it compare S with R according to the order type.
Directly derive function inequalities.

It is reasonable to sacrifice some of the explicit fundamental column steps of R as the next comparative goal. For example, first
It is required that a definite original descendant U and y>=10^10 satisfy H_U(y)<=T_paper(S), or even stronger conditions.
H_U(y)<=#M_paper(S). The latter two are different; a large amount of cut cannot be directly calculated as a large amount of M.
It is necessary to provide a step-by-step simulation or quantitative description of the variable index calculation. It is not sufficient to only provide the first and second items.
Systems with large indicators, substantial remaining budgets, or systems with the same ordinal type for the original/short-tail scenarios.

The existing short/full fundamental sequence convergence with the same marking strategy can compensate for the finite input of the variable index Hardy's Hardy-Weier theorem.
Displacement, but not to turn the indicator that has always been fixed as 2 into an indicator that grows with the operation. This round does not...
This missing comparison is considered to be completed. This paper also does not advocate for the subsequent closure of legacy M to have been proven.

### This round of independent verification
-----------------
marked-entry-initializer.txt provides independent construction of entrances andall-high induction.
marked-entry-extraction.txt provides a more general form of factor successor closure extraction and explicit finiteness.
Transporter construction. The two authors cross-checked the initialization with this manuscript's §5--7.
The third auditor independently reviewed the budgets for the same two significant indicators, as well as the inability to
All owners of the extracted 'family' are still considered to have the same global constraint.

Main agent reruns marked-entry-audit-probe.py: There are 30 bounded small examples.
Peak fields of 260/3126, approximately 0.038 seconds. No mixed retention, factor successor omissions observed.
Non-direct trace or Sat failure; the entire literal output is the same as the original Python.
The small example only checks the implementation; the conclusions of k and n are given by the above induction. There are no huge arrays or declines.
There are no background processes remaining; it is notcommit/push.
