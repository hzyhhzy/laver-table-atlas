# Local linedness Budget algebra: Directly accessible E, as well as an extended successor type · [中文版](local-budget-algebra.txt)

*English reading edition, translated with machine assistance. The title links to the dated Chinese manuscript.*

> Collected reading edition. The three main papers state the results of this collection.
> This edition retains the local proofs, their hypotheses and any withdrawals. Progress reports describe the state of work at the time.
> The locations of omitted passages on preset inputs are recorded in SOURCE_MANIFEST.json.
> The main papers give the numerical derivations for the natural parameters produced by the proofs. This historical note carries no additional Lean certification.

2026-10-16. Subtask parameter_jump_audit. This manuscript only describes this new scratch file.
The conclusion is a paper lemma; it does not claim to complete the original IBLP030 version of the Hardy/FGH comparison.
All embeddings and witnesses in the entire text belong to the same Iter(j), and all called endpoints do not exceed one.
A pregiven cap Θ<κ4. The budget here refers to linedness, not the number of Ms or the number of column deletions.

### Exact interface and sources
------------------

Let L(α, β, γ; r) be assertions with actual witnesses: there exists
  β=μ0<μ1<...<μr=γ
And li:α -> μ(i-1) -> μi, and crit(li)=α.
It is not merely a numerical table recording the value of r; applied operations require actual witnesses (or proofs that can reconstruct them).

Existing dependencies:
1. Qi, Notes on Laver Tables, Definition 2.2, Lemmas 2.3--2.5, 
   Double block extraction of definitions 2.16--2.18 and theorems 2.25.
2. output/iblp-laver-bms-20261013/marked-BLP-quantitative-transfer.zh-CN.md
   A natural truncation certificate class C, witness replacement, arbitrary implementation of new block extraction.
3. Natural Marking Lemma Directory/
   The legal copyclosure of natural_trace_cutoff_semantics.md.
4. The ordinary scan closure of the entry sat_endpoint_packet_theorem.md.

The original IBLP has repeatedly undergone full tail copying and complete scanning, but this does not automatically result in obtaining a unified cap certificate.
The relevant gaps for scratch/iblp030-8h-20261015/FINAL-REPORT.zh-CN.txt remain valid.

### Basic update rules for certificate tables
--------------------

The following mathematical research paper is constructed to provide practical evidence, without treating satisfied numerical inequalities as implementations.

(A) renamed/retained.)
After inserting a new column or extracting an old column, if the three actual ordinals and each witness remain unchanged, only the column names are changed.
The certificate remains intact. The same applies to the removal of irrelevant lines. It is necessary to verify when extracting a marked BLS.
All rows are edge-aligned, with accurate traces and natural truncations; numerical tables cannot be extracted alone.

(B) is applied for transport.)
Given K, L(α, β, γ; r) becomes L(Kα, Kβ, Kγ; r), witnessed as K(li).
Only legal calls under the fixed cap are considered when Kγ≤Θ has been proven.
The coordinates within the source region are named using the actual replication mapping; coordinates across regions must calculate the true K image.
Do not assume that the image is similar based on the similarity of integer subscripts.

Continuation of (C) with the same root.
L(α,β,γ;r) and L(α,γ,δ;s) are concatenated to form L(α,β,δ;r+s).
The first chain is retained as a prefix.

D) reduction in budget/compression.
When r≥s≥1, it is possible to compress the r-lined certificate into the same endpoint as s-lined. A single step r→r-1:
Translate the following mathematical research manuscript as follows: l1,...,l(r-2), and replace the last two with lr(lr)(l(r-1)).
This is an application, not a regular composition. It can be repeated iteratively.
The compression does not replace the third endpoint γ with any smaller γ'.

(E) has a certified end extension.
If there are K, crit(K)=γ, and Kγ=δ, then replace the last lr of the r chain with
K(lr), remain unchanged, resulting in L(α,β,δ;r). The actual K must be provided.
It is not allowed to assume that there is a suitable K between any points simply because of γ<δ.

### Prefix retained exponential multiplication: new convenient form
----------------------------------

Lemma 3.1. Given L(α, β, γ; m) forms a chain A, and L(β, γ, δ; r) forms a chain B.
It is possible to construct L(α,β,δ;m*2^r), and retain the sequence of A as the previous m items.

Proof. Let the endpoints of B be γ=ν0<...<νr=δ, and the witnesses be...
  Gi:β -> ν(i-1) -> νi.
The initial C0=A. The constructed Ci-1 is the root of α, a chain from β to ν(i-1). Because
crit(Gi)=β>α, Gi is fixed at α; Gi(Ci-1) is a root of α, and from ν(i-1) to νi
A chain of equal length. Let
  Ci = Ci-1 follows from Gi(Ci-1).
Each round doubles accurately, and the original chain remains word-for-word prefix-based. All new endpoints are ≤δ. Proof complete.

This proof is consistent with Qi's m*2^r lemma, but retains the prefix explicitly, making it suitable for extraction.
New local budgeting. It does not involve any steps of "iterating M until the shape is correct."

Corollary 3.2 (rearrange the segments and enhance). If L(α,β,γ;m), and there is
  k:α -> β -> γ -> δ，
Then it can be directly constructed
  L(α,γ,δ; R(m)),       R(m)=m*(2^m-1).               (1)

Proof. k(A) proves L(β, γ, δ; m). Using the lemma 3.1, we obtain the transition from β to δ.
m*2^m pieces, α strands of chain. The previous m items are exactly the original A, and the end point is γ. After removing the prefix,
The remaining m*(2^m-1) items constitute the required local certificate. All endpoints are ≤δ. Proof completed.

Therefore, the four points k and m-line correspond to the well-known L(α,β,δ;m*2^m). However, (1)
It is another type of endpoint arrangement, and the two should not be mixed together.R(1)=1,R(m)≥m,m≥2 are strictly so.

### Any valid anchor point has a finite E
-----------------------

The pattern P has n rows, with the last row being a complete column of s, with a step size of ℓ, and the last owner is J. Take
  c=s[0], p=s[-ℓ-2], e=s[-ℓ-1], a=s[ℓ].
The negative subscript here is used for the complete row, rather than omitting the core with an implied endpoint.
Therefore, Jθc=θa, Jθp=θn, Jθe=θ(n+1).

Assume c<p<e, 2≤a≤n-1, and carry L(θc, θp, θe; r).
Apply this local chain using J to obtain the endpoints.
  θn=μ0<μ1<...<μr=θ(n+1)
And the auxiliary witnesses Ki=J(li), crit(Ki)=θa, Ki:θa->μ(i-1)->μi.

Starting from cut(P), in the i round, use Ki as the auxiliary three-point row, shortly copy the current a,..., until the last row.
This is exactly the same as the original E single-round operation, with the only difference being that the source of auxiliary witnesses is no longer limited to the global 012.
Normal replication is legal; the marks are copied using the existing natural truncation to enclose the closure, rather than fixing the boundary with the old θ(y+1).

For t≤r, the number of rows is exactly
  n_t = 2^t*(n-a)+(a-1).                               (2)
Because n_0=n-1, n_(t+1)=2*n_t-a+1.

When t<r, the final cardinality is μt< the original cap; when t=r, the final cardinality is equal to the original cap. For positive round numbers, the final owner
For J(li)(K), in a bounded application, it is related by J→J(li)→J(li)(K)
Strictly decreasing. All critical points are less than the original cap, and they remain within the same Iter(j).

This is a jump that can be explicitly given before invocation of t; it is not a macro equation of the original short M trajectory.
It is also not the original IBLP full tail expansion [2^t], which is a list of equations.

### The standard root I directly leads to a precise local growth of E4
----------------------------------

The standard complete row is I.
  012:1; 0123:1; 01234:2; 012345:2; 23456:2，
In the 4 row, there is a direct mark 3. For natural standard implementations, the first two rows can have the same four-point owner k.
In the third and fourth lines, there is the same owner H, while the last line has another owner J.
In the third line, H maps (θ0,θ1,θ2) to (θ2,θ3,θ4).
Therefore, global m-lined certificates generate L(θ2, θ3, θ4; m).
The last line contains (c,p,e,a)=(2,3,4,4)), so in Section 4, it is allowed to directly use E4(r), and any r≤m.

E4(r) is retained for the rows before 3; there are exactly 2^r structural copies of the 4 row after that. Denote the continuous endpoints as
  The current cap is ζ0=θ4<ζ1<...<ζ(2^r)=.
Each copy's owner Hi satisfies
  Hi(θ0,θ1,θ2,θ3)=(θ2,θ3,ζ(i-1),ζi).
The complete list is (0,1,2,3, last column, last column), with a step size of 2.

Apply Hi to the first two lines of the four-point owner k, resulting in
  Hi(k):θ2 -> θ3 -> ζ(i-1) -> ζi.
Let f(x)=x*2^x be defined. If a local certificate up to ζ(i-1) is Mi-1, then the four-point lemma gives
  Mi=f(Mi-1)，M0=m.
Therefore, the entire finite jump direct proof
  L(θ2,θ3,cap; f^[2^r\](m)).                            (3)

Count includes the first row with cut(I): 4 At r=0, it is one piece. Applied f once;
When r=1, there are two pieces, applied f twice. Therefore, the actual root starts with m=1, r=1 to f(f(1))=8.
Not f(1)=2. This small value certainly is not a numerical improvement on the existing q(5) lower bound.

In the formula (3), the position of each budget update is specified by a clear copy block order, with no implicit assumptions.
The question of how many times it takes to return to the target shape with M. This chain length can be symbolically represented, without the need for actual...
Enumerate the f^[2^r\](m) witnesses or the 2^r row blocks.

### The next step does not need to wait for M: expanding the successor type 0123nn+1
----------------------------------------

The last line of E4(r) is not the successor type of the original paper; it is
  (0,1,2,3,d,d+1):2.                                 (4)
The next auxiliary E requires a source triple of (θ0,θ2,θ3), not (θ2,θ3,cap)).
Therefore, the huge numbers of (3) cannot be written down for free as the budget for the next round of the source.

But this does not mean that it is necessary to repeatedly M. The 2th row of any ordinary BLS provides four owners.
  k:θ0 -> θ1 -> θ2 -> θ3.
For its global m-lined certificate, use the inference 3.2 to directly obtain it.
  L(θ0,θ2,θ3; R(m)).
The last line (4) maps this triple to (θ2,θd,θ(d+1))). So it can be done directly.
  E2(R(m))，R(m)=m*(2^m-1).                            (5)
The calling parameters are given in a closed form, eliminating the need to find the canonical form for the unknown M once or more times.

The geometry of E2 is such that every round copies all patterns except the first row, resulting in both a=2 double-block extraction.
Applicable as it is. Let q=cut(P), g(x) be any established ones in the certificate class of q.
Global linedness: A lower bound function that holds for any implementation on each call. Thus, the same
Double-block inductive proof, which can be obtained on the pattern of (4)
  L(θ0,θ1,cap; g^[2^R(m)\](m)).                        (6)
Note that the initial values within the inner layer remain the original global m; the parameter R(m) controls the number of doubling rounds, which should not be confused with these two parameters.

According to Theorem Qi, the proof of 2.25 can be achieved by adding a subsequent branch with an extended numerical recursion for (4):
  f_new(P,m) = (x -> f_new(cut(P),x))^[2^R(m)\](m).
The rest of the branches remain unchanged. The definitiveness of each recursive call is defined by the same BLS well-founded induction.
Proof. The certificates for the new branch, the descent, and any implementation extraction have been given above.
This is another valid lower bound recursion; it is not proven to dominate the original f_star for every input value.
There is also no proof that the entire original IBLP030 has its index-changing Hardy recursion embedded within it.

The importance of this step is that it provides a direct and explicit next jump after E4, not
Translate the old fixed M trajectory into a named "until encountering a certain shape" operation.

### Fix the cap and the remaining interface of the original IBLP030
---------------------------------

1. Local chain growth usually involves moving the third endpoint from ζi to ζ(i+1). It is not possible to revert a long budget back to its original state.
   The smaller original endpoints cannot be replaced simply due to sufficient numerical values. The next triple required by the original IBLP needs to be considered.
   Section 6 addressed a specific next-step type, but did not address any arbitrary row types.

2. For the complete original R=I[0][3][0], a local macro with a clear upper bound at each step or beforehand is required.
   Update the certificates of all queried source triples by fully expanding the actual tail, completing it, and synchronizing the updates.
   Currently, there is no inductive invariant for the property of 'all ports being covered'.

3. Even given a certain implementation of the original R[n], it is necessary to maintain the same Iter(j) and the same Θ<κ4.
   Please provide a payable n or n+1 before execution. The fact that it can be moved to a larger cap is not sufficient to know anything else.

4. The multiple full tail copies of R will consume the marked completion of a long trace; the ordinary single M/E
   Natural truncation closures cannot replace the incision preservation and multi-block alignment theorem of full raw/scan.

[The three main papers give the natural inputs and their full derivation. This reading edition omits the older treatment with a preset input.]

### State
--------

Proven new interfaces: preservation of multiplication prefixes, enhanced head replacement (1), any given local certificates
Limited E, standard I (3), immediately followed by the available extended successor branch (5)--(6)).

Unproven: These jumps form a closed simulation for each index-changing step of the original R; especially not
It is claimed that a lower bound for Hardy/FGH has been obtained from the original IBLP030.

Resources: Mainly consist of symbol derivations. Section nine adds a fixed small grammar verification involving six rounds of E;
No long-term downswings or searches, no long-term processes, no modification of old documents.

### The original R refers to a more specific condition transition chain: 1, 1, 4, f^[15\](4)
---------------------------------------------------

The conditions for this section are: the original R=I[0][3][0] has been given, along with its counterparts Iter(j), cap<κ4
A naturally marked BLS implementation, with the first three points being 1-lined. No additional proof is provided for the construction of this entry.
The complete core/step structure is as follows:
  012:1; 0123:1; 01234:2; 2345:1; 23456:2; 4567:1.
All marks continue to be transported according to the actual valid E; the following only describes the required local certificate using row boundaries.

First, give two direct jumps to the general m. In the 3 line, H sends the global 012 to the m-line.
234 to m-line; in the 5th row, J, then send it to 456's m-line. Last line: 4567:1
The E cutpoint is a=s[ℓ]=5. Therefore, it can be E5(m), output the d=4+2^m line, with the last line being
  (2,3,4,d,d+1):2.
Its source is 234, so it can be immediately E4(m). The second output is n=3+2^(2m) line.
The last line is:
  (2,3,a',n,n+1):2，    a'=4+2^(2m-1).                 (7)
Derivation: The tail of E5 consists of 2^m copies of the 5th row; the last round of replication mapping by E4 results in 4
Sent to 'the number of lines before this round +1', that is, the above a'. The last two sources are always 2, 3.

Here, the 5 after E5 is the first image of the original owner, not the starting point of the tail section of short-forest.
The end core of the original R is 456, ℓ=1, core[-ℓ]=6; this 6 cannot replace the E tangent point 5.

Now fix m=1. First, create E5(1), E4(1), to obtain the 7 row, whose last line is precisely
  (2,3,6,7,8):2，
The row before it is a four-row row.
  (2,3,6,7):1.                                         (8)
The previous 5 lines and their cardinality remain unchanged. Let the owner mentioned in the 4 line be denoted as K, so
  K:θ2 -> θ3 -> θ4 -> θ5.
Let A be the L(θ2,θ3,θ4;1) obtained from the 3 row transportation. There are:
  J(A) is given to L(θ4, θ5, θ6; 1);
  K(K) is given to L(θ3, θ4, θ5; 1);
  The two lemmas 3.1 are given first to L(θ3, θ4, θ6; 2).
  Against L(θ2, θ3, θ6; 4).                                 (9)
These certificates are located in the current 6 column and below. They are actual old prefix certificates and not available for free reset.

From (8)--(9), it is possible to directly become E6(4). The number of rows changes.
  2^4*(7-6)+(6-1)=21.
The tail is composed of (8) four copies of 16, with each owner having one.
  Ki:θ2 -> θ3 -> ζ(i-1) -> ζi，
Where ζ0 is the retained column of 6, and ζ16 is the cap. The initial budget is 4, so the ith...
The local budget for block termination is at least f^[i\](4), f(x)=x*2^x.

The last line is (2,3,21,22):1); it requires a source of (2,3,21). The third point is...
It is ζ15, not ζ16. Therefore, there is a precise and usable certificate before executing the next E.
  L(θ2,θ3,θ21; N)，    N=f^[15\](4).                    (10)
The first image on the last line is 3, so it can be directly E3(N). The closed form of its row is
  2^N*(21-3)+(3-1)=18*2^N+2.

Thus, a budget chain without any M searches is obtained:
  R --E5(1)--> --E4(1)--> --E6(4)--> --E3(f^[15\](4))-->.
The actual local certificate for the next parameter is provided before each invocation; there is no "repetition until M"
The unknown degree of the "limit type". The precise definition of N only includes 15 iterations and f iterations, which is not a
The unknown count defined by the descent stop condition. All endpoints of the certificates do not exceed the cap of the original R.

This chain is a semantic jump to generalized E, not an assertion of the original R[1][1][4][N].
It does not equal the indexed Hardy orbits of the original R. It proves a truly reusable growth.
Budget mechanism; closing this mechanism to each expansion step of the original R remains a gap in section seven.

Fixed grammar verification (does not undertake embedding semantic proof): Import the original iblp.py, actually execute [0][3][0]
Obtain R; re-utilize the audited marked_blp_em_probe.py correct paper short_copy.
Only proceed to the 1+1+4=6 round of assistance E. Check for ordinary issues at each step (only internal adjacency is allowed)
Report, not actually presented), number of lines ≤25, number of fields ≤250, upper limit of time for 8 seconds. Normal exit throughout the process.
The calculation part takes approximately 0.0005 seconds; no child processes remain. The last E3(N) did not actually execute.

Result PASS; all four states starting from the original R are marked as empty. Count and last line:
  Original R: 6 row, end core 456, step 1;
  E5(1): Row 6, end core 2346, step 2;
  E4(1): The rows from 7, the last two rows have a core of 236:1, 2367:2;
  E6(4): The 21 line, and the i=6,...,21 lines are all core (2,3,i), step 1).
All assertions pass. This minor verification only confirms the formulas and subscripts, and does not prove the semantics on the infinite domain.

This section does not claim to improve the existing numerical lower bounds of BMS/Hardy-C7; the current contribution is to clearly satisfy them.
The actual local jump where there is no unknown length M cycle between budget updates.
