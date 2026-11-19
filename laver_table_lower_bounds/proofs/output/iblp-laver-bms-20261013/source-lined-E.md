# Control the number of copies with rows as the source triplet. · [中文版](source-lined-E.zh-CN.md)

*English reading edition, translated with machine assistance. The title links to the dated Chinese manuscript.*

> Collected reading edition. The three main papers state the results of this collection.
> This edition retains the local proofs, their hypotheses and any withdrawals. Progress reports describe the state of work at the time.
> The locations of omitted passages on preset inputs are recorded in SOURCE_MANIFEST.json.
> The main papers give the numerical derivations for the natural parameters produced by the proofs. This historical note carries no additional Lean certification.

2026-10-14. The linedness obtained during the completion phase does not necessarily fall within the first three global points. Below, the auxiliary E operation of the ordinary BLP is generalized into a local interface: as long as the three images of the last three points of the active row have finite linedness, corresponding auxiliary copies can be performed within the same endpoint. This allows for a quantitative lower bound for the prefix, which is not limited to the parameters initially carried by the state.

This is a finite BLS certificate transformation. It is not the original IBLP fundamental sequence with an odd number of elements, and it does not claim to have a BMS with a higher number of rows. All embeddings belong to the same I3-generating algebra Iter(j). The certificate class and natural marked semantics follow the [Finite-parameter quantitative bridge](<marked-BLP-quantitative-transfer.md>) paradigm.

## Source Triple Lemma

Let P have n≥3 rows, with the last row's owner being J, and the final base number being Θ=θ_(n+1). Assume that the known sides of the last row include

$$
J(\theta_u)=\theta_a,\qquad
J(\theta_v)=\theta_n,\qquad
J(\theta_w)=\Theta,
\qquad u<v<w,\quad 1\le a<n.
\tag{1}
$$

Another witness within the same Iter(j)

$$
\beta_0=\theta_v<\beta_1<\cdots<\beta_r=\theta_w,\qquad
l_i:\theta_u\longmapsto\beta_{i-1}\longmapsto\beta_i.
\tag{2}
$$

Therefore, (θ_u,θ_v,θ_w) are r-lined. Here, r is a clearly finite integer.

Starting from the prefix that removes the p, fix the anchor point a, and define

$$
E_a^0(p)=p.\mathrm{del}.
$$

If there is a line with N in the current pattern, add an unmarked auxiliary complete line.

$$
(a,N+1,N+2),\qquad L=1,
$$

Then, perform a single ordinary short replication to obtain the next round. The auxiliary row is not a complete copy of the original last row; each round replicates the current a,…,N row. For each k≤r, the E_a^k(p) has a complete natural truncation certificate whose end does not exceed Θ; at k=r, the end is exactly Θ, and this certificate is strictly less than P.

### Row embedding and endpoints

Put

$$
H_i=J(l_i),\qquad \mu_i=J(\beta_i).
$$

Directly derived from the application identity

$$
\operatorname{crit}(H_i)=\theta_a,\qquad
H_i(\theta_a)=\mu_{i-1},\qquad
H_i(\mu_{i-1})=\mu_i.
\tag{3}
$$

Before the first round, the end of the prefix with the μ_0=θ_n symbol is retained. If the end of the i−1 round is μ_(i−1), then the formula (3) exactly implements the next auxiliary three-point row. Its short copy inserts the points within the source interval between μ_(i−1) and μ_i. The old prefix is retained, and the owner K of the copied row is changed to H_i(K). By induction, the end becomes μ_i≤μ_r=Θ in each round.

The source replication threshold is a, and it does not have to be equal to the critical point number J. What matters is that the auxiliary embedding H_i occurs at the critical point θ_a.

### Markings and Saturation

The auxiliary copied address mapping is:

$$
\psi(x)=
\begin{cases}
x,&x<a,\\
x+N+1-a,&x\ge a.
\end{cases}
\tag{4}
$$

It is defined on all old addresses, and the row positions are retained. For each current row where v, the copied or retained parent query satisfies B'(ψ(v))=ψ(B(v)); the same applies to p and e. Therefore, the B(e)≤p of Sat is maintained row by row. The positive marked source is also maintained by ψ(δ)≥δ≥1.

The auxiliary lines have no marks, and their replication threshold equals their critical point. Therefore, the marking only takes the full-factor branch or the low branch, without the need for a new high branch condition. In the case of full factors, the entire natural world takes the H_i- image; the low branch uses the natural world that has not replicated the tail word, and this does not exceed θ_a. These are exactly the two branches of [Natural Truncated Copy Lemma](<../../natural-mark-lemmas/natural_trace_cutoff_semantics.en.md>) in the 2 section, including the case where the tail bound equals θ_a.

The first two lines, as well as θ_0, θ_1, and θ_2, remain unchanged with the old prefix. The original global parameter m remains unchanged as well. Here, r represents the number of permissible operations in this process, and it does not mean that the original m will be changed to r without conditions.

### Decrease

When k<r, μ_k<Θ, directly reduce the end. The end of the auxiliary system in the last round is Θ, and the end owner is J(l_r), which is an application starting from J; the end owner after short replication is

$$
\bigl(J(l_r)\bigr)(K),
\tag{5}
$$

Among them, K is the owner of the last copied row. The critical points at both applications are lower than the common end Θ, hence the final certificate is also strictly lower than P. All right factors are within the original Iter(j).

Therefore, the source triple lemma only requires ordinary BLS replication and natural truncation closures, without the need to strengthen the I3 notation. It extends the auxiliary replication permission used in the [Qi is defined as 2.16—2.18](https://arxiv.org/html/2501.06733v5) case, and it is not claimed that all extensions have been proven in this paper.

## Two types of permissions that can be obtained directly from the current mode

Restore the complete last line s, set the length as t, and the step size as L. If t≥L+3, the original images of the last three points in the zero-based index are

$$
(u,v,w)=(s_{t-L-3},s_{t-L-2},s_{t-L-1}),
\qquad a=s_{t-3}.
\tag{6}
$$

This is simply reading out the three existing sides of the original line, without adding any new sides.

### Category 1: Global prefix taken linedness

If (u,v,w)=(0,1,c):

- When c=2, the original certificate is directly given to m-lined.
- When c≥3, limit to the rows c−1, and its end is θ_c.
[Marked Completion Theorem](<marked-BLP-quantitative-transfer.md>) provided

$$
r=f_\star(p|(c-1),m).
\tag{7}
$$

Thus, the quantitative output of the entire prefix can be used for this auxiliary replication. This linedness is provided by the smaller end prefixes, and does not depend on the current E output, hence there is no circular reasoning. If it has been decided to permanently delete the marks, the same conclusion can be applied using the ordinary f.

The limit type in the original paper only uses the special case of c=2. The inputs for c>2 must also satisfy the original Sat condition; they cannot simply change the numbers at the end of the line. For example, the Sat requirements for (0,1,c,a,n,n+1),L=3) are B(c)≤1. Any handwritten c does not automatically make it valid.

For each defined f_star(p,m), it is at least as large as m: By induction over finite evaluation trees, the zero branch increases the parameter, while the cut, limit, and transient parameters are retained. The successor iteration does not reduce the parameter for sub-calls. Therefore, when testing the small index k≤m, there is no need to actually compute the huge values of (7).

### Type II Transport First Triples

If (u,v,w)=(1,2,c),c≥3), then at least we can take r=m.

Take the second row, `owner G`, whose critical sequence begins at `θ_0→θ_1→θ_2→θ_3`. Transport the original `m-lined` witness with `G`, resulting in the `θ_1,θ_2,θ_3)` witness under `m-lined`. At `c=3`, it is sufficient; at `c>3`, name the point transport lemma to `H`, whose critical point is `θ_3` and `H(θ_3)=θ_c`. Transport the newly obtained witness with `H`, retaining the first two points, to obtain the desired triple.

More generally, it is known that the linedness of a given prefix can be transported through a known owner. It is necessary to have both the actual point images of the first two points and the last point, and one cannot simply replace them based on the number of points.

## A specific entry of the fixed pattern after magnification

[Prefix relocation certificate](<marked-prefix-rebase.md>) lies within the same upper bound as Θ_0<κ_4, and has already achieved the fixed pattern of 32 in the Q row. Parameters

$$
B=g^{258}(1),\qquad g(x)=x2^x.
$$

The core in the 30–32 row of Q is

$$
\begin{array}{c|c|c}
r&A_r&L_r\\ \hline
30&(0,1,2,3,30)&2\\
31&(0,1,2,30,31)&3\\
32&(0,1,2,3,30,31,32)&4.
\end{array}
$$

In the 30 row, there is a mark 3; in the 32 row, there is a mark 31. The source triplet in the Q last row is (1,2,3)), and the last three targets are (31,32,33)). According to the second type of permission, the E_31^B(Q) can be legally executed, while the Θ_0 is retained.

The literal result can be written directly: the first 30 rows remain unchanged, followed by 2^B rows.

$$
A_r=(0,1,2,30,r),\qquad L_r=3,\qquad
31\le r\le30+2^B,
\tag{8}
$$

These new lines have no marks. Because each round copies the entire block after the current anchor 31, the block size is doubled, while 0, 1, 2, and 30 remain fixed. Therefore, (8) is derived by finite induction from B. There is no actual calculation for B, nor is an array containing the lines with 2^B established.

The formula (8) provides a huge number of clear blocks under the same low endpoint; however, the step size of the new rows is still only 3. Therefore, this entry itself does not convert B or 2^B into BMS row numbers. It also does not prove that the ordinal of the current initial pattern strictly exceeds the BMS limit.

## The structure conclusion for the two-stage route is still pending.

Deleting all the marks will always preserve ordinary row embeddings, finite parameters, and the same endpoint. If we also want to stop native completion, we need to extract a subsystem that closes under subsequent expansions. Currently, such a subsystem is [Balanced Port BMS](<ribbon-initialization.md>).

To access it from a marked phase with parameters, both the parameters and the marked information need to be provided simultaneously.

$$
U_0<\cdots<U_h<V_0<\cdots<V_{h+1},
$$

And compatible owners

$$
\operatorname{crit}(K_k)=U_0,\quad
K_k(U_i)=V_i\ (i\le k),\quad
K_k(V_0)=V_{k+1}.
$$

It is also necessary to have low-end connectors, so that the number of descent steps of the three columns of seeds can be directly obtained. A unified construction that allows h to grow with the available parameters would conform to the direction of "ten layers are just the baseline"; this unified construction has not yet been proven. Simply recording the number of rows in a huge block as h does not meet these conditions.

## Bounded verification

source_lined_E_probe.py (Historical reference: `source_lined_E_probe.py`) Checks finite syntax: rows after each auxiliary replication, the first two rows, Sat, positive marked source, accurate trace, and precise number of rows.

$$
|E_a^k(p)|=a-1+2^k(n-a).
$$

Starting from the syntax of the aforementioned Q, using cut, M_star, and the smaller indicators 1 and 2 from the two permitted categories, a bounded operation was carried out to inspect 2,400 states, 4,856 structural audits, and 1,912 auxiliary copies. This included an eight-step item-by-item inspection of the equation (8) at k=0,…,7. 297 resource stops were counted as unknown and not considered a valid conclusion. No reachable examples of the first type of c>2 were found within this range; the general lemma does not depend on the success of this search.

Additionally, only the explicitly defined states with 913 were examined in each row, and no new closed higher-order groups were found. This does not exhaust all possible points of similarity that can be derived from real embeddings, combinations, or markings, and therefore does not constitute a conclusion of impossibility.

The resource limit is 15 seconds, 220 rows per state, 15,000 entries per state, and 2,400 states in total. The actual exit takes approximately 2.2 seconds, with no background searching. The program does not verify the existence of embeddings. Its semantics is permitted to be given by the above lemma, and these tests are not considered as a proof of the lower bound for the rapid growth of BMS[10].
