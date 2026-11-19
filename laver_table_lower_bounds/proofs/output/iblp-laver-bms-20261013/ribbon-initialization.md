# BMS with encoded small endpoint initialization conditions · [中文版](ribbon-initialization.zh-CN.md)

*English reading edition, translated with machine assistance. The title links to the dated Chinese manuscript.*

> Collected reading edition. The three main papers state the results of this collection.
> This edition retains the local proofs, their hypotheses and any withdrawals. Progress reports describe the state of work at the time.
> The locations of omitted passages on preset inputs are recorded in SOURCE_MANIFEST.json.
> The main papers give the numerical derivations for the natural parameters produced by the proofs. This historical note carries no additional Lean certification.

The goal remains to place the BMS[10] level below a clear small cycle threshold. This paper carries out a complete BLS initialization of the previous 38, weakening it into a compatible mapping group and its endpoints' upper bounds. At the end of the paper, a finite-term construction of an eleven-layer group with a fixed source point γ₀,…,γ₁₁ is presented; it has not yet been proven that its end is below a clear small K for the j(γₖ₋₁). This remains a substantial gap in obtaining the cycle lower bound, and the comparison with FGH is still incomplete.

The exact syntax for the notation M is replicated, as well as the row deletion count, following the pattern [Proof of balanced ported proof](<balanced-ribbon-bridge.md>). The fixed I3 is embedded in j; all embeddings belong to the same Iter(j), and all named points belong to its set of critical points.

## Zero ports do not require embedding witness.

The original code writes each zero port as a three-point row (0,i,i+1)), and requires it to also have a normal BLS row embedding. For the current M/del descent, this requirement is not utilized.

We can use the weaker term "with implementation". Fix the height h, and denote it as w=h+1. For a parent table with a column of m, select strictly increasing critical points.

$$
\alpha_0<\alpha_1<\cdots<\alpha_{mw}.
$$

In the jth column, we use the points αⱼw,…,αⱼw₊ₕ, and its right endpoints are α₍ⱼ₊₁₎w. For the kth positive port of this column, 1≤k≤h, assume its parent column is c. It is only required to exist an embedding Jⱼₖ, such that

$$
\operatorname{crit}(J_{j,k})=\alpha_{cw},\qquad
J_{j,k}(\alpha_{cw+t})=\alpha_{jw+t}\quad(0\le t\le k),
\tag{1}
$$

$$
J_{j,k}(\alpha_{jw})=\alpha_{jw+k+1}.
\tag{2}
$$

The anchor port k=0 does not have any embedding requirements with respect to the zero coordinates. The two fixed lines in the original syntax, along with the labels 0, 1, and 2, are also only retained for syntactic protection, without being given ordinal meanings. The label α₀ corresponds to the syntactic label 3. All labels that are actually used as critical points in the main lines are at least of the 3 level.

This is not a claim that a general BLS has been constructed. It is a weaker implementation defined for this unmarked subsystem, which must be independently checked for maintainability. It cannot be directly applied to the quantitative theorems of the general BLS.

### Step preservation

**Lemma.** If P has a belt implementation with the end being αₘw, Then, a fixed number of [2] expansions with endlessly increasing bands are implemented. The required form operations are still the previous ordinary M and row deletion. Do not change the basic column rules of the parent table.

In the case of zero-end columns, only the last w endpoints need to be deleted.

When the last column is not zero, let the number of the last column be x, the active port be k, and the parent column be c. First, delete h−k zero tail ports. From (1)–(2), the active embedding J satisfies

$$
J(\alpha_{cw+k})=\alpha_{xw+k},\qquad
J(\alpha_{xw})=\alpha_{xw+k+1}.
\tag{3}
$$

Therefore, for each cw+k<t<xw, the critical point J(αₜ is strictly located between the two endpoints at the current end. Inserting these points in the order of input precisely yields the points introduced by the ordinary Copied. J fixes each point before the critical point in the source band, and the image on the k ports before the source band is specified by (1); thus, the complete address transport is consistent with the previous syntactic identity.

If the copied original line is achieved by K, then the copy is achieved by J(K). Identity

$$
J(K)(J(\xi))=J(K(\xi))
\tag{4}
$$

Ensure that it satisfies the required row relationships. Copies of the zero row remain zero rows, and there is no need to construct a K out of nothing. The pure grammatical proof for anchor point blocking completion remains unchanged, hence M=Copied.

All new points are embeddings of existing critical points within Iter(j), and they still belong to the same set of critical points. The inserted points are strictly located between adjacent old endpoints, do not coincide with the retained points, and do not increase the endpoints. This provides a realizability of preservation.

### Directly controlling cycle thresholds

When the fixed height h≥3 is reached, [Previous finite counts](<balanced-ribbon-bridge.md>) is given.

$$
D_2(P)<\delta,
$$

Here, δ represents the number of endpoints actually deleted during the aforementioned process. This count depends solely on the syntax and has nothing to do with whether there are any embedding witnesses in the zero line.

Every time the subscript of the terminal critical point is strictly reduced, M remains unchanged. Therefore, if the initial terminal is γᵣ, the initial α₀ becomes γᵣ₀, resulting in δ≤r−r₀. Thus

$$
\boxed{\alpha_{mw}\le j(\gamma_{K-1})
\quad\Longrightarrow\quad D_2(P)<q(K).}
\tag{5}
$$

This indicates that the zero-row witness in the original complete BLS is not a necessary condition for the initial linedness. It is known that the well-orderliness of the BMS ensures a fixed termination of the descent; the number of expressions of the form (5) is determined by the aforementioned finite counting.

## A set of mappings automatically generates two high-level sequences.

A compatible family of mappings with height h is defined as a strictly increasing critical point.

$$
U_0<\cdots<U_h<V_0<\cdots<V_{h+1},
$$

And the embedding K₁,…,Kₕ, such that for each 1≤k≤h:

$$
\operatorname{crit}(K_k)=U_0,\qquad
K_k(U_i)=V_i\ (0\le i\le k),\qquad
K_k(V_0)=V_{k+1}.
\tag{6}
$$

These requirements include common inputs and common outputs, which are stronger than simply knowing that there are many embeddings that send U₀ to V₀. They are also stronger than having only one very long row.

Let J=Kₕ, Wᵢ=J(Vᵢ), 0≤i≤h+1. Then

$$
W_0=V_{h+1},\qquad
U_0<\cdots<U_h<V_0<\cdots<V_h<W_0<\cdots<W_{h+1}.
$$

Now, interpret the three columns (0ʰ)(1ʰ)(2ʰ) as the U band, the V band, and the W band, respectively.

- The zero column U does not require any row embeddings.
- The first positive column uses Kₖ. The formula (6) is exactly (1)–(2).
- The second positive column uses J(Kₖ). From (4), it sends Vᵢ=J(Uᵢ to Wᵢ, and sends W₀=J(V₀) to Wₖ₊₁.

Therefore, we obtain a realization of Sₕ=(0ʰ)(1ʰ)(2ʰ), with the end being

$$
W_{h+1}=J(V_{h+1})=J^{\circ3}(U_0).
\tag{7}
$$

This uses only a set of compatible mappings. The second set is not a separate guess, but is generated uniformly by applied operations.

### The specific sufficient condition that needs to be overcome

Take h=11. As long as a eleven-layer mapping set that satisfies (6) is constructed within a fixed Iter(j), and for some specific small K it is proven

$$
K_{11}^{\circ3}(U_0)\le j(\gamma_{K-1}),
\tag{8}
$$

It can be strictly deduced

$$
\boxed{q(K)>D_2\bigl((0^{11})(1^{11})(2^{11})\bigr),}
$$

The starting condition is strictly greater than BMS[10]. What follows is a sufficient condition. At the end of the text, a set with a height of 11 is constructed, but the formula (8) for a clearly smaller K has not yet been proven; these two steps should not be confused. It is also incorrect to assume that the right-hand side has already exceeded the specified FGH value just because of the order of the starting condition.

## It is known that bounded sets of low endpoint materials

The notation [Qi, Chapter 3 of the fifth edition of the paper](https://arxiv.org/html/2501.06733v5) is used in this research manuscript. There are existing implementations where the end point of p_init is below κ₄=j(γ₄).

The bounded grammar check (historical reference: `small_cap_seed_probe.py`) revealed that p_init has a positive critical step size of 12, which has been observed 18 times M. The step size of 128 occurred 232 times and M times. They mainly come from the completion of the same embedding, and it cannot be concluded that there exists a compatible mapping set of corresponding heights.

The embedding identity check (historical reference: `owner_history_probe.py`) retains the 260 times M historical and actually identical row embeddings, as well as known point images. The initial additional relation K(θ₄)=θ₆ (K=j₍₁₁₎) comes from the same section's Dougherty lemma; the application expressions of j′ are also retained, not just their rows.

In the finite closure of at most 750,000 candidate application pairs, 4,063 witness with known point images are obtained, and 57,539 point image equations are recorded. The highest compatible group height found in the recorded equations is 2; after the third critical image with the highest embedding is also within the recorded range, the current height of 1 has been found.

Examples of heights 1 are precisely K=j₍₁₁₎:

$$
(U_0,U_1)=(\kappa_0,\kappa_1),\qquad
(V_0,V_1,V_2)=(\kappa_2,\kappa_3,\kappa_2^7),
$$

$$
K(V_2)=\kappa_3^{10}<\kappa_4.
$$

This is a lower-level proof for the sufficient condition of a compatible group, not the required eleven-layer result. The closure only uses known point images and does not automatically introduce intermediate critical points that have not yet been named; no proof of non-existence for higher groups has been found.

Each procedure has a limit on time, number of steps, and the maximum number of storage entries. All runs exit within a few seconds. The construction of small endpoints still requires ensuring compatibility with the upper bound of the third critical image. The length of long lines cannot replace compatibility.

## Adding new critical points within known endpoints

Fix a finite set of named critical points. If J(a)=b, J(c)=d are known, where a<c, and b, d are adjacent in the currently named set, then every named a<t<c satisfies

$$
b<J(t)<d.
\tag{9}
$$

These J(t) are distinct new critical points, which can be inserted in order of t. They cannot coincide with any existing named points, as there are no named points in the current (b,d)) configuration. This operation maintains the original total number of endpoints, without making any guesses about the size of unknown ordinals, nor assuming that two unknown images are equal.

After supplementation, it can be reused as a constructed application point propagation image. (4) represents the constructed application point propagation image.) Here, we are looking for a finite initialization certificate. The process of repeatedly filling in points to achieve closure is not included in the definition of the marked completion sequence.

A simple example illustrates the limitations of previously finite named sets. Let k=j(j), l=k(j)=j₍₃₎. It is known that

$$
l(\kappa_0)=\kappa_2,\qquad l(\kappa_2)=\kappa_3.
$$

Therefore, l(κ₁) is strictly between κ₂ and κ₃; it is precisely γ₃. Only the initial κ point and the selected completion points of the ordinary M are recorded, possibly omitting points that can be directly obtained from the same algebra.

The bounded point inspection (historical reference: `gap_completion_probe.py`) began after p_init's 24 times M, and performed 200 adjacent interval point additions at fixed original endpoints, resulting in the naming of 636 new points. The application of equation propagation and compatibility group conditions was checked item by item; a total of 672 named points were processed, with the process taking approximately 5 seconds to complete. Compatibility groups with known third critical images still only found a height of 1, not reaching the required 11.

This is the result limited by the search range, not the maximum height limit. A unified ascending layer that does not depend on this search is provided at the end of the text, but the required control of small endpoints is not yet available. Adding named points or increasing the known images of the same embedding alone cannot complete the bounded ascending layer.

## A clear ascending formula and its endpoint cost

There is a simple algebraic process of ascending layers, but it cannot retain the original endpoints for free.

First, we add K₀ to the compatible groups with a high degree h. It is required that the first three elements of the critical sequence with degree K₀ are U₀, V₀, and V₁. This is an additional condition, and it cannot be true by default with (6). Furthermore, assume there is an element H, whose critical point is c<U₀, and also H(c)=V₀.

Define new source points as c,U₀,…,Uₕ, new target points as V₀,H(V₀),…,H(Vₕ₊₁), and take

$$
L_0=H,\qquad L_{k+1}=H\circ K_k\quad(0\le k\le h).
\tag{10}
$$

These embeddings yield a set of compatible heights h+1 with the additional L₀: Kₖ fixes c, so all Lₖ₊₁ transport c to V₀; the remaining common points and second critical images are directly obtained from (6). The strict order of new sources and targets is also guaranteed by the monotonicity of c<U₀<…<Uₕ<V₀ and H.

However, if J=Kₕ, the new highest embedding of the third critical image is

$$
(H\circ J)^{\circ3}(c)
=H\bigl(J(H(J^{\circ2}(U_0)))\bigr)
>J^{\circ3}(U_0).
\tag{11}
$$

The strict inequality arises from H, which strictly moves each Iter(j) critical point above its critical point. This property can also be directly proven using the set of critical points below any fixed endpoint. If H fixes one of the high points, Its own critical sequence will yield infinitely many critical points that do not exceed that point. Contradiction.

Therefore, (10) provides a true compatibility ascending formula, but it lacks an endpoint upper bound for the small K. The repeated application of (10) cannot be considered as a solution to the boundary-preserving initialization for highly 11 cases; if we proceed in this direction, we must also estimate the formula (11), rather than just accumulating the height of compatible groups.)

## Unified ascending layer of fixed sources

There is also a type of augmentation that does not require the addition of smaller critical points, nor any additional K₀. It fixes all the selected source points, target points, and old witnesses, and only adds one source point, one target point, and one embedding at the end of the group.

First use Laver's successor image facts. Let j₍₁₎=j, j₍ₙ₊₁₎=j₍ₙ₎(j), denote

$$
g_r=j_{(2^r)}.
$$

Then crit(gᵣ)=γᵣ, and gᵣ(γᵣ)=γᵣ₊₁; this is a result explicitly cited by [Dougherty's second paper, section 3 begins](https://arxiv.org/pdf/math/9503204) from Laver. Therefore, for any integer a<b, the finite composition

$$
G_{a,b}=g_{b-1}\circ\cdots\circ g_a
\tag{12}
$$

It satisfies crit(Gₐ,ᵦ)=γₐ, Gₐ,ᵦ(γₐ)=γᵦ. Here, it exactly composes b−a times, without any process of finding the normal form or searching for unknown numbers of times.

**Fixing the source point to lift the layer lemma.** already has a highly h compatible group, with the highest embedding being J=Kₕ. If there is another critical point u that satisfies Uₕ<u<V₀, take the critical point G as u, and G(u)=V₀. Define

$$
H=J(G),\qquad K_{h+1}=H(J),\qquad
U_{h+1}=u,\qquad V_{h+2}=H(V_{h+1}).
\tag{13}
$$

The original group, together with these data, is a highly h+1 compatible group.

**Proof.** Let β=J(u). The original compatibility and strict monotonicity are given

$$
V_h<\beta<V_{h+1},\qquad
\operatorname{crit}(H)=\beta,\qquad
H(\beta)=J(G(u))=J(V_0)=V_{h+1}.
\tag{14}
$$

All source points and V₀, …, Vₕ are less than β, and thus are fixed by H. Applying the identity (4) yields

$$
\operatorname{crit}(K_{h+1})=U_0,\qquad
K_{h+1}(U_i)=H(J(U_i))=V_i\quad(0\le i\le h),
$$

$$
K_{h+1}(u)=H(J(u))=V_{h+1},\qquad
K_{h+1}(V_0)=H(V_{h+1})=V_{h+2}.
$$

H strictly moves critical points that are higher than β, so Vₕ₊₂>Vₕ₊₁. The old testimonies and old points remain unchanged, and all compatibility conditions hold. Proof complete.

### A clear eleven-layer group

Generally, take the integer 1≤h<m. Fix Uᵢ=γᵢ0≤i≤h, V₀=γₘ. First let it be.

$$
K_1=j_{(2^m-1)},\qquad V_1=K_1(\gamma_1),\qquad
V_2=K_1(\gamma_m).
\tag{15}
$$

Given that crit(j₍ₙ₎)=γᵥ₂₍ₙ₎, the critical point of K₁ is γ₀. Also, since gₘ=K₁(j), it follows that K₁(γ₀)=γₘ. Combining this with gₘ(γₘ)=γₘ₊₁, we also obtain V₁=γₘ₊₁. m≥2 ensures that γ₁<γₘ, therefore V₂>V₁. This is already a highly 1 group.

For k=2, …, h, take the recursive value.

$$
G_k=G_{k,m},\qquad H_k=K_{k-1}(G_k),\qquad
K_k=H_k(K_{k-1}),\qquad V_{k+1}=K_k(\gamma_m).
\tag{16}
$$

In each step, the application of (13), with the source point being γₖ, is always less than γₘ. Therefore, the induction yields the group with the required height h. Specifically, take h=11, m=12, with all source points being γ₀,…,γ₁₁, and the first target point being γ₁₂.

This construction does not use a large number of M steps, undefined-length completions, or undetermined critical points for comparison. It only uses a specified finite left iteration, a maximum of ten finite compositions, and ten level-ups. The finite-term construction procedure (historical reference: `compatible_fan_terms.py`) shares repeated subterms, with eleven levels resulting in a total of 44 term nodes. The largest left iteration abbreviation is j₍₄₀₉₅₎. These numbers are construction quantities, not the order of the Laver table, nor the proven useful periodic index K.

### The endpoint cost remains crucial

Let C=J³(U₀) denote the state before the level-up, and C′=Kₕ₊₁³(U₀) denote the state after the level-up. By applying the identity (13)–(14),

$$
\boxed{C'=H(C)>C.}
\tag{17}
$$

Specifically, Kₕ₊₁(U₀)=V₀， Kₕ₊₁(V₀)=H(Vₕ₊₁)， and

$$
K_{h+1}(H(V_{h+1}))
=H(J)(H(V_{h+1}))
=H(J(V_{h+1}))=H(C).
$$

Therefore, this construction does not preserve the original total endpoints. It initializes the small cycles into a clear comparison: for the K₁₁ defined by (15)–(16), does there exist a clear small K, such that

$$
C_{11}=K_{11}^{\circ3}(\gamma_0)\le j(\gamma_{K-1})?
\tag{18}
$$

The formula (18) has not been proven, especially that K=100 is feasible. Short written shared terms and small left iteration numbers cannot replace this upper bound; the resulting critical points may have very large subscripts.

The program also examined groups of different instances of 36, h, and m within the limited domain L₁₀: 207 visible points were consistent with the equations; 243 instances where the relationship exceeded γ₁₀ at both ends were only recorded as truncated, not as precise images or evidence of endpoints. The limited examination verified the formulas and composite directions; the full compatibility comes from the proof of (13), and the comparison of small cycle endpoints remains an independent task.

## The specified compound cannot retain the endpoint of the fifth periodic index.

The formula (15)–(16) while uniformly constructs a compatible group, reaches a high level of 2, where its endpoints strictly exceed κ₄. Therefore, this specified construction cannot continue to be considered a candidate for K=5. This does not exclude other compatible groups, nor does it rule out the possibility that this construction could be applicable to larger, well-defined K.

The construction of **Proposition.** for the formula (15)–(16), if 2≤h<m, then

$$
C_h=K_h^{\circ3}(\gamma_0)>\kappa_4.
\tag{19}
$$

**Proof.** let J=K₁. Since J(γ₀)=γₘ, J is strictly increasing on all critical points, therefore

$$
J(\gamma_m)\ge\gamma_{2m}>\gamma_4=\kappa_3.
$$

The last strict inequality uses m≥3. [Dougherty's first paper, section 5, presents 2](https://arxiv.org/pdf/math/9205202) gives j₍₄₎(κ₃)=κ₄; it can also be directly derived from the critical sequence κ₀→κ₂→κ₃→κ₄ of j₍₃ and the application of identity.

The innermost factor of G₂=gₘ₋₁∘⋯∘g₂ is precisely g₂=j₍₄₎, and each outer factor does not decrease in ordinal number. Therefore

$$
G_2(J(\gamma_m))\ge
j_{(4)}(J(\gamma_m))>\kappa_4.
$$

From (17) and applying identity rules,

$$
\begin{aligned}
C_2
&=J(G_2)(J^{\circ3}(\gamma_0))\\
&=J\bigl(G_2(J^{\circ2}(\gamma_0))\bigr)\\
&=J\bigl(G_2(J(\gamma_m))\bigr)
>J(\kappa_4)>\kappa_4.
\end{aligned}
$$

Each subsequent level-up strictly increases the endpoints, hence the conclusion holds for all h≥2. Proof completed.

Since j(γₖ₋₁)≤j(γ₄)=κ₄ holds for all K≤5, the formula (19) excludes this specified construction from satisfying the corresponding formula (18). In particular, the 44 shared item nodes of the eleven-layer instance do not imply a low endpoint; the instance already has an unavoidable lower bound at the endpoint.

## A transport embedding with lower cost for direct endpoint selection

The H required for leveling up does not have to take the specific form of J(G). The following weaker conditions are sufficient.

Given a compatible set with a high degree of h, denoted as J=Kₕ, take Uₕ<u<V₀, let

$$
\beta=J(u),\qquad S=J(V_0)=V_{h+1},\qquad C=J(S).
$$

If there exists a H that satisfies

$$
\operatorname{crit}(H)=\beta,\qquad H(\beta)=S,
\qquad H(C)\le\Theta,
\tag{20}
$$

Then Kₕ₊₁=H(J), Uₕ₊₁=u, Vₕ₊₂=H(S) form a compatible set with a high degree of h+1, and their third critical image is H(C)≤Θ. The proof is identical to that of (13): H fixes all old sources and V₀,…,Vₕ; the new source u is sent by H(J) to S, and the new second critical image is H(S). All old witnesses are retained.

Endpoint checking only requires an upper bound, and there is no need to determine the exact position of H(C). If D≥C and H(D)≤Θ are known, monotonicity gives (20). This can be used for finite certificate search, but it is not possible to directly fill in the missing H(C) as Θ.

### Supplemented bounded sets after critical points

The low critical point certificate procedure (historical reference: `low_gamma_fan_probe.py`) uses the precise names of γ₀,…,γ₂₅₆, as well as the original θ₅, θ₆. Here, θ₄=γ₂₅₆ comes from the calculation of [Dougherty's second paper, section 8](https://arxiv.org/pdf/math/9503204) on j₍₁₃₎(κ₃), and does not treat the zero residue class in the finite table as a precise subscript. Other initialization facts come from the subsequent conclusions of the same paper, the lemma 6.2, the theorem 7.2, and the previous θ₅<θ₆<κ₄ relationships.

After maintaining the finite complement of the total upper bound θ₆ and applying closure, the program recorded 764 points, 5, 000 embeddings, and 23, 847 point-to-point equations. It examined direct H, finite compositions consisting of known point images, as well as those that only required a monotonic upper bound of 20). The current record did not yield any new high 2 bound-preserving certificates; this is merely the result of a limited set of certificates, not a proof that high 2 does not exist.

The program has a limit of 25 seconds, 1, 500 points, approximately 5, 000 witnesses, and 500, 000 facts. The maximum time for this session is about one second. The closed search will not be included in the basic column definition of the parent table, nor will an attempt be made to actually calculate the complete descent of BMS[10].

## The necessary space given by the subscripts of critical points

Even without specifying the ascending formula, the compatible group cannot arbitrarily push into very short critical point intervals. Let

$$
U_i=\gamma_{u_i},\qquad V_i=\gamma_{v_i},\qquad
K_h^{\circ3}(U_0)=\gamma_c,\qquad d=v_0-u_0.
$$

Therefore, d≥h+1, and moreover

$$
\boxed{c\ge u_0+3d+h(h-1)
       \ge u_0+(h+1)^2+2.}
\tag{21}
$$

The proof only uses strictly increasing integer subscripts. K₁ gives v₁−v₀≥u₁−u₀; each Kₖ also gives

$$
v_{k+1}-v_k\ge v_0-u_k.
$$

After addition, the first term and the k=1 term combine to form d, while for the k=2,…,h terms, we have v₀−uₖ≥h+1−k. Therefore

$$
v_{h+1}-v_0\ge d+\frac{h(h-1)}2.
$$

Finally, using Kₕ(V₀)=Vₕ₊₁, we obtain c−vₕ₊₁≥vₕ₊₁−v₀, which is (21).

In particular, any third critical image of an eleven-layer compatible group is at least γ₁₄₆. If we unify the eleven-layer groups with **The entire mathematical research manuscript is as follows:** and transport them through j, their endpoints are at least j(γ₁₄₆), and thus they cannot fall below j(γ₉₉). This only excludes the scenario where such a holistic transport is done as K≤100, but it does not exclude the use of other critical points and embeddings that are below j(γ₉₉) but do not belong to the entire group's j image. K≤100 is still just a research preference, not a hard upper limit for the goal.
