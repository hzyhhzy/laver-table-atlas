# BLP one-step length and bridging routes of direct fundamental sequences · [中文版](direct-step-bridge.zh-CN.md)

*English reading edition, translated with machine assistance. The title links to the dated Chinese manuscript.*

> Collected reading edition. The three main papers state the results of this collection.
> This edition retains the local proofs, their hypotheses and any withdrawals. Progress reports describe the state of work at the time.
> The locations of omitted passages on preset inputs are recorded in SOURCE_MANIFEST.json.
> The main papers give the numerical derivations for the natural parameters produced by the proofs. This historical note carries no additional Lean certification.

At this stage, we first compare the number of steps of descent, without directly comparing FGH. It is necessary to construct a sequence notation and to define a starting formula, whose ordinal position strictly exceeds a certain BMS[N], where N is at least 10. Then, repeatedly take each step of [2], simulating it as a non-empty BLP operation with Laver table quantification semantics. Achieving the BMS limit for the entire system is still a desirable enhancement, but first, we need to bridge the starting formula with a fixed BMS[10] level.

The requirement here is that a single fundamental sequence can be directly counted, and the potentially very long M sequences cannot be condensed into a single expansion. The existing quantitative theorems for the general BLP do not directly accumulate the number of M sequences; this paper presents a general finite table counting lemma, which only provides a bound on the size of the table. Subsequent work has established a stronger column deletion count for the special case of [Balanced port encoding](<balanced-ribbon-bridge.md>), which directly controls the order parameter; the initialization of small cycles remains unresolved.

## Initial form and counting direction

Following this catalog convention, BMS[N] represents a two-column matrix located in the row N+1.

$$
B_{N+1}=(0^{N+1})(1^{N+1}).
$$

Fix the N=10 first, so what needs to be covered are eleven rows of BMS seeds, not ten rows. Let the clear starting notation for the new notation be s. It can be written as a fundamental term of some simple upper end A, A[n₀], but N and n₀ should not be confused beforehand.

Definition

$$
s_0=s,\qquad s_{i+1}=s_i[2],\qquad
D_2(s)=\min\{t:s_t=0\}.
$$

The following should be established separately:

1. The order of s is strictly greater than that of BMS[10]. It would be desirable to have an explicit finite pattern embedding, rather than relying solely on experimental growth to make predictions.
2. Each non-zero [2] step of s is simulated by a non-empty actual M operation. If there are column deletions, [E] steps, etc., it is necessary to have clear rules and maintain the same finite implementation.
3. The total number of Ms in the actual BLP process is controlled by a definite, small parameter Laver cycle threshold.

If the 2th term is realized by a matching relation, then a time point should be able to be selected.

$$
0=t_0<t_1<\cdots<t_{D_2(s)}
$$

Ensure that at least one M occurs between two adjacent matching times. Therefore, the required direction is

$$
D_2(s)\le\#M.
$$

Conversely, breaking down a single M into many new markers [2] steps does not result in the desired inequality by itself. Matching time can exist in the proof; however, when calculating a new marker [n], one cannot first search for the next matching time.

This is the initially envisioned direction of gradual matching. A slightly weaker but sufficient clear matching has been adopted: non-zero last columns require a M operation at each step, while zero last columns only require row deletion. Additionally, it has been proven that D≤2·#M+z₀, where z₀ is the initial number of zero columns, to avoid missing the downward steps associated with deleting zero columns.

## Acceptable range for a single expansion

The expression retains the previous column sequence format: A[0] removes the last column, while the columns before the old last column remain unchanged. A[n] is the column prefix for A[n+1]. The number of copies or the scanning range should be clearly defined by the input structure and n.

The following two cyclic properties are different:

- Direct definitions involve copying the finite column specified by n the number of times required, or scanning the entrance to exist. No requirement that the expanded expression be very small.
- Repeat the M operation until a limit form, successor form, or some normal form appears. The number of repetitions does not have a direct limit, and a fundamental sequence cannot be hidden in one repetition.

In this stage, the latter cycle is not renamed as "normalization" to circumvent the requirements. If an intermediate state is needed, it must have a clear column structure and direct expansion rules, and the prefix properties, ordinal lower bounds, and matching relationships must be proven separately.

## A lemma for the true counting of the number of M

In this section, we use a fixed embedding of I3 into j, along with the same algebraic structure that is generated by it, Iter(j). Let γ₀<γ₁<⋯ enumerate the critical points of this algebra. Each named point of a BLS is one of these critical points, hence its endpoint can be written as γᵣ.

Let the last line of P be embedded as J, and crit(J)<γᵣ. Denote a as the residue class of J in the finite quotient Lᵣ, using the representatives 1,…,2ʳ; therefore

$$
1\le a<2^r.
$$

The correspondence between finite quotient and application operations, as well as the property that M preserves the endpoints and embeds the last row into J(K), is implemented using BLS in [Paper Qi, Fifth Edition](https://arxiv.org/html/2501.06733v5). The following integer potential functions are direct consequences of these properties, not the f recursion from the original paper.

### Strict increase in a finite table

For any a<2ʳ and any b, the ordinary Laver table satisfies

$$
a*_r b>a.
\tag{1}
$$

This can be proven directly from the definition. Inductively from a, we have that the first value a*1=a+1 is greater than a. If the previous value is 2ʳ, then the next value is 2ʳ*(a+1)=a+1); otherwise, the previous value c satisfies c>a. By the established properties of the c row, we have c*(a+1)>c>a. Inductively over the column numbers, we obtain (1).

Definition

$$
\Phi(P)=2^{r+1}-a.
\tag{2}
$$

Every practical operation below **Proposition.** reduces Φ by at least 1.

- M, or a copy that maintains the endpoints and changes the last row owner to J(K), where K belongs to Iter(j);
- Delete the last line.
- A E operation with non-increasing endpoints. If the endpoints remain unchanged, the implementation described in the paper, involving two applications, is adopted, ensuring that the critical points of the intermediate owner are strictly below the endpoints.

For **Proof.** with M, the endpoints remain unchanged, and the new classes are a′=a*_r and b. The output is still BLS, so it's a′<2ʳ. From (1), a′>a), it follows that Φ strictly decreases.

For column deletions, the subscript of the end point is changed from r to r′<r. The residual classes of the old and new owners do not need to be compared, because

$$
\Phi(P')\le2^{r'+1}-1\le2^r-1
<2^r+1\le\Phi(P).
$$

For E, when the endpoints decrease strictly, it is the same as above. When the endpoints are the same, the last row owner is obtained after two applications; the owner between the two applications is also not a unitary class, hence it can be used continuously (1). Proof complete.

The condition for the intermediate owner cannot be omitted: the row of the unitary residual class 2ʳ is 2ʳ*b=b, which does not satisfy (1). A single completion retains the potential function and is not separately counted as a strict decrease step here; a single M, after including its prescribed finite completion scan, results in the last row owner being the same as the copied owner, so the entire M still strictly decreases the potential.

### The result is a table of size bounds.

If the starting and ending points do not exceed γᵣ, then the total number of steps in the above process T satisfies

$$
T<2^{r+1}.
\tag{3}
$$

In particular, when only continuously performed as M, the endpoint subscripts remain unchanged. If the starting residual class is a₀, then the number of M does not exceed 2ʳ−1−a₀.

Use the cycle convention of this catalog

$$
q(K)=\min\{m:\pi(m)\ge2^K\},\qquad
j(\gamma_{K-1})=\gamma_{q(K)-1},
$$

If the entire process already has a homomorphic element that lies below j(γₖ₋₁), then (3) is given

$$
\boxed{\#M\le T<2^{q(K)}.}
\tag{4}
$$

This is the bound for the actual accumulation of the number of Ms, without the need to first calculate these M steps, nor to rely on the f values that might be neglected in transient steps.

But 2^{q(K)} is the number of elements at the threshold, and q(K) is the order parameter required by the original task. The exponent cannot be removed arbitrarily from (4). Therefore, even if D₂(s)≤#M is established later, this lemma only produces

$$
D_2(s)<2^{q(K)},
$$

To obtain D₂(s)<q(K′) and K′ still being small, a stronger counting semantics is needed, or a threshold amplification lemma with an independent proof.

## The structural problem that needs to be solved next

The existing BMS without completion has a simulated retention of the entire copy tail block. In the case of ordinary BLP, only one prefix is retained from the short copy; for example, if the old I[0][1] is replaced by the ordinary M, it will reach the p_{ω^ω} of the paper after three runs. Therefore, simply changing to a different cyclic notation does not preserve the original BMS lower bound.

The subsequent search has found [Balanced port encoding](<balanced-ribbon-bridge.md>): Use the IBLP-style metric convention in the parent table representation of the BMS. Each non-zero last column [2] step corresponds precisely to at most h rows of deletion, plus one ordinary M. All completions are empty. Let the number of descent steps be D, the number of M steps be C, and the number of initial zero columns be z. Then C≤D≤2C+z. The starting value A[10] is strictly greater than the original value BMS[10]. Corresponding to the finite BLP in row 38; Initialization within the small cycle endpoints remains unresolved.

Initialization must also be controlled independently: no specification of a huge critical sequence subscript is used to create BMS[10] seeds. Relevant proven obstacles are seen in the two constraints of the replication budget (historical reference: `copy-budget-obstructions.zh-CN.md`).

Further counting of encoded rows can eliminate the exponential loss in the formula (4): when the height is h≥3, the number of steps decreasing D is strictly less than the total number of row deletions in BLP δ, and δ does not exceed the critical point at the initial end. For details, see the article "Directly Obtaining the Lower Bound of Order Parameters for Row Deletion Counting". Therefore, once the row seeds are implemented under 38 and j(γₖ₋₁), D₂(A[10])<q(K) is directly obtained. This is not a general improvement for any BLP, but an additional property of the special encoding.

What remains unfinished is the implementation of this small periodic pattern with the 38 symbol, as well as the final comparison of FGH. Having a high ordinal does not alone guarantee that the [2] decline of any fundamental sequence is slow enough.
