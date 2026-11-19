# The finite-parameter growth function of the parent package and its periodicity of thirty-two · [中文版](parent-packet-quantitative-transfer.reading.zh-CN.md)

*English reading edition, translated with machine assistance. The title links to the dated Chinese manuscript.*

> Collected reading edition. The three main papers state the results of this collection.
> This edition retains the local proofs, their hypotheses and any withdrawals. Progress reports describe the state of work at the time.
> The locations of omitted passages on preset inputs are recorded in SOURCE_MANIFEST.json.
> The main papers give the numerical derivations for the natural parameters produced by the proofs. This historical note carries no additional Lean certification.

2026-10-14. In the algebra of generating elements at the same I3, parent package completion not only has a fixed `[2]` column deletion count boundary, but also can incorporate the finite parameter linedness recursion of the ordinary BLP. For the existing nine-row actual seeds $S$, the following proves that a new, well-defined computational value satisfies the conditions.

$$
\boxed{q(5)>2^{f_{\rm PP}(S,1)}.}\tag{1}
$$

This is an extension of the numerical interface, not a conclusion that $f_{\rm PP}$ is proven to be stronger than BMS. In particular, $f_{\rm PP}$ and the FGH with full indicator parent packages do not have the same definition as the fixed `[2]` occurrences.

## The finite operations used in the recursion of 1.

Following the convention of [Parent Package Rules](<parent-packet-short-tail-definition.md>) for ordinary rows, accurate marks, and correct one-base paper copy guards. The first two rows are retained here, with the zero terms being $(01):1,(012):1$, which is not a completely empty array.

Let $M_{\rm PP}$ be a raw short copy, and start executing the parent package scan from the position of the old last line. First, check the address domain of the first complete copy; items that fail are cut off in the following recursion, without calling $M_{\rm PP}$. Therefore, it is a candidate for `[2]` that is fully indexed on these non-degenerate inputs.

Using the ordinary BLP **Auxiliary Types**: When the last core is $(0,1,2,n):2$, it is called E-successor; when the last core is $(0,1,2,a,n):3$ or $2<a<n$, it is called E-limit. All other non-zero values are called transient. These are the names of the branches in the numerical recursion, and they are not confused with the successor determination of the full index candidates.

For the two types of E mentioned above, let $a=2$ or the corresponding $a>2$, define:

- $E_P(0)=\operatorname{cut}P$; 
- If $E_P(t)$ has $d$ rows, add an auxiliary core $(a,d+1):1$ behind it, then perform another raw short replication to obtain $E_P(t+1)$.

Auxiliary copied coordinate mapping:

$$
\psi_a(x)=\begin{cases}x,&x<a,\\x+d+1-a,&x\ge a.\end{cases}\tag{2}
$$

It is defined everywhere and does not undergo native or mark scanning. After specifying $m$, exactly $m$ copies are performed. This does not introduce a hidden loop into the definition of the fundamental sequence that "runs until a certain type occurs."

## The 2. certificate class and operations are maintained.

Use $\mathcal C_m$ to represent the following actual finite implementations:

1. The ordinary row edges are implemented by the owners in the same $\operatorname{Iter}(j)$, with the first two rows fixed.
2. ActiveSat, proper marks, accurate traces, and positive marked sources are all valid.
3. Each mark has a natural membership truncation certificate defined by the successor of its final factor;
4. The first three $(\theta_0,\theta_1,\theta_2)$ have a finite $m\ge1$ amount of linedness at their endpoints.

For eligible rows with a common step size of one, Sat holds automatically; other rows with a step size are inactive rows. Therefore, the ActiveSat here is consistent with the Sat used in the original proof.

The term "cut" and its prefix maintain the certificate. With [Theorem on the Transport of the Parent Package of Any Real Input](<parent-packet-propagation-selector.md>), $M_{\rm PP}$ maintain the ordinary row, natural truncation, accurate traces, and Sat, while retaining the total cap and the value of the last owner in the raw short copy. The new mark originates from the old positive source or a non-empty native $p\ge1$, thus remaining positive.

The implementation of E does not require any changes. Its auxiliary copy has a valid paper copy certificate; the natural truncation of the general full, low, high closures covers it, including the non-adjacent traces of limits. Sat is also directly maintained by (2): if the copied row originally satisfies $\delta(e)\le p$, the corresponding new inequality is $\delta'(\psi_a(e))\le\psi_a(p)$. When $e<a$, it reads the unchanged prefix; when $e\ge a$, it is the monotonic renumbering of the old row. There are no additional scanning events between the old and new blocks.

The reference is to natural truncation closures, not the semantic definition of "all marks fix the successor integer boundary" which has been proven to have counterexamples. The implementation of E as a cap and the parameters for finite linedness come from [Original finite parameter quantitative bridge](<../iblp-laver-bms-20261013/marked-BLP-quantitative-transfer.md>). This construction relies solely on the three-point image of the E input type, and does not depend on which native package is chosen by M.

Therefore, the cuts allowed in $\mathcal C_m$, $M_{\rm PP}$, and $E_P(m)$ all have real implementations; changing the native selector does not damage the input interface of E.

## 3. defines growth computation

Let $g_0(m)=m2^m$. First, regard the following formula as a partial recursion, without assuming a global termination:

$$
f_{\rm PP}(P,m)=
\begin{cases}
g_0(m),&P\text{ is the fixed two-row zero term},\\
f_{\rm PP}(\operatorname{cut}P,m),&\text{the address check for the first full copy fails},\\
\bigl(x\mapsto f_{\rm PP}(\operatorname{cut}P,x)\bigr)^{\circ2^m}(m),
&P\text{ is an E-successor},\\
f_{\rm PP}(E_P(m),m),&P\text{ is an E-limit},\\
f_{\rm PP}(M_{\rm PP}(P),m),&P\text{ is any other nonzero term}.
\end{cases}\tag{3}
$$

The order of branching priorities is as shown in the formula, with zero items having priority. Each non-recursive structural operation has a clear, finite range; the entire recursion can be extremely long, and this is precisely the computation that needs to be compared, which cannot be hidden within a single fundamental sequence expansion.

This full copy check will not unexpectedly truncate the two types of E: both have $p=1$, the smallest address is 0, the mapping sends 0 to 2 or $a$, and sends all $x\ge1$ to $x+n-1$, so it is defined for all non-negative addresses. The double-block recursion indeed uses the (3) branch of E-successor.

## 4. is a finite table power equivalent to cap

Let a cap with at least two rows of implementation (including two fixed zero rows) be $\Theta=\gamma_r$, and the representative of the last owner in the $2^r$ element Laver table be $1\le b<2^r$. Set

$$
\Phi(P)=2^{r+1}-b.\tag{4}
$$

Here, the real implementation uses 'cap' and 'owner', and it is not claimed that there is only one kind of $\Phi$ for the same grammatical item.

The term 'cut' reduces to $r$, resulting in a strict reduction. The short copy that maintains the cap changes the last owner to $J(K)$, and the $b*_r c>b$ in the finite table also undergoes a strict reduction. The parent package scan retains this last owner. The natural implementation of E involves two applications; the critical point of the intermediate owner is $J(\theta_0)=\theta_a<\Theta$, so it is still not a unit element in the residue class, and it also undergoes a strict reduction. For more details, see [Direct one-step proof](<../iblp-laver-bms-20261013/direct-step-bridge.md>).

Therefore, it is possible to perform strong induction on natural numbers $\Phi$, without the need to invoke the good fundamentality of the abstract Steel relationship in this finite parameter conclusion. I3 is still used in these actual implementations and homomorphic finite quotients, and thus the axiomatic premises cannot be discarded based on this.

## 5. Quantitative Theorem and Double Block Induction

**Theorem.** If $P\in\mathcal C_m$, then $f_{\rm PP}(P,m)$ is defined, and moreover

$$
(\theta_0,\theta_1,\Theta)
\quad\text{we have}\quad f_{\rm PP}(P,m)\text{ segments of linedness.}\tag{5}
$$

We make a strong induction on (4), while quantifying all actual implementations and all finite parameters they carry, namely $m$. We also prove that the call has a definition and is related to (5). The zero terms are derived using the two-line linedness lemma. The address domain failure is first induced by cut, and then the last segment is extended to the original cap. E-limit and transient use the E and $M_{\rm PP}$ from the 2 section for their implementations and strict reduction. Here, only the current finite $m$ witness is used.

E-successor deals with recursive calls where the parameters can grow large. Let $Q=\operatorname{cut}P$, $g(x)=f_{\rm PP}(Q,x)$, $Q_i=E_P(i)$, then $Q_0=Q$, $Q_{i+1}$ are a double-block copy of $Q_i$ at $a=2$.

A inductive proof for $i$ strengthens the assertion: For any $Q_i$ implementation of the 2 section's certificate that satisfies $R$, if $\Phi(R)<\Phi(P)$, then it provides $g^{\circ2^i}(R.m)$ segments of linedness from the current finite parameters $R.m$, and also provides a definitiveness for these calls.

$i=0$ is the outer induction. From $i$ to $i+1$, we first take the old blocks; their cap is $\nu<R.\Theta$, and the induction is given to $M=g^{\circ2^i}(R.m)$ with witness at the same endpoint. Then, from the new blocks, we extract a $Q_i$ to achieve: its cap is the same as the last owner and $R$, but the first three now have witnesses with parameter $M$. All the mark factors of the new block come from replication areas with address at least 2; for the last factors $t$, $\psi_2(t+1)=\psi_2(t)+1$, every natural number remains the same ordinal before and after extraction. The extraction retains the complete certificate, and its $\Phi$ is exactly $\Phi(R)$, still lower than $\Phi(P)$.

Applying the strengthened assertion once more, we obtain

$$
g^{\circ2^i}(M)=g^{\circ2^{i+1}}(R.m).
$$

Extract only the raw E pairs, without relying on PP or the old native way of generating $Q_i$. Finally, use $i=m$ for the natural implementation of $E_P(m)$, whose potential is strictly lower than $P$, resulting in the E-successor branch. The definitiveness of all function calls is generated by this finite induction, without assuming that $g$ is fully defined for any integer.

## The explicit periodic boundary of the nine-row seeds 6.

[Nine lines of ordinary seeds $S$](<same-owner-L3-sat-closure.md>) has all the certificates from section 2, with initial finite parameters of 1, and a total cap of $\theta_6<\kappa_4$. It is not an arbitrary handwritten grammar pattern.

Linedness counting lemma converts (5) into

$$
\theta_6\ge\gamma_{2^{f_{\rm PP}(S,1)}}.
$$

Due to $\kappa_4=\gamma_{q(5)-1}$, strict monotonicity yields the formula (1). Similarly, prefix seeds that satisfy the same certificate can be used, but it is not claimed that deleting prefixes will necessarily preserve the computational intensity.

The formula (1) provides a different interface compared to the simple $\#\mathrm{steps}<2^{q(5)}$: it directly places a recursively growing value below the order parameter $q(5)$, rather than merely bounding the number of elements in the table. However, this comparison does not involve $f_{\rm PP}$ versus the old $f_\star$, nor is it proven to dominate the FGH of the internal hyper-BMS notation. Additional native packages may change the next replication root, making it impossible to compensate for this comparison with the addition of more points.

## The distance from 7. to the main goal

This theorem allows for the subsequent use of the E double block and the parent package short M, which yield a strict numerical bound within the same window. It is still necessary to have a replication-closing internal port code, as well as a non-degenerate computational comparison from it to the (3) or fixed `[2]` cut count. Only when both of these are completed can the formula (1) be considered the required structural upper bound for the BMS.

This paper presents a paper-based derivation; no actual evaluation of $f_{\rm PP}(S,1)$ is performed, and no bounded experiments are considered as universal proofs.

**Independent audit.** conducted a thorough verification of the complete replication of fallback,E's Sat and natural truncation, arbitrary implementation of double-block extraction, finite potential induction and parameter substitution, as well as the final exponential direction. The zero-term potential domain proposed in the audit has been completed in section 4; no other gaps were found.

## 8. is the longest valid prefix version with constant bridge coverage

[Longest valid prefix correction](<parent-packet-partial-copy-audit.md>) changes the handling of replication failure to: Replicate the longest valid initial segment within the specified source interval, stop before the first bad source line, without skipping bad lines. This short replication is marked as $M_\dagger$ with PP scan. If the first source line is bad, the result is cut; resource limits are not considered as mathematical failure conditions here.

When defining $f_\dagger$, retain the zero terms of (3), the branches of E-successor, and the branch of E-limit; the remaining non-zero terms are taken directly.

$$
f_\dagger(P,m)=f_\dagger(M_\dagger(P),m).\tag{6}
$$

A preliminary full-copy check no longer cuts off valid short copies. The address domains for both classes E were already total, so their branching and two-block extraction are unchanged. For $M_\dagger$, zero successful rows already give a cut.

Let the source interval that was successfully copied be $[p,h)$, where $p<h\le e$. Output the cap and the last owner are respectively:

$$
\Theta'=J(\theta_h)\le J(\theta_e)=\Theta,
\qquad J(K_{h-1}).\tag{7}
$$

Even if the core in the $h$ row contains missing references, the address $h\ge p$ itself remains within the translation domain. Therefore, it is implied that the cap indeed exists. There is no need to assume that there is a successful copy in the $h$ row. The copy of each successful row naturally reads only the copied previous text and the old cut prefix. The PP scan then retains (7), with all certificates still in the classes of the 2 section.

If $h=e$, follow the cap-preserving application descending trend. If $h<e$, the cap decreases strictly, regardless of the representation of the last owner in the smaller quotient, (4) also decreases strictly. When the source is bad, follow the cut descending trend. Therefore, the finite trend induction from the 5 section still applies.

**Required endpoint steps:** In the actual partial-short situation, We only provide the corresponding linedness for $(\theta_0,\theta_1,\Theta')$; At this point, it cannot be said to be a transient termination point. Apply the same algebraic endpoint extension lemma used in the original cut branch. Extend the last paragraph from $\Theta'$ to $\Theta$. The number of segments remains unchanged. Only then was the original cap conclusion required by the theorem obtained. This is an extension of the limited testimony. No additional operations are added to the step expansion of the marker.

Therefore, there are the same nine rows of seeds

$$
\boxed{q(5)>2^{f_\dagger(S,1)}.}\tag{8}
$$

The second independent check verified that (7), the final factor of the natural world, the endpoint extension of the partial branch, as well as E and the double-block induction were not affected. Here, the upper bounds of the two calculations are proven, but the upper bound of $f_\dagger\ge f_{\rm PP}$ is not proven. The inclusion of the descending relationship in itself is not sufficient to deduce such numerical monotonicity.
