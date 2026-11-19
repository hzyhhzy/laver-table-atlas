# Short-tailed IBLP retains the original reachability order and its Laver counting interface. · [中文版](short-tail-cofinality.zh-CN.md)

*English reading edition, translated with machine assistance. The title links to the dated Chinese manuscript.*

> Collected reading edition. The three main papers state the results of this collection.
> This edition retains the local proofs, their hypotheses and any withdrawals. Progress reports describe the state of work at the time.
> The locations of omitted passages on preset inputs are recorded in SOURCE_MANIFEST.json.
> The main papers give the numerical derivations for the natural parameters produced by the proofs. This historical note carries no additional Lean certification.

2026-10-14. Shortening the last copy block allows for the fixation of `[2]` to become a regular short copy, while retaining all the reachable expressions and order of the original IBLP. The key is to maintain the original rule for the legality check of the first complete copy, and to continue using complete copies in higher indices; it is not to convert all indices into short copies.

The following presents two separate conclusions. First, the bidirectional simulation of reachability relations is a purely combinatorial conclusion. Second, under the natural truncation realization of the I3 generator, the number of column deletions for the six-row root with fixed `[2]` is less than that for $q(5)$. This has not yet proven that the fixed index computation is stronger than any BMS nesting with a fixed number of layers.

## The original rule adopted for 1.

This text follows the rules of Astra–Qi's IBLP well-order manuscript section 2: complete tail replication, the next source mark guard of the manuscript, frozen mark scanning, and ladder-based native completion. The original text can be found in [IBLP Well-Ordered PDF](https://github.com/QiRenrui/basic-laver-pattern/blob/main/IBLP_wellfoundedness_en.pdf). The version checked locally is the ten-page version from 2026-09-11.

It is necessary to distinguish the local old `iblp.py`: its mixed mark guard is one position less, and it cannot be identical to the manuscript version without verification. The research procedure retains two strategies, `legacy` and `paper`, respectively. The semantic results of this paper are only used for `paper`, and they should not be equated with the small sample of the two as being equivalent across the board.

The expression has a line with $n$. The $i$ line represents an increasing core of $A_i$, a step size of $L_i$, and marks; the last term of the core is $i$, with an implied endpoint of $i+1$. The last line is marked as $A$, with a step size of $L$.

$$
p=A[-L-1],\qquad e=A[-L],\qquad a=\min A.
$$

Original copy address mapped to

$$
f(x)=
\begin{cases}
x,&x<a,\\
A[j+L],&x=A[j]<p,\\
x+n-p,&x\ge p.
\end{cases}
\tag{1}
$$

The rest of the positions are undefined. The following $\mathcal C$ represents a once-uncompleted copy: the last line is deleted, the source line is copied as $p,\ldots,n$, and the last control line is retained in the copy. $\mathcal S$ only reduces the last segment of the source interval to $p,\ldots,e-1$, while the address mapping and marking strategy remain unchanged. $\operatorname{Comp}_n$ indicates the original frozen scan starting from the position $n$ of the original last line.

If the original definition is copied completely for the first time, the original basic terms of the manuscript are

$$
F_m(P)=\operatorname{Comp}_n
       (\operatorname{cut}(\mathcal C^m(P)))\quad(m\ge1),
\qquad F_0(P)=\operatorname{cut}(P).
\tag{2}
$$

Lemma 4 ensures that the definition of complete replication is also valid for the specified number of times that follow. If the first replication fails, all $F_m$ are taken as cut; the subsequent ones also take cut. Zero does not have a strict descending edge.

## 2. Short Tail Rule

The notation $Q_k(P)$ is defined as follows, with the number of terms in the parent row still denoted as $n$:

- When $k=0$ or $P$ is the successor, take cut.
- When attempting to copy completely for the first time, 'cut' is also taken. Even if the necessary parts of the source lines can be copied, this check is still retained.
- In other cases, $Q_1(P)$ is the prefix that is retained to the $n$th row by the $Q_2(P)$ below.
That is, only the first completed new row is retained.
- When the index $k\ge2$,

$$
\boxed{Q_k(P)=\operatorname{Comp}_n
              (\mathcal S(\mathcal C^{k-2}(P))).}
\tag{3}
$$

The number of repetitions here is explicitly marked as $k-2$. The scan only processes the finite old lines at the entrance. The operation M is not repeated in a single fundamental sequence until some unknown normal form appears. In particular, $Q_2$ only has one short replication and its original scan.

The first full replication check only traverses whether the required address belongs to the domain of (1). There is no need to actually construct the complete tail that will be discarded later. This allows the new and old systems to be compared uniformly in case of replication failures, without assuming that all standard descendants can be replicated.

## 3. completes the scan while retaining the prefix

If two scanning entrances have the same prefix and start scanning from the same position, then the completion result of the shorter entrance will contain the prefix of the completion result of the longer entrance, along with marks and step sizes.

Proof based on the old rules for entry. The accurate traceability of the current mark only reads addresses that are no later than the current row. The reverse link of native completion also does not read future lines. The same row that has been processed previously results in the same record and frozen candidate. The entire native family inserted is the same as before. And both sides skip the new family. The address translation caused by insertion only affects the rear direction. Do not reverse the modified prefixes that have already been completed. Therefore, the induction can continue to the last line of the shorter entry and its complete new family.

This assertion differs from "first arbitrarily cutting out a completion family, then completing the result to be the same." What is being compared are prefixes on the same entry old line boundary, whose corresponding completion prefixes contain all the families generated by that old line.

## 4. Prefix Contraction and the Same Reachability Relationship

Let $\preceq$ denote the prefix that contains the core, step size, and marks. For any $m\ge1$, in the case where replication is legal, the original array satisfies

$$
\operatorname{cut}(\mathcal C^{m-1}P)
\preceq \mathcal S(\mathcal C^{m-1}P)
\preceq \operatorname{cut}(\mathcal C^mP).
$$

The reason is simply $1\le p<e\le n$: the source interval that is copied in the short copy is a non-precedential prefix of the source interval after removing the control self-copy. The complete copy retains the same structure in subsequent rounds. Using the prefix properties of scanning, we obtain

$$
\boxed{F_{m-1}(P)\preceq Q_{m+1}(P)
       \preceq F_m(P)\preceq Q_{m+2}(P).}
\tag{4}
$$

There is also $Q_0(P)\preceq Q_1(P)\preceq Q_2(P)$. All failures or subsequent situations are cut, but the prefix relationships remain valid. Therefore, the new basic column meets the requirements of deleting the last row and processing each prefix individually.

**Two-way simulation theorem.** start from the same root, and both sets of rules have exactly the same finite reachable expressions, with the transitive closure of their strict reachability relations being the same.

The proof proceeds step by step. Any new fundamental term $Q_k(P)$ is a prefix of some original fundamental term, so the original version can be expanded by one step, and then finitely many tail elements can be deleted to obtain it. Conversely, the original fundamental term $F_m(P)$ is a prefix of $Q_{m+2}(P)$, and can be obtained using the same method. The cuts on both sides are inherently consistent. Each simulation is a finite and non-empty path; by splicing these paths over a finite history, the proof is complete.

Therefore, as long as the original expansion tree is well-founded, the new expansion tree is also well-founded, and their descending ranks are the same. This is the result of the transitive closure being the same, not just because the fundamental sequences have similar growth rates. In the same radical standard domain, the prefix fundamental sequences and those that only change the last row also provide finite reachability: if the two paths after bifurcation cross a common shorter prefix, they must visit it, because one step at most reduces the number of rows. Combined with well-foundedness, the same well-ordering is given on both sides.

Quoting the theorem from the above manuscript, its six lines root

```text
(1,0)1(2,1,0)1(3,2,1,0)2(4,3,2)1(5,4,3,2)2(6,5,4)1
```

The short tail version is therefore well-founded under ZFC + I3, and the order type generated from this root is the same as the order type generated by the original rules of this manuscript. No exact ordinal number of the root is calculated separately here, nor are the two old Python guards for well-foundedness borrowed from the original text considered the same.

### The finite index displacement also retains the FGH hierarchy.

Co-tailness alone is not sufficient to imply growth comparison, but (4) provides a stronger unified index boundary: for all $x\ge0$,

$$
Q_x(P)\preceq F_x(P)\preceq Q_{x+2}(P).
\tag{4a}
$$

The two sets of systems share common zero forms, common successor determinations, and common successor subterms. Here, the old index strictly refers to the manuscript index of (2), not the display index of the old Python. Non-successor terms that cannot be copied, although all fundamental terms equal cut, are still evaluated according to the following non-successor branches; it is not appropriate to reclassify them as successors in one of the systems just because their fundamental sequence is constant. They are respectively denoted by $f^{\rm old},f^{\rm short}$ to represent their FGH, as agreed upon.

$$
f_0(x)=x+1,\qquad
f_P(x)=f_{\operatorname{cut}P}^{\circ(x+1)}(x)\ (P\text{ successor}),
\qquad f_P(x)=f_{P[x]}(x)\ (P\text{ nonzero nonsuccessor}).
\tag{4b}
$$

On this common base domain, there is a precise comparison with input constraints.

$$
\boxed{f^{\rm short}_P(x)\le f^{\rm old}_P(x)
       \le f^{\rm short}_P(x+2)-2.}
\tag{4c}
$$

First, perform a well-founded induction on a set of last-line prefix rules, and at the same time prove three things: $f_P(x)\ge x+1$, $f_P$ are non-decreasing with respect to the input, and when $A\preceq P$, $f_A(x)\le f_P(x)$ holds. For successor terms, use the monotonicity of smaller sub-terms and their value iteration. For non-successor terms, $P[x]$ contains $\operatorname{cut}P$, thus containing any true prefix that contains $P$. For sub-terms, use the inductive hypothesis to obtain a comparison of prefixes. If $x\le y$, then $P[x]\preceq P[y]$, due to the input of smaller terms and the monotonicity of prefixes.

$$
f_{P[x]}(x)\le f_{P[y]}(x)\le f_{P[y]}(y).
$$

This proves the necessary preliminary lemma. Here, only the monotonicity of **Prefix before words** is proven, without assuming any numerical monotonicity for any ordinal subscript.

Now prove that (4c) for jointly reachable well-orderings. The zero terms can be calculated directly on both sides. In the case of non-successor situations, the inductive hypothesis of (4a) with smaller terms gives

$$
f^{\rm short}_{Q_x(P)}(x)
\le f^{\rm short}_{F_x(P)}(x)
\le f^{\rm old}_{F_x(P)}(x),
$$

and

$$
f^{\rm short}_{Q_{x+2}(P)}(x+2)
\ge f^{\rm old}_{Q_{x+2}(P)}(x)+2
\ge f^{\rm old}_{F_x(P)}(x)+2.
$$

All occurrences of sub-items are strictly less than $P$. The reachable transitive closures of the two sets are the same, so the same induction can be used. In the case of successors, the first direction involves the same number of iterations. In the second direction, starting with the new input $x+2$ and the old input $x$, the induction hypothesis is used to maintain that "the new value is at least the old value plus 2" at each step. The new iteration includes two additional calls, and the additive nature of the values only strengthens the inequality. This proves that (4c).

Therefore, shortening is not just about retaining the order type: the FGH defined by (4b)) only differ by an input compensation of at most 2. However, this still does not fix the FGH lower bound of `[2]`; it is not possible to replace the FGH index, which changes with the input value, with a constant 2.

<a id="proof-section-6"></a>

## All BMSs with positive indicators 5. are simulated in the BMS.

[Balanced port strip](<../iblp-laver-bms-20261013/balanced-ribbon-bridge.md>) was originally written as an identity only once for a fixed short M. For the new fundamental sequence mentioned above, it can be generalized to all positive BM4 indices.

Fix the number of rows in the BMS as $h$, the bandwidth as $w=h+1$, and the base point of the $j$th column in the matrix as $b_j=3+jw$. The complete rows within the band are followed by this notation (7), which is considered an IBLP core when the endpoints are omitted. Denote the encoding as $\mathcal R_h(M)$.

If the last column is non-zero, its highest non-zero coordinate corresponds to the port $k$. First, delete the last zero row without the $h-k$, resulting in $P$. Write the original column number $x$, and if that coordinate's parent column is $c$, then

$$
N=b_x+k,\qquad p=b_c+k,\qquad e=b_x,
\qquad d=N-p=w(x-c).
$$

At this point, for each $m\ge1$,

$$
\boxed{Q_{m+1}(P)=\mathcal R_h(M[m]_{\rm BM4}).}
\tag{5}
$$

The first complete copy provides a parent table copy in the proof of the equilibrium band, and the control that remains from the original copy provides the same active coordinates for the next copy. With each additional complete copy, one more row of $d$ is added, and a next bad block of BM4 is generated. The final short copy ends at $e-1$, exactly at the end of the last complete band; its total number of rows is

$$
N+(m-1)d+(e-p)-1=b_x+md-1.
$$

The point-in-point mapping within the band is the same as the original proof: the lower ports of the tangent bands inherit the control rows, while the upper ports inherit the tangent points. For other bands, the lower regions' parent references remain fixed, while the upper regions' parent references move with the copies. The zero-anchor row causes the original completion scan to stop immediately each time, with no marks, so there is no change in the full scan. The domain of the first complete copy also covers all the references of these bands. This leads to (5), not inferring the array to be the same based on the same total number of rows.

When the last column is all zeros, the $h+1$ lines that follow are deleted, resulting in exactly one zero column in the matrix. This lemma is a full index identity in coding; it does not yet assert that any coding itself is a literal descendant of the six-row root.

<a id="proof-section-7"></a>

## The fixed index counting of six rows with the symbol 6. and the periodic boundary

Starting from the six-row root $R$, repeatedly take $Q_2$, denoted as

$$
G(R)=\text{cuts to the empty term},\qquad
L(R)=\text{total to the empty term }Q_2\text{ steps}.
\tag{6}
$$

The term 'cut' includes deletion after the next occurrence as well as deletion after a first complete replication fails; every other step is a $M_\star$. The 4 section first states that both are finite, and it cannot be assumed that the algorithm has been fully defined just because the following potential function seems to be decreasing.

Following the six-row root initialization (historical reference: `README.zh-CN.md`), the root has a natural truncation within a $\operatorname{Iter}(j)$ with a seal $\theta_7<\kappa_4$, and the initial marks are empty. The [Sat short copy closure](<../../natural-mark-lemmas/sat_endpoint_packet_theorem.en.md>) and [Natural truncation counting interface](<../iblp-laver-bms-20261013/marked-BLP-quantitative-transfer.md>) provide a legal $M_\star$ that maintains this seal, with the final owner becoming a single application; the cut strictly reduces the seal. If an additional complete replication check fails, only the already allowed cuts are selected, thus not destroying the implementation.

The above general BLP interface only maintains the first two lines fixedly. The truly empty steps in the last four steps need to be found separately. The two lines with the core notation $(01):1,(012):1$ have their trailing trajectories exactly as follows:

$$
(01)(012)\longrightarrow(01)(12)\longrightarrow(01)(02)
\longrightarrow(01)\longrightarrow\varnothing.
\tag{6a}
$$

All steps are of length 1. Let the owner of the first row be $K$, and the owner of the second row be $J$:
$K:\theta_0\mapsto\theta_1\mapsto\theta_2$，
$J:\theta_0\mapsto\theta_1\mapsto\theta_2\mapsto\theta_3$.
The first step's new owner $O=J(K)$ implements $\theta_1\mapsto\theta_2\mapsto\theta_3$, with the critical point being $\theta_1$. The critical point of the second step $O(K)$ is $\theta_0$, and

$$
O(K)(\theta_0)=O(K(\theta_0))=\theta_2,\qquad
O(K)(\theta_2)=O(K(\theta_1))=\theta_3.
$$

The two formulas use the symbols $O(\theta_0)=\theta_0$ and $O(\theta_1)=\theta_2$ respectively. Therefore, the application in both cases remains sealed with $\theta_3$, and it is reduced by two subsequent cuts. The empty formula is retained with $\theta_1$ as the final seal, and no final owner is required. This is a direct, unmarked finite implementation, and the closure theorem for the first two rows is not applied outside its domain.

Write the seal as $\gamma_r$, and each cut should reduce its critical point subscript by at least 1. The original subscript is $\theta_7<\kappa_4=\gamma_{q(5)-1}$, therefore

$$
\boxed{G(R)<q(5).}
\tag{7}
$$

The count of all steps is denoted by [Finite table potential function](<../iblp-laver-bms-20261013/direct-step-bridge.md>): If the last owner is $a<2^r$ in a finite quotient of size $2^r$, let it be $\Phi=2^{r+1}-a$. Short replication strictly increases $a$, while cut strictly decreases $r$. Define the potential of the empty form as 0, and the last edge also strictly decreases. Therefore, there is another...

$$
\boxed{L(R)<2^{q(5)}.}
\tag{8}
$$

It is not possible to remove the exponent from (8), nor can $G$ and $L$ be identified without proof. The balanced BMS with its additional row growth properties can connect two types of counts; however, the complete marked system has not yet been proven to have the same properties.

## What else is missing for structural enhancement with 7.?

This bidirectional simulation has eliminated the obstacle of 'short copies inevitably losing the entire original order type', and the rules still retain both the original and marked completions. The formula (4c)) also controls the input loss between the two sets of FGHs. However, this does not mean that the number of column deletions fixed for `[2]` automatically maintains a lower bound for a certain FGH.

The next quantitative task is to find six-row roots or higher-level structures that can be uniformly regenerated, and to prove that $G(R)$ dominates a truly internal enhancement system with clear calculations. It is also possible to establish similar balance band counting conversions for more general marked patterns. Achieving a BMS root using only two cuts of $R$, or simply adding a major name to its ordinal type, is insufficient to complete this task.

The bounded verification files consist of short-tail rules (historical reference: `short_tail_candidate.py`) and full indicator sets with identities (historical reference: `short_tail_ribbon_probe.py`). The latter set checks for 1,200 matrix states, 3,522 complete identities, with a maximum input of 12 rows and peak target rows of 321. There is no resource truncation, and the process exits in approximately 3.1 seconds. These checks are implemented; the comprehensive conclusions from the 3—5 sections are based on prefix causality, bidirectional finite simulation, and replication induction. The original IBLP has not been modified, nor have any repositories been submitted or pushed. These results are not considered to be structural hyper-BMS numerical targets that have been completed.
