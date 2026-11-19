# Direct rule for full gap short tail candidates · [中文版](full-gap-short-tail-definition.zh-CN.md)

*English reading edition, translated with machine assistance. The title links to the dated Chinese manuscript.*

> Collected reading edition. The three main papers state the results of this collection.
> This edition retains the local proofs, their hypotheses and any withdrawals. Progress reports describe the state of work at the time.
> The locations of omitted passages on preset inputs are recorded in SOURCE_MANIFEST.json.
> The main papers give the numerical derivations for the natural parameters produced by the proofs. This historical note carries no additional Lean certification.

2026-10-14. This candidate retains the usual IBLP's finite steps, stride, marks, and copy address mapping. It replaces the completion of the ancestral chain with the completion of the entire source gap. The fundamental sequence is still modified only at the last row and appended with a suffix, and is nested according to the prefix of the index. The fixed $[2]$ can be connected to the same $q(5)$ window; larger indices do not require to retain this window. The candidate's universal well-foundedness, the strength of the relative BMS, and the required numerical lower bounds are still incomplete.

<a id="proof-section-1"></a>

## 1. finite expressions and fundamental operations

The expression is a regular row sequence $(A_i,L_i,M_i)$. The core $A_i$ is a strictly increasing non-negative integer sequence ending with $i$, with the last element implicitly being $i+1$. $L_i$ is the step size, and $M_i$ are the proper marks. The row type, accurate trace, and correct one-base replication guard follow the rules of [Ordinary natural truncation interface](<same-owner-L3-sat-closure.md#proof-section-4>). The zero terms are empty, and the successor conditions follow the original sequence rules: the last core has only two terms, with the first term being zero.

For non-empty last lines with $A=A_n$, let

$$
p=A[-L-1],\qquad e=A[-L],\qquad a=\min A.
$$

The copied address is mapped to

$$
\varphi(x)=
\begin{cases}
x,&x<a,\\
A[j+L],&x=A[j]<p,\\
x+n-p,&x\ge p,
\end{cases}
\tag{1}
$$

The rest of the addresses are undefined. It is required that $p\ge1$. Copy $C$ completely, deleting the last line, and copying the source line $p,\ldots,n$; make a short copy of $S$, which only copies $p,\ldots,e-1$. Both use (1) and the same correct paper mark guard. If the address required by the source line is not within the domain, the copy is undefined.

## 2. full gap scan

Scan from left to right, the entry record is empty. Each current old line is processed first by freezing the old marks, followed by the native processing. The native new line family is skipped, not rechecked in this round. Mark completion still uses the original current $+1$ guard, as well as the source package in the record and the corresponding target package.

The only change to 'native' is: if the length of the core in that row does not exceed $2L$ and $L\ge2$, take

$$
U=(p+1,p+2,\ldots,e-1),
\tag{2}
$$

Instead of selecting points along the ancestral chain of $A_i[-2]$. The rows and long rows of $L=1$ are not native. The entire finite scan is denoted as $\mathcal G$.

The specific formula for inserting the row is as follows. Write $U=(u_1<\cdots<u_t)$, and the current row number is $r$. First, shift all the old addresses behind $>r$ by $t$. For $0\le h<t$:

- Column $|A|=2L$: New core is
$A\cup\{u_1,\ldots,u_{h+1}\}\cup\{r+1,\ldots,r+h\}$, step size $L+h+1$;
- Short line $|A|=2L-1$: The new core is
$(A\setminus\{e\})\cup\{u_1,\ldots,u_{h+1}\}\cup\{r+1,\ldots,r+h\}$, step size $L+h$.

The last item $h=t$ has the same conditions as the previous ones: the core is $A\cup U\cup\{r+1,\ldots,r+t\}$, and the step size is $L+t$. The sets are arranged in ascending order. The $h$th item inherits the old marks and adds $r,\ldots,r+h-1$, without marking its own last item; new source points are not marked. The original row $r$ corresponds to the package $U$, and the subsequent records are shifted along with the address. Empty packages do not take any action.

A pattern is called GapSat if every row that is native satisfies $e=p+1$. Each legal full gap scan outputs GapSat, while cut maintains it.

## 3. is a fully indexed short-tail fundamental sequence.

Use the same rules for roots and their descendants.

1. $P[0]=\operatorname{cut}(P)$. Zero is the endpoint; all successors take the cut as their index.
2. If the attempt to fully copy the address domain of $C(P)$ fails, all indicators are set to cut.
3. In other cases, Let $P[1]$ is $\mathcal G(S(P))$ Prefix of the original line number.
4. For $k\ge2$, define

$$
\boxed{P[k]=\mathcal G\bigl(S(C^{k-2}(P))\bigr).}
\tag{3}
$$

The number of repetitions at the entry is clearly marked as $k-2$; scanning also involves the limited traversal of the old lines at the entry and the frozen marks. There is no unknown number of cycles within the fundamental sequence where "M is repeated until a special type."

### The first legally complete copy guarantees the subsequent original copy's domain.

Here, the subsequent successful replication is not considered as an additional conjecture. If the first replication is defined, its new end control behavior is $\varphi(A)$, the new replication root is $n$, and the new minimum address is $\varphi(a)$. The entries required for the next time are of the form $\varphi(x)$, where the old $x$ belongs to a replicated source line.

- If $x<a$, it remains fixed, and is still lower than the new minimum address;
- If $a\le x<p$, the first replication indicates $x\in A$, therefore $\varphi(x)$ is in the new control line;
- If $x\ge p$, then $\varphi(x)\ge n$, which belongs to the new translation region.

Therefore, the next replication is still defined, and the induction specifies the total number of times. 'marks' are inline addresses, which do not add another missing domain. The final short replication only reads the prefixes of the complete source interval, so it also has a defined meaning. This only handles the addresses of the original replication and does not replace the scanning semantic proof separately.

## 4. Prefix and Comparison

In a single scan of the common old prefix, the same marks, traces, and records are read on both sides, selecting the same entire source gap. Therefore, $\mathcal G$ maintains the prefix on the boundary of the old entry line, including the entire new line family generated by that line. This is consistent with the causal proof of the original ancestor package scan, and it does not require the two to select the same package.

The unscanced array satisfies

$$
\operatorname{cut}(C^{m-1}P)
\sqsubseteq S(C^{m-1}P)
\sqsubseteq\operatorname{cut}(C^mP)
\sqsubseteq S(C^mP).
\tag{4}
$$

Therefore, after scanning, (3) is nested with index prefixes. The parent GapSat causes the original cut prefix to be neither recorded nor completed during scanning, so each fundamental term is retained as it is. The truncation and failure branches of $[1]$ also satisfy these properties.

Use the ordinary short-key

$$
K(A,L)=(A[-1],A[-2],\ldots,A[L],A[0])
\tag{5}
$$

Dictionary comparison for each line. The key of the first copied line is strictly lower than the key of the last line in the old version; the record before that is empty. No matter how many sources (2) are chosen, the key of the first line in the native version remains this reduced key. The addition of new sources and the increase in step size cancel each other out, and the high-end addresses and minimum addresses remain unchanged. Therefore, each non-zero actual fundamental column edge is strictly reduced (5). This excludes finite cycles, but the dictionary reduction itself does not prove that there are no infinite reduction chains.

## 5. Implementation and Proof of Boundaries at Small Endpoints

Take [The eleven lines clearly indicate the seed $G$](<full-gap-native-local-closure.md#proof-section-13>). It is called GapSat, and all actual owners belong to the same $\operatorname{Iter}(j)$. The endpoints are
$\theta_6<\kappa_4=j(\gamma_4)$.

The fixed $[2]$ can only be copied once with a full gap scan, or the cut option is chosen. [GapSat Local Closure](<full-gap-native-local-closure.md>) It has been proven that this scanning preserves true semantics, endpoints, and the final owner after replication. Therefore, the number of column deletions $G_2$ and the total number of deletions $L_2$ satisfy the condition

$$
G_2<q(5),\qquad L_2<2^{q(5)},
\tag{6}
$$

Following the first two lines, the four steps at the end are continued using the verified unmarked ending trajectories.

The larger indicators also contain complete copies, which may enhance the endpoints when they are naturally implemented. They cannot be cited as (6) uniformly constrains all indicators. In fact, finite window obstacles (historical reference: `finite-window-uniformity-obstruction.zh-CN.md`) indicate that if the entire indicator standard domain is controlled by a strictly descending finite table potential, it can only be finite and cannot have an ordinal type above BMS.

[Theorem on prefix sets of any real entrance](<full-gap-unrestricted-prefix-packet.md>) has completed its paper proof and independent audit: the upper layer package only needs to contain the entire family of lower layers as the initial stage, without the need for equal width. Therefore, scans resulting from any finite number of legal complete copies also maintain true semantics, eliminating the need for Sat／Sat_rec. Combined with the address domain lemma from section 3, all specified finite indicators have legal semantics. This conclusion is distinct from the finite cap bounds of fixed short steps and the well-foundedness of all indicators; the latter has not yet been proven.

In terms of strength, the single package projection (historical reference: `native-packet-projection.zh-CN.md`) can statically reduce smaller completion packages, but it does not exchange with the next replication. The strength obstacle analysis (historical reference: `full-gap-strength-obstructions.zh-CN.md`) also indicates that the old balanced BMSs cannot be directly copied. Therefore, this paper does not consider semantic closure as an embedding of BMSs or super-BMSs.

The experimental prototype (historical reference: `full_interval_native_candidate.py`) implements these direct rules and explicit resource bounds. States like 1,000, and transitions like 3,977 undergo finite verification checks for row types, accurate traces, GapSat, prefix sums, and single-step comparisons. Resource truncation at 18 is calculated separately and is not considered as completion. These verifications do not replace a full proof.
