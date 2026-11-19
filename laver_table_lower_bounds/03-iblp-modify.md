# Counts of marked modify steps from large original IBLP terms · [中文版](03-iblp-modify.zh-CN.md)

Work in ZFC + I3. Both operations that construct the initial term use the full fundamental sequences of the specified original IBLP. The subsequent count is for **paper-guard short $M_\star$ with the full frozen scan and cut**. The entrance retains every mark, and the run permits subsequent effective marked completions with several factors.

## 1. The natural initial term

Put $R=I[0][3][0]$. Its six rows are

    01:1; 012:1; 0123:2; 234:1; 2345:2; 456:1.

The root carries no marks. Let $L=C_{\rm line}$ be the actual length of Qi's chain in equation (1) of [the dynamic BMS proof](02-bms-feedback.md). Define

$$
N_0=2^L,\qquad L_1=2^L-1,\qquad N_1=2^{L_1},
$$

$$
S_*=R[N_0][N_1].
\tag{1}
$$

Both fundamental-sequence steps are **full original expansions with the legacy guard**. The entrance proof holds index by index. We may use all $L$ segments of the first current chain and then all $L_1$ segments returned by the first step. This gives the stated initial term.

More generally, suppose

$$
2\le k\le2^L,\qquad 2\le n\le2^{\,2^L-1},
\tag{2}
$$

Then every specified original $R[k][n]$ has the semantic entrance described below. For equal indices one may take $S_{\rm diag}=R[N_0][N_0]$, since $L\le2^L-1$.

Starting from such an initial term $P$, let $\mu(P)$ count all short $M_\star$ steps before the empty term, let $\delta(P)$ count cuts, and let $\tau(P)$ be their sum. Insertions internal to a scan are part of that step. Then

$$
\boxed{\delta(P)<q(5),\qquad
\mu(P)\le\tau(P)<2^{q(5)}.}
\tag{3}
$$

In particular, (3) applies to $P=S_*$. This gives a bound in the stated direction for the natural entrance supplied by the proof. A comparison of $\mu$ or $\tau$ with the Hardy or FGH of the whole of $R$ remains open.

## 2. The rules covered

Cut a nonempty term if it is a genuine successor or fails the address-domain check for the first full copy. Otherwise make one ordinary short copy of the final row from the source interval $[p,e)$, using the paper guard. Perform the prescribed full frozen scan. On each old row process the frozen marks first and the native case second. Skip newly created families. The scan permits words with several factors and effective marked completion.

The address-domain failure includes $p=0$. Source row 0 does not exist, even if Python would accept a negative index there. Each scan visits only finitely many old rows from its input and their finite descending ancestor chains. Thus a single step is finite.

General equivalence of the paper and legacy guards remains open. The entry proof verifies agreement at every step of the two initialization procedures. The subsequent-orbit theorem uses the paper guard.

## 3. Supplying full packets at the exact endpoints in one algebra

Take the application terms

$$
K=j_{(11)},\quad b=K(j),\quad c=K(b),\quad
d=c(K),\quad A_*=c(d),\quad Q=A_*(K).
$$

The standard finite table of points gives

$$
A_*(\kappa_0)=\kappa_2,\quad A_*(\kappa_1)=\kappa_3,\quad
A_*(\kappa_2)=\theta_6,\quad A_*(\kappa_3)=\theta_7,
$$

with the strict upper bound

$$
A_*(<\theta_6)<\theta_8<\kappa_4.
\tag{4}
$$

The original actual $L$-line $(\kappa_0,\kappa_1,\theta_5)$ first takes the $K$ image, then the $Q$ image, to obtain an accurate matching root-end complete package.

$$
L(\theta_6,\theta_7,A_*(\theta_5);L),\qquad
A_*(\theta_5)<\kappa_4.
\tag{5}
$$

The root $R$ has six owners, which are $j,j,K,b,K(K),c$. The final complete package is a single line, starting from $\theta_6$, ending at $\theta_7$, including its implied endpoints. Exactly (5), doubling segment by segment E, produces $2^L$ complete packages; retaining the first $k$ packages, performing a clear $k-1$ number of raw short copies, deleting control lines, scanning again, and extracting, yields an accurate original $R[k]$.

Every repetition count in this finite construction is specified in advance.

## 4. The current chain for the second expansion

Put $V=d(K)$ and $B=V(K)$. The actual point images give

$$
L(\theta_5,\theta_6,\chi;L),\qquad \theta_6<\chi<\theta_7.
$$

The last owner $c$ is given another segment $L(\mu,\theta_5,\theta_6;1)$. Using the index chain multiplication that retains the original prefix, we obtain the $2^L$ segment; delete the original first segment, leaving

$$
L(\mu,\theta_6,\chi;2^L-1).
\tag{6}
$$

This supplies a shadow with the precise starting point required by the penultimate row of the root.

In the first raw forest, the same owner transports both the endpoints and the witnesses of this shadow together with the complete adjacent source block. In each round the internal shadow endpoint lies below the packet cap, which is at most the current active first image. Its transported image therefore stays below the old overall cap. Finally, deleting the control row exposes exactly the transported penultimate row.

The first native-only scan preserves the middle boundary and implicit cap of that last row. If the inserted width is $t$, the pair consisting of core length and step changes from $(h,s)$ to $(h+2t,s+t)$, and the new position of the old middle coordinate is still $(h+2t)-(s+t)$. Extraction preserves the last row and cap as well, so it does not repair this last owner.

Therefore, each $R[k]$ is assigned a segment of $2^L-1$ located at its **exact new packet endpoints**. It can provide a second maximum of $2^{\,2^L-1}$ packages, proving the numerical range of (2). After the second initialization, there is no need to regenerate the third shadow, so this conclusion does not presuppose an infinite budget closure.

See Sections 1–6 and 15 of [Realized entrance](proofs/scratch/iblp-I-to-I0-20261016/local-budget2-initializer.en.md), together with [Decorated shadow forest](proofs/scratch/iblp-I-to-I0-20261016/local-budget2-shadow-forest.en.md) and Section 3 of [Prefix-preserving chain algebra](proofs/scratch/iblp-I-to-I0-20261016/local-budget-algebra.en.md).

## 5. Preserving the natural semantics of marks

The proper mark $y$ has the following exact word of nonterminal factors, $W=F_{v_0}\circ\cdots\circ F_t$. The natural membership cutoff requires

$$
F_r\equiv_{\Delta(W)}W,\qquad
\Delta(W)=(F_{v_0}\circ\cdots\circ F_{\rm prev})(\theta_{t+1}),
$$

where $\theta_y<\Delta(W)\le\theta_{y+1}$. This cutoff concerns membership rather than pointwise restriction of an ordinary function.

**Repair lemma.** if $\operatorname{crit}(G)=c$, then $G(F)\equiv_c F$. For $x,z\in V_c$, $G$ fixes both, and the application is covariant and elementary.

$$
x\in G(F)(z)\iff x\in G(F(z))\iff x\in F(z).
$$

This does not require $F(z)\in V_c$.

If the set of rows selected with **Extraction closed under physical successors of factors.** retains all core/mark/trace references, the last row, and the cap, and also retains the physical successor $v+1$ for each mark factor $v$, then the original natural certificate will remain intact after endpoint repair.

Proof: The owner of each factor, the next physical point, and the entire $\Delta(W)$ remain unchanged. If the old cap $c$ of carrier $r$ is extended to $c'>c$, replace the actual $\operatorname{crit}(G)=c,\ G(c)=c'$ transporter with $G(F_r)$. The property is given as $\Delta(W)\le\theta_r<c$, so the lemma above retains the required membership equivalence. The last line and cap are retained, so the last owner is not repaired. [Proof and construction of the transporter](proofs/scratch/iblp-I-to-I0-20261016/marked-entry-extraction.en.md)

The first forest has no inherited marks. Select a whole native family together. Every newly created direct mark has its factor and physical successor in that family, as required for closure.

The second forest's complete live package consists of the last two complete native families. Its mark has only one non-terminal factor, and both pairing sources are not lower than the active minimum. The new pivot in each round of short copies is exactly at the beginning of the new replication segment, so the next source segment remains an integral image of this property. All replication marks only follow the all-high branch, and the legacy and paper guard are consistent in this macro. The selected complete package, its column deletion control prefix, and the image preservation factor of the selected source remain closed; the second freeze scan is quiet.

According to this, all original versions of $R[k][n]$ within (2) obtain natural membership certificates, ordinary practical instances, Sat, proper accuracy marks, and positive mark sources, with caps strictly below those of $\kappa_4$. [Independent entrance induction](proofs/scratch/iblp-I-to-I0-20261016/marked-entry-initializer.en.md) and [The original forest and the quiet-scan proof](proofs/scratch/iblp030-8h-20261015/original-audit-root-forest-interface.en.md)

## 6. Closure under subsequent short M steps

For the above certificate, a legal paper short copy and a complete scan maintain natural membership, Sat, accurate traces, ordinary row edges, the same generator, and global cap. The last owner changes from $J$ to $J(K')$, and the scan no longer changes it. A legal cut also maintains the certificate.

Here, a marked local theorem is indeed invoked. The specific copy words, nature, Sat internal packet transport, and scanning proofs are all attached to [Index to the natural-mark lemmas](common/natural-marks.md). The local lemmas used do not require a fixed triplet to have all finite linedness, nor do they invoke the global I2 standard domain well-order theorem.

## 7. A finite-table potential bounds the counts

Write the current cap as $\gamma_r$. The critical point of the last owner is strictly below the cap. Its representative in the finite Laver quotient is $1\le a<2^r$. Put

$$
\Phi=2^{r+1}-a.
\tag{7}
$$

The finite Laver table has $a*_r b>a$ ($a<2^r$). The proof is based on a downward induction for $a$, followed by an induction on the column numbers: the first column is $a+1$. If the value is the top element, then the next value returns to $a+1$; otherwise, it is strictly greater than the previous value, obtained by induction on higher rows.

A successful $M_\star$ keeps the cap and changes the last owner's quotient to $a*_r b$, so $\Phi$ decreases by at least 1. A cut gives $r'<r$. To handle the cut there is no need to compare the two owners, since

$$
\Phi_{\rm new}\le2^{r'+1}-1\le2^r-1
<2^r+1\le\Phi_{\rm old}.
\tag{8}
$$

The last two rows and the cases below them are realized separately by

$$
(01)(012)\to(01)(12)\to(01)(02)\to(01)\to0
$$

Implementation; the first two steps are still end owner applications, and the last two steps are cuts, with the empty potential being 0. Therefore, the definability of a single step plus the integer potential strictly decreases, proving that the entire process is finite.

$$
\tau(P)\le\Phi(P)<2^{r_0+1}<2^{q(5)}.
$$

The initial subscript of cap satisfies $r_0<q(5)-1$. Each cut further reduces this subscript, and eventually deleting it can be recorded at a final level, hence $\delta(P)\le r_0+1<q(5)$. From this, we get (3).

This potential also gives the same paper short $M_\star$/cut number bounds for the original five-line initial formula $I$ and the six-line $R$: they already have the same algebra, and the cap is less than $\kappa_4$ in natural implementations. The carrier of the unique mark in the five-line initial formula and the factor owner are both $j_{(11)}$. [Five-row initialization](proofs/output/iblp-laver-bms-20261013/marked-BLP-quantitative-transfer.md)

## 8. Consequences for numerical lower bounds

We obtain $q(5)>\delta(S_*)$ and $\tau(S_*)<2^{q(5)}$. If $\tau(S_*)>0$, the latter gives $q(5)>\log_2\tau(S_*)$ as well. This proof retains the exponential loss.

This is a quantitative link between the large original initial terms and the well-defined modify/cut process. Relating those counts to the Hardy or FGH for an entire original $R$ needs a simulation with a changing index. A high entrance, two large initial indices or an equality of order types alone cannot supply that simulation. The finite-type FGH proof in the first paper is independent of this open comparison.
