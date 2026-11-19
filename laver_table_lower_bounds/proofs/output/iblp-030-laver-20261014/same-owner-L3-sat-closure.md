# A complete Sat certificate for the ordinary L3 seeds and subsequent short operation closures · [中文版](same-owner-L3-sat-closure.zh-CN.md)

*English reading edition, translated with machine assistance. The title links to the dated Chinese manuscript.*

> Collected reading edition. The three main papers state the results of this collection.
> This edition retains the local proofs, their hypotheses and any withdrawals. Progress reports describe the state of work at the time.
> The locations of omitted passages on preset inputs are recorded in SOURCE_MANIFEST.json.
> The main papers give the numerical derivations for the natural parameters produced by the proofs. This historical note carries no additional Lean certification.

2026-10-14. This paper audits the nine-row pattern obtained from [Eight lines L3 for initialization and the first scan](<ordinary-l3-native-mark-seed.md>), $S$. The conclusion is not merely "some points match": $S$ satisfies all the input conditions of the existing general natural truncation Sat closure theorem. Therefore, every subsequent **Legal** short copy with complete scanning, cut, and $E(1)$ that allows finite parameters, has a true implementation.

The term "legal" is not omitted here: Sat does not guarantee that the partial replication mapping is defined everywhere; non-replicable items are selected for cut according to rules. This paper also does not consider the height of this set of short operations as an ordinal of the original IBLP or BMS.

## 1. fixes the actual realization and nine rows of data.

Assume ZFC + I3, where all owners are taken from a fixed $\operatorname{Iter}(j)$. Follow the true terms from the initialization manuscript $K,f,H,D_\beta$, rather than assigning them abstract points. The named points are arranged in order by address.

$$
(\kappa_0,\kappa_1,\kappa_2,\kappa_3,\mu,\theta_5,
\beta,\alpha,\zeta,\eta,\theta_6),\qquad 0,1,\ldots,10.
\tag{1}
$$

They are strictly increasing, and $\theta_6<\kappa_4$. The complete rows in the table below also need to have an implicit endpoint $r+1$ after 'core'. The mark 3 in the 4 row can be either included or omitted; both versions satisfy the conclusions of this paper.

| Row $r$ | core | $L_r$ | marks | owner |
| ---: | --- | ---: | --- | --- |
| 1 | $(0,1)$ | 1 | Empty | $j$ |
| 2 | $(0,1,2)$ | 1 | Empty | $j$ |
| 3 | $(0,1,2,3)$ | 2 | Empty | $K$ |
| 4 | $(0,1,2,3,4)$ | 2 | Empty or $\{3\}$ | $K$ |
| 5 | $(0,1,2,3,5)$ | 3 | Empty | $f$ |
| 6 | $(0,6)$ | 1 | Empty | $D_\beta$ |
| 7 | $(0,1,2,6,7)$ | 3 | Empty | $H$ |
| 8 | $(0,1,2,3,6,7,8)$ | 4 | $\{7\}$ | $H$ |
| 9 | $(0,1,2,3,6,7,8,9)$ | 4 | $\{7,8\}$ | $H$ |

The critical points of all owners are $\kappa_0$, which is consistent with the minimum addresses 0 in each row. The 1-linedness of the initial three $(\kappa_0,\kappa_1,\kappa_2)$ are realized by the actual $j$; this is not a common linedness for all finite parameters.

## 2. ordinary row type and all row edges

Use [The definition of Qi is 2.6.](https://arxiv.org/html/2501.06733v5): The line length should be calculated as **Full length with implied endpoints added back**. The total lengths of the nine lines are as follows:

$$
3,4,5,6,6,3,6,8,9.
$$

The corresponding step size is $1,1,2,2,3,1,3,4,4$, and all normal row types are allowed. In particular, the 4th row with a complete length of 6 and a step size of 2 is allowed as a long row; it is excluded by the restriction that complete length 4 must have a step size of 1.

The 1 and 2 rows are the first three or four critical sequence points of the $j$. The 3 and 4 rows use

$$
K:\kappa_0\mapsto\kappa_2,\quad
\kappa_1\mapsto\kappa_3,\quad
\kappa_2\mapsto\mu,\quad
\kappa_3\mapsto\theta_5.
$$

All edges in the 5th row are

$$
f:\kappa_0\mapsto\kappa_3,\quad
\kappa_1\mapsto\theta_5,\quad \kappa_2\mapsto\beta.
$$

In the 6 row, $D_\beta:\kappa_0\mapsto\beta\mapsto\alpha$ is used. In the 7, 8, and 9 rows, the following lists are used for the previous 3, previous 4, and all 5 sides respectively:

$$
H:\kappa_0\mapsto\beta,\quad\kappa_1\mapsto\alpha,\quad
\kappa_2\mapsto\zeta,\quad\kappa_3\mapsto\eta,\quad
\beta\mapsto\theta_6.
\tag{2}
$$

This also checks the implied endpoints for each row, not just the edges within the visible core.

## 3. Sat, proper traces, positive sources, and natural truncations

To avoid confusion between two parent functions, denoted as

$$
\delta(r)=A_r[-2],\quad p(r)=A_r[-L_r-1],\quad e(r)=A_r[-L_r].
$$

Only the middle and short rows with a core length not exceeding $2L_r$ are executed with native; the 2th and 4th rows are not included in this list. The remaining rows satisfy the following conditions item by item:

| $r$ | $p(r)$ | $e(r)$ | $\delta(e(r))$ |
| ---: | ---: | ---: | ---: |
| 1 | 0 | 1 | 0 |
| 3 | 1 | 2 | 1 |
| 5 | 1 | 2 | 1 |
| 6 | 0 | 6 | 0 |
| 7 | 1 | 2 | 1 |
| 8 | 2 | 3 | 2 |
| 9 | 3 | 6 | 0 |

Therefore, all conditions are met $\delta(e(r))\le p(r)$, which means Sat.

All non-empty marks have only actual traces

$$
\begin{array}{c|c|c|c}
\text{owner row}&\text{mark}&\text{full trace}&\text{owner and nonterminal factors}\\\hline
4&3&(3,1)&K=K\quad(\text{optional})\\
8&7&(7,1)&H=H\\
9&7&(7,1)&H=H\\
9&8&(8,2)&H=H.
\end{array}
\tag{3}
$$

Each mark is strictly less than the address of the corresponding row, accurately matching the step length pairing of the source; the source address is 1 or 2, and is strictly greater than the row's minimum address 0. Therefore, this holds true for proper, accurate traces, PosSource, and even NC.

Natural truncation rule: If the non-terminal word is not $W=J_{v_0}\circ\cdots\circ J_t$, then

$$
\Delta(W)=(J_{v_0}\circ\cdots\circ J_{v_{d-2}})(\xi_{t+1}),
\qquad J_r\equiv_{\Delta(W)}W,
\tag{4}
$$

Here, $\xi_i$ represents the address corresponding to (1) at ($i$), with ($\equiv$ being the Laver membership truncation. In (3), there is only one factor, which is associated with the owner **Global equality**, hence (4) holds automatically. This also covers the complete successor point bounds required for direct marking, eliminating gaps with only lower truncations.

<a id="proof-section-4"></a>

## 4. Directly callable closures, as well as domain conditions that cannot be omitted

The exact range of the following existing paper lemmas is used:

1. [Natural truncation semantics](<../../natural-mark-lemmas/natural_trace_cutoff_semantics.en.md>)
§§2—3 To mark the closure of a legal copy with a full/low/high mark.
2. [Sat Entrance Complete Package Theorem](<../../natural-mark-lemmas/sat_endpoint_packet_theorem.en.md>)
§6 is derived from **A valid short copy of the parent item for Sat.**, which represents all the actual reads of non-empty records in the old terms Sat_rec; §§2—5 completes the event-by-event package, old edges, new edges, and natural truncation proofs.
3. [Ordinal complete marked BLP synthesis](<../../natural-mark-lemmas/full_marked_blp_natural_cutoff_wellorder.en.md>)
Lemma 3.1 They are combined into a short replication plus left-to-right complete scan closure.
4. [Finite-parameter quantitative bridge](<../iblp-laver-bms-20261013/marked-BLP-quantitative-transfer.md>)
The certificate class $\mathcal C$ indicates that these local lemmas only require the current actual certificates, without the requirement for a certain standard generation history.

This paper §1—3 has been given the parameter $S\in\mathcal C$. The parameter $m=1$ is also provided. Therefore:

- Cut to at least two lines of prefixes, maintaining the same class of certificates;
- If the original short copy mapping is defined on the required entries, a single short copy and its complete scan are finite and complete, with the output still
$\mathcal C$, invariant under cap, the last owner changes from $J$ to $J(K')$;
- Copy and adopt the correct one basis `paper` mark guard, and do not replace it with the local `legacy` less-bit filtering.
- If there is no definition for the operation, the allowed operation is 'cut'. In particular, the condition for the original `ap` to become $p>0$ also falls within the domain of definitions.
Sat does not prove, nor does it need to prove, that every object is replicable;
- For the successor/limit terms in the determination of mutually exclusive types, $E(1)$ can be used. It has only one auxiliary triple replication.
The auxiliary replication threshold mapping is always defined; 1-linedness is sufficient to construct its true owner, with the first three elements and their witnesses retained.

This seed indeed has a defined first short copy, which does not immediately fall into cut: the last line is $p=3,e=6,n=9$, while the source lines are 3, 4, 5; lower addresses 0, 1, 2 all appear in the last line, with the copy mapping as follows:

$$
\varphi(0)=6,\quad\varphi(1)=7,\quad\varphi(2)=8,\quad
\varphi(x)=x+6\ (x\ge3).
$$

This covers all the necessary citations for the three source lines. Only the first one is checked here; it is not extrapolated to be replicable for any number of rounds.

The last item does not authorize the use of any $E(k)$ taken from this certificate. The fixed initial triplet 1-linedness and the condition "having the same endpoints for all finite $k$ are different conditions; the latter is data specifically provided in the original I2 full-parameter well-order manuscript. Finite-parameter quantitative recursion, when it is necessary to add $m$, is constructed by induction, extraction, and replacement of witnesses. It also does not directly treat the current $m=1$ as any parameter.

The old prefix is stopped line by line because Sat and the entry record is empty; each old line at that time only processes the frozen old marks, and the new native blocks are skipped. Therefore, a $M_\star$ only executes a single replication and a single finite scan, without any hidden "repetitive M until a certain type" reduction cycle. The geometric validity of the scan is given by the above whole package lemma, and no additional filtering is done after testing enumeration.

<a id="proof-section-5"></a>

## 5. fixes the termination of the calculation for E1／M／cut, and two different counts

Now fix an actual algorithm: two lines as endpoints; for the rest, first process the original non-replicable branches as cut, successor/limit takes $E(1)$, and the rest of the replicable items take $M_\star$. It is also allowed to actively choose cut at each non-endpoint; the following bounds hold for every such chosen path.

All points and owners remain in the same $\operatorname{Iter}(j)$. Let $\gamma_0<\gamma_1<\cdots$ enumerate its critical points, and denote the current cap as $\gamma_r$. Follow the convention of periodic thresholds.

$$
q(5)=\min\{m:\pi(m)\ge 2^5\},\qquad
\kappa_4=j(\gamma_4)=\gamma_{q(5)-1}.
\tag{5}
$$

The initial cap is $\theta_6=\gamma_{r_0}<\kappa_4$, therefore

$$
r_0\le q(5)-2.
\tag{6}
$$

Cut strictly reduces the cap, while the other steps mentioned above maintain the cap. Suppose the path contains $C$ cuts, all operations have$L$ operands, and the terminal cap is$\gamma_{r_{\rm end}}$.

$$
C\le r_0-r_{\rm end}\le r_0<q(5).
\tag{7}
$$

All operations cannot use this linear bound. Unless the terminal owner has a residue class of $a$ in the Laver quotient of size $2^r$, the critical points of the actual row are below the cap given by $1\le a<2^r$. Definition

$$
\Phi=2^{r+1}-a.
\tag{8}
$$

The finite Laver table satisfies $a<2^r$ with $a*_r b>a$. Therefore, a reduction of $M_\star$ strictly reduces $\Phi$; a reduction of $E(1)$ is a two-time application, and both intermediate and final critical points are below the cap, thus also strictly reducing. Cut reduces $r$ to $r'<r$.

$$
\Phi'\le2^{r'+1}-1\le2^r-1<2^r+1\le\Phi.
$$

Set the potential at the two endpoints to 0, and each edge still descends at least 1. This results in both termination and

$$
\boxed{L\le\Phi(S)<2^{r_0+1}\le 2^{q(5)-1}<2^{q(5)}.}
\tag{9}
$$

The complete counting argument for the positivity of finite table values and the quotient—application is provided in [Direct Step Bridge](<../iblp-laver-bms-20261013/direct-step-bridge.md>). Each complete scan of an individual completion event within does not count as a strict reduction step of (9); what is counted is the $E(1),M_\star,\mathrm{cut}$.

If it is necessary to count to an empty formula, four explicit unmarked steps can be added at the fixed first two lines:

$$
(01)(012)\to(01)(12)\to(01)(02)\to(01)\to\varnothing.
\tag{10}
$$

The final owners after the first two steps are $j(j)$ and $(j(j))(j)$, while the cap remains $\kappa_3$. The subsequent two cuts reduce the cap. The pointwise image of these four steps has been proven at [Short tail counting section 6](<short-tail-cofinality.md#proof-section-7>). Assigning a weight to the truly empty formula at 0, the same (7), (9) can be used for counting to the empty; the Sat theorem, which protects the first two lines, is not extended to the end of this section.

## 6. This is an intensity conclusion that has not yet been given.

A truly native and marked propagation mechanism has been established, which can still be naturally computed for a long time afterward. Unlike the old unowned zero port scheme, which loses its owner upon the first replication, it does not exceed the ordinary BLP row type like the short control lines of $L=2$.

However, each node with a fixed $E(1)/M_\star/\mathrm{cut}$ has only a finite number of children, and the finite depth of a given point with (9) is not automatically interpreted as the limit ordinal type of a BMS or IBLP. Similarly, (7) only gives an upper bound on the cut count, and it cannot be proven without a proof that all $M_\star$ counts are cut counts. To obtain a structural super-BMS numerical lower bound, a clear system of fundamental sequences with fixed indicators is also required, and the counting of their indicators up to this natural computation must be preserved in the simulation; or the required strength for the $E$ layer can be directly proven.

It is possible to invoke existing finite-parameter quantitative theorems to obtain another rigorous but non-comparable conclusion:

$$
q(5)>2^{f_\star(S,1)}.
\tag{11}
$$

The reason is that $S\in\mathcal C$ is given to $(\kappa_0,\kappa_1,\theta_6)$ as $f_\star(S,1)$-lined, and then the lemma of linedness using this theorem is applied along with $\theta_6<\kappa_4$. Here, $f_\star$ is a recursively defined computation that is not simply packaging unknown number of consecutive M into new "one-step basic columns". Before proving a lower bound for growth, (11) itself does not equal completing tasks that "exceed BMS".

**Independent audit.** t3_audit For a complete reading of the ordinary Sat, natural truncation, and auxiliary E, which are dependent on the latter, all row edges, Sat triples, and mark traces were recalculated independently. The conditions for valid short copies, the use of $E(1)$ in relation to 1-linedness, step-by-step finiteness, and the potential function count of (7)—(9) were also verified. The audit is consistent with this paper; no finite program examples were used to replace these full-bounded closure lemmas.
