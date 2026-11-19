# Natural cutoffs, transport of marks and the local lemmas used in the proofs · [中文版](natural-marks.zh-CN.md)

These lemmas are used for the marked process in the third paper and the initialization of the parent-packet recursion. They give the actual hypotheses at each use of closure.

## 1. Certificates

A row core is a strictly increasing sequence of integers. Its implicit last point is the next physical column. An owner in the common $\operatorname{Iter}(j)$ realizes both the step edges and the critical point named by the least entry. Marks are proper, and each actual $p$-trace reaches its paired source exactly.

For the word of nonterminal factors $W=F_{v_0}\circ\cdots\circ F_{v_{d-1}}$, define

$$
\Delta(W)=(F_{v_0}\circ\cdots\circ F_{v_{d-2}})(\theta_{v_{d-1}+1}).
$$

The carrier must satisfy $F_r\equiv_{\Delta(W)}W$, where $\equiv$ denotes membership truncation. The natural cutoff satisfies

$$
\theta_{v_0}<\Delta(W)\le\theta_{v_0+1},\qquad
\Delta(P\circ W)=P(\Delta(W)).
$$

Section 1 proves these identities factor by factor. The following sections check the full, low and high copy branches with the appropriate paper guard. [Natural cutoff lemma](../proofs/natural-mark-lemmas/natural_trace_cutoff_semantics.en.md)

## 2. Identifying the copied word

The proof follows the actual $p$-chain and identifies the full-factor copy, the old low tail word and the mixed high branch individually. It derives their identification without assuming the mark semantics to be proved. [Identification of copied words](../proofs/natural-mark-lemmas/copy_trace_word_identification.en.md)

This identification permits transport of the old natural cutoff by embedding application. It also distinguishes the legacy filter on a mixed branch from the paper guard.

## 3. Sat and transport of a packet within a scan

For an ordinary eligible row, Sat means $B(e(v))\le p(v)$. For an internal factor $v\to w$ at which the scan actually reads a nonempty record, the entrance must satisfy

$$
p(v)=w,\qquad B(e(v))\le w.
$$

The packet theorem proves width monotonicity, shows that each internal connection is empty or complete, and then inducts over the full frozen scan. This permits more than immediate internal adjacency while retaining the internal packet condition. [Sat packet theorem](../proofs/natural-mark-lemmas/sat_endpoint_packet_theorem.en.md)

The second half of the natural-cutoff proof uses the transport of realized packets to establish the values read by completion, the edges of new rows and the semantics of the new marks. This and the packet theorem provide different parts of the argument. [Natural cutoff semantics](../proofs/natural-mark-lemmas/natural_trace_cutoff_semantics.en.md)

The other steps of the finite scan use the following lemmas.

- [Interval of marked completion](../proofs/natural-mark-lemmas/marked_completion_interval_lemma.en.md)
- [Commutation of multiple marked completions](../proofs/natural-mark-lemmas/multiple_mark_completion_commutation.en.md)
- [Repairing marks after copying and scanning](../proofs/natural-mark-lemmas/copy_scan_mark_repair.en.md)
- [Preservation of the ordinary domain and Sat](../proofs/natural-mark-lemmas/marked_blp_order_domain.en.md), especially Section 9
- [Natural cutoffs for the auxiliary $E$ rule and extraction of a successor block](../proofs/natural-mark-lemmas/marked_E_transfer_work.en.md), Sections 2, 3 and 7

## 4. Quantification over a finite parameter

The quantitative lemma combines these local results into a growth computation at the current finite parameter $m$ of linedness. Extraction at a successor preserves every factor and its natural cutoff. The actual output of the first half-block may supply the next parameter. The proof does not require joint witnesses for arbitrarily large parameters at the original triple. [Finite-parameter quantitative lemma](../proofs/output/iblp-laver-bms-20261013/marked-BLP-quantitative-transfer.md)

The parent-packet variant uses the new family of the direct parent row to ensure packet transport. Its scan therefore has a different rule from the ordinary scan. [Parent-packet selector](../proofs/output/iblp-030-laver-20261014/parent-packet-propagation-selector.md) · [Finite-parameter parent-packet lemma](../proofs/output/iblp-030-laver-20261014/parent-packet-quantitative-transfer.md)

## 5. Scope of the local results

An archived synthesis also argues for well-ordering of the full standard domain using I2 and witnesses for every finite linedness parameter at one endpoint. Here the three principal theorems use only the proved local row edges, scan properties and Sat interfaces, together with finite realized certificates in ZFC + I3.

The third paper spells out the extraction closed under physical successors of factors and the finite-table potential. Semantic closure and a numerical bound on the running time require separate arguments. [Marked-step proof](../03-iblp-modify.md)
