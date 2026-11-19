# The temporarily bad markers after standardized replication can be repaired through a complete scan. · [中文版](copy_scan_mark_repair.md)

*English reading edition, translated with machine assistance. The title links to the dated Chinese manuscript.*

> Collected reading edition. The three main papers state the results of this collection.
> This edition retains the local proofs, their hypotheses and any withdrawals. Progress reports describe the state of work at the time.
> The locations of omitted passages on preset inputs are recorded in SOURCE_MANIFEST.json.
> The main papers give the numerical derivations for the natural parameters produced by the proofs. This historical note carries no additional Lean certification.

2026-09-07. This paper presents a true I3, Sat, Floor₂ input: its canonical short replication indeed produces a semantic error mark, which will be corrected by the full scan of the original PDF. Ultimately, the marked BLS is completely correct. There are no modifications to the marking rules, no deletions of bad marks, and no replacement of any row embeddings.

**Scope of application.** This indicates that when proving the overall closure of M_star, it is not necessary to consider the condition that "all marks that have not yet been scanned after replication are correctly marked." This manual input has not been proven to be standardly reachable, and therefore is not a counterexample to the standard replication closure.E Without performing this scanning, the necessary and sufficient criterion for Sep_a remains valid as before.

## 1. The precise maximum effective limit of the dangerous low seam

Let the active embedding of a valid short copy be E, the critical point be c=θ_C, and the root of the copy be a≥C. A certain old mark word W=P∘K, after a non-empty copied prefix P, receives the first lower factor w=C−1; it is below the critical index C, so the low branch of the PDF is retained with a mark. Assuming all internal adjacencies are valid, the actual word after copying is H∘K, where H=E(P). The old mark owner F only requires

$$
F\equiv_{\theta_{y+1}}P\circ K.
$$

The original mark is y≥a, and the copied initial requirement boundary is β=E(θ_(y+1)). Let

$$
\eta=H(c).
$$

**Theorem 1.1.** For each γ≤β, After replication, the owner E(F) and the actual word H∘K are weakly equivalent at γ. only when and only if γ≤η .

**Proof.** `E(K)≡_c K` gives

$$
H\circ E(K)\equiv_\eta H\circ K.
$$

The original 'mark' is applied with E, resulting in `E(F)≡_β H∘E(K)`. On the other hand, the original internal adjacency transport is `P(θ_(w+1))=θ_(y+1)`; θ_(w+1)=c, therefore

$$
\beta=H(E(c))>H(c)=\eta.
$$

Therefore, weak equivalence holds when γ≤η. To prove the reverse, let t be the last factor of K, b(t) be its next source, and z=θ_(b(t)). The original internal adjacency is given by the last endpoint edge.

$$
z<c,\qquad K(z)=c,\qquad E(z)=z.
$$

Therefore, `(H∘E(K))(z)=β`, and `(H∘K)(z)=η`. If η<γ≤β, then take the membership witness `(η,z)`, whose two coordinates both belong to V_γ; η belongs to E(F)(z), but does not belong to η itself. Hence, it is not equivalent at γ. Proof complete.

The η here is not some arbitrary lower bound that is merely sufficient: it is the **Exact maximum effective truncation** below the initial β of this dangerous mark. This conclusion extends the calculation of the dangerous seams of `limit_E_semantic_criterion.md` to general short copies with low branches; the copy root a can be strictly greater than the critical index C.

If the subsequent scans maintain the 'owner' and base row factor terms, and the cardinality is only inserted into the historical gaps of the target y, then the requirement for this mark is reduced from the original β to the current immediate successor cardinality. It will be correctly restored when the requirement is lowered to η or below. The initial β should not be considered as having already been valid historical certificates.

### The actual repair criterion for a single copied prefix factor

If P contains only one factor j_v, let its line number be V. The original internal adjacency is given to p(v)=C−1, b(v)=C, so the source gap of the copied line is `(C−1,φ(C))`. If this line is eligible, and the true source sequence of the native in this case is C, then the first new base inserted is exactly

$$
\theta'_{V+1}=H(\theta_C)=\eta.
$$

Therefore, the aforementioned old marks, which start with V, are restored to their correct form. If there is no native, or the first source is >C, and the posterior cardinality is still greater than η, then the witness of theorem 1.1 continues to refute this mark. This is a repair criterion with clear input and scanning conditions, and it does not assume that the standard history will necessarily choose this source.

## A complete I3 input is a 2..

Take any I3 embedding into j, and the critical sequence is κ_i. Use the ordinary composite power j^{∘r}, and let

$$
J_d=(j^{\circ d})(j),\qquad h=J_5\circ J_5,\qquad E=h(J_3).
$$

J_d fixes κ_i (i<d), and at i≥d, it sends κ_i to κ_(i+1). Therefore, h fixes κ₀, …, κ₄, and at i≥5, it sends κ_i to κ_(i+2). Apply the identity to

$$
\operatorname{crit}(E)=\kappa_3,
\qquad E(\kappa_3)=\kappa_4,
\qquad E(\kappa_4)=\kappa_7,
\qquad E(\kappa_7)=\kappa_8.                               \tag{1}
$$

Take θ_i=κ_i (0≤i≤8), the complete data for seven rows is

| i | Complete row | Step size | Embedding | mark |
| --- | --- | ---: | --- | --- |
| 1 | (0,1,2) | 1 | j | Just the translation; all original numbering symbols remain unchanged. |
| 2 | (0,1,2,3) | 1 | j | Just the translation; all original numbering symbols remain unchanged. |
| 3 | (0,1,2,3,4) | 2 | j^{∘2} | Just the translation; all original numbering symbols remain unchanged. |
| 4 | (0,1,2,3,4,5) | 2 | j^{∘2} | Just the translation; all original numbering symbols remain unchanged. |
| 5 | (0,2,3,5,6) | 2 | j^{∘3} | Just the translation; all original numbering symbols remain unchanged. |
| 6 | (0,1,2,3,4,5,6,7) | 4 | j^{∘4} | 5 |
| 7 | (3,4,7,8) | 1 | E | Just the translation; all original numbering symbols remain unchanged. |

The only trace marked with 'mark' is `(5,2,1)`, and the global word equation is j^{∘4}=j^{∘3}∘j. The internal adjacency requirement `3∈A_5` is indeed satisfied; both non-terminal factors are ≥2. m=1 is witnessed by j. The Sats in the 3, 5, and 6 rows are respectively B(2)=1, B(3)=2, and B(3)=2, all equal to the corresponding p. The remaining non-first lines are 'long' and not considered native. All ordinary BLP row types, critical points, and row edges are satisfied.

## The standard short replication of 3. indeed results in bad marks.

The last line's copy root is a=4, the next source is 7, and the smallest entry is C=3. The copy sources are 4, 5, 6, and the mapping...

$$
\varphi(x)=x\ (x<3),\qquad \varphi(3)=4,
\qquad \varphi(x)=x+3\ (x\ge4).
$$

The embeddings in the new rows 7, 8, and 9 are denoted as follows:

$$
R=E(j^{\circ2}),\quad H=E(j^{\circ3}),\quad G=E(j^{\circ4}).
$$

Define the following true embedding images, without numerical approximations:

$$
\alpha=E(\kappa_5),\quad \beta=E(\kappa_6),
\quad \eta=H(\kappa_3),\quad \zeta=G(\kappa_3).
$$

From (1) and application identities,

$$
H(\kappa_2)=\alpha,\quad H(\kappa_4)=\beta,
\qquad G(\kappa_2)=\beta,\quad G(\kappa_4)=\kappa_8.
$$

Strict monotonicity gives

$$
\boxed{\kappa_7<\alpha<\eta<\beta<\zeta<\kappa_8.}        \tag{2}
$$

The copied columns are in the order `κ₀,…,κ₇, α, β, κ₈`; the last three core items are

$$
\begin{array}{c|c|c|c}
\text{rows}&\text{core}&L&\text{mark}\\\hline
7&(0,1,2,4,7)&2&\varnothing\\
8&(0,2,4,8)&2&\varnothing\\
9&(0,1,2,4,7,8,9)&4&\{8\}.
\end{array}
$$

The actual trace of the new mark 8 is `(8,2,1)`. Its semantic requirements

$$
G\equiv_\beta H\circ j.
$$

But G(κ₂)=β, and (H∘j)(κ₂)=η<β, membership witnessing `(η,κ₂)` directly negates this statement. At the same time, `3∉A_8`, internal adjacency also fails temporarily. The correctness of inputting a marked BLS and the correctness of the ordinary row edges after replication cannot eliminate this failure of the mark.

On the other hand, G=H∘E(j) holds globally, and E(j)≡_(κ₃)j, so an exact lower bound is always retained.

$$
\boxed{G\equiv_\eta H\circ j.}                           \tag{3}
$$

## How to repair the original full scan of the 4. from the PDF

The first six lines are marked as "Sat" and have no records; they are retained as they are. The new line starting with "7" is labeled as "long" and is not considered a native entry.

The new line 8 is the middle line, with p=2 and the next source being 4. The actual chain that appears in the B line is

$$
4\longmapsto3\longmapsto2,
$$

Therefore, **Rec(8)=(3)**, native inserts the first cardinal number H(κ₃)=η. It is split into two lines:

$$
A'_8=(0,2,3,4,8),\ L'_8=3;
\qquad A'_9=(0,2,3,4,8,9),\ L'_9=3,\ M'_9=\{8\}.
$$

Both "owner" are H. The row with the old "mark owner" is moved to 10, and there are still "mark 8" and "word H∘j"; however, its requirement boundary is now θ₉=η. The formula (3) exactly satisfies it. At the same time, `3∈A'_8`, the internal adjacency is restored. The native from the factor row is repaired, and the compTo for this external mark is not called.)

When reaching the 10th line, its mark trace `(8,2,1)` queries Rec(2), and the record is empty, so the PDF does not add any points to it. The 10th line itself is a short line, p=2, the next source=4, then obtained from the same B chain as **Rec(10)=(3)**, inserted with G(κ₃)=ζ. The last two core lines are

$$
\begin{array}{c|c|c|c}
10&(0,1,2,3,7,8,10)&4&\{8\}\\
11&(0,1,2,3,4,7,8,10,11)&5&\{8,10\}.
\end{array}
$$

The final cardinal sequence is denoted as `κ₀,…,κ₇,α,η,β,ζ,κ₈`. These two lines have owner as G. Their old mark 8 is still used for (3), with the requirement boundary always being η; The trace of the new mark 10 is `(10,2)`, and it has two owners who are both G global witnesses. The new mark 8 in the 9 row is similar to the global equality witness in the H row. The prefix 'original' remains unchanged. All new and old rows, critical points, and marks thus hold true.

The program `check_copy_scan_mark_repair.py` directly uses precise short copies of the independent PDFs, as well as the original `_mark_completion` and `_native_completion`. It verifies all named row edges, source records, actual traces, cutoff indices, and final structures step by step, with the results stored in `copy_scan_mark_repair_checks.json`. The sizes and mapping values of α, η, β, and ζ are given by the aforementioned mathematical equations. The program does not make any guesses about unknown embedding values or approximate weak equivalents.

## The impact of 5. on the current proof outline

This example includes both Sat, Floor₂, input internal adjacency, and a true I3 implementation. Therefore, the following stronger requirements are not necessary to prove that the M_star semantics remains valid: all replicated outputs are complete marked BLS before the initial scanning. The final output of M_star can be restored to correctness by the original rules themselves.

There are two permitted proof paths for the standard domain: prove that it always avoids dangerous replication seams, or preserve an exact and valid bound η for temporarily invalid marks, and prove that a complete scan ultimately reduces the required bound to η. Both approaches must cover all original marks, and the system cannot be reduced by deleting unverified elements.

The second route also requires separate examination: whether the temporarily invalid mark will be used by compTo before restoration, and how multi-layer prefixes transport the initial repair points. In this example, the original low-end final factor 2 is located in a static old prefix, and Rec(2) is empty, thus preventing incorrect external completion. This is consistent with the general single M_star theorem for `scan_dependency_localization.md`. The repair of multi-layer prefixes still requires a true propagation certificate and cannot be generalized to a complete generating domain in this example.
