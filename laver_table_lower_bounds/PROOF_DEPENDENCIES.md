# Proof dependencies and reading order · [中文版](PROOF_DEPENDENCIES.zh-CN.md)

The table lists the mathematical statements each proof uses. The working notes also record historical goals, finite tests, withdrawn candidates and stronger conjectures. The statements for the natural inputs are proved in the three main papers.

## 1. Results used from the literature

| Required result | Where it is used | Source |
| --- | --- | --- |
| Enumeration of the critical points for one generator, $\kappa_4=\gamma_{q(5)-1}$ | All three papers | Laver–Dougherty correspondence, Qi v5 |
| Standard finite chains and counts of critical indices | Papers 1 and 2, and initialization in Paper 3 | Dougherty I and II, and Qi's construction of a long chain |
| Finite point images, membership cutoffs and strict bounds on suprema | Realized endpoints in the three papers | Dougherty I, Section 5, Qi, Section 5 |
| The standard BMS well-order and parent-table formula | BMS counting argument and typed induction | Hunter, particularly Lemma 2.5 |
| Well-foundedness of bounded application at a common cap | Definedness of the finite-parameter construction | Steel's theorem as cited by Qi |

See the [bibliography](BIBLIOGRAPHY.md) for references and their precise scope. The local covers, forest construction, typed conditions, natural marks and parent-packet lemmas are proved separately in this collection.

## 2. Fixed-index counts in BMS

| Order | Mathematical statement | Proof |
| ---: | --- | --- |
| B1 | Standard parent table, aligned end columns for ancestor coverage, finite preparation, and replication seams | [Nonstandard row bound, Sections 2–5](proofs/output/new-notation-20260918/BMS-nonstandard-row-bound.md) |
| B2 | Covering maintains a fixed count, row width swapping | [Ancestor cover](proofs/output/iblp-laver-bms-20261013/ancestor-cover-growth.md) |
| B3 | One-line forest evaluation, $H_{W(M)}=F_M$ | [Exact growth comparison](proofs/output/iblp-laver-bms-20261013/fixed-index-growth-interface.en.md) |
| B4 | Activity root template, duplicate parent number, parameter forest restoration, and endpoint $e_y$ | [Forest controller](proofs/output/iblp-laver-bms-20261013/diagonal-forest-hardy-proof.md) |
| B5 | $r+1$ rows, $x+4$ columns, and logarithmic row loss | [Combined proof in this collection](common/bms-fixed-index.md) |

The result is $D(h)\ge e_{F_{B_r}(x)}$. These lemmas do not use I3 or Laver notation. [Minimal dependencies of the original argument](proofs/output/iblp-030-laver-20261014/FGH-standalone-dependency-audit.md) explains why B1 cannot be omitted or the terminal tower function discarded.

## 3. Paper 1. Closed syntax, comparison at finite types and the six-level realization

1. **The safe class and the underlying BMS.** [Classification of positive interfaces](proofs/output/iblp-01-equality-20260923/IBLP-01-unconditional-BMS-lower-bound.md) → [Closure without completion](proofs/output/iblp-01-equality-20260923/IBLP-01-no-completion-proof.md) → [A BMS upper cover for every term in the safe class](proofs/output/iblp-01-equality-20260923/IBLP-01-BMS-upper-bound.md). Additionally, there is [Ancestor ribbon lower bound](proofs/output/iblp-bms-20260918/IBLP-01-BMS-lower-bound.md).
2. **The original fundamental sequences.** Sections 1–3 of [Commutation with substitution at the first root](proofs/scratch/iblp030-8h-20261015/hardy-root-continuation-interface.en.md) lead to Sections 1–4 of [Closed finite syntax and an exact rank for the descent tree](proofs/scratch/iblp030-8h-20261015/hardy-root-first-root-tower.en.md). We omit the old initialization withdrawn in Section 5 of the latter paper.
3. **Numerical comparison uniformly in every argument.** [Base Hardy cover](proofs/scratch/iblp030-8h-20261015/hardy-root-bms-interface.en.md) in the 2–4 section, [Relative oracle](proofs/scratch/iblp030-8h-20261015/hardy-root-oracle-upper.en.md) in the 3–4 section → [Typed upper bound](proofs/scratch/iblp030-8h-20261015/hardy-root-typed-bms-bound.en.md), [Tail locality](proofs/scratch/iblp030-8h-20261015/hardy-root-tail-locality.en.md), [Same-input comparison and seed paths](proofs/scratch/iblp030-8h-20261015/hardy-root-fast-type1-C3.en.md) → [Fourfold bound for the whole object](proofs/scratch/iblp030-8h-20261015/hardy-root-low-stack-numeric.en.md).
4. **Realized fans and the ribbon construction.** [Front insertion](proofs/output/iblp-laver-bms-20261013/lined-front-insertion.md) → [Low-open fan and all implicit edges](proofs/scratch/iblp030-8h-20261015/lift-low-open-fan-and-typed-gap.en.md) → Sections 1–5 of [Spare ribbon and endpoint repairs](proofs/scratch/iblp030-8h-20261015/lift-participating-bms-spare.en.md) → Sections 2–4 of [Natural relative BMS construction](proofs/scratch/iblp030-8h-20261015/lift-natural-relative-bms-oracle.en.md). The construction uses induction on the known BMS well-order. It does not use the candidate rank in the older spare-ribbon note.
5. **Typed entrances and their geometric compatibility.** [Mixed base entrance](proofs/scratch/iblp030-8h-20261015/lift-mixed-base-type1-seed.en.md), [Second-type entrance](proofs/scratch/iblp030-8h-20261015/lift-type2-entry-relaxation.en.md), [Strict cap](proofs/scratch/iblp030-8h-20261015/root-low-Q11-strict-cap-proof.en.md), [Endpoints at four types](proofs/scratch/iblp030-8h-20261015/lift-low-four-type-staircase.en.md), [Compression to six levels](proofs/scratch/iblp030-8h-20261015/lift-low-compressed-six-type-staircase.en.md).
6. **Assembly and the natural input.** Sections 3–7 of [C7 combined proof](proofs/scratch/iblp030-8h-20261015/hardy-root-C7-q5-single-file.en.md) give the actual $Y$-line. Sections 3–5 of [main paper](01-blp-tower.md) give the full numerical derivation of $M=\mathcal Q(1)$.
7. **FGH.** Sections 2–4 of [Conversion between inputs](proofs/scratch/iblp-I-to-I0-20261016/port-FGH-existing-bound-C6.en.md) prove $G_Q^h(y)\ge F_Q(x)+1$ for each case ($y\ge x+1$). The main paper uses $x=M-1,y=M$.

## 4. Group 2: Entrance fans, dynamic depth, and reinforcement initialization

| Required result | Proof |
| --- | --- |
| Three-column weak band, finite initialization, first round, and step-by-step feedback | [Single-file proof, section 3–8](proofs/output/iblp-030-laver-20261014/q5-BMS-successor-single-file-proof.md) |
| Strict image comparison at the lower exit promoter | [Short transport endpoints](proofs/output/iblp-030-laver-20261014/small-period-endpoint-Sf.md), [Second-round transport](proofs/output/iblp-030-laver-20261014/promoted-bms-feedback.md) |
| Naturalness of the entire background for any actual entrance | [Recursive corridor](proofs/output/iblp-030-laver-20261014/small-period-recursive-corridor.md), [Paragraph-by-paragraph feedback](proofs/output/iblp-030-laver-20261014/lined-feedback-corridor.md) |
| Dynamic depth unification with low exits and re-ascension | [Proof of the dynamic depth bound](proofs/output/q5-further-bound-20261014/dynamic-depth-Lambda-omega-successor.md) |
| Nine seeds and all ordinary edges, Sat, marks | [L3 Native Construction](proofs/output/iblp-030-laver-20261014/ordinary-l3-native-mark-seed.md), [Complete Certificate](proofs/output/iblp-030-laver-20261014/same-owner-L3-sat-closure.md) |
| Parent package scanning and finite parameter recursion | [Selector](proofs/output/iblp-030-laver-20261014/parent-packet-propagation-selector.md), [Quantitative parent-packet lemma](proofs/output/iblp-030-laver-20261014/parent-packet-quantitative-transfer.md) |
| $H_0=u_{\omega^\omega}$ | [Pure E reduction](proofs/output/piblp-external-FGH-20261014/P4-pure-E-collapse.md) and its four-step calculation baseline |
| Simplified and shared port input | [Finite-level FGH initialization](proofs/output/q5-further-bound-20261014/P5-uniform-and-large-input.md), [Strengthening through shared ports](proofs/output/q5-further-bound-20261014/active-port-stronger-initialization.md), [Function substitution](proofs/output/piblp-external-FGH-20261014/active-E-graft-functional-substitution.md) |

The direct long-chain version does not invoke the parent package reinforcement initialization chain for the last four lines. Its natural $z_{\rm dir}$ is merely the maximum solution for a clearly finite integer budget.

## 5. Group 3: Original forest entrance, natural mark, and integer counting

| Required result | Proof |
| --- | --- |
| All roots are owners, endpoints are packages, and long chain transports | [Actual entry, section 1–6](proofs/scratch/iblp-I-to-I0-20261016/local-budget2-initializer.en.md) |
| The $2^L-1$ segment of the root shadow | Section 15 of this manuscript, Section [The prefix is retained for chain multiplication.](proofs/scratch/iblp-I-to-I0-20261016/local-budget-algebra.en.md), Section 3 |
| Original forest, first-round scanning exchange, $R[k][n]$ quietness | In sections 2, 4, 5, and [Double chain quiet](proofs/scratch/iblp030-8h-20261015/original-audit-two-chain-quiet-cone.en.md) of [Original Forest](proofs/scratch/iblp030-8h-20261015/original-audit-root-forest-interface.en.md), |
| Single tail packet and shadow transport of complete adjacent parent blocks | [shadow forest](proofs/scratch/iblp-I-to-I0-20261016/local-budget2-shadow-forest.en.md) |
| Factor physical successor closure, membership repair | [Extraction theorem](proofs/scratch/iblp-I-to-I0-20261016/marked-entry-extraction.en.md); The main text is also fully presented in section 5 |
| First-round complete family, second-round all-high, and closed induction | [Natural Entrance](proofs/scratch/iblp-I-to-I0-20261016/marked-entry-initializer.en.md) |
| Short copy of the paper, frozen scanning, Sat and accurate marking | [Natural Mark Local Lemma Index](common/natural-marks.md) |
| Finite tables strictly increase, cut, and the last four steps | [Integer potential bridge](proofs/output/iblp-laver-bms-20261013/direct-step-bridge.md), [Short tail interface section 6](proofs/output/iblp-030-laver-20261014/short-tail-cofinality.md), re-proved in section 7 of the main text |

The indexed entries of [Original synthesis draft](proofs/scratch/iblp-I-to-I0-20261016/marked-entry-total-bound.md) and the local closures are still dependent; the new main text directly uses the actual chain length, taking $k=2^L,n=2^{2^L-1}$. After the second initialization, the assumption of infinitely reproducible shadows is no longer made.

## 6. originates from historical content and has been subject to limited verification.

[Index of the entire manuscript](proofs/README.md) includes auxiliary lemmas and local cross-audits.[SOURCE_MANIFEST.json](SOURCE_MANIFEST.json) records the manuscript hash, organized version hash, omitted line numbers for fixed input historical paragraphs, and links to the organization.

The source manuscript may also refer to unrecorded historical scripts, other notations, and failed routes. These are not considered prerequisites for the above interface. The global I2 standard domain theorem is also not a hidden assumption of the three main texts.

Finite verification does not replace standard coverage preparation, forest compilation, actual embedding legality, type quantifiers, or natural mark closures in any universal proof.
