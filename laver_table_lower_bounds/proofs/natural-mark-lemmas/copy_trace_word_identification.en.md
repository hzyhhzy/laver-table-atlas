# Valid continuous copy actual transfer word: Independently combined lemma · [中文版](copy_trace_word_identification.reading.zh-CN.md)

*English reading edition, translated with machine assistance. The title links to the dated Chinese manuscript.*

> Collected reading edition. The three main papers state the results of this collection.
> This edition retains the local proofs, their hypotheses and any withdrawals. Progress reports describe the state of work at the time.
> The locations of omitted passages on preset inputs are recorded in SOURCE_MANIFEST.json.
> The main papers give the numerical derivations for the natural parameters produced by the proofs. This historical note carries no additional Lean certification.

2026-09-07. This lemma has been independently reviewed by another agent. It only identifies actual p chains, does not require the weak semantics of copied intermediate states to be established; nor does it use NC, Sat, internal adjacency, or RowAncestor.

## 1. input

The minimum entry of the core at the last line of activity n is c, the step size is L_n, and the replication root is a=p(n). The source line is a continuous interval [a,b), where b≤n+1; the replication map φ on each source core is defined and strictly increasing. The old prefixes 1,…,n−1 are retained, and the source line i is copied to

$$
\tau(i)=n+i-a=\varphi(i).
$$

Each mark's trace precisely hits its step-length source; the retention of marks follows the third branch and correct one-base guard in PDF section 10. The special copies in auxiliary E also satisfy these pure combinatorial conditions.

For a mark copied by the owner i, let the original word be

$$
T=(v_0,\ldots,v_{k-1},\delta).
$$

Here, δ represents the endpoints, and non-endpoint factors are not counted. Every non-endpoint v_h<i that is ≥a lies within the continuous source interval. The positions are maintained directly.

$$
p'(\varphi(v_h))=\varphi(p(v_h)).
\tag{1}
$$

Additionally, the activity map satisfies

$$
\varphi(x)=x\quad(x<c),\qquad
\varphi(x)>x\quad(x\ge c\text{ and is defined}).
\tag{2}
$$

The intermediate segment is strictly moved upward due to the positive step length, and the translation segment is strictly moved upward due to n−a>0.

## 2. All non-endpoints are in the replication segment

**Lemma.** if v_{k−1}≥a, then the actual new term is

$$
(\varphi(v_0),\ldots,\varphi(v_{k-1}),\varphi(\delta)).
$$

**Proof.** is used sequentially with (1). The step size threshold for the new mark is also φ(δ), so the last step, p, terminates at the right time. δ can be placed on either side of the root; there is no need to continue reading the line corresponding to the endpoint. The strictly increasing φ ensures that every previous node is still strictly greater than the endpoint. Proof complete.

## 3. low branch

Let y be the first non-terminal point below a in the original word, and let y<c be some value. Write the original word as a prefix P followed by the original segment.
$K=(y,\ldots,\delta)$.

The actual new term for **Lemma.** is φ(P) followed by K.

**Proof.** δ<y<c, so the threshold is fixed. The prefix is copied along the p edge until reaching φ(y)=y; all factor rows starting from y are <c≤a<n, belonging to the unchanged old prefix, continuing along the original p chain to δ. The same applies when P is empty. Proof complete.

## 4. plays a key role in high branching and guards.

Let the first low non-terminal satisfy c≤y<a; let z=φ(y). Keep the rule requirement that the active row must have a mark z. Its input trace is precisely

$$
D=(z,\ldots,s,y).
$$

Let the mark of the source owner i be at position q, and the step size be L_i. The original step size source δ is located at q−L_i. Let d be the closely following core entry, and positions q+1−L_i.

The legal mark satisfies q>L_i, so the guard position is at least 2, which is indeed the case; it also does not exceed q, so it is not a false condition that is omitted due to out-of-bounds. The correct PDF guard is indeed...

$$
\varphi(d)\le c.
$$

Obtained from (2)

$$
\boxed{\delta<d<c.}
\tag{3}
$$

In particular, the threshold for copying the mark, φ(δ), remains equal to δ.

The actual new term for **Lemma.** is

$$
\boxed{\varphi(P)\mathbin{\frown}(z,\ldots,s)
\mathbin{\frown}(y,\ldots,\delta).}
\tag{4}
$$

The prefix **Proof.** is copied through the prefix 1) to φ(y)=z. Due to y<a, z<n; all non-terminal points in the activity trace are also ≤z<n. Therefore, although the activity owner n has been deleted, each factor line required for reading D remains in the unchanged prefix, and the actual p chain is still precise from z to y.

Subsequently, y<a<n, the lines of the original tail section are also retained, continuing until δ. The nodes of the active section are all ≥y>δ, and the copied prefix nodes are all ≥n, so there will be no premature termination or confusion with the old section. The final threshold is determined by (3), which becomes δ. Equation (4) is removed at the end of the active section and then reattached to the old tail, so the splicing point y appears only once. When P is empty, the entire argument starts from z. Proof complete.

## 5.: Proven and Unproven Boundaries

Three lemmas cover each retained copy mark, thus legitimate continuous copies maintain "trace-precision definition," and provide their accurate actual meanings. Any fullcopy or shortcopy, as long as it uses the same mapping/screening and satisfies continuous legality, applies to this local combinatorial conclusion.

This does not prove that the new term is weakly equivalent to the copied owner at the required cutoff, nor does it prove that the internal +1 adjacency remains intact. Dangerous low seams may produce temporarily invalid marks; this lemma only ensures that the factors used to calculate the effective lower bounds and the subsequent repaired terms are indeed actual terms.

In section 2 of `internal_factor_floor4.md`, this lemma is applied. The historical lower bounds in section 7 still use the correct compTo geometry and real parallel new terms as interfaces; those overall completion obligations are not omitted here.
