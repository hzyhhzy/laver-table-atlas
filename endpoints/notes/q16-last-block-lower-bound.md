# The last linear block of Q(γ₁₆): advancing the available inputs to 65535 · [中文版](q16-last-block-lower-bound.zh-CN.md)

2026-11-09. Fix the critical spectrum of I3 embedding and the same Iter(j). This paper presents a new relative lower bound, but does not improve the already obtained explicit lower bound for natural numbers, `2^524288`. No translation or Lean proof is provided for the pure ZFC context.

## 1. Object, Conclusions, and Proofs Input

Let J₁=j, Jₐ₊₁=Jₐ(j) be defined. The parentheses between embeddings indicate application, and ordinary composition is written as ∘. Fixed

$$
N=256,\quad Q=J_{11}(J_3),\quad G=Q(j),\quad G_i=Q(J_i),\quad W=G_{13},
$$

$$
\mu=\gamma_N,\quad \zeta=\gamma_{N^2},\quad
\chi=Q(\gamma_4)=\gamma_s,\quad U=Q(\gamma_{16})=\gamma_u,
\quad\Theta=Q(\mu).
$$

For any actual embedding e, let fₑ denote its natural number spectrum indexing function: e(γᵣ) = γ_{fₑ(r)}. Hereinafter, we abbreviate it as f=f_G, and let

$$
a=f(N^2-N),\qquad b=f(N^2-1),\qquad c=f(N-1).
$$

The new conclusion is

$$
\boxed{G(\gamma_{65535})<Q(\gamma_{16}),}\tag{1}
$$

$$
\boxed{u\ge b+(s-c)a
\ge f(65535)+255\cdot256^{65535}.}\tag{2}
$$

Therefore, if it can be proven that f(k)>256ᵏ at some 1≤k≤65535, then the old bound can be strictly improved:

$$
\boxed{u\ge2^{524288}+2^{8(65535-k)}.}\tag{3}
$$

This paper does not prove that such a k already exists. By substituting the currently known f(k)≥256ᵏ, the (2) still yields the old u≥2^524288, rather than a new explicit value.

The mathematical research manuscript is as follows:

1. Q fixes γ₀, γ₁, Q(γ₂)=μ, Q(γ₄)=χ; the first two images of G are γ₁, μ, G(μ)=χ.
2. W(γ₀)=γ₁, W(γ₁)=χ, W(μ)=U, and U<Θ.
3. **G(γ₂)=ζ.** This is the proven eighth image/standard low point derivation, and cannot be guessed solely from the first two images of G.
4. Member truncation congruence J₁₂≡_μ j(J₂).
5. The first two images of Eᵣ=J_{2ʳ−1} are γᵣ and γᵣ₊₁.
6. General Indexing Count: The adjacent increment of each fₑ is at least fₑ(1)−fₑ(0). In particular,
fₑ(0)=1,fₑ(1)=m≥2 implies fₑ(r+1)≥m fₑ(r).

Input 1, 2, and see [The previous Q(γ₁₆) proof](q-gamma16-lower-bound.md). The dependency of input 3 is the adjacent research catalog [Proof of the Eighth Image](eighth-image-equality.md) and its actual embedding identification; this text uses it as a previously proven theorem. Input 4 and the member truncation rules are described in [Dougherty I, Section 5](https://arxiv.org/pdf/math/9205202). Input 5, 6 comes from [Dougherty II, Section 7](https://arxiv.org/pdf/math/9503204) and previous exponential counting derivations. The old bound s≥Nᴺ=2²⁰⁴⁸ is also used.

## Exact input transport of the amount of 2.256 times

Set D=G(j), note that D is generally different from G₂=G(G). Due to G≡_{γ₂}j, transport along G can be achieved.

$$
G_2\equiv_\zeta D.\tag{4}
$$

The critical point of D is γ₁, and the precise consistency gives

$$
D(\gamma_1)=\mu,\qquad D(\mu)=G(j(\gamma_1))=G(\gamma_2)=\zeta.
$$

D is fixed to γ₀. The index counting lemma gives at least N for each adjacent increment, and the total increment from input 0 to N is exactly N². Therefore, each step is taken to be equal:

$$
\boxed{D(\gamma_r)=\gamma_{Nr}\quad(0\le r\le N).}\tag{5}
$$

When r<N, the output is strictly less than ζ. Therefore, (4) can be read as

$$
G_2(\gamma_r)=\gamma_{Nr}\quad(0\le r<N).\tag{6}
$$

It is necessary to exclude r=N: the actual value is G₂(μ)=χ, not D(μ)=ζ, as the two are different.

Set A=G(G₂) back. Transport the input 4 along Q to obtain

$$
G_{12}\equiv_\Theta A,\qquad
W=G_{12}(G)\equiv_\Theta A(G).\tag{7}
$$

cr(A)=μ. For any **Ordinal number** α<μ, if A is fixed at α, then

$$
A(G)(\alpha)=A(G(\alpha))=G(G_2(\alpha)).
$$

Also, W(α)<W(μ)=U<Θ, therefore the output guard for (7) holds strictly, resulting in

$$
\boxed{W(\alpha)=G(G_2(\alpha))\quad(\alpha<\mu).}\tag{8}
$$

(8) does not hold only for critical points; it will be used at a non-critical supremum later on. Combined with (6), it yields a precise relationship for the entire segment.)

$$
\boxed{W(\gamma_r)=G(\gamma_{Nr})\quad(0\le r<N).}\tag{9}
$$

From the exponential count of W, immediately

$$
u\ge s\,f(65280),\qquad
u\ge s^{256-r}f(256r)\quad(1\le r\le255).\tag{10}
$$

Relying solely on (9), it is only possible to directly push the input of G to 65280. Now, we add the final 255 inputs.

## The non-critical supremum 3. provides the last block.

Take the actual finite left power

$$
E=J_{2^{255}-1},\qquad B=D(E).
$$

No need to elaborate on this term; only use the standard two images E(γ₀)=γ₂₅₅ and E(γ₁)=μ. Covariance and (5) give

$$
B(\gamma_0)=\gamma_{65280},\qquad B(\mu)=\zeta.
$$

The natural number index is strictly increasing. The length of the input interval is 256, and the length of the output interval is also 256. Therefore, no spectral points are skipped within the interval:

$$
B(\gamma_r)=\gamma_{65280+r}\quad(0\le r\le256).\tag{11}
$$

Specifically, B(γ₂₅₅)=γ₆₅₅₃₅.

Now define a strict image as a supremum.

$$
t=E(<\gamma_1)=\sup_{\alpha<\gamma_1}E(\alpha).
$$

This is an ordinal, **It is not declared as a critical point**. Since μ=E(γ₁) is a regular cardinal, the supremum only involves |γ₁|<μ values that are less than μ.

$$
\gamma_{255}<t<\mu.\tag{12}
$$

Apply D to the initial segment of E, the consistency of the strict supremum is given

$$
D(t)=B(<D(\gamma_1))=B(<\mu).
$$

Combining (11), (12),

$$
\gamma_{65535}<D(t)<D(\mu)=\zeta.\tag{13}
$$

The reading output of (4) is strictly less than that of (D(t)), which is less than that of (ζ), so it is less than (G₂(t)=D(t)). Using (8),

$$
\boxed{G(\gamma_{65535})<G(D(t))=W(t)<W(\mu)=U.}\tag{14}
$$

This proves (1). It does not prove G(γ₆₅₅₃₆)<U.

## 4. transform the last block into a numerical lower bound

Take H=W(E). Direct covariance is given as

$$
\operatorname{cr}H=\gamma_1,\quad H(\gamma_1)=W(\gamma_{255})=\gamma_a,
\quad H(\chi)=W(\mu)=U.\tag{15}
$$

It is necessary to have an exact intermediate image H(γ_c)=γ_b. The point value equation for (8) cannot be used as an application alone; a true member truncation consistency must be added.

From (7) and W(μ)=U<Θ, we have A(G)(μ)=U. The general approximation of Dougherty I

$$
e(f)\equiv_{e(f)(\operatorname{cr}e)}e\circ f
$$

Used for e=A, f=G, along with A∘G=G∘G₂, to give

$$
W\equiv_U G\circ G_2.
$$

Therefore

$$
H\equiv_U F:=G(G_2(E)).\tag{16}
$$

On the other hand, applying the right action of (4) to E, and then transporting along G, we obtain

$$
F\equiv_{G(\zeta)}F_0:=G(D(E))=G(B).\tag{17}
$$

Because γ_c=G(γ₂₅₅), (11) gives

$$
F_0(\gamma_c)=G(B(\gamma_{255}))=G(\gamma_{65535})=\gamma_b.
$$

This mathematical research manuscript is strictly below both G(ζ) and U, guaranteed by monotonicity and (14) respectively. Therefore, reading through (17) and (16) in sequence is legal. The resulting result is

$$
\boxed{H(\gamma_c)=\gamma_b.}\tag{18}
$$

H fixes γ₀, and sends γ₁ to γ_a, so each adjacent index increment is at least a. This fact is used between c and s, with (15), (18) giving

$$
\boxed{u\ge b+(s-c)a.}\tag{19}
$$

It is also possible to obtain b≥ca, but it does not provide a more explicit numerical value.

From the exponential recurrence of G, we have s=f(N)≥Nc; from the exponential recurrence of (9) and W, we get a=f(N²−N)=f_W(N−1)≥sᴺ⁻¹. Therefore

$$
(s-c)a\ge\frac{N-1}{N}s^N
\ge\frac{N-1}{N}(N^N)^N
=(N-1)N^{N^2-1}.
$$

Substituting (19) gives (2). All the objects being compared here are finite natural number spectra indexed.

## The sufficient condition for strict improvement of 5., as well as the parts that have not been proven yet

If a certain 1≤k≤N²−1 satisfies f(k)>Nᵏ, then it has integer properties and an exponential recurrence.

$$
b=f(N^2-1)\ge N^{N^2-1}+N^{N^2-1-k}.
$$

Substitute (2) to get

$$
u\ge N^{N^2}+N^{N^2-1-k},
$$

That is, (3). When k≤65280, it is advisable to switch to (10) to achieve a stronger increment.
`2^(8*(65536-k))`.

Therefore, if the old explicit bound happens to take the value u=2^524288, then it is necessary that

$$
\boxed{f(k)=256^k\quad\text{for all }0\le k\le65535.}\tag{20}
$$

This is a newly obtained necessary condition; the old derivation only forced the first 256 inputs to take equal values. Combined with another research catalog's [Minimum index image and full row homomorphism criterion](minimal-exponential-image-characterizes-hom.md), 20) also forces a specific block mapping Φ₂₅₆, ₆₅₅₃₅: A₆₅₅₃₆ → A_{256⁶⁵⁵³⁵+1} to maintain Laver operations. This paper does not prove the existence or failure of this massive finite homomorphism, and cannot be extrapolated by tests with smaller parameters.

It is particularly important to exclude one empty route: the premise of the old condition "J₁₃(γ₆₄)=γ_{4⁶⁴} then the main lower bound is strictly increased" has actually been excluded by J₁₃(γ₁₆)>χ≥γ_{2²⁰⁴⁸}. The adjacent research catalog has been clearly revised in [Audit Notes](audit-c16-and-source-A257.md). It cannot be used to determine whether the index image here, G, is invalid.

## 6. The practical meaning of checking records and finite search

- `check_q16_block_transport.py` checks the exact images of r=1, 2, and 255, as well as strict truncation guards.
The general entire formula is proven in section 2.
- `check_q16_supremum_window.py` uses non-critical suprems marked separately, verified (14),
H has three images, as well as strict output conditions for two different truncations, G(ζ) and U. The process involves: 45 names, 29 equivalence classes, 42 embedding terms, 213 image facts, and takes approximately 0.24 seconds. Regularity, standard Eᵣ formulas, and linear counting are explicit paper-based inputs, and the script does not replace these theorems.
- This round also attempted to create a partial catalog of actual words with the symbol 7637, as well as non-standard BLP patterns.
No new numerical bounds were found. All searches were conducted with a finite time and finite number of nodes; no optimality of all terms was established.

This document and audit script only contain content written to the current scratch directory. No large Laver tables were constructed, no old research documents were modified, and no repository was published.
