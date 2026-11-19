# The quantitative lower bound of Q(γ₈) and the current limit · [中文版](q-gamma8-lower-bound.zh-CN.md)

2026-11-09. Fixing the same I3 into j; this paper presents a paperproof in the context of elementary embeddings. No new formalizations in Lean are added, nor is any finite table translation completed that is independent of I3.

Let J₁=j, Jₐ₊₁=Jₐ(j), the brackets between embeddings represent application. γ₀, γ₁, … are the increasing enumeration of critical points of Iter(j). Define

$$
 Q=J_{11}(J_3),\qquad G=Q(j),\qquad
 \chi=J_{11}(\gamma_3)=\gamma_s,\qquad
 T=Q(\gamma_8)=\gamma_t.
$$

**This round is strictly obtained**

$$
 \boxed{t\ge256s\ge2^{2056}.} \tag{A}
$$

The comparison here is the natural number spectrum with subscripts s, t, and does not confuse the uncountable ordinal T with finite integers. There is already an s≥2²⁰⁴⁸; (A) provides a new relative scaling factor, but not just an χ<T. Currently, there is no proof for the exact value, numerical upper bound of t, or the lower bound of the ten-layer ordinary exponential tower.

There are two other matching results:

$$
 G(\gamma_{256})=\chi,\qquad G(\gamma_{257})=T, \tag{B}
$$

$$
 \chi<Q(\gamma_8)<Q(\gamma_{16})<Q(\gamma_{255})
   <(Q(J_7))(\kappa_2)<\Sigma,
 \qquad \Sigma=J_{13}(\gamma_{16}). \tag{C}
$$

The second equation of (B) refers to the paper theorem previously presented in (J₁₂(γ₅)=γ₂₅₇; (A) does not require this theorem at all. In (C), (Q(J₇))(κ₂) represents the carrying endpoint of the existing complete 25 row ordinary BLP pattern. Being below this endpoint does not prove that the value of T is lower than the BLP/BMS level, as what is known about it is its lower bound.

## The strict meaning of the input of the item 1. and the application

The following standard minor items are provided:

$$
 \kappa_0=\gamma_0,\quad\kappa_1=\gamma_1,\quad
 \kappa_2=\gamma_2,\quad\kappa_3=\gamma_4,\quad\mu=\gamma_{256};
$$

$$
 J_{11}(\kappa_0)=\kappa_2,\quad
 J_{11}(\kappa_1)=\kappa_3,\quad J_{11}(\kappa_2)=\mu;
$$

$$
 \operatorname{cr}J_3=\kappa_0,\quad
 J_3(\kappa_0)=\kappa_2,\quad J_3(\kappa_1)=\gamma_3;
$$

$$
 \operatorname{cr}J_{14}=\kappa_1,\quad
 J_{14}(\kappa_1)=\kappa_3,\quad J_{14}(\kappa_2)=\gamma_8.
$$

Source: [Dougherty I, Section 5](https://arxiv.org/pdf/math/9205202); [Dougherty II, Section 8](https://arxiv.org/pdf/math/9503204). Use precise consistency.

$$
 (a(b))(a(x))=a(b(x)),\qquad
 \operatorname{cr}(a(b))=a(\operatorname{cr}b).
$$

Thus obtained

$$
 \operatorname{cr}Q=\kappa_2,\quad Q(\kappa_2)=\mu,\quad
 Q(\kappa_3)=\chi.
$$

Q is fixed to κ₀, κ₁. Therefore, the four-point chain of G=Q(j) is

$$
 G:\kappa_0\longmapsto\kappa_1\longmapsto\mu\longmapsto\chi. \tag{1}
$$

Let H=Q(J₁₄). It has the following exact points:

$$
 \operatorname{cr}H=\kappa_1,\quad H(\gamma_0)=\gamma_0,
 \quad H(\gamma_1)=\chi,\quad H(\gamma_{256})=T. \tag{2}
$$

For example, the last formula is H(Q(κ₂))=Q(J₁₄(κ₂))=Q(γ₈), which does not cross any unknown truncation points.

## 2. Universal Numerical Lemma and Proofs for (A))

For the embedding e, write e(γᵣ)=γ_{f(r)}. The Dougherty II Lemma 7.1 is given as

$$
 f(n)\ge f(0)+n\bigl(f(1)-f(0)\bigr). \tag{3}
$$

The following rephrases the required counting argument. Taking r≥1 as Eᵣ=J_{2ʳ−1}, we have Eᵣ(γ₀)=γᵣ,Eᵣ(γ₁)=γᵣ₊₁). Therefore, e(Eᵣ sends the [γ_{f(0)},γ_{f(1)}) range of f(1)−f(0) critical points strictly increasing into [γ_{f(r)},γ_{f(r+1)}). Thus, f(r+1)−f(r)≥f(1)−f(0). Adding these term by term gives (3). All points lie in the same critical spectrum.

A direct corollary is: If f(0)=1, f(1)=m≥2, then

$$
 f(r+1)\ge m f(r)\quad(r\ge1),\qquad f(r)\ge m^r. \tag{4}
$$

Proof: Let Aᵣ=e(Eᵣ). Its critical point is γ₁, so Aᵣ is fixed by γ₀; the consistency property gives Aᵣ(γ₁)=γ_{f(r)}, Aᵣ(γₘ)=γ_{f(r+1)}. For Aᵣ, applying (3) at the input m yields the previous equation; this can be generalized from f(1)=m.

Translate the following mathematical research manuscript as follows:  
4) is used for G, (1) is given to m=256, and f(256)=s. Therefore

$$
 s\ge256^{256}=2^{2048}.
$$

Use (3) for H, and (2) for the rest.)

$$
 t=f_H(256)\ge256f_H(1)=256s\ge2^{2056}.
$$

This proof relies on (A)), and does not depend on computational examples, optimality conjectures, or complete recursion for BLP.

It can also be proven using actual homologous chains: there is a chain from κ₁ to μ with a segment of 8 rooted in κ₀; through four-point magnification by G, a chain of 2048 segments is obtained from κ₁ to χ; by transporting the original segment of 8 through H, a chain of 8 segments is created from χ to T, which can be concatenated to form a segment of 2056. Each new segment will at least double the existing critical number, thus the relative conclusion of t≥2⁸s remains valid.

## Why is 3. exactly the adjacent two inputs of G?

Let b=J₁₂, U=b(b). The left distributive law gives Q=U(b), and cr U=γ₄. Given b(γ₃)=γ₅. U fixes γ₃, from two times of co-variance, it follows that

$$
 Q(\gamma_3)=U(b(\gamma_3))=U(\gamma_5)
 =b(b(\gamma_3))=b(\gamma_5)=\gamma_{257}. \tag{5}
$$

The final equal sign is denoted by [Complete paperproof of J₁₂(γ₅)=γ₂₅₇](j12-j15-k1-equals-gamma257.md). This proof involves finite tableaux blocks and strict truncation; it is not considered as a minor exception in this paper.

j(γ₃)=γ₈ and G=Q(j) therefore provide

$$
 G(\gamma_{257})=G(Q(\gamma_3))=Q(j(\gamma_3))=Q(\gamma_8)=T.
$$

Combining (1) yields (B). The general recurrence (4) only ensures multiplication with 256 at this step; it does not guarantee exponentiation, fourth-order operations, or higher-level transitions. This does not exclude theorems with stronger lower bounds; in reality, (G may have additional structures that are not utilized in the recurrence.

## 4. completes the order between the two candidates and the old BLP endpoints

Using the actually proven new entrance previously

$$
 q=J_{13}(J_{14})(J_{12}),\quad
 q\equiv_\Sigma Q,\quad q(\gamma_{256})=\Sigma,
 \quad q(\gamma_4)=\chi,
$$

Here, 'application' is combined to the left, and '≡' indicates a membership relationship truncation. Let's denote by b₀=q(J₇) and ξ=b₀(κ₂). It is already known that χ<ξ<Σ exists.

Let σ=j(<κ₁) be defined. The previous calculations of strict supremum provided

$$
 \kappa_1<\sigma<\kappa_2,\qquad
 \gamma_{255}<J_{11}(\sigma)<J_7(\sigma)<\gamma_{256}. \tag{6}
$$

γ₂₅₅<J₁₁(σ) refers to [The 2 section of the single-layer exclusion](single260-exclusions.md); J₁₁(σ)<J₇(σ) refers to [New Entrance Proof Section 4](entry-and-parametric-fgh-bound.md). These are inequalities for non-critical ordinals; σ is not considered a critical point.

q is fixed by σ, therefore precise consistency is given

$$
 q(\gamma_{255})<q(J_7(\sigma))=b_0(\sigma)
    <b_0(\kappa_2)=\xi. \tag{7}
$$

All outputs for reading purposes are strictly less than Σ. Therefore, q(γᵣ) = Q(γᵣ) holds for 5≤r≤255; and ξ=(Q(J₇))(κ₂). Strict monotonicity combined with (7) results in (C). The notation q=Q is not considered a global identity; in fact, q(μ)=Σ<Q(μ).

## The current numerical scale of 5. is incomplete.

2²⁰⁵⁶ is an integer with the value of 619. This proven lower bound is still less than 2↑↑5; therefore, it cannot be inferred from this statement to be t≥2↑↑10, let alone to be a lower bound for Ackermann or BMS levels. This statement merely describes the lower bound itself and is not an assertion of an upper bound for t<2↑↑5.

If we use F₀(n)=n+1, Fᵣ₊₁(n)=Fᵣ for the n+1 iteration, then F₂(n)=(n+1)2ⁿ⁺¹−1, and thus this paper also presents F₂(2044)<t. It's just a rewrite of the same bounds, not an improvement in the FGH level.

If t=2²⁰⁵⁶, then (A) forces s=2²⁰⁴⁸, and the linear count of H becomes equal. The equality of s is not yet determined, so it is not claimed that t is equal.

To significantly improve, what is currently lacking is the ability to achieve stronger iterable configurations below T, or to have additional significant jumps in authentication between the 256th and 257th images at G. It is known that the carrying endpoint of the complete BLP configuration at ξ cannot be directly transferred as a lower bound for T after T.

## 6. bounded program audit

`check_q8_lower.py` checks the actual point images of (1), (2), the precise LD aliases, the small patterns used in the two lower bound arguments, and the covariant derivations of (B)). The program will publicly disclose the details of the sub-items and clearly mark J₁₂(γ₅)=γ₂₅₇ as paper input. It does not replace the general counting lemma in section 2 or the supremum proof in section 4 with finite tests.

`probe_q8_lines.py` undergoes transport, concatenation, and chain multiplication searches within a finite catalog composed of 94 actual embeddings and 274 partial image contours. The longest derived chain is 2056 segments. No standard p₂ configuration was found. This is a search record, not a proof of optimality or impossibility. The actual time taken is less than 1 seconds, and there is no expansion of a huge Laver table or long-term degradation.

All new files are written to the current research directory only; the old research and release repositories remain unchanged.
