# Three smaller iterated endpoints below the full BLP endpoint · [中文版](lower-blp-points.zh-CN.md)

2026-11-09. Fix an I3 embedding j and work throughout in the same Iter(j) with critical spectrum γₙ. We give a paper proof and a finite algebraic audit.

## 1. Results and open comparisons

Write J₁=j and Jₐ₊₁=Jₐ(j). Parentheses between embeddings denote application. We use ∘ for ordinary composition. Put

$$
Q=J_{11}(J_3),\quad U=Q(\gamma_{16}),\quad
b=Q(J_7),\quad e=b(j),\quad \xi=b(\gamma_2),
$$

$$
\chi=Q(\gamma_4),\qquad \Sigma=J_{13}(\gamma_{16}).
$$

The three points have the shorter expressions

$$
\boxed{\nu_1=e(\gamma_{512}),\qquad
\nu_2=e(\gamma_{513}),\qquad
\nu_3=e(\gamma_{1024}).}
$$

They satisfy

$$
\boxed{\chi<\nu_1<\nu_2<\nu_3<\xi<\Sigma.} \tag{1}
$$

| Endpoint | Realized pattern | Lower bound on its critical index |
| --- | --- | --- |
| $\nu_1=\gamma_{v_1}$ | Three-row canonical $p_1$ with initial linedness 8 | $v_1\ge 2^{g^{[256]}(8)}>2\uparrow\uparrow259$, where $g(m)=m\cdot 2^m$ |
| $\nu_2=\gamma_{v_2}$ | Four-row $p_{\mathrm{start}}.\mathrm{del}$ with initial linedness 8 | $v_2\ge m_{\omega+2}(2)$, using the published transformation after reducing its parameter to 1 |
| $\nu_3=\gamma_{v_3}$ | Seven-row $p_{\mathrm{init}}$ with initial linedness 8 | $v_3\ge 2^{f(p_{\mathrm{init}},8)}$ |

The bounds concern the **natural-number critical indices** of the endpoints. Here m denotes Qi's Steinhaus–Moser hierarchy and f is the quantitative function for ordinary BLP.

We already know χ<U<Q(γ₂₅₅)<ξ. The order of U relative to ν₁, ν₂ and ν₃ remains open. Thus the three realized points lie below the full 25-row endpoint ξ. Whether they all lie above U, or whether their estimates improve the known bound on U, requires another comparison. The exact value of U also remains open. The explicit estimate is u≥2^524288, where U=γᵤ.

## 2. Applying the known entrance below its cutoff

The realized entrance

$$
q=J_{13}(J_{14})(J_{12}),\qquad q\equiv_\Sigma Q,
$$

$$
\mu=\gamma_{256},\quad \delta=q(\gamma_3)=\gamma_{257},\quad
q(\gamma_4)=\chi,\quad q(\mu)=\Sigma.
$$

Start with

$$
G=q(j),\quad G_2=q(J_2)=G(G),\quad
b_*=q(J_7),\quad e_*=b_*(j),\quad
\mathcal T=e_*(G_2),\quad H=\mathcal T(j).
$$

The known strict image identities are

$$
G:\gamma_0\mapsto\gamma_1\mapsto\mu\mapsto\chi,
\quad\operatorname{cr}e_*=\delta,
\quad e_*(\delta)=\chi,\quad e_*(\chi)=\xi,
$$

$$
\operatorname{cr}\mathcal T=\gamma_1,\quad
\mathcal T(\gamma_1)=\mu,\quad \mathcal T(\mu)=\xi,
\quad H(\gamma_0)=\mu,\quad H(\gamma_1)=\chi.
$$

The strict truncation readings of these entrances, the last point likeness, and the initial 8-line are described in [Full 25-row transport proof](notes/blp25-strict-transfer.md) §§1–4. It is not claimed that q=Q; in fact, it is q(μ)=Σ<Q(μ).

Put

$$
(\theta_0,\ldots,\theta_6)=
(\gamma_0,\gamma_1,\mu,\chi,H(\mu),H(\chi),H(H(\mu))).
$$

So, G sends θ₀, θ₁, θ₂ to θ₁, θ₂, θ₃ respectively; H sends θᵢ to θᵢ₊₂. Conformality also provides

$$
\theta_4=\mathcal T(\gamma_2),\qquad
\theta_6=\mathcal T(\gamma_4)<\mathcal T(\mu)=\xi. \tag{2}
$$

θ₀<⋯<θ₆ are all actual critical points.

## 3. Why the three inputs are exactly 512, 513 and 1024

[Proof for the final linear block](notes/q16-last-block-lower-bound.md), Section 2, gives

$$
G_2(\gamma_r)=\gamma_{256r}\quad(0\le r<256). \tag{3}
$$

This formula also applies to the lower entry points here: all the read values are strictly below Σ. Since e_* fixes γ₂ and γ₄, the covariance of the application and (2), (3) give

$$
\theta_4=e_*(\gamma_{512}),\qquad
\theta_6=e_*(\gamma_{1024}). \tag{4}
$$

Distinguish the intermediate point θ₅ from $\mathcal T(\gamma_3)$. Put

$$
D=G(j),\qquad A=G_2(j),\qquad \zeta=\gamma_{65536}.
$$

G₂≡_ζD, therefore A≡_ζD(j). The actual finite quotient standard form 2²⁵⁶−3 that already exists with G is applicable to this truncation (see [Normal-form proof, Section 4](notes/after-c6-supremum-lift.md)), thus

$$
A\equiv_\zeta J_{2^{256}-1}.
$$

[Dougherty II，Lemma 6.2](https://arxiv.org/pdf/math/9503204) takes the values of s=256 and n=8, and its valid range is the input r<512. In particular,

$$
J_{2^{256}-1}(\gamma_{257})=\gamma_{513}<\zeta,
$$

The output lies strictly below the cutoff, so we can read off

$$
A(\delta)=\gamma_{513}. \tag{5}
$$

Also e_*(j)≡_δj. Transporting along $\mathcal T$ and using left distributivity gives

$$
e_*(A)=\mathcal T(e_*(j))
\equiv_{\mathcal T(\delta)}\mathcal T(j)=H.
$$

Here, H(χ)=θ₅<ξ=$\mathcal T(\mu)$<$\mathcal T(\delta)$, so it remains a strictly protected read value. From χ=e_*(δ), (5) we get

$$
\boxed{\theta_5=H(\chi)=e_*(A)(e_*(\delta))
=e_*(A(\delta))=e_*(\gamma_{513}).} \tag{6}
$$

Finally, q≡_ΣQ maintains truncation in the first parameter of the application, hence e_*≡_Σe. All outputs of 4) and 6) are less than ξ<Σ, and e_* can be replaced back to the short word e. This proves that νᵢ=θᵢ₊₃ and (1).

## The pattern with three rows 4. has been provided for true iterative magnification.

On θ₀, …, θ₄, the actual owners are G, G, H:

| Research manuscript | Step size | owner |
| --- | ---: | --- |
| 012 | 1 | G |
| 0123 | 1 | G |
| 01234 | 2 | H |

This is the specification for p₁, and there is no need to construct the linedness pattern for 25. The initial θ₀, θ₁, θ₂ have linedness of 8. From [Qi, defined as 2.24, theorem 2.25, and lemma 2.5](https://arxiv.org/html/2501.06733v5), set g(m)=m·2ᵐ, we have

$$
f(p_1,8)=g^{[2^8]}(8)=g^{[256]}(8),\qquad
v_1\ge 2^{g^{[256]}(8)}. \tag{7}
$$

Here, $g^{[256]}$ represents the $g$ after the 256th iteration, where the input for each iteration is the output of the previous iteration.

Let $t_1=2$, $t_{r+1}=2^{t_r}$. Through the iteration from $8>t_2$ to $g(x)\ge 2^x$, we obtain $g^{[256]}(8)>t_{258}$. Taking the exponential with 2 as the base on both sides, we have

$$
\boxed{v_1>2\uparrow\uparrow259.} \tag{8}
$$

No calculations are performed for these enormous integers; (7), (8) are symbolic derivations.

## 5. Keep one more line and keep four more lines

Adding the owner H with 012345:2, we obtain the p_start.del on θ₀, …, θ₅. **It is not the canonical p₂.**: The last line of the specification p₂ is 01245:2.

These four lines are implemented under the initial parameter 8, and can also reduce the initial chain parameter to 1: According to the definition of Qi, the reduction parameter construction after 2.2, replace the two terms at the end of the chain lₘ₋₁ and lₘ with lₘ(lₘ)(lₘ₋₁), and repeat this process. Here, the term "application" is used, not simply replaced by a normal composition, and it is assumed that the first point is invariant. The Proposition 1.3(1) of Qi proves that there are fixed quartic M and cubic E(1), and transforms p_start.del into p_{ω+2}, retaining the end terms and parameter 1. Therefore, its Lemma 3.3...

$$
\boxed{v_2\ge 2^{f(p_{\omega+2},1)}=m_{\omega+2}(2).} \tag{9}
$$

This is the application of the public transformation to the already implemented low-end four-row pattern in this paper; it does not assume that all BLP operations with different initial parameters automatically have some unproven monotonicity, nor does it claim the exact values of f(p_start.del,8).

If we use θ₆, then we construct two internal points along the existing p_init, resulting in a complete p_init of seven rows. The last point remains θ₆=ν₃, and the initial parameters remain 8.

$$
\boxed{v_3\ge2^{f(p_{init},8)}.} \tag{10}
$$

All the sides of the seven rows and their owners are shown in the previous 25 row proof §4. The accompanying script verified this single segment. This article only takes three rows, four rows, and seven rows as entrances of different complexities. It does not claim which one is the smallest possible endpoint, nor does it assign an upper bound to their strength.

## 6. Verification Scope and Subsequent Issues

[check_lower_iteration_endpoints.py](checks/check_lower_iteration_endpoints.py) and [Running record](checks/check_lower_iteration_endpoints.json) have been verified:

- A short form identity with three points and a strict order;
- Old terms refer to the truncation guards at each output read from the lower entry point;
- Three lines of 8, four lines of 12, seven lines of 24 actual step sizes, and each line is critical.
- No crossing order has been assigned to the U and the three new points, resulting in all three comparisons remaining UNRESOLVED.

It runs for approximately 1 seconds, with 100 points of name, 50 owners, and 348 point-like facts. No huge Laver tables are calculated, and no long-term reductions are performed. The shift theorem, initial 8-line, BLP quantitative theorem, and standard form are derived from the aforementioned paper input; the script is not an independent formalization of these inputs.

The comparison between U and ν₁ will provide further insights. If ν₁≤U, then (7) will directly improve the lower bound of U. If U<ν₁, then ν₁ is a smaller iterative load point that is clearly higher than U and lower than the complete BLP endpoint ξ. Neither of these directions has been proven yet, and the stronger known lower bound of ν₁ cannot replace this comparison.

## 7. is rewritten as expressions with only subscript indices, using γ₅₁₂ and γ₅₁₃.

The two inputs can be written using small subscripts.

$$
\boxed{\gamma_{512}=\bigl(J_{13}(J_{15})\bigr)(\gamma_2),}
$$

$$
\boxed{\gamma_{513}=\Bigl(\bigl(J_{13}(J_{15})\bigr)(J_3)\Bigr)(\gamma_1).}
$$

More symmetrically, set R=J₁₃(J₁₅), K=R(J₃), then

$$
\boxed{\gamma_{512}=K(\gamma_0),\qquad\gamma_{513}=K(\gamma_1).} \tag{11}
$$

The proof only requires [Existing precise scaling conclusions, Section Four](notes/after-c6-supremum-lift.md):

$$
R(\gamma_r)=\gamma_{256r}\quad(0\le r<256).
$$

Here, the actual values taken are only r=0, 1, 2, and 3. All of them are strictly less than the truncated γ₆₅₅₃₆ used in the old proof. Also, J₃(γ₀)=γ₂ and J₃(γ₁)=γ₃ are taken. Therefore, the application is consistent.

$$
K(\gamma_0)=K(R(\gamma_0))=R(J_3(\gamma_0))=\gamma_{512},
$$

$$
K(\gamma_{256})=K(R(\gamma_1))=R(J_3(\gamma_1))=\gamma_{768}.
$$

K strictly increases the critical spectrum into the critical spectrum. Let K(γᵣ)=γ_{k(r)}, then k(0)=512, k(256)=768; the difference in the natural number indices of the input and output is also 256. Each increment is at least 1, therefore 256 steps must all increase by exactly 1:

$$
\boxed{K(\gamma_r)=\gamma_{512+r}\quad(0\le r\le256).} \tag{12}
$$

Taking r=1 gives (11). Here, the unprotected application is not treated as a regular composition, nor is the equal sign extended from "small parameter examples"; the index intervals are filled with precise values in the argument itself. The maximum explicit subscript for both notations is 15, and formulas with ν₁ and ν₂ can be directly substituted into them.
