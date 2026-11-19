# An audit of the old sixteenth image, as well as a 257 order source product · [中文版](audit-c16-and-source-A257.zh-CN.md)

2026-11-09. The embedding of fixed I3 is presented. The main problem remains unresolved.

## 1. excludes a research premise that is now impossible to establish

Follow the conventions of $C=J_{13}$, $K=J_{11}$, $\chi=K(\gamma_3)=\gamma_s$, and $T=2^{2048}$. The old document after-c6-supremum-lift.zh-CN.txt, Section 1, has already listed these conventions.

$$
\gamma_T\le\chi<C(\gamma_{16}).
\tag{1}
$$

The input does not depend on the sixth image equivalence; the original source can be found as exclude-2pow2048-rigidity.zh-CN.txt and the REPORT.zh-CN.txt that is only adjacent to the read-only directory.

Therefore, the premise discussed later by c64-equality-would-refute-main.zh-CN.md, that is $C(\gamma_{64})=\gamma_{4^{64}}$, can no longer hold. Specifically, let $f_C(r)$ be the spectral index of $C(\gamma_r)$; the exponential recursion is given as

$$
 f_C(64)\ge4^{48}f_C(16)
 \ge4^{48}(s+1)\ge2^{96}(T+1)>4^{64}.
\tag{2}
$$

The original condition implies no logical error. However, the research route is empty; It should not be continued to be listed as an unresolved test. It has been proven that $f_C(r)=4^r$ holds for $r\le12$. Therefore, the first failure point is unconditionally located at $13,14,15,16$ China. This fact still does not refute the main equality sign: The sixteenth image is above $\chi$.

## 2. precise source product

In the usual forward representation $0,\ldots,2^{257}-1$, there is

$$
\boxed{1*_{257}2=2^{256}+12.}
\tag{3}
$$

Proof uses two existing low points as inputs:

$$
 j(J_2)\equiv_{\gamma_{256}}J_{12},\qquad
 J_{12}(\gamma_4)=\gamma_{256}.
\tag{4}
$$

The first is the $j(j^{(2)})$ approximation from Dougherty I's 5 section, and the second is the low point determined by Dougherty II in the 8 section. Therefore, the 3) on the left side in the $A_{257}$ is only possibly $12$ or $2^{256}+12$.

On the other hand, $j(\gamma_2)=\gamma_4$, $J_2(\gamma_2)=\gamma_4$, thus covariance gives

$$
 j(J_2)(\gamma_4)
 =j(J_2)(j(\gamma_2))
 =j(J_2(\gamma_2))=j(\gamma_4)=\kappa_4
 >\gamma_{256}.
\tag{5}
$$

If the representation is 12, then the member truncation $\gamma_{257}$ consistently transfers the exact output of $J_{12}(\gamma_4)=\gamma_{256}<\gamma_{257}$ to $j(J_2)$, which contradicts (5). It must be another representation, resulting in (3).

Here, "output equal to truncation" is not considered as an exact output; the truncation used is $\gamma_{257}$, and the readout is strictly the lower $\gamma_{256}$.

The pure left distributive law also provides

$$
1*2=2*2=3*3
\tag{6}
$$

It holds in every finite Laver table. Indeed, there are $1*1=2$, $2*1=3$, and also $1*(1*1)=(1*1)*(1*1)$, $2*(1*1)=(2*1)*(2*1)$. So (3) has also determined $2*_{257}2$
$3*_{257}3$.

## 3. calculations and the range of axioms

In source-1-times-2-A257-probe.json, the number of calls is limited to 25 or 000 times, and no specific value is given. Therefore, it cannot be considered a program verification based on 3). The basis for 3) is the aforementioned paper-based derivation. Here, a fixed I3 embedding and the existing theorem of lowest points are used; not all inputs have been rewritten into finite table certificates in pure ZFC.

Mathematical research manuscript

- [Dougherty I, Section 5](https://arxiv.org/pdf/math/9205202).
- [Dougherty II, Section 8](https://arxiv.org/pdf/math/9503204).
