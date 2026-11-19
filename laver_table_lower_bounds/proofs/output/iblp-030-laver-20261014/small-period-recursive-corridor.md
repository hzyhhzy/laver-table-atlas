# Recursive corridor under small cycles: Proven conditions and missing endpoints · [中文版](small-period-recursive-corridor.reading.zh-CN.md)

*English reading edition, translated with machine assistance. The title links to the dated Chinese manuscript.*

> Collected reading edition. The three main papers state the results of this collection.
> This edition retains the local proofs, their hypotheses and any withdrawals. Progress reports describe the state of work at the time.
> The locations of omitted passages on preset inputs are recorded in SOURCE_MANIFEST.json.
> The main papers give the numerical derivations for the natural parameters produced by the proofs. This historical note carries no additional Lean certification.

2026-10-14. This paper only preserves the algebraic results of the conditional algebra, without announcing any new lower bounds for small cycles. The original feedback background is denoted as

$$
k=\kappa_2<a=\theta_6<b=\tau<c=\theta_7,
\quad P(\gamma_0)=a,\ P(\gamma_1)=b,\ P(b)=c.
$$

The original template implements the integer function $T(h)=D(h)+2$. The naturalness of the template means that for any fixed environment $\kappa_0,\kappa_1$, embedding into $Q$, taking the entire finite background as a $Q$-image, it can still process input fans in any global `Iter(j)`, without requiring the input to be a image of some old fan. This is the meaning used by [Background Transport Lemma](<lined-feedback-corridor.md>).

## 1. Upgrading the weaker endpoint condition of a natural template

Let the entrance of the natural template $F$ remain $b$, and the exit be $d\ge c$: fans with a height of $h\ge3$ and a seal lower than $b$ are transformed into fans with a height of $F(h)$ and a seal lower than $d$. Assume that the actual embedding $H$ fixes $\kappa_0,\kappa_1,k$, and

$$
d<H(a),\qquad H(c)<B.
\tag{1}
$$

Then the entrance $b$ and the exit $H(c)$ implement a new natural template

$$
\mathcal U(F)(h)=F^{\circ(D(F(h))+1)}(h).
\tag{2}
$$

Proof: First perform a $F$ operation to obtain a fan with a height of $F(h)$ and a seal of $C<d$. Let's denote it as $N=D(F(h))$. The global count gives $\gamma_N<C<d<H(a)<H(b)$. Still using the original $H(P)$, instead of the new template's internal chain generator, transport and reduce the root, contract the global Dougherty chain to obtain a $(k,H(a),Z)$ with $N$-lined, where

$$
Z<H(P)(H(b))=H(c).
$$

Every segment of the chain $Q_i:k\mapsto u_i\mapsto u_{i+1}$ satisfies $Q_i(b)>u_i$, $Q_i(d)<u_{i+1}$, because it is $k<b$ and $d<H(a)\le u_i$. Therefore, transporting the entire $F$ template along the chain is performed $N$ times. Including the first step, it becomes (2). The entire background of the finite proof is transported as a whole, maintaining the same formulas and strict constraints, so the new template is natural.

Key distinction: The required endpoint is $H(c)$, not the stronger $H(d)$. Here, $c=\theta_7$ is always the exit point of the original chain generator.

<a id="proof-section-2"></a>

## 2. is a long chain that improves the support for variable depth upgrades of common roots.

If there is an actual $M$-lined chain

$$
(r;u_0,\ldots,u_M),\qquad k<r<a<c\le u_0,
\tag{3}
$$

Each segment that has $H_i:r\mapsto u_i\mapsto u_{i+1}$ can be recursively defined.

$$
F_0=T,\qquad F_{i+1}(h)=F_i^{\circ(D(F_i(h))+1)}(h).
\tag{4}
$$

All template entrances remain $b$, and the $i+1$th template exit can be $H_i(c)\le u_{i+1}$. The reason is that $H_i$ is fixed at $k$, and both $H_i(a)>u_i$ and $H_i(c)\le u_{i+1}$ are also fixed. The exit of the previous step is no greater than $u_i$, thus satisfying the strict entrance condition for (1). The first step allows $c=u_0$, because $H_0(a)>u_0$; the sealing of the new fan is always strictly below the template exit.

This is a unified proof for any given finite $M$, and it does not claim that there exists a chain of all lengths with a fixed $B$. Even if $M$ is very large, it only provides a new lower bound and cannot automatically satisfy the design goal of "substantial internal structure exceeding BMS".

## 3. A specific deep-chain candidate with a unique new endpoint

Let $K=j_{(11)}$, take the actual application item

$$
A=K(K)(f).
$$

It resembles an application identity.

$$
A(\gamma_0)=\theta_5,\qquad
A(\gamma_1)=\theta_7,\qquad
A(\theta_5)=K(\theta_6).
\tag{5}
$$

For example, $K(K)(\kappa_3)=K(\kappa_3)=\theta_5$, because of $\kappa_3=K(\kappa_1)$; the other two expressions are also read as $K$ - an application identity on the image. Take the chain $C_{\rm line}$-lined $(\kappa_0,\kappa_1,\theta_5)$ and pick $A$-image to get

$$
(\theta_5;\theta_7,\ldots,K(\theta_6)),
$$

The conditions for exactly satisfying (3) at the root or starting point. Since the critical sequence of $K$ begins with
$\kappa_0,\kappa_2,\mu,\theta_6$，

$$
K(\theta_6)=\kappa_4^K\ge\kappa_4.
$$

Therefore, this chain cannot be placed within the old $q(5)$ budget. The new, explicitly proven condition is

$$
K(\theta_6)<j(\gamma_5)\quad\text{or}\quad K(\theta_6)<j(\gamma_6).
\tag{6}
$$

Currently, no equations have been proven. Additionally, using $K=j_{(10)}(j)$ and $\theta_6=j_{(10)}(\kappa_3)$, the left side can also be written as $j_{(10)}(\kappa_4)$.

## 4. small period index and bounded detection

It is necessary to distinguish between

$$
B_5=j(\gamma_4)=\kappa_4,\quad B_6=j(\gamma_5),\quad B_7=j(\gamma_6).
$$

The counterpart of $q(6)$ is not $\kappa_5$. In fact, it is $\gamma_6<\kappa_4$, and therefore $B_7<\kappa_5$.

A small probing program (historical reference: `small_period_promoter_probe.py`) introduces $L_{10}$ visible 103 exact point images, and checks the conditions of the pre-listed application families relative to three endpoints. It runs for 8.58 seconds, with 118 points, 146 owners, and 1, 127 point images; it returns UNKNOWN. It uses the old, stronger guard $H(S(c))<B$, so it cannot be "mishit" to deny the new, weaker guards or (6) of the 1 section. The program does not enumerate BMS descent, Laver giant tables, or unbounded M processes.
