# The equality of the eighth image: $J_{13}(\gamma_8)=\gamma_{65536}$ · [中文版](eighth-image-equality.zh-CN.md)

2026-11-09. This calculation proves that $J_{13}(\gamma_8)=\gamma_{65536}$ under the embedding of I3 into $j$. The subsequent proof yields $J_{11}(\gamma_3)=\gamma_{2^{2048}}$, and this equality has been verified in Lean.[Subsequent proofs and verification records](../../exact-values/j11-gamma3/README.md)

The core finite table identity is

$$
  65534*_{65537}65534=2^{256}-65536. \tag{S}
$$

It has been proven that the same equation holds for all orders that do not exceed 65536. This time, only one more order is added, but this highest digit is what determines the eighth image.

## 1. conventions and proven inputs

$J_a$ represents the application of left powers: $J_1=j, J_{a+1}=J_a(j)$. It is important to distinguish between application, typically function composition, and ordinal evaluation. $A_d$ contains $2^d$ elements, denoted by $0,\ldots,2^d-1$.
$a*_d1=a+1\pmod {2^d}$.
$e\equiv_{\gamma_d}f$ denotes the Laver membership relation truncation, which is equivalent to the same finite table remainder. $f_e(r)$ is defined by $e(\gamma_r)=\gamma_{f_e(r)}$.

Let's denote the mathematical research manuscript as follows:

$$
 d=65537,\quad B=2^{65536},\quad z=2^{256},
 \quad L=65534,\quad v=z-65536,\quad g=z-3.
$$

The proofs presented below are earlier than this text:

1. [The bit support of D2] includes that the critical point image can only fall at zero, the correspondence between periodicity and critical point images,
   Lemma 7.1, Theorem 7.2, Corollary 6.4, Lemma 6.7.
2. Exponential growth and equicontinuity: If $f_e(0)=1,f_e(1)=m\ge2$, then
$f_e(r)\ge m^r$. If we take it to be equal at $r\ge2$, then
   $e\bmod 2^{m^r+1}=2^m-3$.
3. Lower bound of continuous blocks: For an allowed width $N=2^{2^t}$, if the lower $N$ bit is
In $1,\ldots,2^N-3$, if the $N,\ldots,M-1$th position is entirely 1, then
   $e(\gamma_N)\ge\gamma_{M^2}$.
4. The wide 16 dense high-order lemma: If there are at least 16 1 in the 16 to 255 positions.
If the low 16 positions are within the $1,\ldots,65533$, then there is a $e(\gamma_{16})\ge\gamma_{65536}$. This also holds true when the low rank is 65534 and $e(\gamma_1)<\gamma_{256}$.
5. Old Prefix Theorem: Let $h=h_{16}$ repeat each binary bit 16 times, then
   $J_L(J_r)\equiv_{\gamma_{65536}}J_{h(r)}$，$1\le r\le65534$.
6. The high-order product from the previous round of independent proofs

$$
     v*_{65537}65533=B+g. \tag{V}
$$

This formula uses only the old prefix theorem, without using $S$. The same document also proves
   $J_{13}(\gamma_8)=\gamma_{65536}\iff\text{(S)}$.

Input 2 and see `exclude-2pow2048-rigidity.zh-CN.txt`. Input 3–5 and see the adjacent read-only directories.
`c4-filled-block-period-bridge.zh-CN.txt`, 
`c4-density-and-odd-carries.zh-CN.txt`, 
`c4-gamma4096-even-carries.zh-CN.txt`.
Enter 6 to see this catalog `one-carry-eliminated.zh-CN.txt`, especially sections 3–5.

The following text repeatedly uses two critical bridge chains:

$$
 \mathcal C_{16}=(0,1,4,8,12,14,15),
$$

$$
 \mathcal C_{256}'=(16,64,128,192,224,240,248,252,254,255).
$$

For adjacent indices $a,b$ in the chain, there exist embedding critical sequences that start with $\gamma_a\to\gamma_b\to\gamma_{16}$ or $\gamma_a\to\gamma_b\to\gamma_{256}$. The first two pairs in the second chain come from [D2] Theorem 7.2$a$, taking $n=3,m=1,0$:

$$
 2^{2^n-2^{m+1}}\longrightarrow 2^{2^n-2^m}
       \longrightarrow 2^{2^n}.
$$

The remaining parts are taken from Theorem 3.1$a$, with $n=8,m=6,5,\ldots,0$ substituted. The existence of the chain does not depend on the equality to be proven.

## 2. New Rigorous Critical Point Lemma

**Lemma 1.** if

$$
 16\le r<256,\qquad \operatorname{cr} e=\gamma_r,\qquad
 e(\gamma_r)\ge\gamma_{256},
$$

Then

$$
 e(\gamma_{256})>\gamma_{65536}. \tag{J+}
$$

Prove $r=16$. Write $e(\gamma_{16})=\gamma_b$, $b\ge256$. If $b>256$, the continuous 1 description of the first critical image, combined with the continuous lower bounds of the wide 256 blocks, gives $e(\gamma_{256})\ge\gamma_{b^2}>\gamma_{65536}$.

Now let $b=256$. Take $a=J_{65533}$. By the [D2] Theorem 7.2$c$ and $a(j)=J_L$,$a$, the first three spectral images are $1,16,256$. $e$ fixes $\gamma_0,\gamma_1,\gamma_2$, so the first three images of $F=e(a)$ are

$$
  \gamma_1,\quad\gamma_{256},\quad e(\gamma_{256}).
$$

Provide the lower bound of the exponent as $e(\gamma_{256})\ge\gamma_{65536}$. If set to equal, set to equal rigidity forcing

$$
  F\bmod 2^d=g.
$$

The bit support contains $\operatorname{bits}(e)\subseteq \operatorname{bits}(F-1)$ (taking the same finite remainder), indicating that $e$ in positions 256 to 65536 are all 0. On the other hand, the critical point is 16, and the first image is 256, indicating that the low 16 positions are all 0, and the positions from 16 to 255 are all 1. Therefore, it is $e\bmod2^d=v$. Thus

$$
 F\bmod2^d=v*_d65533=B+g,
$$

This proves the completion of $r=16$. It contradicts the concept of equicontinuity.

Propagate this conclusion along $\mathcal C_{256}'$. Assuming that the critical point is $\gamma_\alpha$, the next link point is $\beta$. For any $\alpha<r\le\beta$, consider the critical bridge.
$t:\gamma_\alpha\to\gamma_\beta\to\gamma_{256}$.
$e$ is fixed by $\gamma_\alpha$, so the critical point of $H=e(t)$ is $\gamma_\alpha$, and the initial image is $e(\gamma_\beta)\ge\gamma_{256}$. The inductive hypothesis gives

$$
 H(\gamma_{256})>\gamma_{65536}.
$$

Covariance and monotonicity are given.

$$
 e(\gamma_{256})=H(e(\gamma_\beta))
 \ge H(\gamma_{256})>\gamma_{65536}.
$$

The finite intervals cover 16 to 255, thus the lemma is proven.

## All protection points of 3. even steps have crossed the endpoint.

**Lemma 2.** if $s$ is a multiple of 16, $16\le s<256$, and

$$
 k\bmod2^{s+16}=2^sx+2^s-1,\qquad 1\le x\le65534,
$$

Then

$$
 k(\gamma_{16})>\gamma_{65536}. \tag{Shift+}
$$

Inductively downward towards $x$; the position above $s+16$ is arbitrary. The base case $x=65534$ yields $k(\gamma_0)=\gamma_s$, $k(\gamma_1)\ge\gamma_{s+16}$. Linear growth thus yields

$$
 k(\gamma_{15})\ge\gamma_{s+240}\ge\gamma_{256}.
$$

Along $\mathcal C_{16}$, crossing $\gamma_{256}$, take the adjacent $\alpha,\beta$ and the corresponding critical bridge $t$, to make

$$
 \gamma_s\le k(\gamma_\alpha)<\gamma_{256}
       \le k(\gamma_\beta).
$$

The critical point indices that are embedded $H=k(t)$ are located at $[16,256)$, and their first images are not lower than 256. The lemma 1 provides $H(\gamma_{256})>\gamma_{65536}$, hence
$k(\gamma_{16})=H(k(\gamma_\beta))>\gamma_{65536}$.

By applying the [D2] Theorem 7.2 to the proof in the Claim 1, we obtain $H=k(t)$, which satisfies the conditions.

$$
 \gamma_s<\operatorname{cr}H<\gamma_{s+16}\le k(\gamma_\beta),
 \qquad H\bmod2^{s+16}=2^sx',\quad x<x'\le65534.
$$

Let $H'=H+2^s-1$, where the addition is applied repeatedly using the successor. The inductive hypothesis gives $H'(\gamma_{16})>\gamma_{65536}$. The Corollary 6.4 is given as follows

$$
 k(\gamma_{16})=H(k(\gamma_\beta))
 \ge H(\gamma_{s+16})\ge H'(\gamma_{16})>\gamma_{65536}.
$$

Lemma proved.

Now assume that $t$ is even, and $2\le t\le65534$. Set

$$
 m=v_2(t),\quad s=16m,\quad a=h(t-2^m),\quad G=65535.
$$

$1\le m\le15$, so $16\le s<256$, and $2^{s+16}\mid a$. All the protected points in Lemma 6.7 are

$$
 J_{a+2^s z-1}(\gamma_{16}),\qquad 2\le z\le G.
$$

Its low level is $2^s(z-1)+2^s-1$, all the lemmas 2 apply, and the protection level is at least $\gamma_{65537}$. Therefore

$$
 h(t-1)*_d G=h(t). \tag{Even+}
$$

## 4. Odd steps: Permitted without interfering with recursive periodic doubling

First, strengthen the exceptional low-case scenario of the density lemma.

**Lemma 3.** If $k\bmod2^{16}=65534$, there are at least 16 1 in the 16 to 255 positions, and $k(\gamma_1)=\gamma_b<\gamma_{256}$, then

$$
 k(\gamma_{16})>\gamma_{65536}. \tag{DenseB+}
$$

The proof of the old dense lemma has been given $k(\gamma_{15})\ge\gamma_{256}$. From the chain point 1 to 15 across 256, we obtain $H=k(t)$, whose critical point index is at $[b,256)\subseteq[16,256)$, and its initial image is not lower than 256. The lemma 1 and co-variance immediately provide the required strict inequality. Note that the requirement $b<256$ is still explicitly stated here.

**Lemma 4.** if $1\le k\bmod2^{16}\le65533$, and in the positions 16 to 255, there are at least 16 instances of 1, the position 16 is 1, and none of these 240 positions are 1, then

$$
 k(\gamma_{16})>\gamma_{65536}. \tag{DenseA+}
$$

Using the wide 16 standard for crossing, let $H=k(t)$ be such that its lower 16 bit is a strictly larger non-zero even number, and it inherits all the 1 bits of $k$ at the 16 position and above. Let the critical bridge be $\alpha\to\beta\to\gamma_{16}$. Since the 16 bit of $k$ is 1, $k(\beta)$ is not equal to $\gamma_{16}$, thus
$k(\beta)>\gamma_{16}$.

If the low position of $H$ is not 65534, the old dense lemma gives $H(\gamma_{16})\ge\gamma_{65536}$, and strict monotonicity provides the result.
$k(\gamma_{16})=H(k(\beta))>\gamma_{65536}$.

If $H$ has a lower bit set to 65534, write it as $H(\gamma_1)=k(\beta)=\gamma_b$. When using $b<256$, use the lemma 3; when using $b>256$, use linear growth.
$H(\gamma_b)\ge\gamma_{b^2}>\gamma_{65536}$.

Only $b=256$ remains. At this point, we have $k(\alpha)=\gamma_1$ and $k(\beta)=\gamma_{256}$. Assuming that the required strict inequality fails, the old lower bound will be exactly equal. There are only two possibilities in the chain:

- $(\alpha,\beta)=(\gamma_0,\gamma_1)$: The first two images of $k$ are 1 and 256.
Exponential growth is directly contradictory.
- $(\alpha,\beta)=(\gamma_1,\gamma_4)$: $k$ is fixed to $\gamma_1$.
And $k(\gamma_4)=\gamma_{256}$. The critical points can only be 2, 3, 4.

The three sub-scenarios for the second case are as follows. For details on the small growth lemma, please refer to the previous document's section 1.

1. The critical point is 4: The first image being 256 forces the positions from 4 to 255 to all be 1, which contradicts the fact that the higher parts are not filled.
2. The critical point is 3: Let $k(\gamma_3)=\gamma_m$, $m\ge4$.
The small growth lemma gives $f_k(4)\ge m^m$, and is strict when $m>4$. $f_k(4)=256$ forces $m=4$, and also $k(J_3)\bmod2^{257}=11$. The bit support includes that the 16th bit of the $k$ is contradictory to the 1th bit.
3. The critical point is 2: Let $a=f_k(2)\ge3$. The first two images of $c=k(j)$ are 1 and $a$.
And $c(\gamma_a)=\gamma_{256}$, so $a^a\le256$, can only be $a=3,4$. When $a=3$, let $A=k(J_3)$, $h=A(j)$, $m=f_k(3)\ge4$. Then $A(\gamma_3)=\gamma_{256}$, $\operatorname{cr}h=\gamma_3$, $h(\gamma_3)=\gamma_m$, and $h(\gamma_m)=A(\gamma_2)<\gamma_{256}$. The small growth lemma, however, gives $h(\gamma_4)\ge\gamma_{m^m}\ge\gamma_{256}$, which is a contradiction. When $a=4$, the exponential equality rigidity gives $c\bmod2^{257}=13$. But the successors of the low 16 positions do not overflow, so the $c=k+1$ at the 16 position remains 1, which is a contradiction.

Having exhausted all possibilities, the lemma 4 is proven.

Let $t$ be an odd number, and let $3\le t\le65533$ be set as

$$
 a=h(t-1),\qquad m=v_2(t-1),\qquad s=16m.
$$

In position 16 to 255 of $a$, there is at least one block of 16 1, and these positions are not filled. Consider the rows $a+i$ in the recurrence, $1\le i\le65534$.

If $m=1$, the 16th position is 1. For the $i\le65533$, use the lemma 4; when $i=65534$, the first critical image is less than 256, use the lemma 3. Therefore, the periods of these rows in $A_d$ are divisible by $2^{16}$. Because $a+1\equiv1\pmod {2^{16}}$, each step of the recursion only adds 1.

If $m\ge2$, only the old non-strictly dense lower bound is needed:

$$
 J_{a+i}(\gamma_{16})\ge\gamma_{65536}
 \ \Longrightarrow\ J_{a+i}(\gamma_{17})\ge\gamma_{65537}.
$$

Therefore, the period is divisible by $2^{17}$, although it may not be divisible by $2^{16}$. But for $s\ge32>17$, there is still $a+1\equiv1\pmod{2^{17}}$, and the recurrence only adds 1. Thus, in both cases, it is the case.

$$
 a*_d1=a+1,\qquad
 a*_d(i+1)=(a+i)*_d(a+1)=a+i+1,
$$

And it was obtained that

$$
 h(t-1)*_dG=h(t). \tag{Odd+}
$$

The part where the period doubles at most once is part of the proof; it does not convert all old protection points to strict inequalities without conditions.

## 5. are merged and connected back to the eighth image

$L*_d1=65535=h(1)$. Combine $Even+$ and $Odd+$, and use finite induction on $r$ to obtain

$$
 L*_d r=h(r),\qquad 1\le r\le65534.
$$

Finally, $h(65534)=2^{256}-65536=v$, this is $S$.

The proven necessary and sufficient condition from the previous document is now presented.

$$
 \boxed{J_{13}(\gamma_8)=\gamma_{65536}.}
$$

Therefore, the currently known value of this point can be written as

$$
 J_{13}(\gamma_r)=\gamma_{4^r},\qquad 0\le r\le8.
$$

The previous document has already determined $v*65520=2^{256}-16$, and $(2^{256}-16)*14=2^{256}-2$ has been obtained with a sufficiently high truncation. Therefore, there are no new uncalculated products when returning to the eighth image.

## 6. Non-circularity and Unresolved Range

The dependency order is as follows: old prefixes (up to 65536) → $V$ of the previous file → lemma 1 → strict displacement/dense lemma → new prefixes (up to 65537) → eighth image equality. There is no reverse deduction from the new prefixes to their own input $V$.

Do not replace the $d=65537$ in this text with $2^{2048}+1$. The proof uses only first-order periodic control, and it is not possible to cross extremely long order intervals without proof. Therefore, this text has not been proven yet.

$$
 J_{11}(\gamma_3)=\gamma_{2^{2048}},
$$

There is also no proof that it is not equal to that value.

In the context of fixing I3, this paper presents a paperproof. The high truncation recognition involved still adopts ordinary restrictions and their enhancements. Translating the entire dependency chain into a finite table proof without large bases is another unfinished task. Program checks for low-order patterns cannot replace the aforementioned proofs.

## 7. is bounded and verified

The eighth_image_audit.py/.json was completed and exited within 0.828 seconds. It checked to cover all 32767 even steps, 16383 odd steps that require strict protection, 16383 odd steps that allow periodic doubling, as well as 1048544 extraction displacement protection point patterns. The critical bridge formula was verified for 9 adjacent intervals, covering all indices from 16 to 255.

According to the definition, establish $A_9,A_{10}$ independently. Check the periodic enhancement of the 511 row, where the 57 row indeed doubles, and verify the corresponding modulus replacement for the 3130. These checks are used to rule out errors in indexing and periodic usage; the $A_{65537}$ has not been constructed, and does not replace the paper proofs presented in this paper.

## Mathematical research manuscript

- Randall Dougherty, [Critical points in an algebra of elementary embeddings, II]$https://arxiv.org/pdf/math/9503204$.
- This catalog: `one-carry-eliminated.zh-CN.txt`, `eighth-image-two-carries.zh-CN.txt`.
  `after-c6-supremum-lift.zh-CN.txt`, `exclude-2pow2048-rigidity.zh-CN.txt`.
- The old lemmas listed at the beginning of this section in the adjacent read-only directory `../small-jn-km-100-20261109/`.
