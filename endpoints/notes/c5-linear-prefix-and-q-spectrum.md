# Before the fifth item: 256 spectral images with a complete linear prefix, gamma16384, and Q · [中文版](c5-linear-prefix-and-q-spectrum.zh-CN.txt)

2026-11-09. FixingI3 embedsj;J_a is the application of the left power.

This document proves a new equality.
  J13(gamma7)=gamma16384，
Precisely determine the critical spectrum images of the two auxiliary embeddings with the numbers 0..255.
The equality of the fifth item C5=J13(gamma8) has not yet been proven.

0. It has been proven that the input and notations are correct.
-----------------
B=J13，E=J14，Q=E(E)=B(J2)，D=Q(E)=B(J3)，
M=J65520，L=J65534，mu=gamma256，alpha=gamma16.

[D2] Dougherty, Critical points in an algebra of elementary embeddings, II：
https://arxiv.org/pdf/math/9503204
Use the ordinary restrictions in section 8, Lemma6.2, Lemma7.1, and equality rigidity.
Using the verified Drápal1995 extension theorem, the range is specified in c3-gamma1024-drapal.zh-CN.txt.

Already available:
  Q|V_mu=M|V_mu，D|V_mu=L|V_mu; 
  D ==_gamma4287 L; 
  E(gamma16)=mu，Q(gamma16)=mu; 
  cr D=cr L=gamma1，D(gamma1)=L(gamma1)=alpha，
  D(alpha)=L(alpha)=mu; 
  C5=B(gamma8)=E(gamma64)>=gamma65536.

The new C4 proof gives L(L) ==_gamma65536 J_T, T=2^256-2^16.
The short period of consecutive blocks also gives T *_65536 65534=T+65534=2^256-2.
Therefore, letU=L(L)(L),W=J_(2^256-2), have
  U ==_gamma65536 W.                               (U)
Drápal's wide 256 homomorphism gives W(gamma_m)=gamma_(256*m), m<65536.
In particular, due to strict output protection,
  U(gamma_m)=gamma_(256*m)，0<=m<=255.             (U-images)

1. Ordinary restrictions can be passed to these two finite application formulas
--------------------------------
LetR=D|V_alpha=L|V_alpha. Sincealpha<mu andD(alpha)=mu are unreachable cardinals.
In the 8 section, the rank estimate used indicates that R belongs to V_mu, rather than just R being contained within V_mu.

Therefore, it is D(R)=L(R). The two sides are respectively D(D)|V_mu and L(L)|V_mu.
  D(D)|V_mu=L(L)|V_mu.                             (A)

Also, due to covariance and D(gamma1)=alpha,
  D(D)(alpha)=D(D)(D(gamma1))=D(D(gamma1))=D(alpha)=mu.
The calculations for L are the same. Two embeddings from (A)) are applied to the same R again, resulting in
  D(D)(D)|V_mu=L(L)(L)|V_mu=U|V_mu.               (B)

Pure left distributive law.
  D(D)=Q(E)(Q(E))=Q(E(E))=Q(Q)，
  Q(D)=Q(Q(E))=Q(Q)(Q(E))=D(D)(D).
So (B) is exactly
  Q(D)|V_mu=U|V_mu.                               (C)

This does not directly expand existing members with 4287 without truncation; it uses full ordinary restrictions
And it was confirmed thatR indeed belongs to the rank estimate ofV_mu. The domains of the two applied formulas were examined separately.

2. Complete linear prefixes of H and V
---------------------
LetH=B(J15),V=Q(L). The ordinaryA8 finite operation yields2 *_8 3=15.
Apply the B to this member's truncation, resulting in
  H ==_C5 B(J2(J3))=Q(D).
Due to C5>=gamma65536, and (C) can take values in each gamma_m (m<=255).
(The output of (U-images) is strictly less than that of (gamma65536))
  H(gamma_m)=gamma_(256*m)，0<=m<=255.             (H-prefix)

On the other hand, D ==_gamma4287 L gives
  Q(D) ==_(Q(gamma4287)) Q(L)=V.
Q(gamma256)=E(gamma256)>E(gamma64)=C5>=gamma65536，
Here, the consistency of E(gamma16)=gamma256 and Q=E(E) is used.
Therefore, Q(gamma4287)>gamma65536. All items (U-images): can also be read safely.
  V(gamma_m)=gamma_(256*m)，0<=m<=255.             (V-prefix)

Both have a linear lower bound equal to n=255 in Lemma7.1; the last two positions are 0
The equality rigidity thus yields
  H ==_gamma65281 W，V ==_gamma65281 W.            (Normal)
Because of 256*255=65280, the equality rigidity determines all positions including the 65280th position.

3. Equality sign at the midpoint
---------------
J15(gamma3)=gamma7, B(gamma3)=gamma64. Therefore
  B(gamma7)=B(J15)(B(gamma3))=H(gamma64)=gamma16384.

The spectrum of B at gamma0..gamma7 is entirely gamma_(4^m).
It cannot be extended to m=8: What is needed is H(gamma256), which exactly exceeds (H-prefix).

4. Q's low16 spectral representations: avoiding long-periodic enumeration
--------------------------------
Write Q(gamma_m)=gamma_(q_m). Because cr Q=gamma4, q0..q3=0, 1, 2, 3.

First calculate the low64 position ofQ(J15).Q ==_gamma4287 M; it has been proven thatM*14=L, therefore
  M*15=L*(M+1).
The wide 16 expansion (where A64 is sufficient) yields
  L*65521=h16(65521)=2^256-2^64+65535 mod2^64=65535.
Therefore
  Q(J15) ==_gamma64 J65535.
The action of J65535 on gamma_m (m<32) is gamma_(16+m).
Combining with J15 and m |-> m+4 (m<8), we obtain successively
  q4..q7=16,17,18,19，q8..q11=32,33,34,35.

FindQ*255 fromA64 below. The new C4 proof of the N=4 even-step algorithm
  J15(J15) ==_gamma256 J240.
Apply the Q to it, then with the Q(gamma256)>gamma65536, and finally with the Q*15=65535 mod2^64.
Obtained
  Q*240=65535*65535=2^32-2^16=:K.
The last step is LocalShift (N=16, s=16, y=65535), which has already been proven by the Displacement Protection.

Multiply the right-hand factor by Q*1=M+1=65521 mod2^64. The consecutive block lemma is given.
  K*65521=K+65521.
For x=65521,...,65533, K+x, the low 4 digits are 1,...,13, and the digits from the 4th to the 31th are all 1.
The strengthened N=4 block lemma indicates that these rows have a periodic divisibility with 16 in A64.
Therefore, the right factor 65521 is equal to 1 modulo the period, and subsequently, every step from 13 onwards is simply adding 1.
Specifically, we obtainQ*(240+i)=K+65520+i (1<=i<=14).
Final draft of the mathematical research paper
  Q*255=(2^32-2)*65521=2^32-1，
This step uses the wide 32 Drápal homomorphism A2->A64 and 65521==1 mod4.

So Q(J255) ==_gamma64 J_(2^32-1). J255 sends gamma_r to gamma_(r+8).
(r<16); J_(2^32-1) sends gamma_t to gamma_(t+32) (t<64).
Substitute r=4, 5, 6, 7 (q_r=16, 17, 18, 19), to obtain
  q12..q15=48,49,50,51.

This section only proves the64-order normal form ofQ*255; it does not claim that the128-order is also the same.
In summary, if 0<=r<16, then
  q_r=16*floor(r/4)+(r mod4).                      (q-small)

5. Extending to all the256 spectral representations
----------------------
Take1<=r<=15, denoteK_r=J_(2^(16*r)-1), andR_r=J_(2^r-1).
The prefix normal form of the new C4 is given as
  L(R_r) ==_gamma65536 K_r，
Because2^r-1<=32767<65534. ApplyingQ, the target truncation only needs to not exceed13312, therefore
  Q(K_r) ==_gamma13312 V(Q(R_r)).
Here, Q(gamma65536)>=gamma65536 is already higher than 13312.

The expressions (Normal),V can be replaced with W to 65281 order.
The image of Q(R_r) under gamma0 is gamma_(q_r), because Q fixes gamma0.
The rightmost 0 theorem provides
  Q(R_r) mod2^(q_r+1)=2^q_r-1.
Letd_r=256*(q_r+1), at most13312. The wide256 bits are extended inA_(d_r)
The period is exactly 2^(q_r+1), so
  W *_d_r Q(R_r)=h256(2^q_r-1)=2^(256*q_r)-1.
Therefore
  Q(K_r) ==_gamma_(d_r) J_(2^(256*q_r)-1).        (Block)

Take again 0<=s<=15. Lemma6.2 are given separately.
  K_r(gamma_s)=gamma_(16*r+s)，
  J_(2^(256*q_r)-1)(gamma_(q_s))=gamma_(256*q_r+q_s).
The former is because 16|16r and s<32; the latter is because 256|256q_r and q_s<=51<512.
Its output 256q_r+q_s is less than d_r, therefore the strict output protection of (Block) applies.
Coherence leads to
  q_(16*r+s)=256*q_r+q_s.                         (Digits)
When r=0, the same formula directly holds true from q0=0.

In other words, if the quaternary expansion of n<256 is n=a0+4a1+16a2+64a3,
If0<=a_i<=3, then it is strictly true that
  q_n=a0+16a1+256a2+4096a3.                       (Q-spectrum)
Specifically, q15=51, q63=819, q240=13056, q255=13107.
This is not a guess of a digit model based on a few sample points, but rather a conclusion derived from (Block) and finite inductive reasoning.
It cannot be taken as n=256; in fact, it is Q(gamma256)=E(gamma256)>C5.

6. The new truncated results and the still missing parts
-------------------------------
Because Q|V_mu=M|V_mu, Q(gamma255)=M(gamma255)=gamma13107.
The ordinary restriction lifting results in Q ==_gamma13107 M; both at the 13107 position are also 0.
It is the critical spectrum image of both; therefore
  Q ==_gamma13108 M.
From the proven valid range of the 65536 order of 65520*14=65534.
  D ==_gamma13108 L.

For C5, stronger and more direct existing conclusions are (Normal):
  13 *_65281 15=2^256-2.
The necessary and sufficient condition that remains to be proven is still
  13 *_65537 15=2^256-2.
What is unknown is from the 65281 Bit to the next 65536 bit 256 Single digit Instead of being only a few steps away 1 Bit.
The linear prefix from H up to 255, where C5=H(gamma256) is exactly one point below.

This document is a paper proof and does not claim to be formalized in Lean or translated into pure ZFC.
Finite verification is used only to check displacements and short products, and does not replace the ordinary limit arguments in sections 1, 2, and 5.
