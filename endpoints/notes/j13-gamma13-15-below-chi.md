# J13(gamma13), J13(gamma14), J13(gamma15) are all strictly less than J11(gamma3) · [中文版](j13-gamma13-15-below-chi.zh-CN.txt)

2026-11-09. Paper proof; the usual presentation of fixing I3 into j.

Let J1=j, J_(a+1)=J_a(j), and the embedding operations within the parentheses be application.
gamma_r is an increasing enumeration of the critical points of Iter(j).
kappa0=gamma0，kappa1=gamma1，kappa2=gamma2，kappa3=gamma4.
The ordinal inequalities in this paper do not mix the spectrum of natural numbers with critical points for comparison.

Put
  K=J11，A=J12，B=J13，E=J14，
  U=A(gamma16)，chi=K(gamma3)，Theta=K(kappa3).

Conclusion
----
  B(gamma13)<B(gamma14)<B(gamma15)<U<chi<B(gamma16)<Theta.

Therefore, the four possible orders listed previously with upper-list-and-gap-order.zh-CN.txt
Now there's only one left. More precisely, a critical point that controls the gap in this domain
  s=B(j(<kappa1))=E(<kappa3)
Satisfies gamma15<s<gamma16.

This proof does not rely on the conjecture of chi=gamma_(2^2048), nor does it rely on B in the input.
Exact values on gamma9 to gamma15. It does not provide a new independent value for B(gamma15).
The upper bound of natural numbers; the lower bound of chi cannot be reversed to serve as the upper bound of B(gamma15).

### Input and Source
--------------
[D1] R. Dougherty, Critical points in an algebra of elementary embeddings,
Section 5, page 22--24 of the print:
https://arxiv.org/pdf/math/9205202

[D2] R. Dougherty, Critical points in an algebra of elementary embeddings, II,
Section 7--8 and the correspondence between finite tables and embedding truncations:
https://arxiv.org/pdf/math/9503204

[Dr95] A. Drapal, Persistence of cyclic left distributive algebras,
J. Pure Appl. Algebra 105(2) (1995), 137--165：
https://www.sciencedirect.com/science/article/pii/0022404994001421
https://doi.org/10.1016/0022-4049(94)00142-1
The complete parameters of the bit extension theorem are listed in the publisher's public abstract; this proof refers to
This published theorem does not claim to re-formulate or re-examine the original proof page by page.

Local previous derivation:
  ../small-jn-km-100-20261109/c3-gamma1024-drapal.zh-CN.txt
  ../small-jn-km-100-20261109/c4-after-drapal.zh-CN.txt
  ../small-jn-km-100-20261109/upper-list-and-gap-order.zh-CN.txt
Here is the actual derivation required, so as to avoid making judgments based solely on the state summary of old documents.

### Finite extension gives E(gamma15)=gamma60
----------------------------------
Repeat each binary bit4 times, denoted ash:
  h(sum a_i 2^i)=sum a_i(2^(4i+4)-2^(4i)).

The theorem for [Dr95] takes d=2, v2(d)=1, and the source order k=16:
  k=16 <= 2^(2^(1+1))=16.
Therefore, h:A16 -> A64 is indeed a homomorphism, and h(1)=15.

In A64, the left translation x |-> 14*x also satisfies the left distribution recurrence, and the same holds for 14*1=15.
By making finite inductions according to 1<=x<2^16, we obtain
  14 *_64 x=h(x).
The specific inductive step is as follows:
  14*(x+1)=(14*x)*15，h(x+1)=h(x)*h(1)=h(x)*15.
The equations are explained in the target table A64; the x+1 from the source table A16 has not yet been returned.

Taking x=2^15, we have
  14 *_64 2^15=15*2^60.
The value on the right side is strictly between 0 and 2^64, with 2 being assigned the value 60. Finite tables and critical point images
Correspondingly, it is given as E(gamma15)=gamma60.
Similarly, E(gamma_r)=gamma_(4r) holds for all 0<=r<16.
The strict r<16 cannot be omitted: E(gamma16)=gamma256, rather than gamma64.

Also use B(gamma3)=gamma64. This represents an existing precise lower bound, which can be derived from [D2]
Section 8 Revisited: Let D=B(J3), L=J65534, mu=gamma256, as given in the text
  D|V_mu=L|V_mu.
Combining B(gamma1)=gamma4, J3(gamma1)=gamma3, and the section numbered 7
L(gamma4)=gamma64, there is
  B(gamma3)=D(B(gamma1))=D(gamma4)=L(gamma4)=gamma64.
Here, the ordinary restriction on the domain is used, and the input gamma4 is strictly less than mu.

### Improve the old gamma12<s<gamma16 to gamma15<s<gamma16
------------------------------------------------------
Put
  sigma=j(<kappa1)，tau=j(sigma)，s=B(sigma).
The symbol f(<alpha) denotes the strict supremum of {f(beta):beta<alpha}.
Section [D1], Section [5] provides
  kappa1<sigma<kappa2，j(<sigma)<gamma3<tau.

Because E=B(j), the covariant identity is given as follows
  E(s)=E(B(sigma))=B(j(sigma))=B(tau)>B(gamma3)=gamma64.
On the other hand, the finite computation in the second section provides
  E(gamma15)=gamma60<gamma64<E(s).
E is strictly increasing, hence gamma15<s.

From sigma<kappa2 and B(kappa2)=gamma16, there is also s<gamma16.
In summary
  gamma15<s<gamma16.                                      (1)

This is a key step added in this round. Only use the linear values of E on gamma15;
No linear patterns are crossed through gamma16, nor is the assumption of B(gamma15)=gamma_(4^15) made.

### Both sides of the gap indeed contain U and chi
------------------------------
The following proves the necessary formulas for the old gap lemma.
Let sigma2=j(<kappa2), S=K(sigma), zeta=B(<kappa2).

[D1] indicates]
  tau<sigma2<kappa3，
  K|V_(kappa2)=(j o j)|V_(kappa2)，
  B|V_(kappa2)=(j o J2)|V_(kappa2).

cr A=kappa2, hence A(sigma)=sigma. From B=A(j),
  s=B(A(sigma))=A(tau).                                  (2)
Supremum transport and K(kappa1)=kappa3 provide
  S=K(j(<kappa1))=A(<kappa3)，
Whereas ordinary restrictions give S=j(j(sigma))=j(tau).

J2(<kappa2)=tau, therefore the ordinary restriction of B gives
  zeta=j(<tau)<B(kappa2)=gamma16.                          (3)
The strictness here is also given by cofinality: kappa2 is regular and
B(kappa2)>kappa2, so B(<kappa2)<B(kappa2).

Apply A to j(<tau) and obtain (2),
  B(<s)=A(j(<tau))=A(zeta)<A(gamma16)=U.                  (4)

Secondly, B(<kappa3)=A(sigma2). Since kappa2<kappa3,
sigma2<kappa3, there is
  gamma16=B(kappa2)<A(sigma2)<A(<kappa3)=S.
Apply K to j(<sigma)<gamma3 to obtain
  A(<S)<K(gamma3)=chi.
Therefore
  U=A(gamma16)<A(<S)<chi.                                (5)

Finally, from gamma3<tau and S=j(tau), it is
  chi<K(tau)=A(K(sigma))=A(S)
     =A(j(tau))=B(A(tau))=B(s).                         (6)

Combining (1), (4)--(6)) immediately yields
  B(gamma15)<=B(<s)<U<chi<B(s)<B(gamma16).                (7)
From B, which is strictly increasing, we obtain the three sorts referred to throughout the text.

### Supplementary notes on the relationship with the upper end Theta
--------------------------
If you wish to retain the upper bound of the old order, let it be T=A(sigma2)=B(<kappa3).
It has been proven that gamma16<T.
Also, the ordinary restrictions of K yield
  j(<sigma2)=K(<kappa2)<K(kappa2)=mu.
The supremum transport is thus defined.
  B(gamma16)<=B(<T)=A(j(<sigma2))<A(mu)=Theta.
The last A(mu)=Theta comes from K(kappa2)=mu, A=K(j).

### Significance and boundaries for subsequent research
------------------------
1. The three items B13, B14, and B15 are all below chi, and none of them has crossed the boundary.
   The situation between chi and B16; three of the original four possible orders have been excluded.
2. In a fixed integer input, B crosses between gamma15 and gamma16, passing through U, chi.
   This does not mean that the interval has only these two critical points, nor does it quantify the magnitude of this jump.
3. This paper does not prove the independent upper bound of chi, nor does it deny that B13--15 may have new ones.
   Higher-order operations or FGH lower bounds. Cannot be derived from chi>=gamma_(2^2048)
   B15<gamma_(2^2048).
4. This text is a paper proof presented in the context of I3 embeddings; it does not claim to introduce any new Lean formalizations or
   The translation of the pure ZFC finite table for the argument of the non-critical supremum has been completed.

Verification record: check_j13_gap_order.py/.json Only examines position expansion parameters, finite
The product sum uses integer indices. It refers to the Dr95 theorem, which is not an independent proof.
The proof of non-critical point sorting is the mathematical derivation in the third and fourth sections above.
