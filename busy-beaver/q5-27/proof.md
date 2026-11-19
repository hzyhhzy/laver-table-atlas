# How 27 states write $2^{q(5)}+3$ ones on a blank tape · [中文版](proof.zh-CN.md)

Let $A_n$ be the ordinary binary Laver table on $2^n$ elements, with first-row period $\pi_n(1)$. Write

$$
q(5)=\min\{n\ge0\mid\pi_n(1)\ge32\}.
$$

**Theorem.** The two-symbol machine in the appendix has 27 working states and starts on a two-way infinite all-zero tape. It halts if and only if $q(5)$ exists. On halting, the entire tape contains exactly

$$
\boxed{2^{q(5)}+3}
$$

ones. Counting $H$ ones thus recovers the order $q(5)=\log_2(H-3)$ and the table width $2^{q(5)}$. In ZFC, existence of $q(5)$ gives $\Sigma(27)\ge2^{q(5)}+3$ for the maximum number of ones left by a halting machine. In ZFC + I3, Laver's theorem gives unbounded first-row periods, so $q(5)$ exists. [First-row periods under I3, Biane §7.2](https://www.mat.univie.ac.at/~slc/wpapers/s80biane.pdf#page=18)

For the step-count convention, each step can add at most one new 1 to a computation starting from a blank tape. Under the same existence hypothesis,

$$
BB(27)\ge\Sigma(27)\ge2^{q(5)}+3>q(5).
$$

## Construction

Row 1, column 16 detects period 32. Row 5, column 8 vanishes at exactly the same orders and admits a short unary stack program. For $K=4,8,16,\ldots$ the machine computes a natural number $x$ with the same zero test as $5\star_{2K}8$. At the first success $x=2K$, so the width itself is already on the tape as a run of $x$ ones. An earlier Busy Beaver construction using the first-row periods of ordinary Laver tables is Taylor's 64-state machine. [Taylor's paper](https://cheddarmonk.org/papers/laver.pdf)

Two choices save states. One copying routine prepares the next trial's operands and a spare block, and also pushes operands onto the recursion stack. The spare block provides the size of the next trial after a zero result. After a positive result it identifies the bottom of the stack and lets the machine halt. In the following description each variable names a block length on the tape.

~~~text
w = 0
loop
    N = 2w + 12
    x = Z(N - 5, N - 7)
    if x > 0, halt with x + 3 ones on the tape
    w = N - 6
~~~

## 1. Why row 5, column 8 detects the exact threshold

Use the width as subscript. The operation $\star_W$ for $W=2^n$ uses positive representatives $1,\ldots,W$, with $W$ representing zero. Read integer column numbers modulo $W$. Left distributivity $a\star(b\star c)=(a\star b)\star(a\star c)$ and $a\star1=a+1\bmod W$ give

$$
a\star(b+1)=(a\star b)\star(a+1).
$$

Row $W$ is the identity. For $a<W$, a period of row $a$ increases strictly from $a+1$ to $W$. Its length is at most $W-a$, and it takes the value zero precisely at multiples of that length. Row periods are powers of two. Projection from width $W$ to $W/2$ is a homomorphism, and lifting the same lower row by one order preserves or doubles its period. [Dougherty–Jech, Proposition 3.2](https://arxiv.org/pdf/math/9209202#page=9)

It follows that $1\star_W16$ is nonzero exactly when $\pi_n(1)>16$, equivalently $\pi_n(1)\ge32$. We shall prove in the finite tables that

$$
5\star_W8\text{ is zero}\quad\Longleftrightarrow\quad1\star_W16\text{ is zero}.
\tag{1}
$$

**Left multiplication on valuations.** Fix $n\ge5$. For a positive representative $y$, let $v(y)$ be the exponent of 2 in $y$, so $v(W)=n$. Define $F_a(r)=v(a\star_W2^r)$ for $0\le r\le n$. Then $v(a\star_W y)=F_a(v(y))$. Indeed, for each $1\le m\le n$, divisibility of $a\star_W y$ by $2^m$ means that the period of the projected row at width $2^m$ divides $y$. Each period is a power of two, so the answer depends only on $v(y)$. Taking all $m$ determines the valuation.

Write $F=F_1$. Take $b=1$ and $c=2^r$ in left distributivity to get

$$
F_{a+1}(F_a(r))=F_a(F(r))\qquad(1\le a\le4).
\tag{2}
$$

At width 32, $(1\star1,1\star2,1\star4,3\star2)=(2,12,16,8)$. Their valuations remain $1,2,4,3$ at every $n\ge5$ by projection. Also $3\star1=4$, so $F_3(0)=2$. Equation (2) gives the following calculation with $F(4)$ left symbolic.

| Substitution in (2) | Consequence |
|---|---|
| $a=1$ | $F_2$ agrees with $F$ at $F(0)=1,F(1)=2,F(2)=4$. Thus $F_2(1)=2,F_2(2)=4,F_2(4)=F(4)$. |
| $a=2,\ r=1,2$ | $F_3(2)=F_2(2)=4$ and $F_3(4)=F_2(4)=F(4)$. |
| $a=3,\ r=0,2$ | $F_4(2)=F_3(1)=3$ and $F_4(4)=F_3(4)=F(4)$. |
| $a=4,\ r=2$ | $F_5(3)=F_4(4)=F(4)$. |

The last identity says $v(5\star_W8)=v(1\star_W16)$. Setting the valuations equal to $n$ gives (1). At width 16 the period of row 5 is at most $16-5=11$, so it divides 8. The period of row 1 divides 16. Both entries therefore vanish at width 16, and projection covers the smaller widths.

## 2. The arithmetic recursion on the tape

The machine represents $p,q$ by unary runs. Define $Z(0,q)=q-1$ for $q\ge1$. For $p>0$, $q\ge2$, let $C(q)$ be the least power of two at least $q-1$, and set

$$
Z(p,q)=
\begin{cases}
0,&q-1=C(q),\\
Z\bigl(Z(p,q+1),p\bigr),&q-1<C(q).
\end{cases}
\tag{3}
$$

The second branch is the local stack rewrite $(p,q,\ldots)\mapsto(p,q+1,p,\ldots)$. Once the first two operands have been evaluated, the saved $p$ is the next right operand.

**Meaning and termination.** For $1\le p<W$ and $2\le q\le W+1$,

$$
Z(p,q)=W-\bigl((W-p)\star_W(C(q)+1-q)\bigr),\qquad 0\le Z(p,q)<p .
\tag{4}
$$

Induct lexicographically on $p$ and $b=C(q)+1-q$. If $b=0$, the forward column is zero and the table entry is $W$, giving zero on both sides. If $b>0$, then $C(q+1)=C(q)$. The inner call reduces the second induction parameter by one, so $z=Z(p,q+1)=W-((W-p)\star_W(b-1))<p$. If $z=0$ the outer call returns $p-1$. If $z>0$ then $p\ge2$. Row $W-z$ has period a power of two at most $z\le p-1$, and this period divides $C(p)$. In (4) applied at the smaller left operand $z$, column $C(p)+1-p$ can therefore be replaced by $W-p+1$. In both cases

$$
Z(z,p)=W-\bigl((W-z)\star_W(W-p+1)\bigr).
$$

The forward successor recurrence gives (4). Every entry in row $W-p$ lies between $W-p+1$ and $W$, which proves the range bound. Any given operands fit in some sufficiently large $W$. Each arithmetic trial therefore terminates, and a recursive call with positive left operand never needs $Z(p,1)$.

## 3. One test at each width

Each trial uses $N=3K$. For the first trial $K=4$ and (3) gives $Z(7,5)=0$. Now let $K\ge8$ be a power of two and put $W=4K$. The actual right operand satisfies $q-1=3K-8\ge2K$, so $C(q)$ is $2K$ or $4K$. The period of row $K+5$ divides $2K$. Equation (4) gives

$$
Z(3K-5,3K-7)=4K-\bigl((K+5)\star_{4K}(K+8)\bigr).
\tag{5}
$$

Consider left multiplication $L(t)=K\star_{4K}t$. A full period consists of two segments. For $1\le s\le K$,

$$
L(s)=K+s,\qquad L(K+s)=3K+s.
\tag{6}
$$

Start with $L(1)=K+1$. For $1\le s<K$, row $K+s$ at width $2K$ has period at most $K-s<K$, hence at most $K/2$. Its period at width $4K$ still divides $K$, so the successor calculation for $L(s+1)$ reads column $K+1$ as column 1. Induction gives $L(K)=2K$. The first $2K$ entries of row $2K$ at width $4K$ are $2K+1,\ldots,4K$ because every intermediate row $2K+r$ has period dividing $2K$ and column $2K+1$ reads as column 1. Thus $L(K+1)=3K+1$. Every later intermediate row $3K+s$ has period at most $K-s$, so the same argument gives the second segment. Its last entry is the first $4K$, at column $2K$, proving the exact period.

Let $z=5\star_{2K}8$ in positive representatives. Left distributivity gives $L(5)\star_{4K}L(8)=L(5\star_{4K}8)$. The product at width $4K$ projects to $z$ at width $2K$, which is the period of $L$, so the right side is $L(z)$. Since $K\ge8$, $L(5)=K+5$ and $L(8)=K+8$. Equations (5) and (6) yield

$$
x:=Z(3K-5,3K-7)=
\begin{cases}
3K-z,&1\le z\le K,\\
2K-z,&K<z\le2K.
\end{cases}
\tag{7}
$$

In particular $x=0$ exactly when $z=2K$. At the first nonzero entry of width $2K$, the same entry at width $K$ was zero. Its two possible lifts are $K$ and $2K$, so here $z=K$ and (7) gives $x=2K$. By Section 1, that first successful width is $2^{q(5)}$.

## 4. Reusing one routine for copying, stack pushes and doubling

Write $1^s$ for $s$ consecutive ones. State numbers refer to the transition table below. States 10–17 implement the shared copier.

**Copier invariant.** The local input is $1^s\,0\,1^L\,0\,1^u$, with blank tape to its left and possibly further blocks separated by zeros on its right. Take the first source cell as coordinate 0. Set $e=0$ for entry in state 11 within the source or at its right separator. For entry in state 16 on the final source bit (the left separator for an empty source), state 17 seeds the left copy with one bit, so $e=1$. The exit is the first time state 12 reads 0 at coordinate $-1$. The tape is then

$$
1^{s+e}\,0\,1^{L+1}\,0\,1^{s+u}.
\tag{8}
$$

The separators are at $-1$ and $L+1$. The tail remains at its original coordinates. After $i$ bits have been moved, a pass starting at state 11 has a left copy of length $i+e$, source remainder $s-i$, central block $L$ and right block $i+u$. State 11 fills the 0 to the right of the remaining source and moves left to state 12. If a source bit remains, 12 erases its last bit, 13 scans right to fill the 0 beyond the central block, and 14 erases the filled cell's left neighbor. Both moving separators shift one place left and the right copy gains one bit. States 15 and 16 cross the central block and source remainder to the left. State 17 adds one bit to the left copy, and 10 returns to the source to begin pass $i+1$. When the source runs out, the 1 just written by 11 extends the central block by one and 12 finds the 0 at $-1$. This proves (8), and every scan is finite.

**Three continuations.** At the exit, the middle block begins at coordinate 0. Its first three cells choose the continuation. The final state in each path is the handoff.

| Original central length | State path | Effect |
|---|---|---|
| $L=1$ | `12→23→24→25→1→11` | Fill both separators next to the middle to obtain a single run of ones and enter the unseeded copier. |
| $L=0$ with nonempty right copy | `12→23→24→20→16` | Leave ones at $-1,0,1$, cut a separator at cell 2 and enter the seeded copier with the head at 1. |
| $L\ge2$, left copy contains a guard | `12→23→24→25→7→7→4` | Cells $-2,-1$ are guards, cells $0,1,2$ read $1,0,0$, and state 4 resumes counting the right operand at cell 3. |

The first case includes the empty source at blank-tape startup. The second is only used to split a run of at least four ones. Every real transition from state 12 on a blank to state 23 puts the head on the first 1 of the middle block. Thus state 23 never executes its halt-on-zero instruction in the blank-start computation.

**Preparing a trial.** At a round boundary the only nonblank pattern is $1^w\,0\,1$, with source length $w$. Initial state 1 writes a 1 on the blank tape and moves left to 11, setting up $w=0$.

1. Copy $s=w,L=1,u=0$ without a seed. The first exit gives one run of $V=2w+4$ ones.
2. Copy those $V$ bits without a seed, with $L=u=0$. The second exit extends the $V$-bit left copy by cells $-1,0,1$, giving $s=V+3$. A cut at cell 2 leaves a middle block $L=V-1$.
3. Copy this new left block with a seed. Equation (8) gives $1^{s+1}\,0\,1^{L+1}\,0\,1^s$. The third exit uses the extra bit of the left copy and the old separator as the left guard and the first bit of the right operand, respectively. It enters the calculation of $Z(p,q)$ with a spare run of length $D$, where

$$
p=s=V+3,\qquad q=L+2=V+1,\qquad D=s .
$$

For $N=2w+12$, this is $(p,q,D)=(N-5,N-7,N-5)$. The finite-table width tested in that trial is $2N/3$.

## 5. The numbered states implement the arithmetic recursion

State 2 processes the active value. Pending operands follow it, separated by zeros. A stack $(p,q,u,\ldots)$ first evaluates $Z(p,q)$ and then combines its value with $u$, proceeding to the right. The spare run $1^D$ terminates the stack.

**Zero row.** For an active zero, state 2 reads 0 and enters 18. State 18 passes blanks to the right, erases the first bit of the next block, and hands control back to 2. An operand of length $u$ now has length $u-1$, implementing $Z(0,u)=u-1$. If $u=1$ the next active value is again zero.

**Power-of-two test.** For $p>0$, states 2 and 3 pass the active block. For a normal right operand $q\ge2$, states 1, 14, 6 and 8 set the left separator to 1, retain the first bit of the right operand and begin counting its remaining $q-1$ bits. The two ones just described act as guards. After $t\ge1$ counted bits, when state 4 is reading the next bit, precisely one of the counted cells is marked. Its position, counting from 1, is

$$
h(t)=2^{1+\lfloor\log_2t\rfloor}-t .
$$

For $t=1$ the mark is in the first position. At each step states 4 and 5 find the old mark to the left and erase it, and 6 inspects its left neighbor. If the mark was past the first position, 6 moves it one cell left and 7 returns right. If the mark was first, 6 meets the guard at the start of the right operand, and 8 marks the newly read last bit. These updates give $h(t+1)=h(t)-1$ and $h(t+1)=t+1$, respectively. The final bit is therefore marked exactly when $t=q-1$ is a power of two. The third copier exit already has the configuration $h(3)=1$, allowing state 4 to continue the same scan.

**Return.** On the zero after the right operand, state 4 moves right into 19. If the next cell is 1, another operand remains. States 19 and 20 return to the last bit of the right operand and state 9 reads its mark.

- If this bit is 1, state 9 erases the unique mark. State 26 crosses the zeros and erases the first bit of the right operand. State 27 erases the left guard and the active block, and 18 processes the next operand with active value zero. This implements the power-of-two branch of (3).
- If the last bit is 0, state 9 leaves it blank. States 21 and 22 restore the earlier part of the right operand to a run of ones, and 20 erases the left guard and enters 16. The source now has length $p$, the middle has length $q-1$, and the initial right block is empty. The seeded copy in (8) gives $1^{p+1}\,0\,1^q\,0\,1^p$. The third exit interprets it as the stack $(p,q+1,p,\ldots)$. All operands farther right stay in place, as required by the recursive branch of (3).

In the recursive branch $q-1\ge3$, so this is indeed the third exit. If the pushed $p$ is 1, the inner result is less than 1 and hence zero. The zero row consumes that single bit on return. Tape to the left of the active block is blank throughout. Copying extends into this blank area, and the zero branch erases the old operands before popping the next block. Thus the termination induction for (3) applies to the physical stack. Each trial reaches its root result in finite time. Every actual right operand has another nonempty block beyond it until a positive root result begins to scan the final $D$.

## 6. Retrying, halting and counting the output

If the root returns $x=0$, state 18 erases the first bit of the spare block, leaving $D-1$ ones. States 2 and 3 pass them. At the blank after their right separator, state 1 writes a 1 and returns left to 11. This sets up $1^{D-1}\,0\,1$ for the next trial, with $w'=D-1=N-6$. In particular,

$$
N'=2w'+12=2N .
$$

The first blank-tape trial makes $(p,q,D)=(7,5,7)$. It returns zero since $5-1=4$ is a power of two, leaving six source bits. The second trial makes $(19,17,19)$. Repeated doubling tests exactly $N=12,24,48,\ldots$, or $K=4,8,16,\ldots$.

If $x>0$, the final $D$ is scanned as a right operand. For the first time, state 19 sees a 0 beyond its right separator and halts with instruction `0→0`. The count on the whole tape is as follows.

| Location | Ones |
|---|---:|
| Positive root result | $x$ |
| Guard immediately to the right of the active block | 1 |
| First bit of the spare | 1 |
| Unique mark among the other $D-1$ spare cells | 1 |

Every other cell is zero. The preceding state analysis excludes an earlier halt, and the count is exactly $x+3$. By (1), (7), and the initial width-8 check, the first halt occurs at width $2^{q(5)}$, where $x=2^{q(5)}$. If that order never occurs, each trial finishes and starts the next. This proves both directions of the halting criterion and the output formula.

## Appendix. Complete numerical transition table

The two-way infinite tape starts blank, with symbols 0 and 1. State 1 starts, state 0 halts, and states 1–27 are the working states. A row gives the state number followed by its read-0 and read-1 instructions. For example, `1←11` writes a 1, moves one cell left and enters state 11. There are 54 instructions. [Numerical table](transitions.txt) · [Simulator-readable machine](machine.tm)

~~~text
 1  1←11  1←14
 2  0→18  1→3
 3  0→1   1→3
 4  0→19  1←5
 5  0←5   0←6
 6  1→7   1→8
 7  0→7   0→4
 8  0→8   1→4
 9  0←21  0←26
10  0→11  1→10
11  1←12  1→11
12  1→23  0→13
13  1←14  1→13
14  1→6   0←15
15  0←16  1←15
16  0←17  1←16
17  1→10  1←17
18  0→18  0→2
19  0→0   1←20
20  0←9   0←16
21  1←21  1←22
22  1←22  1←20
23  0→0   1→24
24  1→20  0→25
25  1←1   1←7
26  0←26  0←27
27  0→18  0←27
~~~

## Bounded checks and reproduction

The 54 numbered transitions agree entry by entry with the named machine. An independent forward-table calculation checks 86,368 reverse recurrence values, including 42,439 with $q<p$. Tape tests cover 912 copies with trailing data, five copier exits, 1,185 complete products with tails (549 zero and 636 positive), and seven failed-trial restarts. A genuinely blank start reaches the $N=12$ and $N=24$ arithmetic reference configurations at steps 300 and 2,630. [Checks](verification/verify.py) · [State-merge certificate](verification/state-groups.json)

For a small run that reaches the halt, initialize the layout at $w=3$. Then $N=18$ and $Z(13,11)=8$. After 126,983 steps the tape contains exactly $8+3=11$ ones. That test exercises the successful exit. The blank start generates $N=12\cdot2^i$, whose first successful trial is identified by the proof. To reproduce the checks from this directory, run

~~~text
python -B verification/verify.py
~~~
