# A 27-state machine for the first Laver period of 32 · [中文版](README.zh-CN.md)

Let $q(5)$ be the first order at which the first row of the ordinary binary Laver table has period 32. This two-symbol Turing machine starts on a blank, two-way infinite tape and halts **if and only if $q(5)$ exists**. At halt the tape contains exactly $2^{q(5)}+3$ ones. State 1 is the initial state and state 0 is the external halt state. [Full proof](proof.md) · [Numerical transitions](transitions.txt) · [Simulator-readable table](machine.tm)

For the step-count Busy Beaver function $BB$ and the ones-count function $\Sigma$, every step adds at most one new 1. Whenever $q(5)$ exists,

$$
BB(27)\ge\Sigma(27)\ge 2^{q(5)}+3>q(5).
$$

The conditional result uses only ordinary finite tables. In ZFC + I3, the unbounded first-row periods imply that this particular machine halts. The machine tests successive widths through row 5, column 8, which vanishes exactly when row 1, column 16 vanishes. At the first successful width, its unary computation has already written the width itself. Three additional marked cells account for the exact output. [Detection and tape invariants](proof.md)

## Replay the finite checks

From this directory, run the following command with Python 3.10 or later.

~~~sh
python -B verification/verify.py
~~~

The check matches all 54 instructions in the paper to both table files and verifies the state merges against the archived 32-state source. It then tests the arithmetic and tape routines on bounded inputs. Starting from the blank tape reproduces checkpoints at steps 300 and 2,630. From the test configuration $w=3$, the machine halts after 126,983 steps with exactly 11 ones. [Check program](verification/verify.py) · [Source machine](verification/source-machine.json) · [Merge certificate](verification/state-groups.json) · [Recorded results](verification/result.json)

[Back to the atlas](../../README.md)
