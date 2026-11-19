# Retain the grafting of the E ports to accurately implement function substitution. · [中文版](active-E-graft-functional-substitution.zh-CN.md)

*English reading edition, translated with machine assistance. The title links to the dated Chinese manuscript.*

> Collected reading edition. The three main papers state the results of this collection.
> This edition retains the local proofs, their hypotheses and any withdrawals. Progress reports describe the state of work at the time.
> The locations of omitted passages on preset inputs are recorded in SOURCE_MANIFEST.json.
> The main papers give the numerical derivations for the natural parameters produced by the proofs. This historical note carries no additional Lean certification.

After freezing the prefix, the source graph will lose its global E ports; however, for shared 0, 1, and 2, only addresses greater than or equal to 3 are translated. This has accurate function substitution theorems in the pure E paradigm. This conclusion does not modify the pIBLP, and no external large notation has been compiled into this paradigm yet.

## 1 definition

Let F be a regular pattern with at least two rows, with r rows, and take b=r−2. For the exemplary pattern p_α in [P4 Pure E Analysis](<P4-pure-E-collapse.md>) (α<ε0), delete the first two fixed rows of p_α, and connect the remaining rows to F. The coordinate mapping is

$$
\iota_b(x)=
\begin{cases}
x,&x=0,1,2,\\
x+b,&x\ge3.
\end{cases}
\tag{1}
$$

The step size remains unchanged. The marks and rows of F are completely preserved, while the exemplary tail has no marks. The result is denoted as F⋆p_α. This is not a global translation; the source's first three points are identical to the target's global first three points.

If ps(α)=(u_1, …, u_k), and the ith tail line is specifically: u_i=0 at (0, 1, 2, r+i):2, otherwise it is (0, 1, 2, r+u_i, r+i):3).

## The operation of 2 and E is commutative.

When α is succeeded by another, the last line of F⋆p_α is still succeeded by E, and

$$
\operatorname{cut}(F\star p_\alpha)=F\star p_{\alpha-1}.
\tag{2}
$$

When α is the limit, let the last parent pointer of ps(α) be t>0. The source E threshold t+2 changes through the formula (1) becomes r+t≥r+1, strictly after F. Each round of auxiliary raw short copies of E only copies the same parent pointer blocks at the end of the paradigm, and never copies the lines or marks of F; the shared 0, 1, 2 remain fixed, and the internal pointers at the end are shifted by the same amount. Therefore, the coordinate-based copying formula provides

$$
E_{F\star p_\alpha}(m)=F\star E_{p_\alpha}(m)
=F\star p_{\alpha[2^m]}.
\tag{3}
$$

Note that the replication zone threshold is also shifted here, rather than being maintained as the source threshold. The shift length for the auxiliary E high zones is determined by the tail block length, and the F increase in b addresses is offset between the starting and ending points.

All E type complete copies of the guard still pass: the last control line contains 0, 1, 2, the starting point is p=1, and the low address 0 has a specified image. All other addresses are in the high translation area. This check does not require the ordinary M steps of F to also be copied. E is not scanned as a parent package, so the completion pattern of F is not read in reverse at the end.

## Theorem of Substitution for Functions3

Let B(m)=f_PP(F, m) be partial recursive functions. Define

$$
U_0^B(m)=B(m),\qquad
U_{\alpha+1}^B(m)=(U_\alpha^B)^{\circ2^m}(m),\qquad
U_\lambda^B(m)=U_{\lambda[2^m]}^B(m).
\tag{4}
$$

By induction from the formula (2), (3) for α), we obtain the exact equation for partial functions.

$$
\boxed{f_{\rm PP}(F\star p_\alpha,m)=U_\alpha^B(m).}
\tag{5}
$$

Here, the domain is accurately defined: the recursive calls on the left will invoke the values of the F parameters, while the calls on the right will also invoke the same parameters. If only F is known to have a practical realization on a certain parameter, then B should not be treated as a fully defined function without authorization. If the entire grafting graph has practical implementations that require quantitative bridges on a certain finite m, then the quantitative bridges will also ensure that all the call definitions used in the expression (5) are properly accounted for.

In the same algebra, when there are such actual grafting implementations of cap<κ4, the first two points κ0, and κ1, immediate results are obtained.

$$
q(5)>2^{U_\alpha^B(m)}.
\tag{6}
$$

This requires the actual initialization or controlled reachability of the grafting itself; it cannot be simply represented by a semantic-free hand-drawn pattern.

## 4 Scope of Action

The formula (5) is a true function substitution, not just an ordinal sum. In particular, the E successor line that only has one shared port transforms the B(m) into the B of the 2^m iteration; the tail parameters do not become invalid due to translation.

However, the control subscripts at the end of the paradigm are still limited to those below ε0. It does not directly provide the encoding for RPD, ARD, Y, wY, or other strictly super-BMS systems; nor does it constitute a structural strength conclusion of "a large structure wrapped in a small shell." Its purpose is to provide a proven correct successor iteration module for general external encodings, as well as a local grafting model that does not engulf the global 0, 1, 2 ports.

If a general source graph requires a transient M, it is only possible to replicate the root ≥3, perform scanning, and ensure that all parent references maintain this partition. Similar exchanges are possible. M with roots of 1 or 2 will transition into F, and the parent package scanning may also alter the output. This cannot be generalized by the formula (3). For truly external candidates beyond BMS, it is still necessary to address this cross-port controller issue, rather than simply referring to the pure E theorem.

## 5 bounded certificate

The exemplary E is verified (historical reference: `canonical-E-family-audit.py`). It is also denoted by the actual form F=P4 and F=S. The verification involves checking the subsequent cuts with m=0 up to 3, and grafting all the E identities. The verification focuses on the complete equality of core, step size, and marks, rather than just comparing the number of rows. The certificate does not provide the actual realization of the grafting diagram within the q5 window; this remains an independent assumption of the formula (6).
