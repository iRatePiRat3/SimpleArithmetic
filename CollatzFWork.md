# A Structural Remainder Framework for the Collatz Dynamics
### iRatePiRat3
### Draft — February 2026

---

## Abstract

We develop a structural decomposition of the Collatz map based on *dynamic box scaling* and *fractional remainder accumulation*.  
This framework models the evolution of an integer under the map  


\[
T(n) = \frac{3n+1}{2^{v_2(3n+1)}}
\]


as an interaction between stable mass (full boxes), dynamic mass (fractional remainders), and scale changes induced by powers of two.  
The affine map \(3n+1\) is shown to exert systematic upward pressure on the fractional remainder, while division by powers of two reduces the effective scale.  
These opposing forces suggest a cycle of *charging*, *overflow*, and *discharge* phases.  
We formalize this structure and identify a central conjecture—the **Remainder‑Amplification Conjecture**—which, if established, would complete the framework and imply global descent.  
The purpose of this paper is to present the structural model, not to claim a proof of the Collatz conjecture.

---

## 1. Introduction

The Collatz problem remains unresolved despite extensive study.  
Existing approaches typically rely on modular casework, parity sequences, or probabilistic heuristics.  
These methods provide insight into local behavior but do not yield a unified structural explanation for the global dynamics.

This paper proposes a new viewpoint based on:

- dynamic scaling,
- remainder accumulation,
- overflow events,
- and a structural invariant.

The framework is mechanistic rather than case‑based.  
It does not claim to prove convergence; instead, it isolates a single conjectural component whose resolution would complete the argument.

---

## 2. Box Decomposition

For any odd integer \(n\), choose a dynamic scale (“box size”)


\[
B(n) = 2^{\ell(n)},
\]


where \(\ell(n)\) is a structural level parameter.

Decompose \(n\) uniquely as


\[
n = q(n)\,B(n) + r(n), \qquad 0 \le r(n) < B(n).
\]



Define the **fractional remainder**


\[
R(n) = \frac{r(n)}{B(n)}.
\]



Interpretation:

- \(q(n)\): stable mass  
- \(r(n)\): dynamic mass  
- \(R(n)\): proximity to overflow at the current scale  

This decomposition is algebraically valid and serves as the coordinate system for the dynamics.

---

## 3. The Odd Collatz Step in Box Coordinates

The odd step is


\[
T(n) = \frac{3n+1}{2^{v_2(3n+1)}}.
\]



Expanding \(3n+1\) in box form:


\[
3n + 1 = 3qB + (3r + 1).
\]



Let


\[
s = \left\lfloor \frac{3r+1}{B} \right\rfloor, \qquad 
r' = (3r+1) \bmod B.
\]



Before division:


\[
3n+1 = (3q + s)B + r'.
\]



Division by \(2^{v_2(3n+1)}\) rescales both terms.  
The constant term \(+1\) is never removed; it is redistributed across scales.

All statements in this section follow directly from algebraic expansion.

---

## 4. Fractional Remainder Recurrence

Let \(R_k = r_k / B\).  
The odd step induces:


\[
R_{k+1} = \frac{1}{2^{v_k}} \left( 3R_k + \frac{1}{B} \right) \bmod 1,
\]


where \(v_k = v_2(3n_k+1)\).

Interpretation:

- **Tripling** amplifies the remainder.  
- **The +1 term** injects new mass.  
- **Division** reduces scale but does not eliminate remainder.  
- **Modulo 1** captures overflow into new full boxes.

This recurrence is exact and follows from the decomposition.

---

## 5. Structural Accumulation Dynamics

The recurrence suggests three qualitative phases:

### 5.1 Early Phase  
Full boxes dominate; remainder is small.

### 5.2 Middle Phase  
Division by powers of two reduces the effective scale; remainder becomes proportionally larger.

### 5.3 Late Phase  
Full boxes diminish; remainder carries accumulated contributions.

These phases are descriptive and based on the algebraic structure of the recurrence.  
They do not assert inevitability of any particular long‑term behavior.

---

## 6. Emergent Structural Patterns

As remainder mass accumulates, the binary representation of \(n\) may develop complex patterns (e.g., \(11000010101\ldots\)).  
These patterns arise from:

- accumulation of \(+1\) units in the remainder,
- amplification by the tripling operation,
- carry propagation from \(3n+1 = 2n + n + 1\).

These observations are structural consequences of binary arithmetic and do not imply convergence.

---

## 7. The Remainder‑Amplification Conjecture

**Conjecture (Remainder‑Amplification).**  
Let \(n\) be any odd integer not in a discharge configuration.  
Let \(R_k\) denote the fractional remainder at step \(k\).  
Then:


\[
\limsup_{k\to\infty} R_k = 1.
\]



Interpretation:

> Under the proposed structural model, the fractional remainder cannot remain uniformly bounded away from 1 indefinitely.

This conjecture is the central open component of the framework.  
No claim is made that it is proven.

---

## 8. Global Structural Invariant

Define:


\[
F(n) = \alpha\,\ell(n) - \beta\,R(n),
\]


for fixed \(\alpha,\beta > 0\).

If the Remainder‑Amplification Conjecture holds, then \(F(n)\) behaves like a Lyapunov‑style potential across the charging, overflow, and discharge phases.

This section describes a proposed invariant; it does not assert that \(F(n)\) is proven to be monotone or coercive.

---

## 9. Conclusion

This paper presents a structural framework for analyzing the Collatz dynamics using dynamic scaling and fractional remainder accumulation.  
All algebraic components of the model are exact.  
The global behavior depends on a single conjectural component—the Remainder‑Amplification Conjecture.  
The framework is intended as a conceptual and structural contribution rather than a completed proof.

---

## References

*(To be added in final submission.)*
