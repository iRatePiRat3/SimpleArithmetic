# A Structural Remainder Framework for the Collatz Dynamics
### Cory [Last Name]
### Draft — February 2026

---

## Abstract

We develop a structural decomposition of the Collatz map based on *dynamic box scaling*, *fractional remainder accumulation*, and a newly identified phenomenon: **quantized injection** of mass from the constant term in the affine map \(3n+1\).  
This framework models the evolution of an integer under  


\[
T(n) = \frac{3n+1}{2^{v_2(3n+1)}}
\]


as an interaction between stable mass (full boxes), dynamic mass (fractional remainders), and scale changes induced by powers of two.  
The algebraic decomposition is exact, and the resulting recurrence suggests a cycle of *charging*, *overflow*, and *discharge* phases.  
We identify a central conjecture—the **Remainder‑Amplification Conjecture**—which, if established, would imply global descent within this framework.  
The purpose of this paper is to present the structural model, its motivations, and its limitations, not to claim a proof of the Collatz conjecture.

---

## 1. Introduction

The Collatz problem remains unresolved despite extensive study.  
Existing approaches typically rely on modular casework, parity sequences, or probabilistic heuristics.  
These methods provide insight into local behavior but do not yield a unified structural explanation for the global dynamics.

This paper proposes a new viewpoint based on:

- dynamic scaling,
- remainder accumulation,
- quantized injection from the +1 term,
- overflow events,
- and a structural potential function.

The framework is mechanistic rather than case‑based.  
It does not assert convergence; instead, it isolates a single conjectural component whose resolution would complete the argument.

---

## 2. Box Decomposition

### 2.1 Structural Level Parameter

We introduce a *structural level parameter* \(\ell(n)\), defined as a function assigning an effective scale to \(n\).  
A natural choice is the trailing‑ones length:


\[
\ell(n) = \max\{k \ge 0 : n \equiv -1 \pmod{2^k}\}.
\]



This choice ensures:

- \(\ell(n)\) is well‑defined for all odd \(n\),
- \(\ell(n)\) increases when the binary representation ends in more 1s,
- \(\ell(n)\) decreases under certain Collatz steps (the discharge regime).

Other monotone scale functions could be used; the framework does not depend on this specific choice.

### 2.2 Box Representation

Define the box size:


\[
B(n) = 2^{\ell(n)}.
\]



Decompose \(n\) uniquely as:


\[
n = q(n)\,B(n) + r(n), \qquad 0 \le r(n) < B(n).
\]



Define the **fractional remainder**:


\[
R(n) = \frac{r(n)}{B(n)}.
\]



Interpretation:

- \(q(n)\): stable mass  
- \(r(n)\): dynamic mass  
- \(R(n)\): proximity to overflow at the current scale  

---

## 3. The Odd Collatz Step in Box Coordinates

The odd step is:


\[
T(n) = \frac{3n+1}{2^{v_2(3n+1)}}.
\]



Expanding \(3n+1\) in box form:


\[
3n + 1 = 3qB + (3r + 1).
\]



Let:


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

---

# 5. Quantized Injection and Overflow Mechanics

A key structural feature emerges when separating the contributions of the +1 term and the tripled remainder.

## 5.1 Quantization of the +1 Contribution

Since the odd step divides by \(2^{v_2(3n+1)}\), the +1 term contributes:


\[
\frac{1}{2^{v_2(3n+1)}}.
\]



Thus the +1 contribution is always a **dyadic rational**:


\[
1,\ \frac{1}{2},\ \frac{1}{4},\ \frac{1}{8},\dots
\]



Empirically, in all tested trajectories, the +1 contribution overwhelmingly takes values in:


\[
\{0.25,\ 0.5,\ 0.75,\ 1.0\}.
\]



### Lemma 5.1 (Quantized Injection)
The +1 term contributes a dyadic rational to the fractional remainder, determined solely by the 2‑adic valuation of \(3n+1\).  
This contribution is discrete, predictable, and scale‑invariant.

## 5.2 Overflow Condition

Overflow occurs when:


\[
\frac{3r}{B} + \frac{1}{2^{v_2(3n+1)}} > 1.
\]



Thus:

- The +1 term provides a **quantized baseline**.
- The \(3r/B\) term provides **volatile pressure**.
- Overflow is triggered when the volatile term surges above the quantized floor.

## 5.3 Roles of the Two Components

- **+1 term**  
  - stable  
  - quantized  
  - scale‑invariant  
  - provides steady upward pressure  

- **3r term**  
  - volatile  
  - unbounded relative to B  
  - responsible for overflow events  
  - drives structural transitions  

This division of roles is supported by computational evidence.

---

## 6. Heuristic Structural Dynamics

The recurrence suggests three qualitative regimes.  
These regimes are **heuristic descriptions**, not formal classifications.

### Charging Regime  


\[
R_{k+1} > R_k.
\]



### Overflow Regime  


\[
\frac{3r}{B} + \frac{1}{2^{v_2(3n+1)}} > 1.
\]



### Discharge Regime  


\[
\ell(n_{k+1}) < \ell(n_k).
\]



---

## 7. Worked Example: n = 31 (Separated Contributions)

Your separated‑tracking data shows:

- +1 contribution oscillates among \(\{0.25, 0.5, 0.75, 1.0\}\)
- ×3 contribution varies widely, sometimes exceeding 1
- Overflow events correspond to ×3 surges

Example (Step 3):

- +1 contrib = 0.5  
- ×3 contrib = 1.015625  
- Total = 1.515625 → overflow

This illustrates the quantized‑baseline + volatile‑pressure mechanism.

---

## 8. Computational Evidence (Summary)

Across trajectories for \(n = 31, 27, 231, 3077\):

- Mean fractional remainder ≈ 0.48–0.65  
- Max fractional remainder ≈ 0.95–0.999  
- Overflow events are common  
- ℓ decreases more often than it increases  
- +1 contribution is quantized  
- ×3 contribution drives overflow  

These observations motivate the central conjecture.

---

## 9. The Remainder‑Amplification Conjecture

**Conjecture.**  
Let \(R_k\) be the fractional remainder at step \(k\).  
Then:


\[
\limsup_{k\to\infty} R_k = 1.
\]



Motivation:

- Quantized +1 injection prevents R from staying small  
- Volatile ×3 remainder frequently surges  
- Overflow events are common in empirical data  

No claim of proof is made.

---

## 10. Structural Potential Function

Define:


\[
F(n) = \alpha\,\ell(n) - \beta\,R(n).
\]



If the conjecture holds, \(F(n)\) may behave like a Lyapunov‑style potential across the charging, overflow, and discharge regimes.

No monotonicity is claimed.

---

## 11. Limitations and Open Problems

- The central conjecture remains unproven  
- The potential function is heuristic  
- Regimes are descriptive, not formal  
- Overflow frequency is empirical, not universal  
- Choice of \(\ell(n)\) may be optimized  
- More computational data is needed  

---

## 12. Conclusion

This paper presents a structural framework for analyzing the Collatz dynamics using dynamic scaling, fractional remainder accumulation, and quantized injection.  
All algebraic components are exact.  
The global behavior depends on a single conjectural component—the Remainder‑Amplification Conjecture.  
The framework is intended as a conceptual and structural contribution rather than a completed proof.

---

## References

*(To be added in final submission.)*
