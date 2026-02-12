# A Structural Remainder Framework for the Collatz Dynamics
### Cory 
### Draft — February 2026

---

## Abstract

We develop a structural decomposition of the Collatz map based on *dynamic box scaling* and *fractional remainder accumulation*.  
This framework models the evolution of an integer under the map  


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
- overflow events,
- and a structural potential function.

The framework is mechanistic rather than case‑based.  
It does not assert convergence; instead, it isolates a single conjectural component whose resolution would complete the argument.

---

## 2. Box Decomposition

### 2.1 Structural Level Parameter

We introduce a *structural level parameter* \(\ell(n)\), defined as a function assigning an effective scale to \(n\).  
A natural and canonical choice is the trailing‑ones length:


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

This decomposition is algebraically valid and serves as the coordinate system for the dynamics.

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

## 5. Heuristic Structural Dynamics

The recurrence suggests three qualitative regimes.  
These regimes are **heuristic descriptions**, not formal classifications.

### Definition 5.1 (Charging Regime)
A step is in the charging regime when the fractional remainder increases:


\[
R_{k+1} > R_k.
\]



### Definition 5.2 (Overflow Regime)
A step is in the overflow regime when:


\[
r_k + \text{new mass} \ge B(n_k),
\]


causing:


\[
\ell(n_{k+1}) = \ell(n_k) + 1.
\]



### Definition 5.3 (Discharge Regime)
A step is in the discharge regime when:


\[
\ell(n_{k+1}) < \ell(n_k).
\]



These regimes are intended as interpretive tools rather than proven universal behaviors.

---

## 6. Worked Example: The Trajectory of 3077

Consider \(n = 3077\) with \(B = 31\).



\[
3077 = 99\cdot 31 + 8, \qquad R = \frac{8}{31} \approx 0.258.
\]



Odd step:


\[
3n + 1 = 9232 = 297\cdot 31 + 29,
\]




\[
R' = \frac{29}{31} \approx 0.935.
\]



This example illustrates:

- amplification of the remainder,
- the effect of the +1 term,
- and the potential for overflow.

It does not imply that such behavior occurs universally.

---

## 7. Heuristic Motivation for the Remainder‑Amplification Conjecture

The recurrence


\[
R_{k+1} = \frac{1}{2^{v_k}} \left( 3R_k + \frac{1}{B} \right) \bmod 1
\]


contains three structural forces:

1. **Amplification:**  
   The factor of 3 tends to increase the remainder.

2. **Accumulation:**  
   The constant term \(1/B\) injects new mass at every step.

3. **Scale Reduction:**  
   Division by \(2^{v_k}\) shrinks the effective box size.

These forces suggest that the remainder may drift upward over time, potentially approaching the overflow threshold.  
This motivates the central conjecture.

---

## 8. The Remainder‑Amplification Conjecture

**Conjecture (Remainder‑Amplification).**  
Let \(n\) be any odd integer not in a discharge configuration.  
Let \(R_k\) denote the fractional remainder at step \(k\).  
Then:


\[
\limsup_{k\to\infty} R_k = 1.
\]



Interpretation:

> Under the proposed structural model, the fractional remainder may tend to approach the overflow threshold in the long run.

This conjecture is the central open component of the framework.  
No claim is made that it is proven.

---

## 9. Structural Potential Function

Define:


\[
F(n) = \alpha\,\ell(n) - \beta\,R(n),
\]


for fixed \(\alpha,\beta > 0\).

If the Remainder‑Amplification Conjecture holds, then \(F(n)\) may behave like a Lyapunov‑style potential across the charging, overflow, and discharge regimes.

This section describes a **candidate** invariant; no monotonicity or coercivity is claimed.

---

## 10. Limitations and Open Problems

### 10.1 Central Conjecture Unproven  
The framework depends on the Remainder‑Amplification Conjecture.  
Without it, the connection to global convergence remains speculative.

### 10.2 Underdeveloped Potential Function  
The proposed invariant \(F(n)\) is heuristic.  
A full analysis would require:

- understanding how \(\ell(n)\) evolves under \(T(n)\),
- determining whether \(F\) decreases in any regime,
- and establishing a connection to descent.

### 10.3 Qualitative Regimes Not Formalized  
The charging, overflow, and discharge regimes are descriptive and not formally defined as universal behaviors.

### 10.4 Gap Between Structure and Convergence  
The framework explains structural forces but does not yet show that these forces guarantee eventual descent to 1.

### 10.5 Limited Computational Evidence  
Only one example is provided.  
Further computational exploration could strengthen the plausibility of the conjecture.

### 10.6 Choice of \(\ell(n)\)  
The structural level parameter is flexible.  
A more canonical or optimized choice may improve the framework.

---

## 11. Conclusion

This paper presents a structural framework for analyzing the Collatz dynamics using dynamic scaling and fractional remainder accumulation.  
All algebraic components of the model are exact.  
The global behavior depends on a single conjectural component—the Remainder‑Amplification Conjecture.  
The framework is intended as a conceptual and structural contribution rather than a completed proof.

---

## References

*(To be added in final submission.)*
