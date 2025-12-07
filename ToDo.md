#  To-Do List 

## I. Core Proof Closures 

These tasks involve replacing existing placeholders (`admit`/`sorry`) with the necessary arithmetic or structural proofs in the Lean code.

---

### **P1: Collatz Descent Lemma** 
* **Structural Purpose:** Proves the core **κ < 0** (negative curvature/convergence) principle. This closes the gap in the Lean proof (`CollatzResistanceCombined.md`).
* **Mathematical Notation:** $\forall n: n \equiv 2^t - 1 \pmod{2^t} \implies T(n) \equiv 2^{t-1} - 1 \pmod{2^{t-1}}$  **OR** $$T(2^t - 1) = (2^t - 1) + 2^{t-1} = 3 \cdot 2^{t-1} - 1$$
* **Descriptive Detail:** Formal proof that applying the Collatz transformation $T(n) = \frac{3n+1}{2^k}$ to a number $n$ with maximum resistance ($\mathbf{2^t-1}$) **always** results in a number with **strictly reduced resistance** ($2^{t-1}-1$). This proves the geometric necessity of descent.

---

### **P2 : Beal's Contradiction Primitives**
* **Structural Purpose:** Closes the final four `sorry` gaps in the Beal's Conjecture proof by enforcing fundamental parity constraints.
* **Mathematical Notation:** $x,y,z \ge 3 \implies \nu_2(A^x+B^y) = \nu_2(C^z)$ and $(A^x \pmod 4) + (B^y \pmod 4) \not\equiv C^z \pmod 4$
* **Descriptive Detail:** Formalization of the $\mathbf{\nu_2}$ (2-adic valuation) and $\mathbf{\pmod 4}$ parity constraints on large powers ($x, y, z \ge 3$). This verifies that the only way $A^x+B^y=C^z$ can hold without a $\mathbf{\pmod 4}$ contradiction is if the terms share a common factor, establishing the **gcd > 1** result.

---

## II. Conceptual Principles

These tasks formalize the **Rules of Motion** derived from the $\mathbf{\pmod{16}}$ analysis, establishing the foundational theorems for the AGR framework.

---

### **P3 : Structural Equivalence & Shift Operator** 
* **Structural Purpose:** Formalizes the non-random, deterministic nature of the $\mathbf{\pmod{16}}$ transformation.
* **Mathematical Notation:** $\forall n: n \equiv 1 \pmod{16} \implies T^k(n) \equiv 1 \pmod{4}$, and $T(n) \pmod{16} = n \pmod{16} - 2^m \quad (m \in \{2, 3\})$
* **Descriptive Detail:** Proves that the $\mathbf{1 \pmod{16}}$ class (**Geodesic Anchor**) is a **stable attractor** (e.g., $577 \to 433$). Crucially, it shows that the Collatz transformation acts as a **deterministic linear shift operator** ($\mathbf{-4}$ or $\mathbf{-8}$ jump) on the $\mathbf{\pmod{16}}$ residue, proving the structural control over the path.

---

### **P4 : Resistance Degradation Failure** 
* **Structural Purpose:** Proves that all temporary resistance gains are structurally unstable, guaranteeing ultimate convergence.
* **Mathematical Notation:** $\exists k > 0: \text{res}(T^k(n)) < \text{res}(n) \quad \text{where } \text{res}(n) = \nu_2(n+1)$
* **Descriptive Detail:** Proof that any temporary $\mathbf{climb in resistance}$ (e.g., $7 \to 11 \pmod{16}$) or temporary **resistance invariance** ($15 \to 15 \pmod{16}$) must be followed by a structurally mandated large-factor collapse ($\mathbf{\gg 4}$), leading to the **Geodesic Anchor Capture** and reduction of $\text{res}(n)$.

---

### **P5 : Mod 16 Resistance Classification** 
* **Structural Purpose:** Formalizes the **Rules of Motion** by linking residue to required division factor.
* **Mathematical Notation:** $n \equiv r \pmod{16} \implies \nu_2(3n+1) = k_r \quad (k_r \in \{1, 2, 4\} \text{ is constant for fixed } r)$
* **Descriptive Detail:** Formal proof that the $\mathbf{\pmod{16}}$ residue $r$ **deterministically** dictates the next even number's exact divisibility factor, $2^{k_r}$. This proves the local control mechanism (e.g., $\mathbf{5 \pmod{16}}$ guarantees $k_r \ge 4$).

---

### **P6 : Sparse Cycle Hypothesis** 
* **Structural Purpose:** Eliminates the possibility of non-trivial cycles by targeting numbers with low structural complexity.
* **Mathematical Notation:** $\nexists n = 2^k+1: \frac{3^{N_{odd}} \cdot n + \sum (\text{terms})}{2^{N_{total}}} = n \quad \text{for } n > 1$
* **Descriptive Detail:** Proof that numbers with sparse binary patterns ($\mathbf{2^k+1}$) cannot satisfy the required growth-to-collapse ratio ($\mathbf{3^{N_{odd}} = 2^{N_{total}}}$) necessary for a non-trivial cycle, confirming $\mathbf{1}$ as the unique Attractor.

---

### **P7 : Difference Sequence Principle** 
* **Structural Purpose:** Provides a linear algebra perspective on the growth/collapse dynamics.
* **Mathematical Notation:** $T_{\text{even}}(n) = \frac{3n+1}{2} \implies T_{\text{even}}(n) - n = 2n+1$
* **Descriptive Detail:** Simple arithmetic proof demonstrating that the linear difference between consecutive odd numbers is an odd number ($2n+1$). This provides a complementary linear view of the geometric growth/collapse.

---

### **P8 : Structural Reduction Principle** 
* **Structural Purpose:** Proves the core assumption that the Collatz function operates purely on the odd component.
* **Mathematical Notation:** $n = 2^k \cdot n_{odd} \implies \text{Collatz}(n) \to \dots \to n_{odd}$ is the only structural path
* **Descriptive Detail:** Proof that any number $n$ is structurally equivalent to its odd component $n_{odd}$, formalizing the idea that **trailing zeros are structurally irrelevant** and the Collatz function is purely an operator on the $n_{odd}$ domain.

---

### **P9 : Popcount Parity Classification** 
* **Structural Purpose:** Links information theory (binary patterns) to Collatz dynamics.
* **Mathematical Notation:** $\text{Popcount}(2^k-1) = k \implies \text{Parity}(k) \text{ predicts } \nu_2(T(2^k-1))$
* **Descriptive Detail:** Proof that the parity of the number of set bits (Popcount) for a **Maximum Resistance** number ($2^k-1$) is structurally predictive of the subsequent strength of the collapse, further detailing the **Descent Lemma**.

---

## III.  Structural Contradiction 

---

### **P10 : Axiom Contradiction Cleanup** 
* **Structural Purpose:** Ensures the AGR framework's claim of being "axiom-free" is rigorously defensible.
* **Mathematical Notation:** *Non-mathematical task: Refactor/Rephrase "no axioms" claim.*
* **Descriptive Detail:** Must resolve the contradiction between the AGR claim and the citation of axioms (e.g., Cook-Levin, Binary Gap) in the code/comments. The recommended action is to rephrase the claim to "**no *extrinsic* axioms**," meaning only axioms derived directly from the fundamental binary structure are used.
