Purpose: Expanded, beginner-friendly introductions to the key concepts referenced in connections.md,
so readers understand the background before you connect each topic to Arithmetic General Relativity (AGR).

How to use this file:
- Read each short primer to get the essential idea and why the topic is relevant.
- Each primer ends with 1–3 suggested references for deeper study. These references are the same canonical sources
  I recommended previously and are listed at the end for convenience.

1. I Ching (Book of Changes)
- What it is: An ancient Chinese text that encodes a system of divination and symbolic patterns built from two basic line types: solid (yang) and broken (yin).
- Core structure: Lines are combined into trigrams (3 lines, 8 possibilities) and hexagrams (6 lines, 64 possibilities). Each hexagram is read as a distinct symbolic state or transformation.
- Why it matters here: The I Ching is an early, culturally independent example of a binary symbolic system that naturally produces a 2^6 = 64 state space—useful as an empirical hint that finite combinatorial boundaries appear in symbolic systems.
- Further reading:
  - Wilhelm & Baynes, The I Ching (translations)
  - Shaughnessy, scholarly commentary on the I Ching

2. Genetic Code and Codons
- What it is: Biological information in DNA/RNA is encoded using four nucleotides. Groups of three nucleotides (codons) map to amino acids.
- Core structure: With 4 choices at each of 3 positions, the codon space has 4^3 = 64 distinct triplets, many coding for amino acids and a few acting as stops.
- Why it matters: Like the I Ching, the genetic code demonstrates a natural, functional system that closes at 64—showing the same combinatorial number can appear across very different domains.
- Further reading:
  - Watson & Crick introductory articles
  - Nirenberg & Matthaei on early decoding experiments

3. Turing Machines and the Halting Problem
- What it is: A Turing machine is an abstract model of computation with a finite control (states) and a tape over a finite alphabet. The Halting Problem asks whether an algorithm can decide for every program+input whether it halts.
- Core result: Alan Turing proved no single algorithm can decide halting for all program/input pairs; this yields fundamental limits on mechanistic self-analysis.
- Why it matters: This shows structural boundaries to what finite symbolic systems can determine about themselves — a key motivation for Symbolic Finitism.
- Further reading:
  - Turing (1936), "On Computable Numbers"
  - Davis, "Computability and Unsolvability"

4. P vs NP and the Exponential Wall
- What it is: P is the set of decision problems solvable in polynomial time; NP is the set for which a proposed solution can be verified in polynomial time. P vs NP asks whether every verifiable problem is also efficiently solvable.
- Core intuition: Many natural problems appear to require checking an exponentially large set of candidates; verification is short, search is long.
- Why it matters: If symbolic spaces are inherently exponentially large because of finite alphabets, then P ≠ NP becomes a statement about geometry of search spaces in AGR.
- Further reading:
  - Garey & Johnson, "Computers and Intractability"
  - Standard surveys on SAT and NP-completeness

5. Collatz (3n + 1) Problem
- What it is: Iterate n → n/2 if even, n → 3n+1 if odd. Conjecture: every positive integer eventually reaches 1.
- Core observations for beginners:
  - Look at trailing bits: even numbers shift right (divide by 2); odd numbers cause an ascent then often immediate descent.
  - Classifying residues mod 4 reveals a simple local rule difference: numbers ≡1 (mod 4) tend to get two divisions after 3n+1; numbers ≡3 (mod 4) behave differently.
- Why it matters: It is a simple rule producing complex global behavior; AGR uses modular/binary structure to explain why descent dominates over time.
- Further reading:
  - Surveys by Jeffrey Lagarias; historical notes on Collatz

6. Modular Arithmetic and the mod 4 Patterns
- What it is: Arithmetic of remainders; n mod 4 classifies integers by their last two binary bits.
- Core use: Many structural behaviors (odd powers, immediate descent in Collatz, parity arguments in exponential Diophantine equations) can be read off from small moduli.
- Why it matters: mod 4 acts as a tiny local geometry that can drive global behavior when aggregated across many numbers.
- Further reading:
  - Ireland & Rosen, "A Classical Introduction to Modern Number Theory"
  - Koblitz, "Number Theory and Cryptography"

7. Beal’s Conjecture and Exponential Diophantine Equations
- What it is: A conjecture about solutions to A^x + B^y = C^z with large exponents; it posits shared prime factors when exponents ≥ 3.
- Core modular insight: Simple residues (e.g., mod 4) can often rule out classes of solutions; such modular contradictions are standard tools.
- Why it matters: Demonstrates how small-base binary geometry can create impossibility constraints on algebraic equations.
- Further reading:
  - Statements and surveys on Beal’s Conjecture; classical material on Fermat’s Last Theorem

8. Mersenne Primes
- What it is: Primes of the form 2^p − 1 (p prime). In binary they appear as strings of p ones.
- Why rare: Structural constraints (divisibility tests like Lucas–Lehmer) plus combinatorial scarcity make them uncommon.
- Why it matters: They’re natural boundary cases in binary structure and are useful examples for discussing maximal resistance to factorization.
- Further reading:
  - Ribenboim, "The New Book of Prime Number Records"

9. Division Algebras, Hurwitz and Frobenius Theorems
- What it is: The classification of normed division algebras over the reals: only dimensions 1, 2, 4, 8 (R, C, H, O) occur.
- Core result: As dimension grows (2^k), algebraic properties (commutativity, associativity) are progressively lost.
- Why it matters: Shows rigid structural limits tied to binary powers; useful when arguing for discrete allowed geometries in arithmetic space.
- Further reading:
  - Hurwitz’s original work; Baez, "The Octonions"

10. Fibonacci Sequence and the Golden Ratio φ
- What it is: A simple linear recurrence F_n = F_{n−1} + F_{n−2}; the ratio F_n/F_{n−1} → φ (≈1.618).
- Why it matters: φ emerges as an optimal growth constant under minimal-memory recursion—an example of a universal structural constant.
- Further reading:
  - Koshy, "Fibonacci and Lucas Numbers"

11. Lie Groups, Noether’s Theorem, and Conservation Laws
- What they are: Lie groups model continuous symmetries; Noether’s theorem links continuous symmetries to conserved quantities.
- Why it matters: AGR interprets symmetry as zero curvature (κ = 0), and conservation laws as geodesics—this is the conceptual bridge to analytic dualities like functional equations.
- Further reading:
  - Noether’s original work; Fulton & Harris, representation theory

12. L‑functions, the Riemann Zeta Function, and BSD
- What they are: L-functions are complex-analytic objects encoding arithmetic data (primes, coefficients). Riemann’s ζ(s) encodes prime distribution; elliptic-curve L-functions encode rational points.
- Core statements:
  - Riemann Hypothesis: nontrivial zeros of ζ(s) lie on Re(s) = 1/2.
  - Birch & Swinnerton‑Dyer (BSD): relates the rank of an elliptic curve (algebraic) to the order of vanishing of its L-function at s = 1 (analytic).
- Why it matters: These are canonical examples of algebraic/analytic duality; AGR treats the critical line/point as a κ = 0 balance condition.
- Further reading:
  - Riemann’s 1859 memoir; Titchmarsh; Silverman on elliptic curves

13. Yang–Mills Theory and the Mass Gap
- What it is: A framework for fundamental forces using gauge fields. The Millennium problem asks to prove a positive lower bound Δ > 0 for non-zero energy excitations (the mass gap).
- Why it matters: AGR uses the mass gap as a physics analog of an information sink/discreteness enforced by negative curvature.
- Further reading:
  - Yang & Mills (1954); Clay Institute Millennium Problem page

14. Navier–Stokes Equations and Regularity
- What they are: PDEs describing viscous fluid flow. A major open question is whether smooth initial data can evolve singularities in finite time.
- Why it matters: AGR uses the physics of energy/enstrophy balance as an example where arithmetic curvature constraints can be interpreted as preventing blow-up (convergence/smoothing).
- Further reading:
  - Leray (foundational); Fefferman (Clay problem statement); Constantin & Foias

References (selected canonical sources)
- Turing, A. M., "On Computable Numbers..." (1936).
- Garey, M. R., & Johnson, D. S., "Computers and Intractability" (1979).
- Riemann, B., "Über die Anzahl der Primzahlen..." (1859); Titchmarsh, "Theory of the Riemann Zeta‑Function".
- Silverman, "The Arithmetic of Elliptic Curves"; Silverman & Tate, "Rational Points on Elliptic Curves".
- Baez, "The Octonions" (survey).
- Lagarias (ed.), "The Ultimate Challenge: The 3x+1 Problem".
- Clay Mathematics Institute, Millennium Problems pages (Yang–Mills, Navier–Stokes).

Next steps I can take
- Insert these primers into the main connections.md, chapter-by-chapter, with inline citations.
- Split the primers into separate chapter files (one primer per file) and add a shared references.md.
- Create a PR/branch on your repo with the expanded content; tell me branch name preference.

If you want me to proceed with inserting inline citations and preparing a PR, tell me whether to:
- modify connections.md in-place, or
- create a new folder (e.g., /chapters or /primers) and add one file per concept.
