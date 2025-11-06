# Proof Status (Arithmetic General Relativity & Collatz)

This file records formalization status and any axiom dependencies. Update as proofs are completed or dependencies change.

| Claim / Theorem name | Status | File path | Theorem name (in file) | Dependencies / Notes |
|---|---:|---|---|---|
| Collatz structured formalization (canonical) | Present (depends on axiom) | `Lagorithmically/CollatzCleanStructured.lean` | multiple lemmas culminating in structured convergence lemmas | Relies on axiom declared in `Lagorithmically/CollatzEscapePatterns.lean` (`mod16_15_eventually_escapes`) to break a circular dependency. |
| `mod16_15_eventually_escapes` (escape from n ≡ 15 mod 16) | AXIOM | `Lagorithmically/CollatzEscapePatterns.lean` | axiom / placeholder | Intentionally declared as an axiom to avoid circular imports. Replace with a proof to remove axiom dependency. |
| Curvature classification (AGR) | Present (needs dependency verification) | `Lagorithmically/ArithmeticGeneralRelativity.lean` | `curvature_classification_theorem_rigorous` | Depends on `Lagorithmically.BirkhoffErgodicThm`, `Lagorithmically.PvNP_BinaryPatterns`, `Lagorithmically.RiemannBinary` etc. Verify all local modules typecheck. |
| Geodesic attractor principle (κ < 0) | Present (verify) | `Lagorithmically/ArithmeticGeneralRelativity.lean` | `geodesic_attractor_principle_rigorous` | Uses Birkhoff helpers and well-foundedness lemmas. |
| Geodesic symmetry principle (κ = 0) | Present (placeholder elements) | `Lagorithmically/ArithmeticGeneralRelativity.lean` | `geodesic_symmetry_principle_rigorous` | Some proof bodies are placeholders — review zero-one law usage. |
| Geodesic barrier principle (κ > 0) | Present (logical details to verify) | `Lagorithmically/ArithmeticGeneralRelativity.lean` | `geodesic_barrier_principle_rigorous` | Clarify modeling of search/verify cost and gap argument. |
| PvNP mapping (P vs NP) | Partial / depends | `Lagorithmically/PvNP_BinaryPatterns.*` | — | Verify domain-specific reductions and definitions of ProblemInNP/ProblemInP used by theorem statements. |
| Riemann mapping (RH) | Partial / depends | `Lagorithmically/RiemannBinary.*` | `riemann_hypothesis` (claimed) | Check mapping from analytic zeros to AGR curvature and ensure no hidden axioms. |
| Beal's, BSD, Yang-Mills, Navier-Stokes, Hodge | Sketch / conceptual | `Lagorithmically/*` | — | These require significant domain-specific formal reductions; list exact files and theorem names when ready. |

Notes and actions:
- Mark any theorem that uses nonstandard axioms explicitly with `AXIOM` and list those axioms and where they are declared.
- Add per-module READMEs or docstrings summarizing the key lemmas supporting each top-level claim (helps reviewers jump to the right lemmas).
- Add a CI workflow to run `lake build` and include the badge in README so reviewers can quickly verify typechecking.
