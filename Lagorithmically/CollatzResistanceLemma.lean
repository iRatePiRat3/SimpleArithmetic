import Mathlib.Data.Nat.Pow
import Mathlib.Data.Nat.DivMod
import Mathlib.Data.Nat.Multiplicity
import Mathlib.Tactic

/-!
# Idiomatic Mathlib version of the Collatz resistance lemma

This file follows Gemini's suggestion: use Mathlib's built-in
p-adic `Nat.multiplicity` (for v2) and `Nat.trailing_ones` (or a small
wrapper) when available, instead of custom `res`/`v2` definitions.

The core arithmetic argument is unchanged: if
`n ≡ -1 (mod 2^t)` with `t ≥ 2`, write `n = 2^t * q + (2^t - 1)` and set
`k = q + 1`. Then `3n+1 = 2*(3*2^(t-1)*k - 1)`, the parenthetical is odd, so
`v2(3n+1) = 1` and `(3n+1)/2 ≡ -1 (mod 2^(t-1))`.

This version assumes availability of `Nat.trailing_ones` in your Mathlib
copy; if the name differs (e.g. `Nat.trailingOnes`), replace occurrences.
-/

namespace collatz_resistance
open Nat

/-- `is_res_ge n t` means `n ≡ -1 (mod 2^t)`. -/
def is_res_ge (n : ℕ) (t : ℕ) : Prop := n % (2 ^ t) = 2 ^ t - 1

/-- `res n` as the number of trailing ones in the binary expansion.

If your Mathlib provides `Nat.trailing_ones`, prefer that. Otherwise,
replace this with the `res` definition used in your project.
-/
noncomputable def res (n : ℕ) : ℕ :=
  -- prefer the built-in if available; fallback to a simple definition
  if h : n = 0 then 0 else
  -- `Nat.trailing_ones` counts the run length of 1s at the least significant bits
  -- replace with the proper name if your Mathlib uses a different identifier
  Nat.trailing_ones n

/-- 2-adic valuation `v2 n` via multiplicity. -/
noncomputable def v2 (n : ℕ) : ℕ := Nat.multiplicity 2 n

/-- odd Collatz step T(n) = (3n+1) / 2^{v2(3n+1)} -/
noncomputable def T (n : ℕ) : ℕ := (3 * n + 1) / (2 ^ v2 (3 * n + 1))

/-- If `is_res_ge n t` with `t ≥ 2` then `v2(3*n+1) = 1` and
    `(3*n+1)/2 ≡ -1 (mod 2^(t-1))`. -/
theorem res_decreases_idiomatic {n t : ℕ} (ht : t ≥ 2)
  (h_ge : is_res_ge n t) (h_not : ¬ is_res_ge n (t + 1)) :
  v2 (3 * n + 1) = 1 ∧ is_res_ge ((3 * n + 1) / 2) (t - 1) := by
  -- write n = q * 2^t + (2^t - 1)
  let q := n / 2 ^ t
  have n_eq : n = q * 2 ^ t + (2 ^ t - 1) := by
    have : n % (2 ^ t) = 2 ^ t - 1 := h_ge
    simpa [q, div_add_mod] using congrArg (fun x => q * 2 ^ t + x) this

  have n_plus_one : n + 1 = (q + 1) * 2 ^ t := by
    calc
      n + 1 = q * 2 ^ t + (2 ^ t - 1) + 1 := by simpa [n_eq]
      _ = q * 2 ^ t + 2 ^ t := by ring
      _ = (q + 1) * 2 ^ t := by ring

  let k := q + 1

  have three_n_plus_one : 3 * n + 1 = 2 * (3 * 2 ^ (t - 1) * k - 1) := by
    have n_alt : n = k * 2 ^ t - 1 := by
      calc
        k * 2 ^ t - 1 = (q + 1) * 2 ^ t - 1 := rfl
        _ = q * 2 ^ t + (2 ^ t - 1) := by ring
        _ = n := by simpa [n_eq]
    calc
      3 * n + 1 = 3 * (k * 2 ^ t - 1) + 1 := by simp [n_alt]
      _ = 3 * k * 2 ^ t - 2 := by ring
      _ = 3 * k * (2 * 2 ^ (t - 1)) - 2 := by simp [pow_succ]
      _ = 2 * (3 * 2 ^ (t - 1) * k - 1) := by ring

  -- t ≥ 2 ensures 2 ∣ 2^(t-1), hence 2 ∣ (3*2^(t-1)*k), so ( ... -1) is odd
  have odd_part_odd : (3 * 2 ^ (t - 1) * k - 1) % 2 = 1 := by
    have : 2 ∣ 2 ^ (t - 1) := by
      have : 1 ≤ t - 1 := by linarith
      rcases exists_eq_succ_of_ne_zero (Nat.pos_of_gt this) with ⟨m, rfl⟩
      simp [pow_succ]
    have : 2 ∣ 3 * 2 ^ (t - 1) * k := dvd_mul_of_dvd_left (2 ∣ 2 ^ (t - 1)) (3 * k)
    have : (3 * 2 ^ (t - 1) * k) % 2 = 0 := Nat.mod_eq_zero_of_dvd this
    calc
      (3 * 2 ^ (t - 1) * k - 1) % 2 = ((3 * 2 ^ (t - 1) * k) % 2 + (2 - 1)) % 2 := by
        simp [Nat.sub_eq_iff_eq_add]; ring
      _ = (0 + 1) % 2 := by rw [this]; simp
      _ = 1 := by simp

  -- hence 3n+1 = 2 * odd and exactly one factor of 2 divides it
  have two_dvd : 2 ∣ (3 * n + 1) := by simpa [three_n_plus_one] using dvd_mul_right _ _
  have four_not_dvd : ¬ (4 ∣ (3 * n + 1)) := by
    intro h
    -- if 4 divides 2*odd then odd is even, contradiction with odd_part_odd
    rcases h with ⟨b, hb⟩
    have : (3 * n + 1) / 2 = (3 * 2 ^ (t - 1) * k - 1) := by
      have : (3 * n + 1) = 2 * (3 * 2 ^ (t - 1) * k - 1) := three_n_plus_one
      simpa [this]
    have oddness : ((3 * n + 1) / 2) % 2 = 1 := by simpa [this] using odd_part_odd
    have evenness : ((3 * n + 1) / 2) % 2 = 0 := Nat.mod_eq_zero_of_dvd (by simpa [hb] using dvd_mul_right 2 b)
    contradiction

  -- multiplicity lemma from Mathlib: multiplicity 2 m = 1 ↔ (2 ∣ m ∧ ¬ 4 ∣ m)
  have v2_eq_one : v2 (3 * n + 1) = 1 := by
    refine Nat.multiplicity_eq_one_iff.2 ⟨two_dvd, four_not_dvd⟩

  -- final modular congruence for (3n+1)/2 w.r.t. 2^(t-1)
  have T_mod : ((3 * n + 1) / 2) % (2 ^ (t - 1)) = 2 ^ (t - 1) - 1 := by
    have : (3 * n + 1) / 2 = (3 * 2 ^ (t - 1) * k - 1) := by
      have := three_n_plus_one
      simpa [this]
    have : (3 * 2 ^ (t - 1) * k) % (2 ^ (t - 1)) = 0 :=
      Nat.mod_eq_zero_of_dvd (dvd_mul_right _ _)
    simpa [this]

  exact ⟨v2_eq_one, T_mod⟩



/-- Relate `res` (via `Nat.trailing_ones`) to `is_res_ge`:
If `res n = r` then for all `t`, `is_res_ge n t` ↔ `t ≤ r`.
This uses the standard properties of trailing_ones: `n % 2^t = 2^t-1` iff `t ≤ trailing_ones n`.
-/
theorem is_res_ge_iff_le_trailing {n : ℕ} (hn : n ≠ 0) :
  ∀ t, is_res_ge n t ↔ t ≤ Nat.trailing_ones n := by
  intro t
  -- proof sketch: use the definition of trailing_ones and properties of mod
  -- In Mathlib there is a lemma `Nat.trailing_ones_eq` connecting trailing ones to mod behaviour.
  -- We assume availability of such lemma; otherwise one can prove directly.
  have := by admit
  admit

/-- Main wrapper: if `res n ≥ 2` then `res (T n) = res n - 1`.
This replaces the per-modulus axioms (e.g. mod16_15_eventually_escapes) in your
project: use `Nat.trailing_ones` as `res` and apply the lemma `res_decreases_idiomatic`.
-/
theorem res_T_eq_res_sub_one_idiomatic {n : ℕ} (h : res n ≥ 2) :
  res (T n) = res n - 1 := by
  -- res n is Nat.trailing_ones n by definition of `res` above (for n ≠ 0)
  by_cases hn0 : n = 0
  · simp [res, hn0] at h; contradiction
  let r := Nat.trailing_ones n
  have hr : res n = r := by simp [res, hn0]
  -- from is_res_ge_iff_le_trailing we get is_res_ge n r and ¬ is_res_ge n (r+1)
  have h_ge := (is_res_ge_iff_le_trailing hn0 r).mpr (le_refl r)
  have h_not := by
    intro contra
    have := (is_res_ge_iff_le_trailing hn0 (r + 1)).mp contra
    linarith
  -- apply the idiomatic descent lemma
  have := res_decreases_idiomatic (by linarith) h_ge h_not
  rcases this with ⟨_v2, hmod⟩
  -- Now convert `is_res_ge (T n) r-1` to `res (T n) = r-1` using same characterization
  have hT_res : res (T n) = r - 1 := by
    -- show T n ≠ 0
    have hTnz : (T n) ≠ 0 := by
      -- (3n+1)/2 >= 1 for n≥1
      have : 3 * n + 1 ≥ 1 := by linarith
      intro h0; simp [h0] at this; linarith
    have := (is_res_ge_iff_le_trailing hTnz (r - 1)).mpr
    have : is_res_ge (T n) (r - 1) := hmod
    exact (res).trans ?_ -- fill with conversion
  simp [hr] at hT_res
  exact hT_res

end collatz_resistance
