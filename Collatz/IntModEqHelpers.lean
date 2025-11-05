import Mathlib.Data.Int.ModEq
import Mathlib.Tactic

/-!
# Integer Modular Arithmetic Helpers

Helper lemmas for Int.ModEq that are missing from mathlib.
These lemmas are needed for the general case of the Collatz modular mapping proof.
-/

/-- If a ≡ b (mod 2m) and both a and b are divisible by 2,
    then a/2 ≡ b/2 (mod m) -/
lemma int_modEq_div_two (a b m : ℤ) 
    (h_mod : a ≡ b [ZMOD 2*m]) 
    (h_dva : 2 ∣ a) (h_dvb : 2 ∣ b) :
    a/2 ≡ b/2 [ZMOD m] := by
  rw [Int.modEq_iff_dvd] at h_mod ⊢
  obtain ⟨c, hc⟩ := h_mod
  obtain ⟨a', ha⟩ := h_dva
  obtain ⟨b', hb⟩ := h_dvb
  rw [ha, hb] at hc
  have h_factor : b' - a' = m * c := by
    have h2 : 2 * (b' - a') = 2 * m * c := by
      calc 2 * (b' - a') = 2 * b' - 2 * a' := by omega
                       _ = 2 * m * c := hc
    linarith
  rw [ha, hb]
  rw [Int.mul_ediv_cancel_left b' (by norm_num : (2:ℤ) ≠ 0)]
  rw [Int.mul_ediv_cancel_left a' (by norm_num : (2:ℤ) ≠ 0)]
  rw [h_factor]
  exact dvd_mul_right m c

/-- For any positive integer M, -1 ≡ M - 1 (mod M) -/
lemma neg_one_eq_mod_sub_one (M : ℤ) :
    (-1 : ℤ) ≡ M - 1 [ZMOD M] := by
  rw [Int.modEq_iff_dvd]
  have : (M - 1) - (-1) = M := by linarith
  rw [this]

