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

/-- Power identity: 2^k = 2 * 2^(k-1) for k > 0, casted to Int -/
lemma int_pow_two_succ_pred (k : ℕ) (hk : k > 0) :
    (2^k : ℤ) = 2 * (2^(k-1) : ℤ) := by
  have : k = (k - 1) + 1 := (Nat.sub_add_cancel hk).symm
  conv_lhs => rw [this, pow_add, pow_one]
  norm_cast
  ring

/-- If n ≡ -2 (mod m) and 2 ∣ m, then 2 ∣ n -/
lemma int_dvd_two_of_modEq_neg_two (n m : ℤ) (h_mod : n ≡ (-2) [ZMOD m]) (h_2_dvd_m : 2 ∣ m) :
    2 ∣ n := by
  rw [Int.modEq_iff_dvd] at h_mod
  obtain ⟨k, hk⟩ := h_mod
  obtain ⟨m', hm'⟩ := h_2_dvd_m
  use -(1 + m' * k)
  calc n = (-2) - m * k := by linarith
       _ = -2 - (2 * m') * k := by rw [hm']
       _ = -2 - 2 * (m' * k) := by ring
       _ = 2 * (-(1 + m' * k)) := by ring

/-- Convert Nat modular equality to Int.ModEq
    If n % m = r in ℕ, then (n : ℤ) ≡ (r : ℤ) [ZMOD (m : ℤ)] -/
lemma nat_mod_to_int_modEq (n m r : ℕ) (h : n % m = r) (hm : m > 0) :
    (n : ℤ) ≡ (r : ℤ) [ZMOD (m : ℤ)] := by
  -- Use the definition: n = (n / m) * m + r
  have h_def : m * (n / m) + (n % m) = n := Nat.div_add_mod n m
  rw [h] at h_def
  -- So n = m * (n / m) + r
  have h_form : n = m * (n / m) + r := by omega
  -- Cast to Int: (n : ℤ) = (m : ℤ) * ((n / m) : ℤ) + (r : ℤ)
  have h_int : (n : ℤ) = (m : ℤ) * ((n / m) : ℤ) + (r : ℤ) := by
    norm_cast
  rw [Int.ModEq, h_int]
  simp

/-- Convert Int.ModEq to Nat modular equality
    If (n : ℤ) ≡ (r : ℤ) [ZMOD (m : ℤ)] and n, r, m are Nat with r < m,
    then n % m = r -/
lemma int_modEq_to_nat_mod (n m r : ℕ) (h : (n : ℤ) ≡ (r : ℤ) [ZMOD (m : ℤ)])
    (hr : r < m) (hm : m > 0) :
    n % m = r := by
  -- Use Int.ModEq to show that n % m and r % m are equal
  -- Since r < m, we have r % m = r
  have h_r_mod : r % m = r := Nat.mod_eq_of_lt hr
  -- We need to show n % m = r
  -- From h: (n : ℤ) ≡ (r : ℤ) [ZMOD m], we get n % m ≡ r % m in Nat
  rw [Int.ModEq] at h
  -- Since 0 ≤ r < m, we have (r : ℤ) % (m : ℤ) = r
  have : (r : ℤ) % (m : ℤ) = (r : ℤ) := by
    exact Int.emod_eq_of_lt (by omega) (by omega)
  rw [this] at h
  -- Now (n : ℤ) % (m : ℤ) = (r : ℤ)
  -- And (n : ℤ) % (m : ℤ) = ((n % m) : ℤ) from Int.coe_nat_mod
  have : ((n % m) : ℤ) = (r : ℤ) := by omega
  exact Nat.cast_injective this
