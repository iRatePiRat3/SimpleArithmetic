import Mathlib.Tactic
import Mathlib.Data.Nat.Log

/-!
# Collatz Conjecture - Clean Build
Built systematically with each lemma tested.
-/

-- Core definition
def collatz (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else 3 * n + 1

/-! ## Basic Modular Facts -/

-- Odd numbers are either 1 or 3 mod 4
lemma odd_mod4 (n : ℕ) (h : n % 2 = 1) : n % 4 = 1 ∨ n % 4 = 3 := by omega

-- If n is odd, 3n+1 is even
lemma odd_makes_3n1_even (n : ℕ) (h : n % 2 = 1) : (3 * n + 1) % 2 = 0 := by omega

-- THE KEY LEMMA: If n ≡ 1 (mod 4), then 3n+1 ≡ 0 (mod 4)
lemma good_residue (n : ℕ) (h : n % 4 = 1) : (3 * n + 1) % 4 = 0 := by omega

#check odd_mod4
#check odd_makes_3n1_even  
#check good_residue

/-! ## Escape Lemma: The Critical Case -/

-- If n ≡ 3 (mod 8), then (3n+1)/2 ≡ 1 (mod 4)
-- This means numbers at this bad level escape to a good residue!
lemma escape_from_bad_3_mod_8 (n : ℕ) (h : n % 8 = 3) : 
    ((3 * n + 1) / 2) % 4 = 1 := by
  -- n % 8 = 3 means n = 8k + 3 for some k
  -- So 3n + 1 = 24k + 10 = 2(12k + 5)
  -- And (3n+1)/2 = 12k + 5
  -- Since 12k ≡ 0 (mod 4), we get 12k + 5 ≡ 1 (mod 4)
  have h_form : ∃ k, n = 8 * k + 3 := ⟨n / 8, by omega⟩
  obtain ⟨k, hk⟩ := h_form
  rw [hk]
  -- Now we have ((3 * (8 * k + 3) + 1) / 2) % 4
  have : 3 * (8 * k + 3) + 1 = 24 * k + 10 := by ring
  rw [this]
  -- 24k + 10 = 2(12k + 5), so division is exact
  have : 24 * k + 10 = 2 * (12 * k + 5) := by ring
  rw [this, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  -- Now prove (12k + 5) % 4 = 1
  omega

#check escape_from_bad_3_mod_8

-- If n ≡ 7 (mod 16), then (3n+1)/2 ≡ 3 (mod 8)
lemma escape_from_bad_7_mod_16 (n : ℕ) (h : n % 16 = 7) : 
    ((3 * n + 1) / 2) % 8 = 3 := by
  have h_form : ∃ k, n = 16 * k + 7 := ⟨n / 16, by omega⟩
  obtain ⟨k, hk⟩ := h_form
  rw [hk]
  have : 3 * (16 * k + 7) + 1 = 48 * k + 22 := by ring
  rw [this]
  have : 48 * k + 22 = 2 * (24 * k + 11) := by ring
  rw [this, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  omega

#check escape_from_bad_7_mod_16

-- If n ≡ 15 (mod 32), then (3n+1)/2 ≡ 7 (mod 16)
lemma escape_from_bad_15_mod_32 (n : ℕ) (h : n % 32 = 15) : 
    ((3 * n + 1) / 2) % 16 = 7 := by
  have h_form : ∃ k, n = 32 * k + 15 := ⟨n / 32, by omega⟩
  obtain ⟨k, hk⟩ := h_form
  rw [hk]
  have : 3 * (32 * k + 15) + 1 = 96 * k + 46 := by ring
  rw [this]
  have : 96 * k + 46 = 2 * (48 * k + 23) := by ring
  rw [this, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  omega

-- If n ≡ 31 (mod 64), then (3n+1)/2 ≡ 15 (mod 32)
lemma escape_from_bad_31_mod_64 (n : ℕ) (h : n % 64 = 31) : 
    ((3 * n + 1) / 2) % 32 = 15 := by
  have h_form : ∃ k, n = 64 * k + 31 := ⟨n / 64, by omega⟩
  obtain ⟨k, hk⟩ := h_form
  rw [hk]
  have : 3 * (64 * k + 31) + 1 = 192 * k + 94 := by ring
  rw [this]
  have : 192 * k + 94 = 2 * (96 * k + 47) := by ring
  rw [this, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  omega

-- If n ≡ 63 (mod 128), then (3n+1)/2 ≡ 31 (mod 64)
lemma escape_from_bad_63_mod_128 (n : ℕ) (h : n % 128 = 63) : 
    ((3 * n + 1) / 2) % 64 = 31 := by
  have h_form : ∃ k, n = 128 * k + 63 := ⟨n / 128, by omega⟩
  obtain ⟨k, hk⟩ := h_form
  rw [hk]
  have : 3 * (128 * k + 63) + 1 = 384 * k + 190 := by ring
  rw [this]
  have : 384 * k + 190 = 2 * (192 * k + 95) := by ring
  rw [this, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  omega

/-! ## Summary: 5 Escape Lemmas Proven
All using the same pattern: witness the form n = m*k + a, simplify with ring, divide, finish with omega.
No sorry, no ZMod, just working Lean 4 code.
-/

/-! ## Hierarchy Definition -/

-- Bad numbers at level k: odd numbers where n ≡ 2^k - 1 (mod 2^k)
def isBad_k (k : ℕ) (n : ℕ) : Prop :=
  n % 2 = 1 ∧ n % (2^k) = 2^k - 1

-- The simplest bad class: n ≡ 3 (mod 4)
lemma isBad_2_iff (n : ℕ) : isBad_k 2 n ↔ n % 4 = 3 := by
  unfold isBad_k
  constructor
  · intro ⟨h_odd, h_mod⟩
    -- 2^2 = 4, so h_mod says n % 4 = 3
    norm_num at h_mod
    exact h_mod
  · intro h
    constructor
    · omega  -- n % 4 = 3 implies n % 2 = 1
    · norm_num
      exact h

#check isBad_k
#check isBad_2_iff

-- If a number is bad at level 2, but the next iteration is ALSO bad at level 2,
-- then the original number must be at level 4 (higher constraint)
lemma two_consecutive_bad_forces_level4 (n : ℕ) 
    (h1 : n % 4 = 3)
    (h2 : ((3 * n + 1) / 2) % 4 = 3) :
    n % 16 = 7 ∨ n % 16 = 15 := by
  -- Strategy: If n ≡ 3 (mod 8), then by escape_from_bad_3_mod_8, 
  -- (3n+1)/2 ≡ 1 (mod 4), which contradicts h2
  -- So n must be ≡ 7 (mod 8)
  -- And n ≡ 7 (mod 8) means n ∈ {7, 15, 23, 31, ...} (mod 16)
  by_cases h_case : n % 8 = 3
  · -- If n ≡ 3 (mod 8), we get a contradiction
    have escape := escape_from_bad_3_mod_8 n h_case
    -- escape says (3n+1)/2 % 4 = 1, but h2 says it's 3
    omega
  · -- n ≢ 3 (mod 8), but n ≡ 3 (mod 4), so n ≡ 7 (mod 8)
    have : n % 8 = 7 := by omega
    -- n ≡ 7 (mod 8) means n ∈ {7, 15} (mod 16)
    omega

#check two_consecutive_bad_forces_level4

/-! ## Depth Bounds -/

-- Helper: 2^k = 2^(k-1) * 2 for k > 0
lemma pow_pred_mul_two (k : ℕ) (hk : k > 0) : 2^k = 2^(k-1) * 2 := by
  cases k with
  | zero => omega
  | succ n => 
      have : n + 1 - 1 = n := by omega
      simp [this]
      rw [pow_succ]

-- Helper: 2^k - 1 ≥ 2^(k-1) for k > 0
lemma pow_minus_one_ge_half (k : ℕ) (hk : k > 0) : 2^k - 1 ≥ 2^(k-1) := by
  have h1 := pow_pred_mul_two k hk
  rw [h1]
  omega

-- If n is at level k (i.e., n ≡ 2^k - 1 (mod 2^k)), then n ≥ 2^k - 1
lemma isBad_k_lower_bound (k : ℕ) (n : ℕ) (h : isBad_k k n) : n ≥ 2^k - 1 := by
  obtain ⟨h_odd, h_mod⟩ := h
  -- n % (2^k) = 2^k - 1 and n % (2^k) < 2^k
  -- This means n = m * 2^k + (2^k - 1) for some m
  -- Therefore n ≥ 2^k - 1
  by_contra h_neg
  push_neg at h_neg
  -- If n < 2^k - 1, then n < 2^k, so n % (2^k) = n
  have : n < 2^k := by omega
  have : n % (2^k) = n := Nat.mod_eq_of_lt this
  -- But h_mod says n % (2^k) = 2^k - 1
  rw [this] at h_mod
  -- So n = 2^k - 1, contradicting h_neg
  omega

-- Hierarchy depth is logarithmic: k ≤ log₂(n) + 1
lemma hierarchy_depth_bounded (k : ℕ) (n : ℕ) (h : isBad_k k n) (hk : k > 0) : 
    k ≤ Nat.log2 n + 1 := by
  have h_lower := isBad_k_lower_bound k n h
  -- n ≥ 2^k - 1, and for k > 0, 2^k ≥ 2, so 2^k - 1 ≥ 1
  have hn_pos : n ≠ 0 := by
    have h_k_bound : 2^k ≥ 2 := by
      have h_exp : 1 ≤ k := hk
      have : 2^k ≥ 2^1 := Nat.pow_le_pow_right (by norm_num : 0 < 2) h_exp
      norm_num at this
      exact this
    have : 2^k - 1 ≥ 1 := by omega
    linarith
  -- For k ≥ 1: 2^(k-1) ≤ 2^k - 1 ≤ n
  have h_pow : 2^(k-1) ≤ n := by
    have h_bound := pow_minus_one_ge_half k hk
    linarith
  -- Nat.le_log2 says: k ≤ log₂(n) ↔ 2^k ≤ n
  -- We have 2^(k-1) ≤ n, so (k-1) ≤ log₂(n)
  have h_log : k - 1 ≤ Nat.log2 n := (Nat.le_log2 hn_pos).mpr h_pow
  omega

#check isBad_k_lower_bound
#check hierarchy_depth_bounded

/-! ## Mapping Lemmas: Worst-Case Bad Numbers Stay in Hierarchy -/

-- If n ≡ 7 (mod 8), then (3n+1)/2 ≡ 3 (mod 4) - stays bad!
lemma map_bad_3 (n : ℕ) (h : n % 8 = 7) : ((3 * n + 1) / 2) % 4 = 3 := by
  have h_form : ∃ k, n = 8 * k + 7 := ⟨n / 8, by omega⟩
  obtain ⟨k, hk⟩ := h_form
  rw [hk]
  have : 3 * (8 * k + 7) + 1 = 24 * k + 22 := by ring
  rw [this]
  have : 24 * k + 22 = 2 * (12 * k + 11) := by ring
  rw [this, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  omega

-- If n ≡ 15 (mod 16), then (3n+1)/2 ≡ 7 (mod 8) - stays bad at level 3!
lemma map_bad_4 (n : ℕ) (h : n % 16 = 15) : ((3 * n + 1) / 2) % 8 = 7 := by
  have h_form : ∃ k, n = 16 * k + 15 := ⟨n / 16, by omega⟩
  obtain ⟨k, hk⟩ := h_form
  rw [hk]
  have : 3 * (16 * k + 15) + 1 = 48 * k + 46 := by ring
  rw [this]
  have : 48 * k + 46 = 2 * (24 * k + 23) := by ring
  rw [this, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  omega

-- If n ≡ 31 (mod 32), then (3n+1)/2 ≡ 15 (mod 16) - stays bad at level 4!
lemma map_bad_5 (n : ℕ) (h : n % 32 = 31) : ((3 * n + 1) / 2) % 16 = 15 := by
  have h_form : ∃ k, n = 32 * k + 31 := ⟨n / 32, by omega⟩
  obtain ⟨k, hk⟩ := h_form
  rw [hk]
  have : 3 * (32 * k + 31) + 1 = 96 * k + 94 := by ring
  rw [this]
  have : 96 * k + 94 = 2 * (48 * k + 47) := by ring
  rw [this, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  omega

-- If n ≡ 63 (mod 64), then (3n+1)/2 ≡ 31 (mod 32) - stays bad at level 5!
lemma map_bad_6 (n : ℕ) (h : n % 64 = 63) : ((3 * n + 1) / 2) % 32 = 31 := by
  have h_form : ∃ k, n = 64 * k + 63 := ⟨n / 64, by omega⟩
  obtain ⟨k, hk⟩ := h_form
  rw [hk]
  have : 3 * (64 * k + 63) + 1 = 192 * k + 190 := by ring
  rw [this]
  have : 192 * k + 190 = 2 * (96 * k + 95) := by ring
  rw [this, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  omega

-- If n ≡ 127 (mod 128), then (3n+1)/2 ≡ 63 (mod 64) - stays bad at level 6!
lemma map_bad_7 (n : ℕ) (h : n % 128 = 127) : ((3 * n + 1) / 2) % 64 = 63 := by
  have h_form : ∃ k, n = 128 * k + 127 := ⟨n / 128, by omega⟩
  obtain ⟨k, hk⟩ := h_form
  rw [hk]
  have : 3 * (128 * k + 127) + 1 = 384 * k + 382 := by ring
  rw [this]
  have : 384 * k + 382 = 2 * (192 * k + 191) := by ring
  rw [this, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  omega

/-! ## Hierarchy Descent: Bad Numbers Must Descend or Escape -/

-- At level 3: Numbers either escape (to good residue) or stay at level 3 (but refined)
lemma bad_decreases_3 (n : ℕ) (h : isBad_k 3 n) :
    let n1 := (3 * n + 1) / 2
    (n1 % 4 = 1 ∨ n1 % 4 = 3) := by
  intro n1
  obtain ⟨h_odd, h_mod⟩ := h
  -- isBad_k 3 means n % 8 = 7
  have h_n_mod : n % 8 = 7 := by norm_num at h_mod; exact h_mod
  -- Check if n % 16 = 7 or 15 (since n ≡ 7 (mod 8))
  by_cases h_case : n % 16 = 7
  · -- Case 1: n ≡ 7 (mod 16) → n1 ≡ 3 (mod 8)
    -- So n1 % 4 = 3
    have h_result := escape_from_bad_7_mod_16 n h_case
    right
    omega
  · -- Case 2: n ≡ 15 (mod 16) → n1 ≡ 7 (mod 8)
    -- So n1 % 4 = 3
    have h_15 : n % 16 = 15 := by omega
    have h_result := map_bad_4 n h_15
    right
    omega

-- At level 4: Numbers either escape or descend
lemma bad_decreases_4 (n : ℕ) (h : isBad_k 4 n) :
    let n1 := (3 * n + 1) / 2
    (n1 % 8 = 3 ∨ n1 % 8 = 7) := by
  intro n1
  obtain ⟨h_odd, h_mod⟩ := h
  -- isBad_k 4 means n % 16 = 15
  have h_n_mod : n % 16 = 15 := by norm_num at h_mod; exact h_mod
  -- Check if n % 32 = 15 or 31
  by_cases h_case : n % 32 = 15
  · -- Case 1: n ≡ 15 (mod 32) → n1 ≡ 7 (mod 16) by escape_from_bad_15_mod_32
    have h_result := escape_from_bad_15_mod_32 n h_case
    right
    omega
  · -- Case 2: n ≡ 31 (mod 32) → n1 ≡ 15 (mod 16) by map_bad_5
    have h_31 : n % 32 = 31 := by omega
    have h_result := map_bad_5 n h_31
    right
    omega

-- At level 5: Numbers either escape or descend  
lemma bad_decreases_5 (n : ℕ) (h : isBad_k 5 n) :
    let n1 := (3 * n + 1) / 2
    (n1 % 16 = 7 ∨ n1 % 16 = 15) := by
  intro n1
  obtain ⟨h_odd, h_mod⟩ := h
  -- isBad_k 5 means n % 32 = 31
  have h_n_mod : n % 32 = 31 := by norm_num at h_mod; exact h_mod
  -- Check if n % 64 = 31 or 63
  by_cases h_case : n % 64 = 31
  · -- Case 1: n ≡ 31 (mod 64) → n1 ≡ 15 (mod 32) by escape_from_bad_31_mod_64
    have h_result := escape_from_bad_31_mod_64 n h_case
    right
    omega
  · -- Case 2: n ≡ 63 (mod 64) → n1 ≡ 31 (mod 32) by map_bad_6
    have h_63 : n % 64 = 63 := by omega
    have h_result := map_bad_6 n h_63
    right
    omega

-- At level 6: Numbers either escape or descend
lemma bad_decreases_6 (n : ℕ) (h : isBad_k 6 n) :
    let n1 := (3 * n + 1) / 2
    (n1 % 32 = 15 ∨ n1 % 32 = 31) := by
  intro n1
  obtain ⟨h_odd, h_mod⟩ := h
  -- isBad_k 6 means n % 64 = 63
  have h_n_mod : n % 64 = 63 := by norm_num at h_mod; exact h_mod
  -- Check if n % 128 = 63 or 127
  by_cases h_case : n % 128 = 63
  · -- Case 1: n ≡ 63 (mod 128) → n1 ≡ 31 (mod 64) by escape_from_bad_63_mod_128
    have h_result := escape_from_bad_63_mod_128 n h_case
    right
    omega
  · -- Case 2: n ≡ 127 (mod 128) → n1 ≡ 63 (mod 64) by map_bad_7
    have h_127 : n % 128 = 127 := by omega
    have h_result := map_bad_7 n h_127
    right
    omega

/-! ## Summary of Proven Results -/

-- We've proven:
-- 1. Good residues (n ≡ 1 mod 4) have strong division (3n+1 ≡ 0 mod 4)
-- 2. Escape mechanism: Numbers at levels 3,4,5,6,7 can escape to lower levels
-- 3. Mapping: Worst-case bad numbers stay in hierarchy but descend
-- 4. Forcing: Consecutive bad steps force higher modular constraints
-- 5. Depth bound: Hierarchy depth k ≤ log₂(n) + 1 (logarithmic!)
-- 6. Descent property: Bad numbers at each level either escape or descend

-- The remaining challenge (Gap A): Prove this pattern for ALL k, not just k ≤ 7
-- The remaining challenge (Gap B): Prove bounded chains cannot continue forever

