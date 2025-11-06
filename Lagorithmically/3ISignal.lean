import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace InterstellarSignal

-- Define a bit as ℕ constrained to 0 or 1 
-- Note: In practice, values should be validated to be 0 or 1
def Bit := ℕ
def isBit (b : Bit) : Prop := b = 0 ∨ b = 1

-- XOR two bits
def xorBit (a b : Bit) : Bit := (a + b) % 2

-- XOR two lists of bits
def xorList : List Bit → List Bit → List Bit
| [], [] => []
| a::as, b::bs => xorBit a b :: xorList as bs
| _, _ => [] -- fallback for unequal lengths

-- Convert 8 bits to decimal
def bitsToNat (bs : List Bit) : ℕ :=
  bs.reverse.enum.foldl (fun acc ⟨i, b⟩ => acc + b * 2^i) 0

-- Define the signal S (24 bits)
-- Note: The source/origin of this bit sequence is not proven here
def S : List Bit :=
  [1,0,0,0,1,1,0,1, 1,0,0,0,0,1,0,1, 1,1,0,1,1,0,0,0]

-- Define the Bereshit key K = 001100 repeated 4 times
def K : List Bit :=
  [0,0,1,1,0,0] ++ [0,0,1,1,0,0] ++ [0,0,1,1,0,0] ++ [0,0,1,1,0,0]

-- XOR the signal with the key
def P : List Bit := xorList S K

-- Split P into 3 chunks of 8 bits
def chunks (l : List Bit) : List (List Bit) :=
  [l.take 8, l.drop 8 |>.take 8, l.drop 16 |>.take 8]

-- Convert each chunk to decimal
def decodedValues : List ℕ := chunks P |>.map bitsToNat

-- ============================================================================
-- Symbolic Primes and Fibonacci Factors
-- ============================================================================

-- Symbolic primes and Fibonacci factors
def symbolicPrimes : Finset ℕ := {5, 13, 19, 47}

def fibonacciFactors : Finset ℕ := {5, 8, 13, 21, 34, 55, 89}

-- Check if a number has any symbolic prime as a factor
def hasSymbolicPrimeFactor (n : ℕ) : Prop :=
  ∃ p ∈ symbolicPrimes, p ∣ n

-- Check if a number has any Fibonacci factor
def hasFibonacciFactor (n : ℕ) : Prop :=
  ∃ f ∈ fibonacciFactors, f ∣ n

-- A number is symbolically saturated if it has symbolic primes or Fibonacci factors
def isSymbolicallySaturated (n : ℕ) : Prop :=
  hasSymbolicPrimeFactor n ∨ hasFibonacciFactor n

-- A sequence is symbolically closed if all its elements are saturated
def isSymbolicallyClosed (seq : List ℕ) : Prop :=
  ∀ n ∈ seq, isSymbolicallySaturated n

-- ============================================================================
-- Theorems
-- ============================================================================

-- Theorem: Decoded values are [190, 182, 235] and certain primes exist
theorem symbolicResidueFactors :
  decodedValues = [190, 182, 235] ∧
  Nat.Prime 5 ∧ Nat.Prime 13 ∧ Nat.Prime 19 ∧ Nat.Prime 47 :=
by
  -- First, compute P = xorList S K
  -- S = [1,0,0,0,1,1,0,1, 1,0,0,0,0,1,0,1, 1,1,0,1,1,0,0,0]
  -- K = [0,0,1,1,0,0, 0,0,1,1,0,0, 0,0,1,1,0,0, 0,0,1,1,0,0]
  have h_S_def : S = [1,0,0,0,1,1,0,1, 1,0,0,0,0,1,0,1, 1,1,0,1,1,0,0,0] := rfl
  have h_K_def : K = [0,0,1,1,0,0, 0,0,1,1,0,0, 0,0,1,1,0,0, 0,0,1,1,0,0] := rfl

  -- Compute XOR element by element
  have h_P_computed : P = [1,0,1,1,1,1,1,0, 1,0,1,1,0,1,1,0, 1,1,1,0,1,0,1,1] := by
    unfold P
    rw [h_S_def, h_K_def]
    -- Compute xorList recursively
    simp only [xorList, xorBit]
    norm_num

  -- Compute chunks
  have h_chunks : chunks P = [
    [1,0,1,1,1,1,1,0],
    [1,0,1,1,0,1,1,0],
    [1,1,1,0,1,0,1,1]
  ] := by
    rw [h_P_computed]
    simp only [chunks]
    norm_num

  -- Compute decimal values from chunks
  have h_vals : decodedValues = [190, 182, 235] := by
    unfold decodedValues
    rw [h_chunks]
    simp [bitsToNat]
    norm_num

  -- Prove primes
  have h_prime_5 : Nat.Prime 5 := by norm_num
  have h_prime_13 : Nat.Prime 13 := by norm_num
  have h_prime_19 : Nat.Prime 19 := by norm_num
  have h_prime_47 : Nat.Prime 47 := by norm_num

  exact ⟨h_vals, h_prime_5, h_prime_13, h_prime_19, h_prime_47⟩

-- Theorem: Decoded sequence is symbolically closed
theorem decodedSequenceIsClosed :
  decodedValues = [190, 182, 235] →
  isSymbolicallyClosed decodedValues :=
by
  intro h_vals
  rw [h_vals]
  unfold isSymbolicallyClosed isSymbolicallySaturated hasSymbolicPrimeFactor hasFibonacciFactor
  intros n h_n
  -- Handle each case in the list [190, 182, 235]
  -- n is either 190, 182, or 235
  have h_n_in : n ∈ [190, 182, 235] := h_n
  -- Prove each case separately
  have h_case1 : n = 190 → isSymbolicallySaturated n := by
    intro h_eq
    rw [h_eq]
    left
    use 19
    constructor
    · simp [symbolicPrimes]
      norm_num
    · use 10
      norm_num
  have h_case2 : n = 182 → isSymbolicallySaturated n := by
    intro h_eq
    rw [h_eq]
    left
    use 13
    constructor
    · simp [symbolicPrimes]
      norm_num
    · use 14
      norm_num
  have h_case3 : n = 235 → isSymbolicallySaturated n := by
    intro h_eq
    rw [h_eq]
    left
    use 47
    constructor
    · simp [symbolicPrimes]
      norm_num
    · use 5
      norm_num
  -- Use the fact that n must be one of the three values
  simp at h_n_in
  cases h_n_in with
  | inl h_eq => exact h_case1 h_eq
  | inr h_rest =>
    cases h_rest with
    | inl h_eq => exact h_case2 h_eq
    | inr h_rest2 =>
      cases h_rest2 with
      | inl h_eq => exact h_case3 h_eq
      | inr => contradiction

-- Combined theorem: The decoded sequence has the expected values and is symbolically closed
theorem decodedSequenceProperties :
  decodedValues = [190, 182, 235] ∧
  isSymbolicallyClosed decodedValues ∧
  Nat.Prime 5 ∧ Nat.Prime 13 ∧ Nat.Prime 19 ∧ Nat.Prime 47 :=
by
  obtain ⟨h_vals, h_p5, h_p13, h_p19, h_p47⟩ := symbolicResidueFactors
  have h_closed := decodedSequenceIsClosed h_vals
  exact ⟨h_vals, h_closed, h_p5, h_p13, h_p19, h_p47⟩

end InterstellarSignal
