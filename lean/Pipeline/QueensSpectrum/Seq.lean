import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic

/-!
# Queens spectrum: sums of sequences used in the sector lemmas

Pure lemmas about finite sums of a sequence `r : ℕ → K` (row values) and a function
`D : ℤ → K` (diagonal values), with the notation of `PROOF.md` §1:

* `TT D p = T_p = ∑_{s ∈ S(p)} D s` with `S(p) = {-p, -p+2, …, p}`, and `T_{-1} = 0`;
* `rho n r k = ρ_k = ∑_{i=k}^{n-1} r_i`.
-/

namespace QueensSpectrum

open Finset

variable {K : Type*} [Field K]

/-- `T_p = ∑_{j=0}^{p} D(2j - p)`; for `p = -1` the sum is empty. -/
def TT (D : ℤ → K) (p : ℤ) : K := ∑ j ∈ range (p + 1).toNat, D (2 * (j : ℤ) - p)

/-- `ρ_k = ∑_{j < n-k} r (j + k) = ∑_{i=k}^{n-1} r_i`. -/
def rho (n : ℕ) (r : ℕ → K) (k : ℕ) : K := ∑ j ∈ range (n - k), r (j + k)

lemma TT_neg_one (D : ℤ → K) : TT D (-1) = 0 := by simp [TT]

lemma TT_zero (D : ℤ → K) : TT D 0 = D 0 := by simp [TT]

lemma TT_one (D : ℤ → K) : TT D 1 = D (-1) + D 1 := by
  simp [TT, sum_range_succ]

/-- `T_{p+2} = T_p + 2 D(p+2)` for an even `D` and `p ≥ -1`. -/
lemma TT_step {D : ℤ → K} (hD : ∀ k, D (-k) = D k) (p : ℤ) (hp : -1 ≤ p) :
    TT D (p + 2) = TT D p + 2 * D (p + 2) := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, p = (m : ℤ) - 1 := ⟨(p + 1).toNat, by omega⟩
  have h1 : ((m : ℤ) - 1 + 2 + 1).toNat = m + 1 + 1 := by omega
  have h2 : ((m : ℤ) - 1 + 1).toNat = m := by omega
  simp only [TT, h1, h2]
  rw [sum_range_succ, sum_range_succ']
  have h3 : ∀ j : ℕ, D (2 * ((j + 1 : ℕ) : ℤ) - ((m : ℤ) - 1 + 2)) =
      D (2 * (j : ℤ) - ((m : ℤ) - 1)) := by
    intro j; congr 1; push_cast; ring
  rw [sum_congr rfl (fun j _ => h3 j)]
  have h4 : D (2 * ((0 : ℕ) : ℤ) - ((m : ℤ) - 1 + 2)) = D ((m : ℤ) - 1 + 2) := by
    rw [← hD]; congr 1; push_cast; ring
  have h5 : D (2 * ((m + 1 : ℕ) : ℤ) - ((m : ℤ) - 1 + 2)) = D ((m : ℤ) - 1 + 2) := by
    congr 1; push_cast; ring
  rw [h4, h5]; ring

/-- For an odd `D`, `T_p = 0`. -/
lemma TT_odd {D : ℤ → K} [CharZero K] (hD : ∀ k, D (-k) = -D k) (p : ℤ) : TT D p = 0 := by
  have h : TT D p = -TT D p := by
    unfold TT
    conv_lhs => rw [← sum_range_reflect]
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro j hj
    rw [mem_range] at hj
    rw [← hD]
    congr 1
    have h0 : 0 < (p + 1).toNat := by omega
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    have : (((p + 1).toNat : ℕ) : ℤ) = p + 1 := by omega
    rw [this]; push_cast; ring
  have : (2 : K) * TT D p = 0 := by linear_combination h
  simpa using this

/-- The window identity behind (E1), (A.1): sliding the window `i-n+1 … i` by one. -/
lemma window_step (n : ℕ) (D : ℤ → K) (i : ℤ) :
    ∑ j ∈ range n, D (i - j) + D (i - n) = ∑ j ∈ range n, D (i - 1 - j) + D i := by
  have h1 := sum_range_succ (fun j : ℕ => D (i - j)) n
  have h2 := sum_range_succ' (fun j : ℕ => D (i - j)) n
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, sub_zero] at h1 h2
  have h3 : ∀ j : ℕ, D (i - (j + 1)) = D (i - 1 - j) := fun j => by congr 1; ring
  simp only [h3] at h2
  rw [← h1, h2]

/-- Reflection of the antidiagonal window: `∑_j D(i + j - (n-1)) = ∑_j D(i - j)`. -/
lemma reflect_window (n : ℕ) (D : ℤ → K) (i : ℤ) :
    ∑ j ∈ range n, D (i + j - (n - 1)) = ∑ j ∈ range n, D (i - j) := by
  rw [← sum_range_reflect]
  apply sum_congr rfl
  intro j hj
  rw [mem_range] at hj
  congr 1
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast; ring

/-- The antidiagonal part of a diagonal component is a `T`. -/
lemma diag_TT (n : ℕ) (A : ℤ → K) (k : ℕ) (hk : k < n) :
    ∑ j ∈ range (n - k), A (2 * (j : ℤ) + k - (n - 1)) = TT A ((n : ℤ) - 1 - k) := by
  unfold TT
  have : ((n : ℤ) - 1 - k + 1).toNat = n - k := by omega
  rw [this]
  apply sum_congr rfl
  intro j _
  congr 1; ring

lemma rho_succ (n : ℕ) (r : ℕ → K) (k : ℕ) (hk : k < n) :
    rho n r k = r k + rho n r (k + 1) := by
  unfold rho
  have : n - k = (n - (k + 1)) + 1 := by omega
  rw [this, sum_range_succ']
  simp only [zero_add]
  rw [add_comm]
  congr 1
  apply sum_congr rfl
  intro j _
  congr 1; ring

lemma rho_self (n : ℕ) (r : ℕ → K) : rho n r n = 0 := by simp [rho]

lemma eq_zero_of_rho (n : ℕ) (r : ℕ → K) (h : ∀ k, k < n → rho n r k = 0) :
    ∀ k, k < n → r k = 0 := by
  intro k hk
  have h1 := rho_succ n r k hk
  have h2 : rho n r (k + 1) = 0 := by
    rcases Nat.lt_or_ge (k + 1) n with h' | h'
    · exact h _ h'
    · have : k + 1 = n := by omega
      rw [this]; exact rho_self n r
  rw [h k hk, h2] at h1
  linear_combination -h1

/-- `∑_{j<k} r_j + ρ_k = ∑_{j<n} r_j`. -/
lemma sum_split (n : ℕ) (r : ℕ → K) (k : ℕ) (hk : k ≤ n) :
    ∑ j ∈ range k, r j + rho n r k = ∑ j ∈ range n, r j := by
  unfold rho
  have := sum_range_add r k (n - k)
  rw [show k + (n - k) = n by omega] at this
  rw [this]
  congr 1
  apply sum_congr rfl
  intro j _
  congr 1; ring

/-- For a palindromic `r`, `∑_{j < n-k} r_j = ρ_k`. -/
lemma sigma_palin (n : ℕ) (r : ℕ → K) (hr : ∀ i, i < n → r (n - 1 - i) = r i) (k : ℕ)
    (hk : k ≤ n) : ∑ j ∈ range (n - k), r j = rho n r k := by
  unfold rho
  rw [← sum_range_reflect]
  apply sum_congr rfl
  intro j hj
  rw [mem_range] at hj
  rw [← hr _ (by omega)]
  congr 1; omega

/-- For an antipalindromic `r`, `∑_{j < n-k} r_j = -ρ_k`. -/
lemma sigma_anti (n : ℕ) (r : ℕ → K) (hr : ∀ i, i < n → r (n - 1 - i) = -r i) (k : ℕ)
    (hk : k ≤ n) : ∑ j ∈ range (n - k), r j = -rho n r k := by
  unfold rho
  rw [← sum_range_reflect, ← sum_neg_distrib]
  apply sum_congr rfl
  intro j hj
  rw [mem_range] at hj
  have := hr (j + k) (by omega)
  rw [show n - k - 1 - j = n - 1 - (j + k) by omega]
  exact this

/-- The sum of an even function over `[0, n)` read backwards from `0`. -/
lemma sum_neg_even (n : ℕ) (D : ℤ → K) (hD : ∀ k, D (-k) = D k) :
    ∑ j ∈ range n, D (0 - j) = ∑ j ∈ range n, D j := by
  apply sum_congr rfl
  intro j _
  rw [zero_sub, hD]

end QueensSpectrum
