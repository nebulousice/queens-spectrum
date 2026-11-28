import Pipeline.QueensSpectrum.Seq

/-!
# Queens spectrum: sector `E` (Lemma 7 of `PROOF.md`), as a statement about sequences

The hypotheses `hrow`, `hdiag` are the row and diagonal components of `M v = n v` for
`v = (r, c, d, a)` written as in Lemma 5, (4.0a)–(4.0b); the shape hypotheses `hr`, `hc`, `hD`,
`hA` say `v ∈ V_E` ((3.4): `r` antipalindromic, `c = 0`, `d` odd, `a = d`).
-/

namespace QueensSpectrum

open Finset

variable {K : Type*} [Field K]

/-- Row component of `M v` (4.0a), expanded. -/
lemma row_expand (n : ℕ) (a : K) (c : ℕ → K) (D A : ℤ → K) (i : ℤ) :
    ∑ j ∈ range n, (a + c j + D (i - j) + A (i + j - (n - 1))) =
      n * a + ∑ j ∈ range n, c j + ∑ j ∈ range n, D (i - j) +
        ∑ j ∈ range n, A (i + j - (n - 1)) := by
  simp only [sum_add_distrib, sum_const, card_range, nsmul_eq_mul]

/-- Diagonal component of `M v` (4.0b), expanded. -/
lemma diag_expand (n : ℕ) (r c : ℕ → K) (D A : ℤ → K) (k : ℕ) (hk : k < n) :
    ∑ j ∈ range (n - k), (r (j + k) + c j + D k + A (2 * (j : ℤ) + k - (n - 1))) =
      rho n r k + ∑ j ∈ range (n - k), c j + ((n : K) - k) * D k +
        TT A ((n : ℤ) - 1 - k) := by
  simp only [sum_add_distrib, sum_const, card_range, nsmul_eq_mul, rho]
  rw [diag_TT n A k hk, Nat.cast_sub hk.le]

/-- **Lemma 7 (sector `E`).** The only solution is zero. -/
theorem sectorE_pure [CharZero K] (n : ℕ) (r c : ℕ → K) (D A : ℤ → K)
    (hr : ∀ i, i < n → r (n - 1 - i) = -r i) (hc : ∀ j, j < n → c j = 0)
    (hD : ∀ k, D (-k) = -D k) (hA : ∀ s, A s = D s)
    (hrow : ∀ i, i < n →
      ∑ j ∈ range n, (r i + c j + D ((i : ℤ) - j) + A ((i : ℤ) + j - (n - 1))) = n * r i)
    (hdiag : ∀ k, k < n →
      ∑ j ∈ range (n - k), (r (j + k) + c j + D k + A (2 * (j : ℤ) + k - (n - 1))) =
        n * D k) :
    (∀ i, i < n → r i = 0) ∧ (∀ k : ℕ, k < n → D k = 0) := by
  have hsc : ∀ m, m ≤ n → ∑ j ∈ range m, c j = 0 :=
    fun m hm => sum_eq_zero (fun j hj => hc j (by simp at hj; omega))
  -- (row_i): the window sums vanish
  have hW : ∀ i : ℕ, i < n → ∑ j ∈ range n, D ((i : ℤ) - j) = 0 := by
    intro i hi
    have h := hrow i hi
    rw [row_expand] at h
    simp only [hA] at h
    rw [reflect_window, hsc n le_rfl] at h
    have : (2 : K) * ∑ j ∈ range n, D ((i : ℤ) - j) = 0 := by linear_combination h
    simpa using this
  -- (E1): d_i + d_{n-i} = 0
  have hDsym : ∀ i : ℕ, 1 ≤ i → i < n → D i = -D ((n : ℤ) - i) := by
    intro i h1 h2
    have e := window_step n D i
    have w1 := hW i h2
    have w2 := hW (i - 1) (by omega)
    rw [show ((i - 1 : ℕ) : ℤ) = (i : ℤ) - 1 by omega] at w2
    rw [← hD, show -((n : ℤ) - i) = (i : ℤ) - n by ring]
    linear_combination -e + w1 - w2
  -- (diag_k): ρ_k = k d_k
  have hrho : ∀ k, k < n → rho n r k = k * D k := by
    intro k hk
    have h := hdiag k hk
    rw [diag_expand n r c D A k hk, hsc (n - k) (by omega)] at h
    have hT : TT A ((n : ℤ) - 1 - k) = 0 := by
      have : A = D := funext hA
      rw [this]; exact TT_odd hD _
    rw [hT] at h
    linear_combination h
  -- (E2)
  have hS : ∑ j ∈ range n, r j = 0 := by
    have h1 := sigma_anti n r hr 0 (Nat.zero_le _)
    have h2 : rho n r 0 = ∑ j ∈ range n, r j := by simp [rho]
    simp only [Nat.sub_zero] at h1
    rw [h2] at h1
    have : (2 : K) * ∑ j ∈ range n, r j = 0 := by linear_combination h1
    simpa using this
  have hrho_sym : ∀ k, k ≤ n → rho n r k = rho n r (n - k) := by
    intro k hk
    have h1 := sum_split n r k hk
    have h2 := sigma_anti n r hr (n - k) (by omega)
    rw [show n - (n - k) = k by omega] at h2
    rw [hS, h2] at h1
    linear_combination h1
  -- (E3)
  have hDk : ∀ k, 1 ≤ k → k < n → D k = 0 := by
    intro k h1 h2
    have e1 := hrho k h2
    have e2 := hrho (n - k) (by omega)
    have e3 := hrho_sym k h2.le
    have e4 := hDsym k h1 h2
    push_cast [Nat.cast_sub h2.le] at e2
    have : (n : K) * D k = 0 := by
      linear_combination -e1 + e3 + e2 + ((n : K) - k) * e4
    have hn0 : (n : K) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    exact (mul_eq_zero.mp this).resolve_left hn0
  refine ⟨?_, ?_⟩
  · apply eq_zero_of_rho n r
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simpa [rho] using hS
    · rw [hrho k hk, hDk k hk0 hk, mul_zero]
  · intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · have := hD 0
      simp only [neg_zero] at this
      have h2 : (2 : K) * D 0 = 0 := by linear_combination this
      simpa using h2
    · exact hDk k hk0 hk

end QueensSpectrum
