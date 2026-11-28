import Pipeline.QueensSpectrum.SectorA1

/-!
# Queens spectrum: sector `B₂` (Lemmas 10–12 of `PROOF.md`), as a statement about sequences

Shape of `V_{B2}` ((3.3)): `r = c = 0`, `d` even, `a = -d`.  Only the diagonal equations are
used.  Lemma 10 (weighted means) is proved in a slightly more general form: instead of "the
sequence `j, α(j), α(α(j)), …` reaches `j₀`" we assume a rank function that strictly decreases
along `α` off `j₀`; for the index maps of Lemma 12 the rank is `j` (or `j + n` for even `j` in
the case `n` even), and the two hypotheses are equivalent for these maps.
-/

namespace QueensSpectrum

open Finset

/-- The kernel vector of the `B₂` sector for odd `n` (Lemma 12(b)):
`d°_0 = n - 1`, `d°_k = -1` for even `k ≠ 0`, `d°_k = 0` for odd `k`. -/
def dcirc (K : Type*) [Field K] (n : ℕ) (k : ℤ) : K :=
  (if k = 0 then (n : K) else 0) - (if k % 2 = 0 then 1 else 0)

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- **Lemma 10 (weighted means)**, one half: every value is at most the value at `j₀`. -/
lemma weighted_means_le {ι : Type*} (I : Finset ι) (j0 : ι) (hj0 : j0 ∈ I) (e : ι → K)
    (α β : ι → ι) (lam : ι → K) (rk : ι → ℕ)
    (hα : ∀ j ∈ I, j ≠ j0 → α j ∈ I) (hβ : ∀ j ∈ I, j ≠ j0 → β j ∈ I)
    (hlam : ∀ j ∈ I, j ≠ j0 → 0 < lam j ∧ lam j ≤ 1)
    (he : ∀ j ∈ I, j ≠ j0 → e j = lam j * e (α j) + (1 - lam j) * e (β j))
    (hrk : ∀ j ∈ I, j ≠ j0 → rk (α j) < rk j) :
    ∀ j ∈ I, e j ≤ e j0 := by
  obtain ⟨jm, hjm, hmax⟩ := I.exists_max_image e ⟨j0, hj0⟩
  have key : ∀ N, ∀ j ∈ I, rk j ≤ N → e j = e jm → e j0 = e jm := by
    intro N
    induction N with
    | zero =>
      intro j hj hr hej
      by_cases hjj : j = j0
      · rw [← hjj]; exact hej
      · have := hrk j hj hjj; omega
    | succ N ih =>
      intro j hj hr hej
      by_cases hjj : j = j0
      · rw [← hjj]; exact hej
      · apply ih (α j) (hα j hj hjj) (by have := hrk j hj hjj; omega)
        have h1 := he j hj hjj
        have h2 := hmax (α j) (hα j hj hjj)
        have h3 := hmax (β j) (hβ j hj hjj)
        obtain ⟨hl1, hl2⟩ := hlam j hj hjj
        have hint := mul_nonneg (sub_nonneg.mpr hl2) (sub_nonneg.mpr h3)
        have h4 : lam j * (e jm - e (α j)) ≤ 0 := by nlinarith
        have h5 : e jm - e (α j) ≤ 0 := by
          by_contra hc
          push_neg at hc
          have := mul_pos hl1 hc
          linarith
        linarith
  intro j hj
  have := key (rk jm) jm hjm le_rfl rfl
  rw [this]; exact hmax j hj

/-- **Lemma 10 (weighted means).** All values are equal to the value at `j₀`. -/
lemma weighted_means {ι : Type*} (I : Finset ι) (j0 : ι) (hj0 : j0 ∈ I) (e : ι → K)
    (α β : ι → ι) (lam : ι → K) (rk : ι → ℕ)
    (hα : ∀ j ∈ I, j ≠ j0 → α j ∈ I) (hβ : ∀ j ∈ I, j ≠ j0 → β j ∈ I)
    (hlam : ∀ j ∈ I, j ≠ j0 → 0 < lam j ∧ lam j ≤ 1)
    (he : ∀ j ∈ I, j ≠ j0 → e j = lam j * e (α j) + (1 - lam j) * e (β j))
    (hrk : ∀ j ∈ I, j ≠ j0 → rk (α j) < rk j) :
    ∀ j ∈ I, e j = e j0 := by
  intro j hj
  apply le_antisymm (weighted_means_le I j0 hj0 e α β lam rk hα hβ hlam he hrk j hj)
  have := weighted_means_le I j0 hj0 (fun i => -e i) α β lam rk hα hβ hlam
    (fun i hi hi0 => by rw [he i hi hi0]; ring) hrk j hj
  linarith

/-- The step `e_j = ((j-2)/j) e_{j-2} + (2/j) e_{n+1-j}` from `j e_j = (j-2) e_{j-2} + 2 e_{n+1-j}`. -/
lemma step_weights (j : ℕ) (hj : 3 ≤ j) (x y z : K) (h : (j : K) * x = ((j : K) - 2) * y + 2 * z) :
    x = ((j : K) - 2) / j * y + (1 - ((j : K) - 2) / j) * z := by
  have hj0 : (j : K) ≠ 0 := by exact_mod_cast (by omega : j ≠ 0)
  field_simp
  linear_combination h

lemma step_lam (j : ℕ) (hj : 3 ≤ j) : 0 < ((j : K) - 2) / j ∧ ((j : K) - 2) / j ≤ 1 := by
  have hj' : (3 : K) ≤ j := by exact_mod_cast hj
  constructor
  · apply div_pos <;> linarith
  · rw [div_le_one (by linarith)]; linarith

/-- **Lemma 12 (sector `B₂`).** For even `n` the only solution is zero; for odd `n` every
solution is a multiple of `d°`. -/
theorem sectorB2_pure (n : ℕ) (hn : 4 ≤ n) (r c : ℕ → K) (D A : ℤ → K)
    (hr : ∀ i, i < n → r i = 0) (hc : ∀ j, j < n → c j = 0)
    (hD : ∀ k, D (-k) = D k) (hA : ∀ s, A s = -D s)
    (hdiag : ∀ k, k < n →
      ∑ j ∈ range (n - k), (r (j + k) + c j + D k + A (2 * (j : ℤ) + k - (n - 1))) =
        n * D k) :
    (n % 2 = 0 → ∀ k : ℕ, k < n → D k = 0) ∧
      (n % 2 = 1 → ∀ k : ℕ, k < n → D k = -D 2 * dcirc K n k) := by
  have hn0 : (n : K) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  -- (7.1): Eq(k) : k d_k + T_{n-1-k} = 0
  have hEq : ∀ k, k < n → (k : K) * D k + TT D ((n : ℤ) - 1 - k) = 0 := by
    intro k hk
    have h := hdiag k hk
    rw [diag_expand n r c D A k hk] at h
    have h1 : rho n r k = 0 := sum_eq_zero (fun j hj => hr _ (by simp at hj; omega))
    have h2 : ∑ j ∈ range (n - k), c j = 0 :=
      sum_eq_zero (fun j hj => hc _ (by simp at hj; omega))
    have h3 : TT A ((n : ℤ) - 1 - k) = -TT D ((n : ℤ) - 1 - k) := by
      unfold TT; simp only [hA, sum_neg_distrib]
    rw [h1, h2, h3] at h
    linear_combination -h
  -- (7.4): F_k = 0, in the form  (k+2) d_{k+2} = k d_k + 2 d_{n-1-k}
  have hF : ∀ j : ℕ, 2 ≤ j → j ≤ n - 1 →
      (j : K) * D j = ((j : K) - 2) * D ((j : ℤ) - 2) + 2 * D ((n : ℤ) + 1 - j) := by
    intro j h1 h2
    have e1 := hEq (j - 2) (by omega)
    have e2 := hEq j (by omega)
    have t := TT_step hD ((n : ℤ) - 1 - j) (by omega)
    rw [show (n : ℤ) - 1 - j + 2 = (n : ℤ) - 1 - ((j - 2 : ℕ) : ℤ) by push_cast [Nat.cast_sub h1]; ring]
      at t
    rw [t] at e1
    push_cast [Nat.cast_sub h1] at e1
    rw [show (n : ℤ) - 1 - ((j : ℤ) - 2) = (n : ℤ) + 1 - j by ring] at e1
    linear_combination e2 - e1
  have hF0 : D 2 = D ((n : ℤ) - 1) := by
    have e1 := hEq 0 (by omega)
    have e2 := hEq 2 (by omega)
    have t := TT_step hD ((n : ℤ) - 1 - 2) (by omega)
    rw [show (n : ℤ) - 1 - 2 + 2 = (n : ℤ) - 1 by ring] at t
    simp only [Nat.cast_zero, sub_zero, zero_mul, zero_add] at e1
    push_cast at e2
    rw [t] at e1
    linear_combination (e2 - e1) / 2
  have hEnd1 : ((n : K) - 2) * D ((n : ℤ) - 2) + 2 * D 1 = 0 := by
    have e := hEq (n - 2) (by omega)
    push_cast [Nat.cast_sub (by omega : 2 ≤ n)] at e
    rw [show (n : ℤ) - 1 - ((n : ℤ) - 2) = 1 by ring, TT_one, hD] at e
    linear_combination e
  have hEnd0 : ((n : K) - 1) * D ((n : ℤ) - 1) + D 0 = 0 := by
    have e := hEq (n - 1) (by omega)
    push_cast [Nat.cast_sub (by omega : 1 ≤ n)] at e
    rw [show (n : ℤ) - 1 - ((n : ℤ) - 1) = 0 by ring, TT_zero] at e
    exact e
  refine ⟨?_, ?_⟩
  · -- (a) n even
    intro hpar k hk
    let α : ℕ → ℕ := fun j => if j = 2 then n - 1 else j - 2
    let β : ℕ → ℕ := fun j => if j = 2 then n - 1 else n + 1 - j
    let lam : ℕ → K := fun j => if j = 2 then 1 else ((j : K) - 2) / j
    let rk : ℕ → ℕ := fun j => if j % 2 = 1 then j else j + n
    have hall := weighted_means (Icc 1 (n - 1)) 1 (by simp only [mem_Icc]; omega) (fun j => D j) α β lam rk
      (by intro j hj hj1; simp only [mem_filter, mem_Icc] at hj ⊢; simp only [α]; split_ifs <;> omega)
      (by intro j hj hj1; simp only [mem_filter, mem_Icc] at hj ⊢; simp only [β]; split_ifs <;> omega)
      (by
        intro j hj hj1; simp only [mem_filter, mem_Icc] at hj
        simp only [lam]; split_ifs with h2
        · norm_num
        · exact step_lam j (by omega))
      (by
        intro j hj hj1; simp only [mem_filter, mem_Icc] at hj
        simp only [α, β, lam]; split_ifs with h2
        · subst h2
          have hn1 : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
          rw [hn1]; push_cast; rw [hF0]; ring
        · apply step_weights j (by omega)
          have := hF j (by omega) (by omega)
          rw [show ((j - 2 : ℕ) : ℤ) = (j : ℤ) - 2 by omega,
            show ((n + 1 - j : ℕ) : ℤ) = (n : ℤ) + 1 - j by omega]
          exact this)
      (by intro j hj hj1; simp only [mem_filter, mem_Icc] at hj; simp only [α, rk]; split_ifs <;> omega)
    have hc1 : ∀ j : ℕ, 1 ≤ j → j ≤ n - 1 → D j = D 1 := by
      intro j h1 h2
      have := hall j (by simp only [mem_Icc]; omega)
      simpa using this
    have hD1 : D 1 = 0 := by
      have e1 := hc1 (n - 2) (by omega) (by omega)
      rw [show ((n - 2 : ℕ) : ℤ) = (n : ℤ) - 2 by omega] at e1
      rw [e1] at hEnd1
      have : (n : K) * D 1 = 0 := by linear_combination hEnd1
      exact (mul_eq_zero.mp this).resolve_left hn0
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · have e1 := hc1 (n - 1) (by omega) le_rfl
      rw [show ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 by omega, hD1] at e1
      rw [e1] at hEnd0
      simpa using hEnd0
    · rw [hc1 k hk0 (by omega), hD1]
  · -- (b) n odd
    intro hpar
    let α : ℕ → ℕ := fun j => j - 2
    let β : ℕ → ℕ := fun j => n + 1 - j
    let lam : ℕ → K := fun j => ((j : K) - 2) / j
    let rk : ℕ → ℕ := fun j => j
    have hstep : ∀ j : ℕ, 3 ≤ j → j ≤ n - 1 →
        (fun j : ℕ => D (j : ℤ)) j = lam j * (fun j : ℕ => D (j : ℤ)) (α j) +
          (1 - lam j) * (fun j : ℕ => D (j : ℤ)) (β j) := by
      intro j h1 h2
      simp only [α, β, lam]
      apply step_weights j h1
      have := hF j (by omega) (by omega)
      rw [show ((j - 2 : ℕ) : ℤ) = (j : ℤ) - 2 by omega,
        show ((n + 1 - j : ℕ) : ℤ) = (n : ℤ) + 1 - j by omega]
      exact this
    -- even indices
    have hev := weighted_means ((Icc 2 (n - 1)).filter (fun j => j % 2 = 0)) 2
      (by rw [mem_filter, mem_Icc]; exact ⟨⟨le_rfl, by omega⟩, rfl⟩) (fun j => D j) α β lam rk
      (by intro j hj hj1; simp only [mem_filter, mem_Icc] at hj ⊢; simp only [α]; omega)
      (by intro j hj hj1; simp only [mem_filter, mem_Icc] at hj ⊢; simp only [β]; omega)
      (by intro j hj hj1; simp only [mem_filter, mem_Icc] at hj; exact step_lam j (by omega))
      (by intro j hj hj1; simp only [mem_filter, mem_Icc] at hj; exact hstep j (by omega) (by omega))
      (by intro j hj hj1; simp only [mem_filter, mem_Icc] at hj; simp only [α, rk]; omega)
    -- odd indices
    have hod := weighted_means ((Icc 3 (n - 2)).filter (fun j => j % 2 = 1)) 3
      (by rw [mem_filter, mem_Icc]; exact ⟨⟨le_rfl, by omega⟩, rfl⟩) (fun j => D j) α β lam rk
      (by intro j hj hj1; simp only [mem_filter, mem_Icc] at hj ⊢; simp only [α]; omega)
      (by intro j hj hj1; simp only [mem_filter, mem_Icc] at hj ⊢; simp only [β]; omega)
      (by intro j hj hj1; simp only [mem_filter, mem_Icc] at hj; exact step_lam j (by omega))
      (by intro j hj hj1; simp only [mem_filter, mem_Icc] at hj; exact hstep j (by omega) (by omega))
      (by intro j hj hj1; simp only [mem_filter, mem_Icc] at hj; simp only [α, rk]; omega)
    have hce : ∀ j : ℕ, 2 ≤ j → j ≤ n - 1 → j % 2 = 0 → D j = D 2 := by
      intro j h1 h2 h3
      have := hev j (by simp only [mem_filter, mem_Icc]; omega)
      simpa using this
    have hco : ∀ j : ℕ, 3 ≤ j → j ≤ n - 2 → j % 2 = 1 → D j = D 3 := by
      intro j h1 h2 h3
      have := hod j (by simp only [mem_filter, mem_Icc]; omega)
      simpa using this
    have hDn2 : D ((n : ℤ) - 2) = D 3 := by
      have := hco (n - 2) (by omega) le_rfl (by omega)
      rwa [show ((n - 2 : ℕ) : ℤ) = (n : ℤ) - 2 by omega] at this
    have hF1 : D 1 = D 3 := by
      have := hF 3 (by omega) (by omega)
      rw [show (n : ℤ) + 1 - ((3 : ℕ) : ℤ) = (n : ℤ) - 2 by push_cast; ring, hDn2,
        show ((3 : ℕ) : ℤ) - 2 = 1 by norm_num, show (((3 : ℕ) : ℤ)) = 3 by norm_num] at this
      push_cast at this
      linear_combination -this
    have hD3 : D 3 = 0 := by
      rw [hDn2, hF1] at hEnd1
      have : (n : K) * D 3 = 0 := by linear_combination hEnd1
      exact (mul_eq_zero.mp this).resolve_left hn0
    have hD0 : D 0 = -((n : K) - 1) * D 2 := by
      have := hce (n - 1) (by omega) le_rfl (by omega)
      rw [show ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 by omega] at this
      rw [this] at hEnd0
      linear_combination hEnd0
    intro k hk
    unfold dcirc
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [if_pos (by norm_num : ((0 : ℕ) : ℤ) = 0), if_pos (by norm_num : ((0 : ℕ) : ℤ) % 2 = 0)]
      simp only [Nat.cast_zero]
      rw [hD0]; ring
    rcases Nat.mod_two_eq_zero_or_one k with hk2 | hk2
    · have hne : (k : ℤ) ≠ 0 := by omega
      have hm : (k : ℤ) % 2 = 0 := by omega
      rw [if_neg hne, if_pos hm, hce k (by omega) (by omega) hk2]; ring
    · have hne : (k : ℤ) ≠ 0 := by omega
      have hm : ¬ (k : ℤ) % 2 = 0 := by omega
      rw [if_neg hne, if_neg hm]
      rcases Nat.lt_or_ge k 3 with h3 | h3
      · have : k = 1 := by omega
        subst this
        simp only [Nat.cast_one]
        rw [hF1, hD3]; ring
      · rw [hco k h3 (by omega) hk2, hD3]; ring

end QueensSpectrum
