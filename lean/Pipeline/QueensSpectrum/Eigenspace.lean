import Pipeline.QueensSpectrum.Count
import Pipeline.QueensSpectrum.Reduction
import Mathlib.Basic.Real.Basic

/-!
# Queens spectrum, ledger QS-2: the explicit eigenspace (Corollary 13 of `PROOF.md` §8)

For `n ≥ 4` the eigenspace of the adjacency matrix `A` of `𝒬(n)` for the eigenvalue `n - 4`
consists exactly of the functions
`x (i, j) = r i - r j + γ * ([i = j] - [i + j = n - 1])`
with `r` palindromic (`r (n - 1 - i) = r i`) and `γ` a scalar, `γ = 0` when `n` is even
(0-indexed squares, as in `Defs.lean`).

Proof, as in `PROOF.md`: by Lemma 1 the eigenspace is the `n`-eigenspace of `N Nᵀ`, which is
`N (ker (M - n I))` (Lemma 2, `v = Nᵀ x / n`).  `ker (M - n I)` is identified exactly by
`ker_char`, `vecB1_mem`, `vecB2_mem`; its image under `N` is computed by (1.1):
`N (r, -r, 0, 0) = r_i - r_j` and, for odd `n`, `N (0, 0, d°, -d°) = n ([i = j] - [i + j = n - 1])`.
-/

set_option linter.deprecated false

namespace QueensSpectrum

open Matrix Finset Module

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {n : ℕ}

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- `N (r, -r, 0, 0) (i, j) = r_i - r_j`. -/
lemma N_vecB1 (r : Fin n → K) (i j : Fin n) : (N K n *ᵥ vecB1 r) (i, j) = r i - r j := by
  rw [N_mulVec, rr_vecB1 r i i.2, cc_vecB1 r j j.2, dd_vecB1, aa_vecB1]
  simp only [Fin.eta]
  ring

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- For odd `n`: `N (0, 0, d°, -d°) (i, j) = n ([i = j] - [i + j = n - 1])`. -/
lemma N_vecB2 (hodd : n % 2 = 1) (i j : Fin n) :
    (N K n *ᵥ vecB2 K n) (i, j) =
      (n : K) * ((if i = j then 1 else 0) - (if (i : ℕ) + (j : ℕ) = n - 1 then 1 else 0)) := by
  rw [N_mulVec]
  have e1 : rr (vecB2 K n) (i, j).1 = 0 := by rw [rr_of (i, j).1.2]; rfl
  have e2 : cc (vecB2 K n) (i, j).2 = 0 := by rw [cc_of (i, j).2.2]; rfl
  have e3 : dd (vecB2 K n) (((i, j).1 : ℤ) - (i, j).2) = dcirc K n ((i : ℤ) - j) := by
    rw [dd_of (sub_mem_DI (i, j))]; rfl
  have e4 : aa (vecB2 K n) (((i, j).1 : ℤ) + (i, j).2 - (n - 1)) =
      -dcirc K n ((i : ℤ) + j - (n - 1)) := by
    rw [aa_of (add_mem_DI (i, j))]; rfl
  rw [e1, e2, e3, e4]
  unfold dcirc
  obtain ⟨i, hi⟩ := i
  obtain ⟨j, hj⟩ := j
  simp only [Fin.mk.injEq]
  split_ifs <;> first | (exfalso; omega) | ring

/-- `ker (A - (n - 4) I) = N (ker (M - n I))`, membership form. -/
lemma mem_eigenspace_adj_iff (hn : 1 ≤ n) (x : Fin n × Fin n → K) :
    x ∈ End.eigenspace (toLin' ((queensGraph n).adjMatrix K)) ((n : K) - 4) ↔
      ∃ v ∈ E K n, x = N K n *ᵥ v := by
  have hn0 : (n : K) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  rw [eigenspace_adj_eq, End.mem_eigenspace_iff, toLin'_apply]
  constructor
  · intro hx
    refine ⟨(n : K)⁻¹ • ((N K n)ᵀ *ᵥ x), ?_, ?_⟩
    · rw [mem_E, M, mulVec_smul, mulVec_mulVec, Matrix.mul_assoc, ← mulVec_mulVec, hx,
        mulVec_smul, smul_comm]
    · rw [mulVec_smul, mulVec_mulVec, hx, smul_smul, inv_mul_cancel₀ hn0, one_smul]
  · rintro ⟨v, hv, rfl⟩
    rw [mem_E, M] at hv
    rw [mulVec_mulVec, Matrix.mul_assoc, ← mulVec_mulVec, hv, mulVec_smul]

/-- **Corollary 13 (QS-2).** For `n ≥ 4`, a function `x` on the squares is an eigenvector of `A`
for `n - 4` (or zero) if and only if `x (i, j) = r i - r j + γ ([i = j] - [i + j = n - 1])` with
`r` palindromic and `γ = 0` when `n` is even. -/
theorem queens_eigenspace (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (n : ℕ) (hn : 4 ≤ n) (x : Fin n × Fin n → K) :
    x ∈ End.eigenspace (toLin' ((queensGraph n).adjMatrix K)) ((n : K) - 4) ↔
      ∃ r : Fin n → K, (∀ i, r i.rev = r i) ∧ ∃ γ : K, (Even n → γ = 0) ∧
        ∀ i j : Fin n, x (i, j) = r i - r j +
          γ * ((if i = j then 1 else 0) - (if (i : ℕ) + (j : ℕ) = n - 1 then 1 else 0)) := by
  have hn0 : (n : K) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  rw [mem_eigenspace_adj_iff (by omega)]
  constructor
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨r, hpal, -, γ, hγ, rfl⟩ := ker_char hn hv
    refine ⟨r, hpal, γ * n, fun he => by rw [hγ (Nat.even_iff.mp he), zero_mul], ?_⟩
    intro i j
    rw [mulVec_add, mulVec_smul, Pi.add_apply, Pi.smul_apply, N_vecB1, smul_eq_mul]
    rcases Nat.mod_two_eq_zero_or_one n with hpar | hpar
    · rw [hγ hpar]; ring
    · rw [N_vecB2 hpar]; ring
  · rintro ⟨r, hpal, γ, hγ, hx⟩
    set c : K := (∑ i, r i) / n with hc
    set r' : Fin n → K := fun i => r i - c with hr'
    have hpal' : ∀ i, r' i.rev = r' i := fun i => by simp only [hr', hpal i]
    have hsum' : ∑ i, r' i = 0 := by
      simp only [hr', Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, hc]
      field_simp
      ring
    rcases Nat.mod_two_eq_zero_or_one n with hpar | hpar
    · refine ⟨vecB1 r', vecB1_mem r' hpal' hsum', ?_⟩
      funext ⟨i, j⟩
      rw [hx, N_vecB1, hγ (Nat.even_iff.mpr hpar)]
      simp only [hr']
      ring
    · refine ⟨vecB1 r' + (γ / n) • vecB2 K n,
        add_mem (vecB1_mem r' hpal' hsum') (Submodule.smul_mem _ _ (vecB2_mem hpar)), ?_⟩
      funext ⟨i, j⟩
      rw [hx, mulVec_add, mulVec_smul, Pi.add_apply, Pi.smul_apply, N_vecB1, smul_eq_mul,
        N_vecB2 hpar]
      simp only [hr']
      field_simp
      ring

/-- **Corollary 13 (QS-2)** over `ℝ`. -/
theorem queens_eigenspace_real (n : ℕ) (hn : 4 ≤ n) (x : Fin n × Fin n → ℝ) :
    x ∈ End.eigenspace (toLin' ((queensGraph n).adjMatrix ℝ)) ((n : ℝ) - 4) ↔
      ∃ r : Fin n → ℝ, (∀ i, r i.rev = r i) ∧ ∃ γ : ℝ, (Even n → γ = 0) ∧
        ∀ i j : Fin n, x (i, j) = r i - r j +
          γ * ((if i = j then 1 else 0) - (if (i : ℕ) + (j : ℕ) = n - 1 then 1 else 0)) :=
  queens_eigenspace ℝ n hn x

end QueensSpectrum
