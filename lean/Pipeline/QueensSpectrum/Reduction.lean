import Pipeline.QueensSpectrum.Defs
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Lemma 2 of `PROOF.md`: reduction to the Gram matrix of the lines

For any matrix `B` and any `μ ≠ 0`, the `μ`-eigenspaces of `B Bᵀ` and `Bᵀ B` have the same
dimension (`v ↦ B v` and `w ↦ Bᵀ w` are injective between them).  With Lemma 1 this gives
`dim ker (A - (n-4) I) = dim ker (M - n I)`.
-/

set_option linter.deprecated false

namespace QueensSpectrum

open Matrix Module

variable {K : Type*} [Field K]

/-- `v ↦ B v` maps the `μ`-eigenspace of `Bᵀ B` injectively into that of `B Bᵀ` (`μ ≠ 0`). -/
lemma finrank_eigenspace_le_of_mul {m l : Type*} [Fintype m] [Fintype l] [DecidableEq m]
    [DecidableEq l] (B : Matrix m l K) (μ : K) (hμ : μ ≠ 0) :
    finrank K (End.eigenspace (toLin' (Bᵀ * B)) μ) ≤
      finrank K (End.eigenspace (toLin' (B * Bᵀ)) μ) := by
  have hmap : ∀ v ∈ End.eigenspace (toLin' (Bᵀ * B)) μ,
      toLin' B v ∈ End.eigenspace (toLin' (B * Bᵀ)) μ := by
    intro v hv
    rw [End.mem_eigenspace_iff, toLin'_apply] at hv ⊢
    rw [toLin'_apply, mulVec_mulVec, Matrix.mul_assoc, ← mulVec_mulVec, hv, mulVec_smul]
  let f := ((toLin' B).domRestrict (End.eigenspace (toLin' (Bᵀ * B)) μ)).codRestrict
    (End.eigenspace (toLin' (B * Bᵀ)) μ) (fun v => hmap v.1 v.2)
  apply LinearMap.finrank_le_finrank_of_injective (f := f)
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  have hv0 : B *ᵥ (v : l → K) = 0 := congrArg Subtype.val hv
  have hv2 := v.2
  rw [End.mem_eigenspace_iff, toLin'_apply, ← mulVec_mulVec, hv0, mulVec_zero] at hv2
  apply Subtype.ext
  have : μ • (v : l → K) = 0 := hv2.symm
  simpa [hμ] using this

/-- **Lemma 2 (general form).** For `μ ≠ 0`, `dim ker (B Bᵀ - μ) = dim ker (Bᵀ B - μ)`. -/
theorem finrank_eigenspace_mul_comm {m l : Type*} [Fintype m] [Fintype l] [DecidableEq m]
    [DecidableEq l] (B : Matrix m l K) (μ : K) (hμ : μ ≠ 0) :
    finrank K (End.eigenspace (toLin' (B * Bᵀ)) μ) =
      finrank K (End.eigenspace (toLin' (Bᵀ * B)) μ) := by
  apply le_antisymm
  · have := finrank_eigenspace_le_of_mul Bᵀ μ hμ
    rwa [transpose_transpose] at this
  · exact finrank_eigenspace_le_of_mul B μ hμ

variable {n : ℕ}

/-- The `(n-4)`-eigenspace of `A` is the `n`-eigenspace of `N Nᵀ` (Lemma 1). -/
lemma eigenspace_adj_eq :
    End.eigenspace (toLin' ((queensGraph n).adjMatrix K)) ((n : K) - 4) =
      End.eigenspace (toLin' (N K n * (N K n)ᵀ)) (n : K) := by
  ext x
  rw [End.mem_eigenspace_iff, End.mem_eigenspace_iff, toLin'_apply, toLin'_apply, lemma1,
    add_mulVec, smul_mulVec, one_mulVec, sub_smul]
  constructor
  · intro h; rw [h]; abel
  · intro h
    have : (queensGraph n).adjMatrix K *ᵥ x = (n : K) • x - (4 : K) • x := by
      rw [← h]; abel
    exact this

/-- **Lemma 2.** For `n ≥ 1`: `dim ker (A - (n-4) I) = dim ker (M - n I)`. -/
theorem lemma2 [CharZero K] (hn : 1 ≤ n) :
    finrank K (End.eigenspace (toLin' ((queensGraph n).adjMatrix K)) ((n : K) - 4)) =
      finrank K (End.eigenspace (toLin' (M K n)) (n : K)) := by
  rw [eigenspace_adj_eq, finrank_eigenspace_mul_comm _ _ (by exact_mod_cast (by omega : n ≠ 0))]
  rfl

end QueensSpectrum
