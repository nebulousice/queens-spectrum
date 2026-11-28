import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Geometric = algebraic multiplicity for symmetric matrices over an ordered field

`PROOF.md` §1 uses that `A` is real symmetric, so the multiplicity of an eigenvalue as a root of
the characteristic polynomial equals `dim ker (A - λ I)`.  This file proves that standard fact
for a symmetric matrix over any linearly ordered field (if `(A - λ)² y = 0` then
`|(A - λ) y|² = y · (A - λ)² y = 0`), so that the main theorem can also be stated for the
algebraic multiplicity.
-/

set_option linter.deprecated false

namespace QueensSpectrum

open Matrix Module

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- For a symmetric matrix over a linearly ordered field, the maximal generalized eigenspace is
the eigenspace. -/
lemma maxGenEigenspace_eq_eigenspace_of_symm (A : Matrix ι ι K) (hA : Aᵀ = A) (μ : K) :
    End.maxGenEigenspace (toLin' A) μ = End.eigenspace (toLin' A) μ := by
  have hsym : ∀ x y : ι → K,
      (toLin' A - μ • (1 : End K (ι → K))) x ⬝ᵥ y =
        x ⬝ᵥ (toLin' A - μ • (1 : End K (ι → K))) y := by
    intro x y
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, End.one_apply, toLin'_apply,
      sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul]
    congr 1
    rw [dotProduct_mulVec, ← mulVec_transpose, hA, dotProduct_comm]
  have hsq : ∀ y, (toLin' A - μ • (1 : End K (ι → K)))
      ((toLin' A - μ • (1 : End K (ι → K))) y) = 0 →
        (toLin' A - μ • (1 : End K (ι → K))) y = 0 := by
    intro y hy
    apply dotProduct_self_eq_zero.mp
    rw [hsym, hy, dotProduct_zero]
  have hpow : ∀ (k : ℕ) (x : ι → K), ((toLin' A - μ • (1 : End K (ι → K))) ^ (k + 1)) x = 0 →
      (toLin' A - μ • (1 : End K (ι → K))) x = 0 := by
    intro k
    induction k with
    | zero => intro x hx; simpa using hx
    | succ k ih =>
      intro x hx
      apply ih
      rw [pow_succ', pow_succ', End.mul_apply, End.mul_apply] at hx
      rw [pow_succ', End.mul_apply]
      exact hsq _ hx
  apply le_antisymm
  · intro x hx
    rw [End.mem_maxGenEigenspace] at hx
    obtain ⟨k, hk⟩ := hx
    rw [End.mem_eigenspace_iff]
    rcases k with _ | k
    · simp only [pow_zero, End.one_apply] at hk
      simp [hk]
    · have := hpow k x hk
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, End.one_apply] at this
      exact sub_eq_zero.mp this
  · intro x hx
    rw [End.mem_eigenspace_iff] at hx
    rw [End.mem_maxGenEigenspace]
    refine ⟨1, ?_⟩
    simp only [pow_one, LinearMap.sub_apply, LinearMap.smul_apply, End.one_apply, hx, sub_self]

/-- For a symmetric matrix over a linearly ordered field, the algebraic multiplicity of `μ`
(as a root of the characteristic polynomial) equals the geometric multiplicity. -/
theorem rootMultiplicity_eq_finrank_of_symm (A : Matrix ι ι K) (hA : Aᵀ = A) (μ : K) :
    A.charpoly.rootMultiplicity μ = finrank K (End.eigenspace (toLin' A) μ) := by
  rw [← charpoly_toLin', ← LinearMap.finrank_maxGenEigenspace_eq,
    maxGenEigenspace_eq_eigenspace_of_symm A hA μ]

end QueensSpectrum
