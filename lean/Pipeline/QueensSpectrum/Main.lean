import Pipeline.QueensSpectrum.Count
import Pipeline.QueensSpectrum.Reduction
import Pipeline.QueensSpectrum.AlgMult
import Pipeline.QueensSpectrum.Eigenspace
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Ring.Rat

/-!
# Queens spectrum, ledger QS-1: the multiplicity of the eigenvalue `n - 4` of the `n`-Queens graph

Source: Cardoso, Costa, Duarte, Conjecture 1(b) of arXiv:2301.08106 (Discrete Math. 347 (2024)
114065); proof in `targets/queens-spectrum/PROOF.md`.

**Statement formalized.** For every `n ≥ 4`, the eigenspace of the adjacency matrix `A` of the
`n`-Queens graph `𝒬(n)` for the eigenvalue `n - 4` has dimension `(n-2)/2` if `n` is even and
`(n+1)/2` if `n` is odd.  This is the *geometric* multiplicity `dim ker (A - (n-4) I)`, which is
the meaning of "multiplicity" fixed in `PROOF.md` §1 (`A` is real symmetric).  It is stated
over any linearly ordered field `K` (`queens_mult`), and in particular over `ℝ` and `ℚ`.
Since `A` is symmetric, the same number is also the algebraic multiplicity, i.e. the
multiplicity of `n - 4` as a root of the characteristic polynomial (`queens_alg_mult`).

Conventions (as in `PROOF.md` §1): squares `(i, j) ∈ Fin n × Fin n`; two distinct squares are
adjacent iff they share a row (`i = i'`), a column (`j = j'`), a diagonal (`i - j = i' - j'`) or
an antidiagonal (`i + j = i' + j'`); `A = (queensGraph n).adjMatrix K`.

Files: `Defs` (graph, incidence matrix, Lemma 1, Lemma 5), `Reduction` (Lemma 2), `Seq`
(sums), `SectorE` (Lemma 7), `SectorA1` (Lemmas 8–9), `SectorB2` (Lemmas 10–12), `Symmetry`
(Lemma 3), `Kernel` (Lemmas 4, 6 and the sector decomposition), `Count` (§8), `AlgMult`
(geometric = algebraic multiplicity for symmetric matrices over an ordered field).
-/

set_option linter.deprecated false

namespace QueensSpectrum

open Matrix Module

/-- Sanity check of the definition (kernel `decide`): on the `4 × 4` board, `(0,0)` attacks
`(1,1)` (diagonal), `(0,3)` (row) and `(3,0)` (column), `(0,3)` attacks `(3,0)` (antidiagonal),
and `(0,0)` does not attack the knight-move square `(1,2)` nor itself. -/
theorem queensGraph_sanity :
    (queensGraph 4).Adj (0, 0) (1, 1) ∧ (queensGraph 4).Adj (0, 0) (0, 3) ∧
      (queensGraph 4).Adj (0, 0) (3, 0) ∧ (queensGraph 4).Adj (0, 3) (3, 0) ∧
      ¬ (queensGraph 4).Adj (0, 0) (1, 2) ∧ ¬ (queensGraph 4).Adj (0, 0) (0, 0) := by
  decide

/-- **Theorem (QS-1).** For `n ≥ 4`, `dim ker (A - (n - 4) I)` is `(n-2)/2` for even `n` and
`(n+1)/2` for odd `n`, over any linearly ordered field. -/
theorem queens_mult (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] (n : ℕ)
    (hn : 4 ≤ n) :
    finrank K (End.eigenspace (toLin' ((queensGraph n).adjMatrix K)) ((n : K) - 4)) =
      if Even n then (n - 2) / 2 else (n + 1) / 2 := by
  rw [lemma2 (by omega)]
  exact finrank_E hn

/-- **Theorem (QS-1), algebraic multiplicity.** The multiplicity of `n - 4` as a root of the
characteristic polynomial of `A` is the same number (`A` is symmetric). -/
theorem queens_alg_mult (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] (n : ℕ)
    (hn : 4 ≤ n) :
    ((queensGraph n).adjMatrix K).charpoly.rootMultiplicity ((n : K) - 4) =
      if Even n then (n - 2) / 2 else (n + 1) / 2 := by
  rw [rootMultiplicity_eq_finrank_of_symm _ (SimpleGraph.transpose_adjMatrix _) _]
  exact queens_mult K n hn

/-- **Theorem (QS-1), first sentence.** `n - 4` is an eigenvalue of `A` for every `n ≥ 4`. -/
theorem queens_hasEigenvalue (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (n : ℕ) (hn : 4 ≤ n) :
    End.HasEigenvalue (toLin' ((queensGraph n).adjMatrix K)) ((n : K) - 4) := by
  rw [End.hasEigenvalue_iff]
  intro h
  have := queens_mult K n hn
  rw [h, finrank_bot] at this
  split_ifs at this <;> omega

/-- **Theorem (QS-1)** over `ℝ`. -/
theorem queens_mult_real (n : ℕ) (hn : 4 ≤ n) :
    finrank ℝ (End.eigenspace (toLin' ((queensGraph n).adjMatrix ℝ)) ((n : ℝ) - 4)) =
      if Even n then (n - 2) / 2 else (n + 1) / 2 :=
  queens_mult ℝ n hn

/-- **Theorem (QS-1)** over `ℚ`. -/
theorem queens_mult_rat (n : ℕ) (hn : 4 ≤ n) :
    finrank ℚ (End.eigenspace (toLin' ((queensGraph n).adjMatrix ℚ)) ((n : ℚ) - 4)) =
      if Even n then (n - 2) / 2 else (n + 1) / 2 :=
  queens_mult ℚ n hn

/-- **Theorem (QS-1)** over `ℝ`, algebraic multiplicity. -/
theorem queens_alg_mult_real (n : ℕ) (hn : 4 ≤ n) :
    ((queensGraph n).adjMatrix ℝ).charpoly.rootMultiplicity ((n : ℝ) - 4) =
      if Even n then (n - 2) / 2 else (n + 1) / 2 :=
  queens_alg_mult ℝ n hn

end QueensSpectrum

#print axioms QueensSpectrum.queensGraph_sanity
#print axioms QueensSpectrum.lemma1
#print axioms QueensSpectrum.lemma2
#print axioms QueensSpectrum.ker_char
#print axioms QueensSpectrum.finrank_E
#print axioms QueensSpectrum.queens_mult
#print axioms QueensSpectrum.queens_mult_real
#print axioms QueensSpectrum.queens_mult_rat
#print axioms QueensSpectrum.queens_alg_mult
#print axioms QueensSpectrum.queens_hasEigenvalue
#print axioms QueensSpectrum.queens_alg_mult_real
#print axioms QueensSpectrum.queens_eigenspace
#print axioms QueensSpectrum.queens_eigenspace_real
