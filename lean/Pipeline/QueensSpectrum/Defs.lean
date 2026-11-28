import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Data.Int.Interval
import Mathlib.Tactic

/-!
# Queens spectrum: definitions, Lemma 1 and Lemma 5 of `PROOF.md`

Squares are `Fin n × Fin n`, square `(i, j)` has row `i` and column `j` (0-indexed, as in
`PROOF.md` §1).  Two **distinct** squares are adjacent in the `n`-Queens graph when they share a
row, a column, a diagonal (`i - j` constant) or an antidiagonal (`i + j` constant).

Lines: `Line n = Fin n ⊕ Fin n ⊕ DI n ⊕ DI n` (rows, columns, diagonals, antidiagonals), where a
diagonal or antidiagonal is indexed by an integer `k` with `|k| ≤ n - 1` (the set `DI n`).
Square `(i, j)` lies on row `i`, column `j`, diagonal `i - j` and antidiagonal `i + j - (n - 1)`,
exactly as in `PROOF.md` §1.
-/

namespace QueensSpectrum

open Finset Matrix

/-- `x` and `y` lie on a common row, column, diagonal or antidiagonal. -/
def Attack (n : ℕ) (x y : Fin n × Fin n) : Prop :=
  x.1 = y.1 ∨ x.2 = y.2 ∨ ((x.1 : ℤ) - x.2 = (y.1 : ℤ) - y.2) ∨
    ((x.1 : ℤ) + x.2 = (y.1 : ℤ) + y.2)

/-- The `n`-Queens graph `𝒬(n)`: vertices are the `n²` squares, two distinct squares are
adjacent when they share a row, a column, a diagonal or an antidiagonal. -/
def queensGraph (n : ℕ) : SimpleGraph (Fin n × Fin n) where
  Adj x y := x ≠ y ∧ Attack n x y
  symm := ⟨by
    intro x y h
    refine ⟨h.1.symm, ?_⟩
    rcases h.2 with h2 | h2 | h2 | h2
    exacts [Or.inl h2.symm, Or.inr (Or.inl h2.symm), Or.inr (Or.inr (Or.inl h2.symm)),
      Or.inr (Or.inr (Or.inr h2.symm))]⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance (n : ℕ) : DecidableRel (Attack n) := fun x y => by unfold Attack; infer_instance

instance (n : ℕ) : DecidableRel (queensGraph n).Adj := fun x y =>
  inferInstanceAs (Decidable (x ≠ y ∧ Attack n x y))

/-- Index set of the diagonals and antidiagonals: integers `k` with `-(n-1) ≤ k ≤ n-1`. -/
abbrev DI (n : ℕ) : Finset ℤ := Finset.Ioo (-(n : ℤ)) n

/-- The `6n - 2` lines: rows, columns, diagonals, antidiagonals. -/
abbrev Line (n : ℕ) := Fin n ⊕ Fin n ⊕ {k // k ∈ DI n} ⊕ {k // k ∈ DI n}

variable {K : Type*} [Field K] {n : ℕ}

/-- The square–line incidence matrix `N` (`N x L = [x ∈ L]`). -/
def N (K : Type*) [Zero K] [One K] (n : ℕ) : Matrix (Fin n × Fin n) (Line n) K := fun x L =>
  match L with
  | Sum.inl i => if x.1 = i then 1 else 0
  | Sum.inr (Sum.inl j) => if x.2 = j then 1 else 0
  | Sum.inr (Sum.inr (Sum.inl k)) => if (x.1 : ℤ) - x.2 = k.1 then 1 else 0
  | Sum.inr (Sum.inr (Sum.inr s)) => if (x.1 : ℤ) + x.2 - (n - 1) = s.1 then 1 else 0

/-- The Gram matrix of the lines, `M = Nᵀ N`, `M L L' = |L ∩ L'|`. -/
def M (K : Type*) [CommRing K] (n : ℕ) : Matrix (Line n) (Line n) K := (N K n)ᵀ * N K n

/-! ### Coordinates of a function on lines (extended by zero) -/

/-- Row values `r_i` (zero for `i ≥ n`). -/
def rr (v : Line n → K) (i : ℕ) : K := if h : i < n then v (Sum.inl ⟨i, h⟩) else 0
/-- Column values `c_j`. -/
def cc (v : Line n → K) (j : ℕ) : K := if h : j < n then v (Sum.inr (Sum.inl ⟨j, h⟩)) else 0
/-- Diagonal values `d_k` (zero for `|k| ≥ n`). -/
def dd (v : Line n → K) (k : ℤ) : K :=
  if h : k ∈ DI n then v (Sum.inr (Sum.inr (Sum.inl ⟨k, h⟩))) else 0
/-- Antidiagonal values `a_s`. -/
def aa (v : Line n → K) (s : ℤ) : K :=
  if h : s ∈ DI n then v (Sum.inr (Sum.inr (Sum.inr ⟨s, h⟩))) else 0

lemma mem_DI {k : ℤ} : k ∈ DI n ↔ -(n : ℤ) < k ∧ k < n := Finset.mem_Ioo

lemma sum_DI_ite (f : {k // k ∈ DI n} → K) (a : ℤ) :
    ∑ k : {k // k ∈ DI n}, (if a = k.1 then (1 : K) else 0) * f k =
      if h : a ∈ DI n then f ⟨a, h⟩ else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨a, h⟩]
    · simp
    · intro b _ hb
      rw [if_neg, zero_mul]
      intro hab
      exact hb (Subtype.ext hab.symm)
    · simp
  · apply Finset.sum_eq_zero
    intro k _
    rw [if_neg, zero_mul]
    intro hak
    exact h (hak ▸ k.2)

lemma sub_mem_DI (x : Fin n × Fin n) : (x.1 : ℤ) - x.2 ∈ DI n := by
  rw [mem_DI]; have := x.1.isLt; have := x.2.isLt; omega

lemma add_mem_DI (x : Fin n × Fin n) : (x.1 : ℤ) + x.2 - (n - 1) ∈ DI n := by
  rw [mem_DI]; have := x.1.isLt; have := x.2.isLt; omega

/-- (1.1): `(N v)(i, j) = r_i + c_j + d_{i-j} + a_{i+j-(n-1)}`. -/
lemma N_mulVec (v : Line n → K) (x : Fin n × Fin n) :
    (N K n *ᵥ v) x = rr v x.1 + cc v x.2 + dd v ((x.1 : ℤ) - x.2) +
      aa v ((x.1 : ℤ) + x.2 - (n - 1)) := by
  simp only [mulVec, dotProduct, Fintype.sum_sum_type, N]
  rw [sum_DI_ite, sum_DI_ite]
  simp [ite_mul, rr, cc, dd, aa, x.1.isLt, x.2.isLt, sub_mem_DI x, add_mem_DI x]
  abel

/-! ### Lemma 1: `N Nᵀ = A + 4 I` -/

lemma NNt_apply (x y : Fin n × Fin n) :
    (N K n * (N K n)ᵀ) x y =
      (if x.1 = y.1 then 1 else 0) + (if x.2 = y.2 then 1 else 0) +
      (if (x.1 : ℤ) - x.2 = (y.1 : ℤ) - y.2 then 1 else 0) +
      (if (x.1 : ℤ) + x.2 = (y.1 : ℤ) + y.2 then 1 else 0) := by
  simp only [Matrix.mul_apply, transpose_apply, Fintype.sum_sum_type, N]
  rw [sum_DI_ite (fun k => if (y.1 : ℤ) - y.2 = k.1 then (1 : K) else 0),
    sum_DI_ite (fun k => if (y.1 : ℤ) + y.2 - (n - 1) = k.1 then (1 : K) else 0)]
  simp only [sub_mem_DI x, add_mem_DI x, dite_true]
  have e1 : ∑ i : Fin n, (if x.1 = i then (1 : K) else 0) * (if y.1 = i then 1 else 0) =
      if x.1 = y.1 then 1 else 0 := by
    simp [eq_comm]
  have e2 : ∑ i : Fin n, (if x.2 = i then (1 : K) else 0) * (if y.2 = i then 1 else 0) =
      if x.2 = y.2 then 1 else 0 := by
    simp [eq_comm]
  rw [e1, e2]
  have c3 : ((y.1 : ℤ) - y.2 = (x.1 : ℤ) - x.2) ↔ ((x.1 : ℤ) - x.2 = (y.1 : ℤ) - y.2) := eq_comm
  have c4 : ((y.1 : ℤ) + y.2 - (n - 1) = (x.1 : ℤ) + x.2 - (n - 1)) ↔
      ((x.1 : ℤ) + x.2 = (y.1 : ℤ) + y.2) := by omega
  simp only [c3, c4]
  ring

/-- **Lemma 1.** `N Nᵀ = A + 4 I`, where `A` is the adjacency matrix of `𝒬(n)`. -/
theorem lemma1 : N K n * (N K n)ᵀ = (queensGraph n).adjMatrix K + (4 : K) • (1 : Matrix _ _ K) := by
  ext x y
  rw [NNt_apply, Matrix.add_apply, SimpleGraph.adjMatrix_apply, Matrix.smul_apply, Matrix.one_apply]
  obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := x
  obtain ⟨⟨i', hi'⟩, ⟨j', hj'⟩⟩ := y
  simp only [queensGraph, Attack, ne_eq, Prod.mk.injEq, Fin.mk.injEq, smul_eq_mul]
  split_ifs <;> first | (exfalso; omega) | norm_num

/-! ### Lemma 5: the row and diagonal components of `M v` -/

lemma Nt_mulVec_row (w : Fin n × Fin n → K) (i : Fin n) :
    ((N K n)ᵀ *ᵥ w) (Sum.inl i) = ∑ j : Fin n, w (i, j) := by
  simp only [mulVec, dotProduct, transpose_apply, N, Fintype.sum_prod_type, ite_mul, one_mul,
    zero_mul]
  rw [Finset.sum_eq_single i]
  · simp only [if_true]
  · intro b _ hb
    exact Finset.sum_eq_zero (fun j _ => if_neg hb)
  · intro h; exact absurd (Finset.mem_univ i) h

/-- Sum over the squares of the diagonal `k ≥ 0` of a function of the coordinates. -/
lemma sum_diag (g : ℕ → ℕ → K) (k : ℕ) :
    ∑ x : Fin n × Fin n, (if ((x.1 : ℕ) : ℤ) - (x.2 : ℕ) = k then (1 : K) else 0) * g x.1 x.2 =
      ∑ j ∈ range (n - k), g (j + k) j := by
  rw [Fintype.sum_prod_type]
  simp only [ite_mul, one_mul, zero_mul]
  rw [Fin.sum_univ_eq_sum_range (fun a => ∑ b : Fin n, if (a : ℤ) - (b : ℕ) = k then g a b else 0),
    Finset.sum_congr rfl (fun (a : ℕ) _ => Fin.sum_univ_eq_sum_range
      (fun b : ℕ => if (a : ℤ) - (b : ℤ) = k then g a b else 0) n)]
  rw [Finset.sum_comm]
  have h1 : ∀ b ∈ range n, (∑ a ∈ range n, if (a : ℤ) - (b : ℤ) = k then g a b else 0) =
      if b + k < n then g (b + k) b else 0 := by
    intro b _
    rw [Finset.sum_congr rfl (g := fun a => if a = b + k then g a b else 0)]
    · rw [Finset.sum_ite_eq']; simp
    · intro a _
      congr 1
      apply propext; omega
  rw [Finset.sum_congr rfl h1, ← Finset.sum_filter]
  congr 1
  ext b; simp; omega

lemma Nt_mulVec_diag (w : Fin n × Fin n → K) (W : ℕ → ℕ → K) (hw : ∀ x, w x = W x.1 x.2)
    (k : ℕ) (hk : (k : ℤ) ∈ DI n) :
    ((N K n)ᵀ *ᵥ w) (Sum.inr (Sum.inr (Sum.inl ⟨k, hk⟩))) =
      ∑ j ∈ range (n - k), W (j + k) j := by
  simp only [mulVec, dotProduct, transpose_apply, N, hw]
  exact sum_diag W k

/-- (4.0a): the row component of `M v`. -/
lemma M_mulVec_row (v : Line n → K) (i : ℕ) (hi : i < n) :
    (M K n *ᵥ v) (Sum.inl ⟨i, hi⟩) =
      ∑ j ∈ range n, (rr v i + cc v j + dd v ((i : ℤ) - j) + aa v ((i : ℤ) + j - (n - 1))) := by
  rw [M, ← mulVec_mulVec, Nt_mulVec_row]
  simp only [N_mulVec]
  exact Fin.sum_univ_eq_sum_range
    (fun j => rr v i + cc v j + dd v ((i : ℤ) - j) + aa v ((i : ℤ) + j - (n - 1))) n

/-- (4.0b): the diagonal component of `M v`, for a diagonal `k ≥ 0`. -/
lemma M_mulVec_diag (v : Line n → K) (k : ℕ) (hk : (k : ℤ) ∈ DI n) :
    (M K n *ᵥ v) (Sum.inr (Sum.inr (Sum.inl ⟨k, hk⟩))) =
      ∑ j ∈ range (n - k), (rr v (j + k) + cc v j + dd v k +
        aa v (2 * (j : ℤ) + k - (n - 1))) := by
  rw [M, ← mulVec_mulVec, Nt_mulVec_diag (N K n *ᵥ v) (fun a b : ℕ => rr v a + cc v b +
      dd v ((a : ℤ) - b) + aa v ((a : ℤ) + b - (n - 1))) (fun x => N_mulVec v x)]
  apply Finset.sum_congr rfl
  intro j _
  push_cast
  congr 3 <;> ring_nf

end QueensSpectrum
