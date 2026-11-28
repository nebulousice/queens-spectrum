import Pipeline.QueensSpectrum.Kernel
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Queens spectrum: the dimension count (proof of the Theorem, `PROOF.md` §8)

`ker (M - n I)` is the image of the injective linear map
`(r, γ) ↦ (r, -r, 0, 0) + γ (0, 0, d°, -d°)` on `{r palindromic, ∑ r = 0} × K` (odd `n`), or of
`r ↦ (r, -r, 0, 0)` on `{r palindromic, ∑ r = 0}` (even `n`).  The palindromic vectors form a
space of dimension `⌈n/2⌉ = (n+1)/2`, and `∑ r = 0` cuts it down by one (Lemma 6).
-/

set_option linter.deprecated false

namespace QueensSpectrum

open Matrix Finset Module

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {n : ℕ}

/-- Palindromic vectors `r_{n-1-i} = r_i`. -/
def Pal (K : Type*) [Field K] (n : ℕ) : Submodule K (Fin n → K) where
  carrier := {r | ∀ i, r i.rev = r i}
  add_mem' := by intro a b ha hb i; simp [ha i, hb i]
  zero_mem' := by intro i; simp
  smul_mem' := by intro c a ha i; simp [ha i]

/-- A palindromic vector is determined by its first `⌈n/2⌉` entries. -/
def palEquiv (K : Type*) [Field K] (n : ℕ) : Pal K n ≃ₗ[K] (Fin ((n + 1) / 2) → K) where
  toFun r := fun a => r.1 ⟨a.1, by omega⟩
  map_add' := by intros; rfl
  map_smul' := by intros; rfl
  invFun f := ⟨fun i => f ⟨min i.1 (n - 1 - i.1), by omega⟩, by
      intro i
      show f _ = f _
      congr 1; ext; simp only [Fin.val_rev]; omega⟩
  left_inv := by
    intro r
    apply Subtype.ext
    funext i
    show r.1 _ = r.1 i
    by_cases h : i.1 ≤ n - 1 - i.1
    · exact congrArg r.1 (Fin.ext (by simp only [Fin.val_mk]; omega))
    · rw [← r.2 i]; exact congrArg r.1 (Fin.ext (by simp only [Fin.val_mk, Fin.val_rev]; omega))
  right_inv := by
    intro f
    funext a
    show f _ = f a
    congr 1; ext; simp only; omega

omit [LinearOrder K] [IsStrictOrderedRing K] in
lemma finrank_Pal : finrank K (Pal K n) = (n + 1) / 2 := by
  rw [(palEquiv K n).finrank_eq, Module.finrank_fin_fun]

/-- `r ↦ ∑ r_i` on palindromic vectors. -/
def sumPal (K : Type*) [Field K] (n : ℕ) : Pal K n →ₗ[K] K where
  toFun r := ∑ i, r.1 i
  map_add' := by intro a b; simp [sum_add_distrib]
  map_smul' := by intro c a; simp [mul_sum]

lemma finrank_ker_sumPal (hn : 1 ≤ n) :
    finrank K (LinearMap.ker (sumPal K n)) = (n + 1) / 2 - 1 := by
  have hn0 : (n : K) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hsurj : Function.Surjective (sumPal K n) := by
    intro c
    refine ⟨⟨fun _ => c / n, fun _ => rfl⟩, ?_⟩
    simp only [sumPal, LinearMap.coe_mk, AddHom.coe_mk, sum_const, card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp
  have h := LinearMap.finrank_range_add_finrank_ker (sumPal K n)
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self, finrank_Pal] at h
  omega

/-- `{r palindromic, ∑ r = 0}`. -/
def P0 (K : Type*) [Field K] (n : ℕ) : Submodule K (Fin n → K) where
  carrier := {r | (∀ i, r i.rev = r i) ∧ ∑ i, r i = 0}
  add_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    exact ⟨fun i => by simp [ha1 i, hb1 i], by simp [sum_add_distrib, ha2, hb2]⟩
  zero_mem' := ⟨fun i => by simp, by simp⟩
  smul_mem' := by
    rintro c a ⟨ha1, ha2⟩
    exact ⟨fun i => by simp [ha1 i], by simp [← mul_sum, ha2]⟩

/-- `P0` is the kernel of `∑` on palindromic vectors. -/
def P0equiv (K : Type*) [Field K] (n : ℕ) : P0 K n ≃ₗ[K] LinearMap.ker (sumPal K n) where
  toFun r := ⟨⟨r.1, r.2.1⟩, LinearMap.mem_ker.mpr r.2.2⟩
  invFun x := ⟨x.1, x.1.2, LinearMap.mem_ker.mp x.2⟩
  map_add' := by intros; rfl
  map_smul' := by intros; rfl
  left_inv := by intro r; rfl
  right_inv := by intro x; rfl

/-- **Lemma 6 (dimension).** `dim {r palindromic, ∑ r = 0} = ⌈n/2⌉ - 1`. -/
lemma finrank_P0 (hn : 1 ≤ n) : finrank K (P0 K n) = (n + 1) / 2 - 1 := by
  rw [(P0equiv K n).finrank_eq, finrank_ker_sumPal hn]

/-- `r ↦ (r, -r, 0, 0)`. -/
def vecB1L (K : Type*) [Field K] (n : ℕ) : (Fin n → K) →ₗ[K] (Line n → K) where
  toFun := vecB1
  map_add' := by
    intro a b; funext L; rcases L with i | j | k | s <;> simp [vecB1]; ring
  map_smul' := by
    intro c a; funext L; rcases L with i | j | k | s <;> simp [vecB1]

/-- The parametrization of the kernel for even `n`. -/
def PsiE (K : Type*) [Field K] (n : ℕ) : P0 K n →ₗ[K] (Line n → K) :=
  vecB1L K n ∘ₗ (P0 K n).subtype

/-- The parametrization of the kernel for odd `n`. -/
def PsiO (K : Type*) [Field K] (n : ℕ) : (P0 K n × K) →ₗ[K] (Line n → K) :=
  (PsiE K n).coprod (LinearMap.toSpanSingleton K (Line n → K) (vecB2 K n))

omit [LinearOrder K] [IsStrictOrderedRing K] in
lemma PsiO_apply (x : P0 K n) (γ : K) :
    PsiO K n (x, γ) = vecB1 x.1 + γ • vecB2 K n := rfl

omit [LinearOrder K] [IsStrictOrderedRing K] in
lemma PsiE_apply (x : P0 K n) : PsiE K n x = vecB1 x.1 := rfl

omit [LinearOrder K] [IsStrictOrderedRing K] in
lemma P0_mem (x : P0 K n) : (∀ i, x.1 i.rev = x.1 i) ∧ ∑ i, x.1 i = 0 := x.2

omit [LinearOrder K] [IsStrictOrderedRing K] in
lemma P0_ext {x : P0 K n} (h : ∀ i, x.1 i = 0) : x = 0 := by
  apply Subtype.ext; funext i; exact h i

omit [LinearOrder K] [IsStrictOrderedRing K] in
lemma PsiE_inj : Function.Injective (PsiE K n) := by
  apply (injective_iff_map_eq_zero (PsiE K n)).mpr
  intro x hx
  rw [PsiE_apply] at hx
  exact P0_ext (fun i => congrFun hx (Sum.inl i))

lemma PsiO_inj (hn : 2 ≤ n) : Function.Injective (PsiO K n) := by
  apply (injective_iff_map_eq_zero (PsiO K n)).mpr
  rintro ⟨x, γ⟩ hx
  rw [PsiO_apply] at hx
  have hr : ∀ i, x.1 i = 0 := by
    intro i
    have := congrFun hx (Sum.inl i)
    simpa [vecB1, vecB2] using this
  have h0 : (0 : ℤ) ∈ DI n := by rw [mem_DI]; omega
  have hg : γ = 0 := by
    have := congrFun hx (Sum.inr (Sum.inr (Sum.inl ⟨0, h0⟩)))
    simp only [Pi.add_apply, Pi.smul_apply, vecB1, vecB2, dcirc, smul_eq_mul, Pi.zero_apply,
      zero_add] at this
    rw [if_pos trivial, if_pos (by norm_num)] at this
    have hn1 : (n : K) - 1 ≠ 0 := by
      have : (2 : K) ≤ n := by exact_mod_cast hn
      intro h; linarith
    exact (mul_eq_zero.mp this).resolve_right hn1
  rw [P0_ext hr, hg]; rfl

/-- For even `n`, `ker (M - n I) = {(r, -r, 0, 0)}`. -/
lemma range_PsiE (hn : 4 ≤ n) (hpar : n % 2 = 0) : LinearMap.range (PsiE K n) = E K n := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    rw [PsiE_apply]
    exact vecB1_mem _ (P0_mem x).1 (P0_mem x).2
  · intro v hv
    obtain ⟨r, hpal, hsum, γ, hγ, rfl⟩ := ker_char hn hv
    refine ⟨⟨r, hpal, hsum⟩, ?_⟩
    rw [PsiE_apply, hγ hpar, zero_smul, add_zero]

/-- For odd `n`, `ker (M - n I) = {(r, -r, 0, 0)} ⊕ K (0, 0, d°, -d°)`. -/
lemma range_PsiO (hn : 4 ≤ n) (hpar : n % 2 = 1) : LinearMap.range (PsiO K n) = E K n := by
  apply le_antisymm
  · rintro _ ⟨⟨x, γ⟩, rfl⟩
    rw [PsiO_apply]
    exact add_mem (vecB1_mem _ (P0_mem x).1 (P0_mem x).2)
      (Submodule.smul_mem _ _ (vecB2_mem hpar))
  · intro v hv
    obtain ⟨r, hpal, hsum, γ, -, rfl⟩ := ker_char hn hv
    exact ⟨(⟨r, hpal, hsum⟩, γ), rfl⟩

/-- **The count** (proof of the Theorem, §8): `dim ker (M - n I)`. -/
theorem finrank_E (hn : 4 ≤ n) :
    finrank K (E K n) = if Even n then (n - 2) / 2 else (n + 1) / 2 := by
  rcases Nat.mod_two_eq_zero_or_one n with hpar | hpar
  · have heven : Even n := Nat.even_iff.mpr hpar
    rw [if_pos heven, ← range_PsiE hn hpar, LinearMap.finrank_range_of_inj PsiE_inj,
      finrank_P0 (by omega)]
    omega
  · have hodd : ¬ Even n := by rw [Nat.not_even_iff]; exact hpar
    rw [if_neg hodd, ← range_PsiO hn hpar, LinearMap.finrank_range_of_inj (PsiO_inj (by omega)),
      Module.finrank_prod, finrank_P0 (by omega), Module.finrank_self]
    omega

end QueensSpectrum
