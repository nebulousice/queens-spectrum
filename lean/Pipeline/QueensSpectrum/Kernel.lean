import Pipeline.QueensSpectrum.Symmetry
import Pipeline.QueensSpectrum.SectorB2
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Queens spectrum: the kernel of `M - n I` (Lemmas 4, 6, 7, 9, 12 and the proof of the Theorem)

`E K n` is the `n`-eigenspace of `M` (= `ker (M - n I)`).  We prove

* `ker_char`: every `v ∈ E` is `vecB1 r + γ • vecB2` with `r` palindromic, `∑ r = 0`, and
  `γ = 0` when `n` is even (the sector decomposition, Lemma 4, with Lemmas 6, 7, 9, 12);
* `vecB1_mem`, `vecB2_mem`: these vectors lie in `E` (`vecB2` only for odd `n`).

The five sector components of `v` are written with explicit projectors built from `t`, `h`,
`z` (`Vp`, `Vm`, `Pp`, `Qq`), exactly as in the proof of Lemma 4(a).
-/

set_option linter.deprecated false

namespace QueensSpectrum

open Matrix Finset

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {n : ℕ}

/-- `ker (M - n I)`, as the `n`-eigenspace of `M`. -/
abbrev E (K : Type*) [Field K] (n : ℕ) : Submodule K (Line n → K) :=
  Module.End.eigenspace (toLin' (M K n)) (n : K)

omit [LinearOrder K] [IsStrictOrderedRing K] in
lemma mem_E {u : Line n → K} : u ∈ E K n ↔ M K n *ᵥ u = (n : K) • u := by
  rw [Module.End.mem_eigenspace_iff, toLin'_apply]

omit [LinearOrder K] [IsStrictOrderedRing K] in
lemma E_comp {u : Line n → K} (hu : u ∈ E K n) (π : Line n → Line n)
    (hc : ∀ v : Line n → K, M K n *ᵥ (v ∘ π) = (M K n *ᵥ v) ∘ π) : u ∘ π ∈ E K n := by
  rw [mem_E] at *; rw [hc, hu]; rfl

/-! ### The projectors of Lemma 4(a) -/

/-- `(I + z)/2`. -/
def Vp (u : Line n → K) : Line n → K := fun L => (u L + u (lz L)) / 2
/-- `(I - z)/2`. -/
def Vm (u : Line n → K) : Line n → K := fun L => (u L - u (lz L)) / 2
/-- `π_{εδ} = (I + ε t)(I + δ h)/4`. -/
def Pp (ε δ : K) (u : Line n → K) : Line n → K :=
  fun L => (u L + ε * u (lt L) + δ * u (lh L) + ε * δ * u (lh (lt L))) / 4
/-- `(I + δ h)/2`. -/
def Qq (δ : K) (u : Line n → K) : Line n → K := fun L => (u L + δ * u (lh L)) / 2

omit [LinearOrder K] [IsStrictOrderedRing K] in
lemma Vp_mem {u : Line n → K} (hu : u ∈ E K n) : Vp u ∈ E K n := by
  have : Vp u = (1 / 2 : K) • (u + u ∘ lz) := by
    funext L; simp only [Vp, Pi.smul_apply, Pi.add_apply, Function.comp, smul_eq_mul]; ring
  rw [this]
  exact Submodule.smul_mem _ _ (add_mem hu (E_comp hu lz M_comm_lz))

omit [LinearOrder K] [IsStrictOrderedRing K] in
lemma Vm_mem {u : Line n → K} (hu : u ∈ E K n) : Vm u ∈ E K n := by
  have : Vm u = (1 / 2 : K) • (u - u ∘ lz) := by
    funext L; simp only [Vm, Pi.smul_apply, Pi.sub_apply, Function.comp, smul_eq_mul]; ring
  rw [this]
  exact Submodule.smul_mem _ _ (sub_mem hu (E_comp hu lz M_comm_lz))

omit [LinearOrder K] [IsStrictOrderedRing K] in
lemma Pp_mem {u : Line n → K} (hu : u ∈ E K n) (ε δ : K) : Pp ε δ u ∈ E K n := by
  have : Pp ε δ u = (1 / 4 : K) • (u + ε • (u ∘ lt) + δ • (u ∘ lh) + (ε * δ) • ((u ∘ lh) ∘ lt)) := by
    funext L
    simp only [Pp, Pi.smul_apply, Pi.add_apply, Function.comp, smul_eq_mul]; ring
  rw [this]
  have h1 := E_comp hu lt M_comm_lt
  have h2 := E_comp hu lh M_comm_lh
  have h3 := E_comp h2 lt M_comm_lt
  exact Submodule.smul_mem _ _ (add_mem (add_mem (add_mem hu (Submodule.smul_mem _ _ h1))
    (Submodule.smul_mem _ _ h2)) (Submodule.smul_mem _ _ h3))

omit [LinearOrder K] [IsStrictOrderedRing K] in
lemma Qq_mem {u : Line n → K} (hu : u ∈ E K n) (δ : K) : Qq δ u ∈ E K n := by
  have : Qq δ u = (1 / 2 : K) • (u + δ • (u ∘ lh)) := by
    funext L; simp only [Qq, Pi.smul_apply, Pi.add_apply, Function.comp, smul_eq_mul]; ring
  rw [this]
  exact Submodule.smul_mem _ _ (add_mem hu (Submodule.smul_mem _ _ (E_comp hu lh M_comm_lh)))

/-- `v = A₁ + B₁ + B₂ + W + E + E'` (Lemma 4(a)). -/
lemma decomp (v : Line n → K) :
    v = Pp 1 1 (Vp v) + Pp (-1) 1 (Vp v) + Pp 1 (-1) (Vp v) + Pp (-1) (-1) (Vp v) +
      Qq 1 (Vm v) + Qq (-1) (Vm v) := by
  funext L
  simp only [Pp, Qq, Vp, Vm, Pi.add_apply]
  ring

omit [LinearOrder K] [IsStrictOrderedRing K] in
lemma Vp_z (u : Line n → K) (L : Line n) : Vp u (lz L) = Vp u L := by
  simp only [Vp, lz_invol L]; ring

omit [LinearOrder K] [IsStrictOrderedRing K] in
lemma Vm_z (u : Line n → K) (L : Line n) : Vm u (lz L) = -Vm u L := by
  simp only [Vm, lz_invol L]; ring

omit [LinearOrder K] [IsStrictOrderedRing K] in
lemma Pp_t (u : Line n → K) (ε δ : K) (hε : ε * ε = 1) (L : Line n) :
    Pp ε δ u (lt L) = ε * Pp ε δ u L := by
  simp only [Pp, lt_invol L]
  linear_combination (-(1 / 4) * (u (lt L) + δ * u (lh (lt L)))) * hε

omit [LinearOrder K] [IsStrictOrderedRing K] in
lemma Pp_h (u : Line n → K) (hz : ∀ L, u (lz L) = u L) (ε δ : K) (hδ : δ * δ = 1)
    (L : Line n) : Pp ε δ u (lh L) = δ * Pp ε δ u L := by
  simp only [Pp, lh_invol L]
  rw [lh_lt_lh L, lt_lh L, hz, hz]
  linear_combination (-(1 / 4) * (u (lh L) + ε * u (lh (lt L)))) * hδ

omit [LinearOrder K] [IsStrictOrderedRing K] in
lemma Qq_h (u : Line n → K) (δ : K) (hδ : δ * δ = 1) (L : Line n) :
    Qq δ u (lh L) = δ * Qq δ u L := by
  simp only [Qq, lh_invol L]
  linear_combination (-(1 / 2) * u (lh L)) * hδ

omit [LinearOrder K] [IsStrictOrderedRing K] in
lemma Qq_z (u : Line n → K) (hz : ∀ L, u (lz L) = -u L) (δ : K) (L : Line n) :
    Qq δ u (lz L) = -Qq δ u L := by
  simp only [Qq]
  rw [lh_lz L, hz, hz]; ring

/-! ### Coordinates -/

omit [LinearOrder K] [IsStrictOrderedRing K] in
lemma two_mul_eq_zero {x : K} [CharZero K] (h : x = -x) : x = 0 := by
  have : (2 : K) * x = 0 := by linear_combination h
  simpa using this

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- If `d_k = 0` for `0 ≤ k < n` and `d_{-k} = ± d_k`, then `d = 0`. -/
lemma dd_zero_of_nat {u : Line n → K} {s : K} (hD : ∀ k, dd u (-k) = s * dd u k)
    (h : ∀ k : ℕ, k < n → dd u k = 0) : ∀ k, dd u k = 0 := by
  intro k
  by_cases hk : k ∈ DI n
  · rw [mem_DI] at hk
    rcases le_or_gt 0 k with h0 | h0
    · have := h k.toNat (by omega)
      rwa [show ((k.toNat : ℕ) : ℤ) = k by omega] at this
    · have := h (-k).toNat (by omega)
      rw [show (((-k).toNat : ℕ) : ℤ) = -k by omega] at this
      rw [show k = -(-k) by ring, hD, this, mul_zero]
  · simp [dd, hk]

/-! ### The zero sectors -/

/-- **Lemma 9** in `V`: an `A₁` vector of the kernel is zero. -/
theorem A1_zero (hn : 4 ≤ n) {u : Line n → K} (hu : u ∈ E K n)
    (hT : ∀ L, u (lt L) = 1 * u L) (hH : ∀ L, u (lh L) = 1 * u L) : u = 0 := by
  obtain ⟨hrow, hdiag⟩ := ker_eqs (mem_E.mp hu)
  obtain ⟨tc, td, -⟩ := T_coords hT
  obtain ⟨-, hc, ha⟩ := H_coords hH
  simp only [one_mul] at tc td hc ha
  have hr : ∀ i, i < n → rr u (n - 1 - i) = rr u i := by
    intro i hi
    rw [← tc (n - 1 - i) (by omega), hc i hi, tc i hi]
  obtain ⟨h1, h2⟩ := sectorA1_pure n hn (rr u) (cc u) (dd u) (aa u) hr tc td ha hrow hdiag
  have hd := dd_zero_of_nat (s := 1) (by simpa using td) h2
  apply eq_zero_of_coords h1 (fun j hj => by rw [tc j hj, h1 j hj]) hd
    (fun k => by rw [ha, hd])

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- The space `W = {tv = -v, hv = -v}` is zero (proof of Lemma 4(c)). -/
theorem W_zero [CharZero K] {u : Line n → K} (hT : ∀ L, u (lt L) = -1 * u L)
    (hH : ∀ L, u (lh L) = -1 * u L) : u = 0 := by
  obtain ⟨tc, -, ta⟩ := T_coords hT
  obtain ⟨hr, -, ha⟩ := H_coords hH
  have hr0 : ∀ i, i < n → rr u i = 0 := fun i hi =>
    two_mul_eq_zero (by linear_combination hr i hi)
  have ha0 : ∀ k, aa u k = 0 := fun k => two_mul_eq_zero (by linear_combination ta k)
  apply eq_zero_of_coords hr0 (fun j hj => by rw [tc j hj, hr0 j hj, mul_zero])
    (fun k => by have := ha k; rw [ha0] at this; linear_combination this) ha0

/-- **Lemma 7** in `V`: an `E` vector of the kernel is zero. -/
theorem E_zero {u : Line n → K} (hu : u ∈ E K n)
    (hZ : ∀ L, u (lz L) = -1 * u L) (hH : ∀ L, u (lh L) = 1 * u L) : u = 0 := by
  obtain ⟨hrow, hdiag⟩ := ker_eqs (mem_E.mp hu)
  obtain ⟨zr, zc, zd⟩ := Z_coords hZ
  obtain ⟨-, hc, ha⟩ := H_coords hH
  simp only [one_mul, neg_one_mul] at zr zc zd hc ha
  have hc0 : ∀ j, j < n → cc u j = 0 := fun j hj =>
    two_mul_eq_zero (by linear_combination zc j hj - hc j hj)
  obtain ⟨h1, h2⟩ := sectorE_pure n (rr u) (cc u) (dd u) (aa u) zr hc0 zd ha hrow hdiag
  have hd := dd_zero_of_nat (s := -1) (by simpa using zd) h2
  exact eq_zero_of_coords h1 hc0 hd (fun k => by rw [ha, hd])

/-! ### The sectors `B₁` and `B₂` -/

/-- The vector `(r, -r, 0, 0)` of `V_{B1}`. -/
def vecB1 (r : Fin n → K) : Line n → K
  | Sum.inl i => r i
  | Sum.inr (Sum.inl j) => -r j
  | Sum.inr (Sum.inr _) => 0

/-- The vector `(0, 0, d°, -d°)` of `V_{B2}`. -/
def vecB2 (K : Type*) [Field K] (n : ℕ) : Line n → K
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 0
  | Sum.inr (Sum.inr (Sum.inl k)) => dcirc K n k.1
  | Sum.inr (Sum.inr (Sum.inr s)) => -dcirc K n s.1

omit [LinearOrder K] [IsStrictOrderedRing K] in
lemma dcirc_neg (k : ℤ) : dcirc K n (-k) = dcirc K n k := by
  unfold dcirc
  congr 1
  · exact if_congr (by omega) rfl rfl
  · exact if_congr (by omega) rfl rfl

/-- **Lemma 6** in `V`: a `B₁` vector of the kernel is `(r, -r, 0, 0)` with `r` palindromic
and `∑ r = 0`. -/
theorem B1_form {u : Line n → K} (hn : 1 ≤ n) (hu : u ∈ E K n)
    (hT : ∀ L, u (lt L) = -1 * u L) (hH : ∀ L, u (lh L) = 1 * u L) :
    (∀ i : Fin n, rr u i.rev = rr u i) ∧ (∑ i : Fin n, rr u i = 0) ∧
      u = vecB1 (fun i : Fin n => rr u i) := by
  obtain ⟨hrow, -⟩ := ker_eqs (mem_E.mp hu)
  obtain ⟨tc, -, ta⟩ := T_coords hT
  obtain ⟨-, hc, ha⟩ := H_coords hH
  simp only [one_mul, neg_one_mul] at tc ta hc ha
  have ha0 : ∀ k, aa u k = 0 := fun k => two_mul_eq_zero (ta k)
  have hd0 : ∀ k, dd u k = 0 := fun k => by rw [← ha, ha0]
  have hpal : ∀ i, i < n → rr u (n - 1 - i) = rr u i := by
    intro i hi
    have e1 := tc (n - 1 - i) (by omega)
    have e2 := tc i hi
    have e3 := hc i hi
    rw [e1, e2] at e3
    linear_combination -e3
  refine ⟨fun i => ?_, ?_, ?_⟩
  · rw [Fin.val_rev, show n - (i + 1) = n - 1 - i by omega]; exact hpal i i.2
  · have h := hrow 0 (by omega)
    simp only [hd0, ha0, add_zero] at h
    rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul, add_eq_left] at h
    rw [Fin.sum_univ_eq_sum_range (fun i => rr u i)]
    have : ∑ j ∈ range n, cc u j = -∑ j ∈ range n, rr u j := by
      rw [← sum_neg_distrib]
      exact sum_congr rfl (fun j hj => tc j (by simpa using hj))
    rw [this] at h
    linear_combination -h
  · funext L
    rcases L with i | j | k | s
    · simp only [vecB1]; rw [rr_of i.2]
    · simp only [vecB1]; rw [← tc j j.2, cc_of j.2]
    · simp only [vecB1]; have := hd0 k.1; rwa [dd_of k.2] at this
    · simp only [vecB1]; have := ha0 s.1; rwa [aa_of s.2] at this

/-- **Lemma 12** in `V`: a `B₂` vector of the kernel is zero for even `n` and a multiple of
`(0, 0, d°, -d°)` for odd `n`. -/
theorem B2_form (hn : 4 ≤ n) {u : Line n → K} (hu : u ∈ E K n)
    (hT : ∀ L, u (lt L) = 1 * u L) (hH : ∀ L, u (lh L) = -1 * u L) :
    (n % 2 = 0 → u = 0) ∧ (n % 2 = 1 → u = (-dd u 2) • vecB2 K n) := by
  obtain ⟨-, hdiag⟩ := ker_eqs (mem_E.mp hu)
  obtain ⟨tc, td, -⟩ := T_coords hT
  obtain ⟨hr, -, ha⟩ := H_coords hH
  simp only [one_mul, neg_one_mul] at tc td hr ha
  have hr0 : ∀ i, i < n → rr u i = 0 := fun i hi => two_mul_eq_zero (hr i hi)
  have hc0 : ∀ j, j < n → cc u j = 0 := fun j hj => by rw [tc j hj, hr0 j hj]
  obtain ⟨hev, hod⟩ := sectorB2_pure n hn (rr u) (cc u) (dd u) (aa u) hr0 hc0 td ha hdiag
  refine ⟨fun hpar => ?_, fun hpar => ?_⟩
  · have hd := dd_zero_of_nat (s := 1) (by simpa using td) (hev hpar)
    exact eq_zero_of_coords hr0 hc0 hd (fun k => by rw [ha, hd, neg_zero])
  · have hval : ∀ k, k ∈ DI n → dd u k = -dd u 2 * dcirc K n k := by
      intro k hk
      rw [mem_DI] at hk
      rcases le_or_gt 0 k with h0 | h0
      · have := hod hpar k.toNat (by omega)
        rwa [show ((k.toNat : ℕ) : ℤ) = k by omega] at this
      · have := hod hpar (-k).toNat (by omega)
        rw [show (((-k).toNat : ℕ) : ℤ) = -k by omega, td, dcirc_neg] at this
        exact this
    funext L
    rcases L with i | j | k | s
    · simp only [Pi.smul_apply, vecB2, smul_zero]; have := hr0 i i.2; rwa [rr_of i.2] at this
    · simp only [Pi.smul_apply, vecB2, smul_zero]; have := hc0 j j.2; rwa [cc_of j.2] at this
    · simp only [Pi.smul_apply, vecB2, smul_eq_mul]; have := hval k k.2
      rwa [dd_of k.2] at this
    · simp only [Pi.smul_apply, vecB2, smul_eq_mul]; have := ha s
      rw [aa_of s.2, hval s s.2] at this
      exact this.trans (by ring)

/-! ### The kernel, upper bound: the sector decomposition -/

/-- Every vector of `ker (M - n I)` is `vecB1 r + γ • vecB2` with `r` palindromic,
`∑ r = 0`, and `γ = 0` for even `n`. -/
theorem ker_char (hn : 4 ≤ n) {v : Line n → K} (hv : v ∈ E K n) :
    ∃ r : Fin n → K, (∀ i, r i.rev = r i) ∧ (∑ i, r i = 0) ∧
      ∃ γ : K, (n % 2 = 0 → γ = 0) ∧ v = vecB1 r + γ • vecB2 K n := by
  have hp := Vp_mem hv
  have hm := Vm_mem hv
  have hpz := Vp_z v
  have hmz := Vm_z v
  have one1 : (1 : K) * 1 = 1 := by norm_num
  have neg1 : (-1 : K) * -1 = 1 := by norm_num
  -- A₁ = 0
  have hA1 : Pp 1 1 (Vp v) = 0 :=
    A1_zero hn (Pp_mem hp 1 1) (Pp_t _ 1 1 one1) (Pp_h _ hpz 1 1 one1)
  -- W = 0
  have hW : Pp (-1) (-1) (Vp v) = 0 :=
    W_zero (Pp_t _ (-1) (-1) neg1) (Pp_h _ hpz (-1) (-1) neg1)
  -- E = 0
  have hE : Qq 1 (Vm v) = 0 :=
    E_zero (Qq_mem hm 1) (fun L => by rw [Qq_z _ hmz 1 L]; ring) (Qq_h _ 1 one1)
  -- E' = 0, through t : V_{E'} → V_E
  have hE' : Qq (-1) (Vm v) = 0 := by
    have hz : ∀ L, Qq (-1) (Vm v) (lz L) = -Qq (-1) (Vm v) L := Qq_z _ hmz (-1)
    have hh : ∀ L, Qq (-1) (Vm v) (lh L) = -1 * Qq (-1) (Vm v) L := Qq_h _ (-1) neg1
    have h0 : Qq (-1) (Vm v) ∘ lt = 0 := by
      apply E_zero (E_comp (Qq_mem hm (-1)) lt M_comm_lt)
      · intro L; simp only [Function.comp]; rw [lt_lz L, hz]; ring
      · intro L; simp only [Function.comp]; rw [lt_lh L, hz, hh]; ring
    funext L
    have := congrFun h0 (lt L)
    simp only [Function.comp, lt_invol L, Pi.zero_apply] at this
    exact this
  -- B₁
  obtain ⟨hpal, hsum, hB1⟩ := B1_form (by omega) (Pp_mem hp (-1) 1)
    (Pp_t _ (-1) 1 neg1) (Pp_h _ hpz (-1) 1 one1)
  -- B₂
  obtain ⟨hB2e, hB2o⟩ := B2_form hn (Pp_mem hp 1 (-1)) (Pp_t _ 1 (-1) one1)
    (Pp_h _ hpz 1 (-1) neg1)
  refine ⟨fun i => rr (Pp (-1) 1 (Vp v)) i, hpal, hsum, ?_⟩
  rcases Nat.mod_two_eq_zero_or_one n with hpar | hpar
  · refine ⟨0, fun _ => rfl, ?_⟩
    conv_lhs => rw [decomp v]
    rw [hA1, hW, hE, hE', hB2e hpar, ← hB1, zero_smul]
    simp
  · refine ⟨-dd (Pp 1 (-1) (Vp v)) 2, fun h => by omega, ?_⟩
    conv_lhs => rw [decomp v]
    rw [hA1, hW, hE, hE', ← hB2o hpar, ← hB1]
    simp

/-! ### The kernel, lower bound -/

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- Signs are inherited by `M u - c u`. -/
lemma sign_M {u : Line n → K} {π : Line n → Line n} {s : K} (h : ∀ L, u (π L) = s * u L)
    (hc : M K n *ᵥ (u ∘ π) = (M K n *ᵥ u) ∘ π) (c : K) :
    ∀ L, (M K n *ᵥ u - c • u) (π L) = s * (M K n *ᵥ u - c • u) L := by
  have hu : u ∘ π = s • u := funext h
  intro L
  have := congrFun hc L
  rw [hu, mulVec_smul] at this
  simp only [Function.comp, Pi.smul_apply, smul_eq_mul] at this
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, h, ← this]
  ring

omit [LinearOrder K] [IsStrictOrderedRing K] in
lemma rr_vecB1 (r : Fin n → K) (i : ℕ) (hi : i < n) : rr (vecB1 r) i = r ⟨i, hi⟩ := by
  rw [rr_of hi]; rfl
omit [LinearOrder K] [IsStrictOrderedRing K] in
lemma cc_vecB1 (r : Fin n → K) (j : ℕ) (hj : j < n) : cc (vecB1 r) j = -r ⟨j, hj⟩ := by
  rw [cc_of hj]; rfl
omit [LinearOrder K] [IsStrictOrderedRing K] in
lemma dd_vecB1 (r : Fin n → K) (k : ℤ) : dd (vecB1 r) k = 0 := by
  unfold dd; split_ifs <;> rfl
omit [LinearOrder K] [IsStrictOrderedRing K] in
lemma aa_vecB1 (r : Fin n → K) (k : ℤ) : aa (vecB1 r) k = 0 := by
  unfold aa; split_ifs <;> rfl

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- `(r, -r, 0, 0)` with `r` palindromic and `∑ r = 0` lies in the kernel (Lemma 6). -/
theorem vecB1_mem [CharZero K] (r : Fin n → K) (hr : ∀ i, r i.rev = r i) (hs : ∑ i, r i = 0) :
    vecB1 r ∈ E K n := by
  rw [mem_E, ← sub_eq_zero]
  have hT : ∀ L, vecB1 r (lt L) = -1 * vecB1 r L := by
    intro L; rcases L with i | j | k | s <;> simp [vecB1, lt]
  have hH : ∀ L, vecB1 r (lh L) = 1 * vecB1 r L := by
    intro L; rcases L with i | j | k | s <;> simp [vecB1, lh, hr]
  have wT := sign_M hT (M_comm_lt (vecB1 r)) (n : K)
  have wH := sign_M hH (M_comm_lh (vecB1 r)) (n : K)
  obtain ⟨tc, -, ta⟩ := T_coords wT
  obtain ⟨-, -, ha⟩ := H_coords wH
  simp only [one_mul, neg_one_mul] at tc ta ha
  have ha0 : ∀ k, aa (M K n *ᵥ vecB1 r - (n : K) • vecB1 r) k = 0 :=
    fun k => two_mul_eq_zero (ta k)
  have hd0 : ∀ k, dd (M K n *ᵥ vecB1 r - (n : K) • vecB1 r) k = 0 :=
    fun k => by rw [← ha, ha0]
  have hcs : ∑ j ∈ range n, cc (vecB1 r) j = 0 := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => cc (vecB1 r) j) n]
    rw [sum_congr rfl (fun (j : Fin n) _ => (cc_vecB1 r j j.2 : cc (vecB1 r) j = -r j))]
    rw [sum_neg_distrib, hs, neg_zero]
  have hr0 : ∀ i, i < n → rr (M K n *ᵥ vecB1 r - (n : K) • vecB1 r) i = 0 := by
    intro i hi
    rw [rr_of hi]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [M_mulVec_row (vecB1 r) i hi]
    simp only [dd_vecB1, aa_vecB1, add_zero]
    rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul, hcs, rr_vecB1 r i hi]
    simp only [vecB1]
    ring
  exact eq_zero_of_coords hr0 (fun j hj => by rw [tc j hj, hr0 j hj, neg_zero]) hd0 ha0

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- `k d°_k + T_{n-1-k}(d°) = 0` for odd `n` (the converse part of Lemma 12(b)). -/
lemma dcirc_eq [CharZero K] (hodd : n % 2 = 1) (k : ℕ) (hk : k < n) :
    (k : K) * dcirc K n k + TT (dcirc K n) ((n : ℤ) - 1 - k) = 0 := by
  have hp : ((n : ℤ) - 1 - k + 1).toNat = n - k := by omega
  unfold TT dcirc
  rw [hp, sum_sub_distrib]
  rcases Nat.mod_two_eq_zero_or_one k with hk2 | hk2
  · have h1 : ∑ j ∈ range (n - k),
        (if 2 * (j : ℤ) - ((n : ℤ) - 1 - k) = 0 then (n : K) else 0) = n := by
      rw [sum_eq_single ((n - 1 - k) / 2)]
      · rw [if_pos (by omega)]
      · intro j _ hj; rw [if_neg (by omega)]
      · intro h; simp at h; omega
    have h2 : ∑ j ∈ range (n - k),
        (if (2 * (j : ℤ) - ((n : ℤ) - 1 - k)) % 2 = 0 then (1 : K) else 0) = ((n - k : ℕ) : K) := by
      rw [sum_congr rfl (fun j _ => if_pos (by omega))]; simp
    rw [h1, h2]
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp
    · rw [if_neg (by omega), if_pos (by omega)]; push_cast [Nat.cast_sub hk.le]; ring
  · have h1 : ∑ j ∈ range (n - k),
        (if 2 * (j : ℤ) - ((n : ℤ) - 1 - k) = 0 then (n : K) else 0) = 0 :=
      sum_eq_zero (fun j _ => if_neg (by omega))
    have h2 : ∑ j ∈ range (n - k),
        (if (2 * (j : ℤ) - ((n : ℤ) - 1 - k)) % 2 = 0 then (1 : K) else 0) = 0 :=
      sum_eq_zero (fun j _ => if_neg (by omega))
    rw [h1, h2, if_neg (by omega), if_neg (by omega)]; ring

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- `(0, 0, d°, -d°)` lies in the kernel for odd `n` (Lemma 12(b)). -/
theorem vecB2_mem [CharZero K] (hodd : n % 2 = 1) : vecB2 K n ∈ E K n := by
  rw [mem_E, ← sub_eq_zero]
  have hT : ∀ L, vecB2 K n (lt L) = 1 * vecB2 K n L := by
    intro L; rcases L with i | j | k | s <;> simp [vecB2, lt, negDI, dcirc_neg]
  have hH : ∀ L, vecB2 K n (lh L) = -1 * vecB2 K n L := by
    intro L; rcases L with i | j | k | s <;> simp [vecB2, lh]
  have wT := sign_M hT (M_comm_lt (vecB2 K n)) (n : K)
  have wH := sign_M hH (M_comm_lh (vecB2 K n)) (n : K)
  obtain ⟨tc, td, -⟩ := T_coords wT
  obtain ⟨hr, -, ha⟩ := H_coords wH
  simp only [one_mul, neg_one_mul] at tc td hr ha
  have hr0 : ∀ i, i < n → rr (M K n *ᵥ vecB2 K n - (n : K) • vecB2 K n) i = 0 :=
    fun i hi => two_mul_eq_zero (hr i hi)
  have hc0 : ∀ j, j < n → cc (M K n *ᵥ vecB2 K n - (n : K) • vecB2 K n) j = 0 :=
    fun j hj => by rw [tc j hj, hr0 j hj]
  have hdu : ∀ x, x ∈ DI n → dd (vecB2 K n) x = dcirc K n x := fun x hx => by rw [dd_of hx]; rfl
  have hau : ∀ x, aa (vecB2 K n) x = -dd (vecB2 K n) x := by
    intro x; by_cases hx : x ∈ DI n
    · rw [aa_of hx, dd_of hx]; rfl
    · simp [aa, dd, hx]
  have hdn : ∀ k : ℕ, k < n → dd (M K n *ᵥ vecB2 K n - (n : K) • vecB2 K n) k = 0 := by
    intro k hk
    have hk' : (k : ℤ) ∈ DI n := by rw [mem_DI]; omega
    rw [dd_of hk']
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [M_mulVec_diag (vecB2 K n) k hk',
      diag_expand n (rr (vecB2 K n)) (cc (vecB2 K n)) (dd (vecB2 K n)) (aa (vecB2 K n)) k hk]
    have e1 : rho n (rr (vecB2 K n)) k = 0 := sum_eq_zero (fun j _ => by
      unfold rr; split_ifs <;> rfl)
    have e2 : ∑ j ∈ range (n - k), cc (vecB2 K n) j = 0 := sum_eq_zero (fun j _ => by
      unfold cc; split_ifs <;> rfl)
    have e3 : TT (aa (vecB2 K n)) ((n : ℤ) - 1 - k) = -TT (dcirc K n) ((n : ℤ) - 1 - k) := by
      unfold TT
      rw [← sum_neg_distrib]
      apply sum_congr rfl
      intro j hj
      simp at hj
      rw [hau, hdu _ (by rw [mem_DI]; omega)]
    have e4 : vecB2 K n (Sum.inr (Sum.inr (Sum.inl ⟨k, hk'⟩))) = dcirc K n k := rfl
    rw [e1, e2, e3, e4, hdu _ hk']
    have := dcirc_eq (K := K) hodd k hk
    linear_combination -this
  have hd := dd_zero_of_nat (s := 1) (by simpa using td) hdn
  exact eq_zero_of_coords hr0 hc0 hd (fun k => by rw [ha, hd, neg_zero])

end QueensSpectrum
