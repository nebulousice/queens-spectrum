import Pipeline.QueensSpectrum.Defs

/-!
# Queens spectrum: the involutions `t`, `h`, `z` (Lemma 3 of `PROOF.md`)

`t`, `h`, `z` act on functions on lines by precomposition with the line permutations `lt`, `lh`,
`lz` induced by the board symmetries `τ(i,j) = (j,i)`, `η(i,j) = (i,n-1-j)`,
`ζ(i,j) = (n-1-i,n-1-j)` (table in the proof of Lemma 3(b)).  Lemma 3(b) (`M` commutes with
them) is `M_mulVec_comp`; the relations of Lemma 3(a) used later are `lt_lh`, `lh_lt_lh`,
`lh_lz`, `lt_lz` (as identities between line maps).
-/

namespace QueensSpectrum

open Matrix Finset

variable {K : Type*} [Field K] {n : ℕ}

/-- `k ↦ -k` on diagonal indices. -/
def negDI (k : {k // k ∈ DI n}) : {k // k ∈ DI n} :=
  ⟨-k.1, by have := k.2; rw [mem_DI] at *; omega⟩

/-- Line map of `τ` (transpose): `R_i ↔ C_i`, `D_k ↦ D_{-k}`, `A_s ↦ A_s`. -/
def lt : Line n → Line n
  | Sum.inl i => Sum.inr (Sum.inl i)
  | Sum.inr (Sum.inl j) => Sum.inl j
  | Sum.inr (Sum.inr (Sum.inl k)) => Sum.inr (Sum.inr (Sum.inl (negDI k)))
  | Sum.inr (Sum.inr (Sum.inr s)) => Sum.inr (Sum.inr (Sum.inr s))

/-- Line map of `η` (column reversal): `R_i ↦ R_i`, `C_j ↦ C_{n-1-j}`, `D_k ↔ A_k`. -/
def lh : Line n → Line n
  | Sum.inl i => Sum.inl i
  | Sum.inr (Sum.inl j) => Sum.inr (Sum.inl j.rev)
  | Sum.inr (Sum.inr (Sum.inl k)) => Sum.inr (Sum.inr (Sum.inr k))
  | Sum.inr (Sum.inr (Sum.inr s)) => Sum.inr (Sum.inr (Sum.inl s))

/-- Line map of `ζ` (half turn): `R_i ↦ R_{n-1-i}`, `C_j ↦ C_{n-1-j}`, `D_k ↦ D_{-k}`,
`A_s ↦ A_{-s}`. -/
def lz : Line n → Line n
  | Sum.inl i => Sum.inl i.rev
  | Sum.inr (Sum.inl j) => Sum.inr (Sum.inl j.rev)
  | Sum.inr (Sum.inr (Sum.inl k)) => Sum.inr (Sum.inr (Sum.inl (negDI k)))
  | Sum.inr (Sum.inr (Sum.inr s)) => Sum.inr (Sum.inr (Sum.inr (negDI s)))

/-- `τ`, `η`, `ζ` on squares. -/
def st (x : Fin n × Fin n) : Fin n × Fin n := (x.2, x.1)
def sh (x : Fin n × Fin n) : Fin n × Fin n := (x.1, x.2.rev)
def sz (x : Fin n × Fin n) : Fin n × Fin n := (x.1.rev, x.2.rev)

lemma negDI_negDI (k : {k // k ∈ DI n}) : negDI (negDI k) = k := by
  apply Subtype.ext; simp [negDI]

lemma lt_invol : Function.Involutive (lt (n := n)) := by
  intro L; rcases L with i | j | k | s <;> simp [lt, negDI_negDI]

lemma lh_invol : Function.Involutive (lh (n := n)) := by
  intro L; rcases L with i | j | k | s <;> simp [lh]

lemma lz_invol : Function.Involutive (lz (n := n)) := by
  intro L; rcases L with i | j | k | s <;> simp [lz, negDI_negDI]

lemma st_invol : Function.Involutive (st (n := n)) := fun _ => rfl
lemma sh_invol : Function.Involutive (sh (n := n)) := fun x => by simp [sh]
lemma sz_invol : Function.Involutive (sz (n := n)) := fun x => by simp [sz]

/-- Relations among the line maps (Lemma 3(a), pointwise). -/
lemma lt_lh (L : Line n) : lt (lh L) = lz (lh (lt L)) := by
  rcases L with i | j | k | s <;> simp [lt, lh, lz, negDI_negDI]

lemma lh_lt_lh (L : Line n) : lh (lt (lh L)) = lz (lt L) := by
  rcases L with i | j | k | s <;> simp [lt, lh, lz, negDI_negDI]

lemma lh_lz (L : Line n) : lh (lz L) = lz (lh L) := by
  rcases L with i | j | k | s <;> simp [lh, lz]

lemma lt_lz (L : Line n) : lt (lz L) = lz (lt L) := by
  rcases L with i | j | k | s <;> simp [lt, lz]

/-- The incidence matrix is invariant: `N (σ x) (π L) = N x L`. -/
lemma N_st (x : Fin n × Fin n) (L : Line n) : N K n (st x) (lt L) = N K n x L := by
  rcases L with i | j | k | s <;> simp only [N, st, lt, negDI] <;>
    first | rfl | (apply if_congr _ rfl rfl; (try simp only [Fin.ext_iff, Fin.val_rev]); constructor <;> intro h <;> omega)

lemma N_sh (x : Fin n × Fin n) (L : Line n) : N K n (sh x) (lh L) = N K n x L := by
  rcases L with i | j | k | s <;> simp only [N, sh, lh] <;>
    first | rfl | (apply if_congr _ rfl rfl; (try simp only [Fin.ext_iff, Fin.val_rev]); constructor <;> intro h <;> omega)

lemma N_sz (x : Fin n × Fin n) (L : Line n) : N K n (sz x) (lz L) = N K n x L := by
  rcases L with i | j | k | s <;> simp only [N, sz, lz, negDI] <;>
    first | rfl | (apply if_congr _ rfl rfl; (try simp only [Fin.ext_iff, Fin.val_rev]); constructor <;> intro h <;> omega)

/-- **Lemma 3(b).** If a permutation of the squares maps lines to lines, the induced action on
functions on lines commutes with `M`. -/
lemma M_mulVec_comp (σ : Fin n × Fin n → Fin n × Fin n) (hσ : Function.Involutive σ)
    (π : Line n → Line n) (hπ : Function.Involutive π)
    (hN : ∀ x L, N K n (σ x) (π L) = N K n x L) (v : Line n → K) :
    M K n *ᵥ (v ∘ π) = (M K n *ᵥ v) ∘ π := by
  have h1 : N K n *ᵥ (v ∘ π) = (N K n *ᵥ v) ∘ σ := by
    funext x
    simp only [mulVec, dotProduct, Function.comp]
    rw [← Equiv.sum_comp (hπ.toPerm π) (fun L => N K n (σ x) L * v L)]
    apply sum_congr rfl
    intro L _
    simp only [Function.Involutive.coe_toPerm, hN]
  rw [M, ← mulVec_mulVec, h1, ← mulVec_mulVec]
  funext L
  simp only [mulVec, dotProduct, transpose_apply, Function.comp]
  rw [← Equiv.sum_comp (hσ.toPerm σ)]
  apply sum_congr rfl
  intro x _
  simp only [Function.Involutive.coe_toPerm, hσ x]
  rw [← hN x (π L), hπ L]

lemma M_comm_lt (v : Line n → K) : M K n *ᵥ (v ∘ lt) = (M K n *ᵥ v) ∘ lt :=
  M_mulVec_comp st st_invol lt lt_invol N_st v
lemma M_comm_lh (v : Line n → K) : M K n *ᵥ (v ∘ lh) = (M K n *ᵥ v) ∘ lh :=
  M_mulVec_comp sh sh_invol lh lh_invol N_sh v
lemma M_comm_lz (v : Line n → K) : M K n *ᵥ (v ∘ lz) = (M K n *ᵥ v) ∘ lz :=
  M_mulVec_comp sz sz_invol lz lz_invol N_sz v

/-! ### Coordinates of vectors with prescribed signs under `t`, `h`, `z` -/

lemma rr_of {v : Line n → K} {i : ℕ} (hi : i < n) : rr v i = v (Sum.inl ⟨i, hi⟩) := by
  simp [rr, hi]
lemma cc_of {v : Line n → K} {j : ℕ} (hj : j < n) : cc v j = v (Sum.inr (Sum.inl ⟨j, hj⟩)) := by
  simp [cc, hj]
lemma dd_of {v : Line n → K} {k : ℤ} (hk : k ∈ DI n) :
    dd v k = v (Sum.inr (Sum.inr (Sum.inl ⟨k, hk⟩))) := by
  simp [dd, hk]
lemma aa_of {v : Line n → K} {k : ℤ} (hk : k ∈ DI n) :
    aa v k = v (Sum.inr (Sum.inr (Sum.inr ⟨k, hk⟩))) := by
  simp [aa, hk]

lemma neg_mem_DI {k : ℤ} : -k ∈ DI n ↔ k ∈ DI n := by
  simp only [mem_DI]; omega

lemma T_coords {u : Line n → K} {s : K} (h : ∀ L, u (lt L) = s * u L) :
    (∀ j, j < n → cc u j = s * rr u j) ∧ (∀ k, dd u (-k) = s * dd u k) ∧
      (∀ x, aa u x = s * aa u x) := by
  refine ⟨fun j hj => ?_, fun k => ?_, fun x => ?_⟩
  · rw [cc_of hj, rr_of hj]; exact h (Sum.inl ⟨j, hj⟩)
  · by_cases hk : k ∈ DI n
    · rw [dd_of hk, dd_of (neg_mem_DI.mpr hk)]; exact h (Sum.inr (Sum.inr (Sum.inl ⟨k, hk⟩)))
    · have hk' : -k ∉ DI n := fun h' => hk (neg_mem_DI.mp h')
      simp [dd, hk, hk']
  · by_cases hx : x ∈ DI n
    · rw [aa_of hx]; exact h (Sum.inr (Sum.inr (Sum.inr ⟨x, hx⟩)))
    · simp [aa, hx]

lemma H_coords {u : Line n → K} {s : K} (h : ∀ L, u (lh L) = s * u L) :
    (∀ i, i < n → rr u i = s * rr u i) ∧ (∀ j, j < n → cc u (n - 1 - j) = s * cc u j) ∧
      (∀ k, aa u k = s * dd u k) := by
  refine ⟨fun i hi => ?_, fun j hj => ?_, fun k => ?_⟩
  · rw [rr_of hi]; exact h (Sum.inl ⟨i, hi⟩)
  · rw [cc_of hj, cc_of (by omega)]
    have := h (Sum.inr (Sum.inl ⟨j, hj⟩))
    simp only [lh] at this
    have e : (⟨n - 1 - j, by omega⟩ : Fin n) = Fin.rev ⟨j, hj⟩ := by
      ext; simp [Fin.val_rev]; omega
    rw [e]; exact this
  · by_cases hk : k ∈ DI n
    · rw [aa_of hk, dd_of hk]; exact h (Sum.inr (Sum.inr (Sum.inl ⟨k, hk⟩)))
    · simp [aa, dd, hk]

lemma Z_coords {u : Line n → K} {s : K} (h : ∀ L, u (lz L) = s * u L) :
    (∀ i, i < n → rr u (n - 1 - i) = s * rr u i) ∧
      (∀ j, j < n → cc u (n - 1 - j) = s * cc u j) ∧ (∀ k, dd u (-k) = s * dd u k) := by
  refine ⟨fun i hi => ?_, fun j hj => ?_, fun k => ?_⟩
  · rw [rr_of hi, rr_of (by omega)]
    have := h (Sum.inl ⟨i, hi⟩)
    simp only [lz] at this
    have e : (⟨n - 1 - i, by omega⟩ : Fin n) = Fin.rev ⟨i, hi⟩ := by
      ext; simp [Fin.val_rev]; omega
    rw [e]; exact this
  · rw [cc_of hj, cc_of (by omega)]
    have := h (Sum.inr (Sum.inl ⟨j, hj⟩))
    simp only [lz] at this
    have e : (⟨n - 1 - j, by omega⟩ : Fin n) = Fin.rev ⟨j, hj⟩ := by
      ext; simp [Fin.val_rev]; omega
    rw [e]; exact this
  · by_cases hk : k ∈ DI n
    · rw [dd_of hk, dd_of (neg_mem_DI.mpr hk)]; exact h (Sum.inr (Sum.inr (Sum.inl ⟨k, hk⟩)))
    · have hk' : -k ∉ DI n := fun h' => hk (neg_mem_DI.mp h')
      simp [dd, hk, hk']

/-- A function on lines vanishes if all its coordinates vanish. -/
lemma eq_zero_of_coords {u : Line n → K} (h1 : ∀ i, i < n → rr u i = 0)
    (h2 : ∀ j, j < n → cc u j = 0) (h3 : ∀ k, dd u k = 0) (h4 : ∀ k, aa u k = 0) : u = 0 := by
  funext L
  rcases L with i | j | k | s
  · have := h1 i i.2; rwa [rr_of i.2] at this
  · have := h2 j j.2; rwa [cc_of j.2] at this
  · have := h3 k.1; rwa [dd_of k.2] at this
  · have := h4 s.1; rwa [aa_of s.2] at this

/-- The row and diagonal equations (Lemma 5) of a vector `u` with `M u = n u`. -/
lemma ker_eqs {u : Line n → K} (hu : M K n *ᵥ u = (n : K) • u) :
    (∀ i, i < n → ∑ j ∈ range n, (rr u i + cc u j + dd u ((i : ℤ) - j) +
        aa u ((i : ℤ) + j - (n - 1))) = n * rr u i) ∧
      (∀ k, k < n → ∑ j ∈ range (n - k), (rr u (j + k) + cc u j + dd u k +
        aa u (2 * (j : ℤ) + k - (n - 1))) = n * dd u k) := by
  refine ⟨fun i hi => ?_, fun k hk => ?_⟩
  · rw [← M_mulVec_row u i hi, hu, rr_of hi]; rfl
  · have hk' : (k : ℤ) ∈ DI n := by rw [mem_DI]; omega
    rw [← M_mulVec_diag u k hk', hu, dd_of hk']; rfl

end QueensSpectrum
