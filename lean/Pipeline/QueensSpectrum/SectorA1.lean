import Pipeline.QueensSpectrum.SectorE

/-!
# Queens spectrum: sector `A₁` (Lemmas 8 and 9 of `PROOF.md`), as a statement about sequences

Shape of `V_{A1}` ((3.1)): `c = r` palindromic, `a = d` even.  Lemma 8 (the window identity) is
used in the equivalent form "`U_k = T_{n-1-k} + T_{k-1}` depends only on the parity of `k`"
(`hUstep`), proved from `T_{p+2} = T_p + 2 d_{p+2}` and `d_{n-k} = d_k`; the values of `U_k`
needed in the two cases are then computed directly.  The final linear systems are those of
`PROOF.md` §6 (determinants `-3` and `-10n`).
-/

namespace QueensSpectrum

open Finset

variable {K : Type*} [Field K]

lemma D_natAbs {D : ℤ → K} (hD : ∀ k, D (-k) = D k) (x : ℤ) : D x = D (x.natAbs : ℤ) := by
  rcases Int.natAbs_eq x with h | h
  · exact congrArg D h
  · rw [← hD]; exact congrArg D (by linarith)

lemma TT_eq_single (D : ℤ → K) (p : ℤ) (q : ℕ) (hq : 2 * (q : ℤ) = p)
    (h : ∀ j : ℕ, j < (p + 1).toNat → j ≠ q → D (2 * (j : ℤ) - p) = 0) : TT D p = D 0 := by
  unfold TT
  rw [sum_eq_single q]
  · congr 1; omega
  · intro j hj hjq; exact h j (by simpa using hj) hjq
  · intro hq'; simp at hq'; omega

lemma TT_const (D : ℤ → K) (p : ℤ) (β : K)
    (h : ∀ j : ℕ, j < (p + 1).toNat → D (2 * (j : ℤ) - p) = β) :
    TT D p = ((p + 1).toNat : K) * β := by
  unfold TT
  rw [sum_congr rfl (fun j hj => h j (by simpa using hj))]
  simp

/-- `∑_{j<2m'} D_j = D_0 + m' D_1` when `D` vanishes at even `k ≥ 2` and is constant at odd `k`. -/
lemma sum_even_odd (D : ℤ → K) (m : ℕ)
    (hev : ∀ k : ℕ, 1 ≤ k → k < 2 * m → k % 2 = 0 → D k = 0)
    (hod : ∀ k : ℕ, k < 2 * m → k % 2 = 1 → D k = D 1) :
    ∀ m', 1 ≤ m' → m' ≤ m → ∑ j ∈ range (2 * m'), D j = D 0 + m' * D 1 := by
  intro m' h1
  induction m', h1 using Nat.le_induction with
  | base => intro _; simp [sum_range_succ]
  | succ m' hm' ih =>
    intro hle
    rw [show 2 * (m' + 1) = 2 * m' + 1 + 1 by ring, sum_range_succ, sum_range_succ,
      ih (by omega)]
    have e1 := hev (2 * m') (by omega) (by omega) (by omega)
    have e2 := hod (2 * m' + 1) (by omega) (by omega)
    push_cast at e1 e2 ⊢
    rw [e1, e2]; ring

/-- **Lemma 9 (sector `A₁`).** The only solution is zero. -/
theorem sectorA1_pure [CharZero K] (n : ℕ) (hn : 4 ≤ n) (r c : ℕ → K) (D A : ℤ → K)
    (hr : ∀ i, i < n → r (n - 1 - i) = r i) (hc : ∀ j, j < n → c j = r j)
    (hD : ∀ k, D (-k) = D k) (hA : ∀ s, A s = D s)
    (hrow : ∀ i, i < n →
      ∑ j ∈ range n, (r i + c j + D ((i : ℤ) - j) + A ((i : ℤ) + j - (n - 1))) = n * r i)
    (hdiag : ∀ k, k < n →
      ∑ j ∈ range (n - k), (r (j + k) + c j + D k + A (2 * (j : ℤ) + k - (n - 1))) =
        n * D k) :
    (∀ i, i < n → r i = 0) ∧ (∀ k : ℕ, k < n → D k = 0) := by
  obtain ⟨S, hS⟩ : ∃ S, S = ∑ j ∈ range n, r j := ⟨_, rfl⟩
  have hn0 : (n : K) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hAD : A = D := funext hA
  subst hAD
  have hsc : ∀ m, m ≤ n → ∑ j ∈ range m, c j = ∑ j ∈ range m, r j :=
    fun m hm => sum_congr rfl (fun j hj => hc j (by simp at hj; omega))
  -- (row_i): S + 2 W(i) = 0
  have hW : ∀ i : ℕ, i < n → S + 2 * ∑ j ∈ range n, A ((i : ℤ) - j) = 0 := by
    intro i hi
    have h := hrow i hi
    rw [row_expand, reflect_window, hsc n le_rfl, ← hS] at h
    linear_combination h
  -- (A.1): d_{n-i} = d_i
  have hsym : ∀ i : ℕ, 1 ≤ i → i < n → A i = A ((n : ℤ) - i) := by
    intro i h1 h2
    have e := window_step n A i
    have w1 := hW i h2
    have w2 := hW (i - 1) (by omega)
    rw [show ((i - 1 : ℕ) : ℤ) = (i : ℤ) - 1 by omega] at w2
    rw [← hD ((n : ℤ) - i), show -((n : ℤ) - i) = (i : ℤ) - n by ring]
    linear_combination -e + (w1 - w2) / 2
  -- (A.2)
  have hA2 : S + 2 * ∑ j ∈ range n, A j = 0 := by
    have := hW 0 (by omega)
    simp only [Nat.cast_zero, zero_sub, hD] at this
    exact this
  -- (diag_k) with (A.3): 2 ρ_k + T_{n-1-k} = k d_k
  have hdg : ∀ k, k < n → 2 * rho n r k + TT A ((n : ℤ) - 1 - k) = k * A k := by
    intro k hk
    have h := hdiag k hk
    rw [diag_expand n r c A A k hk, hsc (n - k) (by omega), sigma_palin n r hr k hk.le] at h
    linear_combination h
  have hsplit : ∀ k, k ≤ n → rho n r k + rho n r (n - k) = S := by
    intro k hk
    have h1 := sum_split n r k hk
    have h2 := sigma_palin n r hr (n - k) (by omega)
    rw [show n - (n - k) = k by omega] at h2
    rw [h2, ← hS] at h1
    linear_combination h1
  -- U_k = T_{n-1-k} + T_{k-1}
  let U : ℕ → K := fun k => TT A ((n : ℤ) - 1 - k) + TT A ((k : ℤ) - 1)
  -- (A.4)
  have hA4 : ∀ k, 1 ≤ k → k < n → (n : K) * A k = 2 * S + U k := by
    intro k h1 h2
    have e1 := hdg k h2
    have e2 := hdg (n - k) (by omega)
    have e3 := hsplit k h2.le
    have e4 := hsym k h1 h2
    push_cast [Nat.cast_sub h2.le] at e2
    rw [show (n : ℤ) - 1 - ((n : ℤ) - k) = (k : ℤ) - 1 by ring] at e2
    show (n : K) * A k = 2 * S + (TT A ((n : ℤ) - 1 - k) + TT A ((k : ℤ) - 1))
    linear_combination -(e1 + e2 - 2 * e3) + ((n : K) - k) * e4
  -- (A.5)
  have hA5 : 2 * S + TT A ((n : ℤ) - 1) = 0 := by
    have e := hdg 0 (by omega)
    have : rho n r 0 = S := by rw [hS]; simp [rho]
    rw [this] at e
    simpa using e
  -- the window identity (Lemma 8), in recurrence form
  have hUstep : ∀ k : ℕ, k + 2 ≤ n - 1 → U (k + 2) = U k := by
    intro k hk
    have t1 : TT A ((n : ℤ) - 1 - k) =
        TT A ((n : ℤ) - 1 - ((k : ℤ) + 2)) + 2 * A ((n : ℤ) - 1 - k) := by
      have := TT_step hD ((n : ℤ) - 1 - ((k : ℤ) + 2)) (by omega)
      rwa [show (n : ℤ) - 1 - ((k : ℤ) + 2) + 2 = (n : ℤ) - 1 - k by ring] at this
    have t2 : TT A ((k : ℤ) + 2 - 1) = TT A ((k : ℤ) - 1) + 2 * A ((n : ℤ) - 1 - k) := by
      have := TT_step hD ((k : ℤ) - 1) (by omega)
      have e := hsym (k + 1) (by omega) (by omega)
      push_cast at e
      rw [show (k : ℤ) - 1 + 2 = (k : ℤ) + 2 - 1 by ring] at this
      rw [this, show (k : ℤ) + 2 - 1 = (k : ℤ) + 1 by ring, e,
        show (n : ℤ) - ((k : ℤ) + 1) = (n : ℤ) - 1 - k by ring]
    show TT A ((n : ℤ) - 1 - ((k + 2 : ℕ) : ℤ)) + TT A (((k + 2 : ℕ) : ℤ) - 1) =
      TT A ((n : ℤ) - 1 - k) + TT A ((k : ℤ) - 1)
    push_cast
    rw [t1, t2]; ring
  have hUpar : ∀ m k : ℕ, k + 2 * m ≤ n - 1 → U (k + 2 * m) = U k := by
    intro m
    induction m with
    | zero => intro k _; simp
    | succ m ih =>
      intro k hk
      rw [show k + 2 * (m + 1) = (k + 2 * m) + 2 by ring, hUstep _ (by omega), ih k (by omega)]
  have hU0 : U 0 = TT A ((n : ℤ) - 1) := by
    show TT A ((n : ℤ) - 1 - ((0 : ℕ) : ℤ)) + TT A (((0 : ℕ) : ℤ) - 1) = _
    simp [TT_neg_one]
  have hU1 : U 1 = TT A ((n : ℤ) - 2) + A 0 := by
    show TT A ((n : ℤ) - 1 - ((1 : ℕ) : ℤ)) + TT A (((1 : ℕ) : ℤ) - 1) = _
    rw [show (n : ℤ) - 1 - ((1 : ℕ) : ℤ) = (n : ℤ) - 2 by push_cast; ring,
      show ((1 : ℕ) : ℤ) - 1 = 0 by norm_num, TT_zero]
  have hUlast : U (n - 1) = U 1 := by
    show TT A ((n : ℤ) - 1 - ((n - 1 : ℕ) : ℤ)) + TT A (((n - 1 : ℕ) : ℤ) - 1) =
      TT A ((n : ℤ) - 1 - ((1 : ℕ) : ℤ)) + TT A (((1 : ℕ) : ℤ) - 1)
    rw [add_comm]
    congr 2 <;> omega
  have hUev : ∀ k, k < n → k % 2 = 0 → U k = U 0 := by
    intro k hk hpar
    have := hUpar (k / 2) 0 (by omega)
    rwa [show 0 + 2 * (k / 2) = k by omega] at this
  have hUod : ∀ k, k < n → k % 2 = 1 → U k = U 1 := by
    intro k hk hpar
    have := hUpar (k / 2) 1 (by omega)
    rwa [show 1 + 2 * (k / 2) = k by omega] at this
  -- the two cases
  have hDall : ∀ k : ℕ, k < n → A k = 0 := by
    obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' n
    · -- n even
      have hDev : ∀ k : ℕ, 1 ≤ k → k < n → k % 2 = 0 → A k = 0 := by
        intro k h1 h2 hpar
        have e := hA4 k h1 h2
        rw [hUev k h2 hpar, hU0, hA5] at e
        exact (mul_eq_zero.mp e).resolve_left hn0
      have hDod : ∀ k : ℕ, k < n → k % 2 = 1 → A k = A 1 := by
        intro k h2 hpar
        have e := hA4 k (by omega) h2
        have e1 := hA4 1 le_rfl (by omega)
        rw [hUod k h2 hpar] at e
        push_cast at e1
        have : (n : K) * (A k - A 1) = 0 := by linear_combination e - e1
        have := (mul_eq_zero.mp this).resolve_left hn0
        linear_combination this
      have hz0 : ∀ x : ℤ, x ≠ 0 → -(n : ℤ) < x → x < n → x % 2 = 0 → A x = 0 := by
        intro x h0 h1 h2 hpar
        rw [D_natAbs hD x]; exact hDev _ (by omega) (by omega) (by omega)
      have hz1 : ∀ x : ℤ, -(n : ℤ) < x → x < n → x % 2 = 1 → A x = A 1 := by
        intro x h1 h2 hpar
        rw [D_natAbs hD x]; exact hDod _ (by omega) (by omega)
      have hT2 : TT A ((n : ℤ) - 2) = A 0 := by
        apply TT_eq_single A _ (m - 1) (by omega)
        intro j hj hjq
        exact hz0 _ (by omega) (by omega) (by omega) (by omega)
      have hT1 : TT A ((n : ℤ) - 1) = n * A 1 := by
        rw [TT_const A _ (A 1) (fun j hj => hz1 _ (by omega) (by omega) (by omega))]
        congr 1
        rw [show ((n : ℤ) - 1 + 1).toNat = n by omega]
      have hDs : ∑ j ∈ range n, A j = A 0 + m * A 1 := by
        rw [hm]
        apply sum_even_odd A m (fun k h1 h2 h3 => hDev k h1 (by omega) h3)
          (fun k h2 h3 => hDod k (by omega) h3) m (by omega) le_rfl
      have e1 := hA4 1 le_rfl (by omega)
      rw [hU1, hT2] at e1
      push_cast at e1
      rw [hT1] at hA5
      rw [hDs] at hA2
      have hnm : (n : K) = 2 * m := by rw [hm]; push_cast; ring
      rw [hnm] at e1 hA5
      -- e1 : 2m D1 = 2S + (D0 + D0);  hA5 : 2S + 2m D1 = 0;  hA2 : S + 2 (D0 + m D1) = 0
      have hS0 : S = 0 := by linear_combination (-e1 + 2 * hA5 - hA2) / 5
      have hD0 : A 0 = 0 := by linear_combination (-e1 - 3 * hA5 + 4 * hA2) / 10
      have hx : (n : K) * A 1 = 0 := by rw [hnm]; linear_combination (2 * e1 + hA5 + 2 * hA2) / 5
      have hD1 : A 1 = 0 := (mul_eq_zero.mp hx).resolve_left hn0
      intro k hk
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · simpa using hD0
      rcases Nat.mod_two_eq_zero_or_one k with hpar | hpar
      · exact hDev k hk0 hk hpar
      · rw [hDod k hk hpar, hD1]
    · -- n odd
      have hU1eq : U 1 = U 0 := by
        rw [← hUlast]
        have := hUpar m 0 (by omega)
        rwa [show 0 + 2 * m = n - 1 by omega] at this
      have hDz : ∀ k : ℕ, 1 ≤ k → k < n → A k = 0 := by
        intro k h1 h2
        have e := hA4 k h1 h2
        have hu : U k = U 0 := by
          rcases Nat.mod_two_eq_zero_or_one k with h | h
          · exact hUev k h2 h
          · rw [hUod k h2 h, hU1eq]
        rw [hu, hU0, hA5] at e
        exact (mul_eq_zero.mp e).resolve_left hn0
      have hz : ∀ x : ℤ, x ≠ 0 → -(n : ℤ) < x → x < n → A x = 0 := by
        intro x h0 h1 h2
        rw [D_natAbs hD x]; exact hDz _ (by omega) (by omega)
      have hT : TT A ((n : ℤ) - 1) = A 0 := by
        apply TT_eq_single A _ m (by omega)
        intro j hj hjq
        exact hz _ (by omega) (by omega) (by omega)
      have hDs : ∑ j ∈ range n, A j = A 0 := by
        rw [sum_eq_single 0]
        · simp
        · intro j hj hj0; simp at hj; exact hz _ (by omega) (by omega) (by omega)
        · intro h; simp at h; omega
      rw [hT] at hA5
      rw [hDs] at hA2
      have hD0 : A 0 = 0 := by linear_combination (2 * hA2 - hA5) / 3
      intro k hk
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · simpa using hD0
      · exact hDz k hk0 hk
  -- conclusion: d = 0, hence ρ = 0, hence r = 0
  refine ⟨?_, hDall⟩
  have hz : ∀ x : ℤ, -(n : ℤ) < x → x < n → A x = 0 := by
    intro x h1 h2
    rw [D_natAbs hD x]; exact hDall _ (by omega)
  apply eq_zero_of_rho n r
  intro k hk
  have e := hdg k hk
  have hT : TT A ((n : ℤ) - 1 - k) = 0 := by
    unfold TT
    apply sum_eq_zero
    intro j hj
    simp at hj
    exact hz _ (by omega) (by omega)
  rw [hT, hDall k hk] at e
  have : (2 : K) * rho n r k = 0 := by linear_combination e
  simpa using this

end QueensSpectrum
