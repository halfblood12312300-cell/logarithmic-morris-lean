import logarithmicmorris.ScratchSkew

noncomputable section

open scoped BigOperators

namespace LogarithmicMorrisFull

def pairUnmatched (m : ℕ) : Fin (2 * m + 1) :=
  ⟨2 * m, by omega⟩

theorem pairLeft_ne_unmatched (m : ℕ) (r : Fin m) :
    pairLeft m r ≠ pairUnmatched m := by
  intro h
  have := congrArg Fin.val h
  simp [pairLeft, pairUnmatched] at this
  omega

theorem pairRight_ne_unmatched (m : ℕ) (r : Fin m) :
    pairRight m r ≠ pairUnmatched m := by
  intro h
  have hr := r.isLt
  have := congrArg Fin.val h
  simp [pairRight, pairUnmatched] at this
  omega

def unmatchedSwapLeft (m : ℕ) (r : Fin m) :
    Equiv.Perm (Fin (2 * m + 1)) :=
  Equiv.swap (pairLeft m r) (pairUnmatched m)

def unmatchedSwapRight (m : ℕ) (r : Fin m) :
    Equiv.Perm (Fin (2 * m + 1)) :=
  Equiv.swap (pairRight m r) (pairUnmatched m)

@[simp] theorem unmatchedSwapLeft_sign (m : ℕ) (r : Fin m) :
    (unmatchedSwapLeft m r).sign = -1 := by
  exact Equiv.Perm.sign_swap (pairLeft_ne_unmatched m r)

@[simp] theorem unmatchedSwapRight_sign (m : ℕ) (r : Fin m) :
    (unmatchedSwapRight m r).sign = -1 := by
  exact Equiv.Perm.sign_swap (pairRight_ne_unmatched m r)

@[simp] theorem unmatchedSwapLeft_left (m : ℕ) (r : Fin m) :
    unmatchedSwapLeft m r (pairLeft m r) = pairUnmatched m := by
  simp [unmatchedSwapLeft, pairLeft_ne_unmatched]

@[simp] theorem unmatchedSwapLeft_right (m : ℕ) (r : Fin m) :
    unmatchedSwapLeft m r (pairRight m r) = pairRight m r := by
  exact Equiv.swap_apply_of_ne_of_ne
    (pairLeft_ne_pairRight m r).symm (pairRight_ne_unmatched m r)

@[simp] theorem unmatchedSwapRight_left (m : ℕ) (r : Fin m) :
    unmatchedSwapRight m r (pairLeft m r) = pairLeft m r := by
  exact Equiv.swap_apply_of_ne_of_ne
    (pairLeft_ne_pairRight m r) (pairLeft_ne_unmatched m r)

@[simp] theorem unmatchedSwapRight_right (m : ℕ) (r : Fin m) :
    unmatchedSwapRight m r (pairRight m r) = pairUnmatched m := by
  simp [unmatchedSwapRight, pairRight_ne_unmatched]

@[simp] theorem unmatchedSwapLeft_left_of_ne (m : ℕ) {q r : Fin m}
    (hqr : q ≠ r) :
    unmatchedSwapLeft m r (pairLeft m q) = pairLeft m q := by
  exact Equiv.swap_apply_of_ne_of_ne
    (pairLeft_ne_of_ne m hqr) (pairLeft_ne_unmatched m q)

@[simp] theorem unmatchedSwapLeft_right_of_ne (m : ℕ) {q r : Fin m}
    (hqr : q ≠ r) :
    unmatchedSwapLeft m r (pairRight m q) = pairRight m q := by
  exact Equiv.swap_apply_of_ne_of_ne
    (pairRight_ne_pairLeft_of_ne m hqr) (pairRight_ne_unmatched m q)

@[simp] theorem unmatchedSwapRight_left_of_ne (m : ℕ) {q r : Fin m}
    (hqr : q ≠ r) :
    unmatchedSwapRight m r (pairLeft m q) = pairLeft m q := by
  exact Equiv.swap_apply_of_ne_of_ne
    (pairLeft_ne_pairRight_of_ne m hqr) (pairLeft_ne_unmatched m q)

@[simp] theorem unmatchedSwapRight_right_of_ne (m : ℕ) {q r : Fin m}
    (hqr : q ≠ r) :
    unmatchedSwapRight m r (pairRight m q) = pairRight m q := by
  exact Equiv.swap_apply_of_ne_of_ne
    (pairRight_ne_of_ne m hqr) (pairRight_ne_unmatched m q)

def subsetPairedFactor (m : ℕ)
    (B : Fin (2 * m + 1) → Fin (2 * m + 1) → ℂ)
    (y : Fin (2 * m + 1) → ℂ) (s : Finset (Fin m))
    (σ : Equiv.Perm (Fin (2 * m + 1))) (q : Fin m) : ℂ :=
  if q ∈ s then y (σ (pairRight m q)) - y (σ (pairLeft m q))
  else B (σ (pairLeft m q)) (σ (pairRight m q))

def subsetPairedProduct (m : ℕ)
    (B : Fin (2 * m + 1) → Fin (2 * m + 1) → ℂ)
    (y : Fin (2 * m + 1) → ℂ) (s : Finset (Fin m))
    (σ : Equiv.Perm (Fin (2 * m + 1))) : ℂ :=
  ∏ q : Fin m, subsetPairedFactor m B y s σ q

def subsetPairedAlternatingSum (m : ℕ)
    (B : Fin (2 * m + 1) → Fin (2 * m + 1) → ℂ)
    (y : Fin (2 * m + 1) → ℂ) (s : Finset (Fin m)) : ℂ :=
  ∑ σ : Equiv.Perm (Fin (2 * m + 1)),
    (((σ.sign : ℤ) : ℂ) * subsetPairedProduct m B y s σ)

theorem subsetPairedFactor_swapLeft_of_ne (m : ℕ)
    (B : Fin (2 * m + 1) → Fin (2 * m + 1) → ℂ)
    (y : Fin (2 * m + 1) → ℂ) (s : Finset (Fin m))
    {q r : Fin m} (hqr : q ≠ r)
    (σ : Equiv.Perm (Fin (2 * m + 1))) :
    subsetPairedFactor m B y s (σ * unmatchedSwapLeft m r) q =
      subsetPairedFactor m B y s σ q := by
  simp [subsetPairedFactor, Equiv.Perm.coe_mul, hqr]

theorem subsetPairedFactor_swapRight_of_ne (m : ℕ)
    (B : Fin (2 * m + 1) → Fin (2 * m + 1) → ℂ)
    (y : Fin (2 * m + 1) → ℂ) (s : Finset (Fin m))
    {q r : Fin m} (hqr : q ≠ r)
    (σ : Equiv.Perm (Fin (2 * m + 1))) :
    subsetPairedFactor m B y s (σ * unmatchedSwapRight m r) q =
      subsetPairedFactor m B y s σ q := by
  simp [subsetPairedFactor, Equiv.Perm.coe_mul, hqr]

theorem subsetPaired_signed_three_term (m : ℕ)
    (B : Fin (2 * m + 1) → Fin (2 * m + 1) → ℂ)
    (y : Fin (2 * m + 1) → ℂ) (s : Finset (Fin m))
    {r : Fin m} (hr : r ∈ s)
    (σ : Equiv.Perm (Fin (2 * m + 1))) :
    (((σ.sign : ℤ) : ℂ) * subsetPairedProduct m B y s σ) +
      ((((σ * unmatchedSwapLeft m r).sign : ℤ) : ℂ) *
        subsetPairedProduct m B y s (σ * unmatchedSwapLeft m r)) +
      ((((σ * unmatchedSwapRight m r).sign : ℤ) : ℂ) *
        subsetPairedProduct m B y s (σ * unmatchedSwapRight m r)) = 0 := by
  have hmem : r ∈ (Finset.univ : Finset (Fin m)) := Finset.mem_univ r
  let R : ℂ := ∏ q ∈ (Finset.univ.erase r), subsetPairedFactor m B y s σ q
  have hprod : subsetPairedProduct m B y s σ =
      subsetPairedFactor m B y s σ r * R := by
    exact (Finset.mul_prod_erase Finset.univ
      (subsetPairedFactor m B y s σ) hmem).symm
  have hprodL : subsetPairedProduct m B y s (σ * unmatchedSwapLeft m r) =
      subsetPairedFactor m B y s (σ * unmatchedSwapLeft m r) r * R := by
    rw [subsetPairedProduct, ← Finset.mul_prod_erase Finset.univ
      (subsetPairedFactor m B y s (σ * unmatchedSwapLeft m r)) hmem]
    congr 1
    apply Finset.prod_congr rfl
    intro q hq
    exact subsetPairedFactor_swapLeft_of_ne m B y s
      (Finset.ne_of_mem_erase hq) σ
  have hprodR : subsetPairedProduct m B y s (σ * unmatchedSwapRight m r) =
      subsetPairedFactor m B y s (σ * unmatchedSwapRight m r) r * R := by
    rw [subsetPairedProduct, ← Finset.mul_prod_erase Finset.univ
      (subsetPairedFactor m B y s (σ * unmatchedSwapRight m r)) hmem]
    congr 1
    apply Finset.prod_congr rfl
    intro q hq
    exact subsetPairedFactor_swapRight_of_ne m B y s
      (Finset.ne_of_mem_erase hq) σ
  rw [hprod, hprodL, hprodR]
  simp only [subsetPairedFactor, hr, if_true, Equiv.Perm.sign_mul,
    unmatchedSwapLeft_sign, unmatchedSwapRight_sign,
    Equiv.Perm.coe_mul, Function.comp_apply, unmatchedSwapLeft_left,
    unmatchedSwapLeft_right, unmatchedSwapRight_left,
    unmatchedSwapRight_right]
  push_cast
  ring

theorem subsetPairedAlternatingSum_eq_zero (m : ℕ)
    (B : Fin (2 * m + 1) → Fin (2 * m + 1) → ℂ)
    (y : Fin (2 * m + 1) → ℂ) (s : Finset (Fin m))
    {r : Fin m} (hr : r ∈ s) :
    subsetPairedAlternatingSum m B y s = 0 := by
  unfold subsetPairedAlternatingSum
  have hpoint := subsetPaired_signed_three_term m B y s hr
  have hsum :
      (∑ σ : Equiv.Perm (Fin (2 * m + 1)),
        ((((σ.sign : ℤ) : ℂ) * subsetPairedProduct m B y s σ) +
          ((((σ * unmatchedSwapLeft m r).sign : ℤ) : ℂ) *
            subsetPairedProduct m B y s (σ * unmatchedSwapLeft m r)) +
          ((((σ * unmatchedSwapRight m r).sign : ℤ) : ℂ) *
            subsetPairedProduct m B y s (σ * unmatchedSwapRight m r)))) = 0 := by
    simp_rw [hpoint]
    simp
  simp only [Finset.sum_add_distrib] at hsum
  have hreindexL :
      (∑ σ : Equiv.Perm (Fin (2 * m + 1)),
        ((((σ * unmatchedSwapLeft m r).sign : ℤ) : ℂ) *
          subsetPairedProduct m B y s (σ * unmatchedSwapLeft m r))) =
      ∑ σ : Equiv.Perm (Fin (2 * m + 1)),
        (((σ.sign : ℤ) : ℂ) * subsetPairedProduct m B y s σ) := by
    simpa only [Equiv.coe_mulRight] using
      (Equiv.sum_comp (Equiv.mulRight (unmatchedSwapLeft m r))
        (fun σ : Equiv.Perm (Fin (2 * m + 1)) =>
          (((σ.sign : ℤ) : ℂ) * subsetPairedProduct m B y s σ)))
  have hreindexR :
      (∑ σ : Equiv.Perm (Fin (2 * m + 1)),
        ((((σ * unmatchedSwapRight m r).sign : ℤ) : ℂ) *
          subsetPairedProduct m B y s (σ * unmatchedSwapRight m r))) =
      ∑ σ : Equiv.Perm (Fin (2 * m + 1)),
        (((σ.sign : ℤ) : ℂ) * subsetPairedProduct m B y s σ) := by
    simpa only [Equiv.coe_mulRight] using
      (Equiv.sum_comp (Equiv.mulRight (unmatchedSwapRight m r))
        (fun σ : Equiv.Perm (Fin (2 * m + 1)) =>
          (((σ.sign : ℤ) : ℂ) * subsetPairedProduct m B y s σ)))
  rw [hreindexL, hreindexR] at hsum
  have hthree : (3 : ℂ) *
      (∑ σ : Equiv.Perm (Fin (2 * m + 1)),
        (((σ.sign : ℤ) : ℂ) * subsetPairedProduct m B y s σ)) = 0 := by
    calc
      _ = (∑ σ : Equiv.Perm (Fin (2 * m + 1)),
          (((σ.sign : ℤ) : ℂ) * subsetPairedProduct m B y s σ)) +
          (∑ σ : Equiv.Perm (Fin (2 * m + 1)),
            (((σ.sign : ℤ) : ℂ) * subsetPairedProduct m B y s σ)) +
          (∑ σ : Equiv.Perm (Fin (2 * m + 1)),
            (((σ.sign : ℤ) : ℂ) * subsetPairedProduct m B y s σ)) := by ring
      _ = 0 := hsum
  exact (mul_eq_zero.mp hthree).resolve_left (by norm_num)

theorem subsetPairedProduct_eq (m : ℕ)
    (B : Fin (2 * m + 1) → Fin (2 * m + 1) → ℂ)
    (y : Fin (2 * m + 1) → ℂ) (s : Finset (Fin m))
    (σ : Equiv.Perm (Fin (2 * m + 1))) :
    subsetPairedProduct m B y s σ =
      (∏ q ∈ s, (y (σ (pairRight m q)) - y (σ (pairLeft m q)))) *
      ∏ q ∈ (Finset.univ \ s),
        B (σ (pairLeft m q)) (σ (pairRight m q)) := by
  unfold subsetPairedProduct subsetPairedFactor
  rw [Finset.prod_ite]
  simp only [Finset.filter_mem_eq_inter]
  rw [Finset.univ_inter]
  have hprod :
      (∏ q with q ∉ s, B (σ (pairLeft m q)) (σ (pairRight m q))) =
        ∏ q ∈ Finset.univ \ s,
          B (σ (pairLeft m q)) (σ (pairRight m q)) := by
    apply Finset.prod_congr
    · ext q
      simp
    · intro q hq
      rfl
  rw [hprod]

theorem pairedAlternatingSum_add_coboundary (m : ℕ)
    (B : Fin (2 * m + 1) → Fin (2 * m + 1) → ℂ)
    (y : Fin (2 * m + 1) → ℂ) :
    pairedAlternatingSum m (fun i j => (y j - y i) + B i j) =
      pairedAlternatingSum m B := by
  unfold pairedAlternatingSum
  calc
    (∑ σ : Equiv.Perm (Fin (2 * m + 1)),
        ((σ.sign : ℤ) : ℂ) *
          ∏ r : Fin m,
            ((y (σ (pairRight m r)) - y (σ (pairLeft m r))) +
              B (σ (pairLeft m r)) (σ (pairRight m r)))) =
        ∑ σ : Equiv.Perm (Fin (2 * m + 1)),
          ((σ.sign : ℤ) : ℂ) *
            ∑ s ∈ (Finset.univ : Finset (Fin m)).powerset,
              subsetPairedProduct m B y s σ := by
      apply Finset.sum_congr rfl
      intro σ _
      congr 1
      rw [Finset.prod_add]
      apply Finset.sum_congr rfl
      intro s hs
      exact (subsetPairedProduct_eq m B y s σ).symm
    _ = ∑ s ∈ (Finset.univ : Finset (Fin m)).powerset,
          subsetPairedAlternatingSum m B y s := by
      simp_rw [Finset.mul_sum]
      unfold subsetPairedAlternatingSum
      rw [Finset.sum_comm]
    _ = subsetPairedAlternatingSum m B y ∅ := by
      apply Finset.sum_eq_single ∅
      · intro s hs hne
        obtain ⟨r, hr⟩ := Finset.nonempty_iff_ne_empty.mpr hne
        exact subsetPairedAlternatingSum_eq_zero m B y s hr
      · simp
    _ = ∑ σ : Equiv.Perm (Fin (2 * m + 1)),
          ((σ.sign : ℤ) : ℂ) *
            ∏ r : Fin m, B (σ (pairLeft m r)) (σ (pairRight m r)) := by
      unfold subsetPairedAlternatingSum subsetPairedProduct subsetPairedFactor
      simp

def orderSign {N : ℕ} (i j : Fin N) : ℂ :=
  if i < j then 1 else if j < i then -1 else 0

theorem sawMatrix_eq_coboundary_add_orderSign (m : ℕ) (c : ℂ)
    (y : Fin (2 * m + 1) → ℂ) (i j : Fin (2 * m + 1)) :
    sawMatrix m c y i j = (y j - y i) + c * orderSign i j := by
  rcases lt_trichotomy i j with hij | hij | hij
  · simp [sawMatrix, orderSign, hij, not_lt_of_ge hij.le]
  · subst j
    simp [sawMatrix, orderSign]
  · simp [sawMatrix, orderSign, hij, not_lt_of_ge hij.le]
    ring

theorem pairedAlternatingSum_sawMatrix_reduce (m : ℕ) (c : ℂ)
    (y : Fin (2 * m + 1) → ℂ) :
    pairedAlternatingSum m (sawMatrix m c y) =
      pairedAlternatingSum m (fun i j => c * orderSign i j) := by
  rw [show sawMatrix m c y = fun i j =>
      (y j - y i) + c * orderSign i j by
    funext i j
    exact sawMatrix_eq_coboundary_add_orderSign m c y i j]
  exact pairedAlternatingSum_add_coboundary m
    (fun i j => c * orderSign i j) y

end LogarithmicMorrisFull
