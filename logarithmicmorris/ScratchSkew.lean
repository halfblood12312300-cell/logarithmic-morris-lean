import logarithmicmorris.LogarithmicMorrisPfaffianDefinitions

noncomputable section

open scoped BigOperators

namespace LogarithmicMorrisFull

def pairSwap (m : ℕ) (r : Fin m) : Equiv.Perm (Fin (2 * m + 1)) :=
  Equiv.swap (pairLeft m r) (pairRight m r)

theorem pairLeft_ne_pairRight (m : ℕ) (r : Fin m) :
    pairLeft m r ≠ pairRight m r := by
  intro h
  have := congrArg Fin.val h
  simp [pairLeft, pairRight] at this

@[simp] theorem pairSwap_left (m : ℕ) (r : Fin m) :
    pairSwap m r (pairLeft m r) = pairRight m r := by
  simp [pairSwap, pairLeft_ne_pairRight]

@[simp] theorem pairSwap_right (m : ℕ) (r : Fin m) :
    pairSwap m r (pairRight m r) = pairLeft m r := by
  simp [pairSwap, pairLeft_ne_pairRight]

theorem pairLeft_ne_of_ne (m : ℕ) {q r : Fin m} (hqr : q ≠ r) :
    pairLeft m q ≠ pairLeft m r := by
  intro h
  apply hqr
  apply Fin.ext
  have := congrArg Fin.val h
  simp [pairLeft] at this
  omega

theorem pairLeft_ne_pairRight_of_ne (m : ℕ) {q r : Fin m} (hqr : q ≠ r) :
    pairLeft m q ≠ pairRight m r := by
  intro h
  have := congrArg Fin.val h
  simp [pairLeft, pairRight] at this
  omega

theorem pairRight_ne_pairLeft_of_ne (m : ℕ) {q r : Fin m} (hqr : q ≠ r) :
    pairRight m q ≠ pairLeft m r := by
  exact (pairLeft_ne_pairRight_of_ne m hqr.symm).symm

theorem pairRight_ne_of_ne (m : ℕ) {q r : Fin m} (hqr : q ≠ r) :
    pairRight m q ≠ pairRight m r := by
  intro h
  apply hqr
  apply Fin.ext
  have := congrArg Fin.val h
  simp [pairRight] at this
  omega

@[simp] theorem pairSwap_left_of_ne (m : ℕ) {q r : Fin m} (hqr : q ≠ r) :
    pairSwap m r (pairLeft m q) = pairLeft m q := by
  exact Equiv.swap_apply_of_ne_of_ne
    (pairLeft_ne_of_ne m hqr) (pairLeft_ne_pairRight_of_ne m hqr)

@[simp] theorem pairSwap_right_of_ne (m : ℕ) {q r : Fin m} (hqr : q ≠ r) :
    pairSwap m r (pairRight m q) = pairRight m q := by
  exact Equiv.swap_apply_of_ne_of_ne
    (pairRight_ne_pairLeft_of_ne m hqr) (pairRight_ne_of_ne m hqr)

@[simp] theorem pairSwap_sign (m : ℕ) (r : Fin m) :
    (pairSwap m r).sign = -1 := by
  exact Equiv.Perm.sign_swap (pairLeft_ne_pairRight m r)

def mixedPairedFactor (m : ℕ)
    (A : Fin (2 * m + 1) → Fin (2 * m + 1) → ℂ)
    (s : Finset (Fin m)) (σ : Equiv.Perm (Fin (2 * m + 1)))
    (q : Fin m) : ℂ :=
  if q ∈ s then
    A (σ (pairLeft m q)) (σ (pairRight m q)) -
      A (σ (pairRight m q)) (σ (pairLeft m q))
  else
    A (σ (pairLeft m q)) (σ (pairRight m q))

def mixedPairedProduct (m : ℕ)
    (A : Fin (2 * m + 1) → Fin (2 * m + 1) → ℂ)
    (s : Finset (Fin m)) (σ : Equiv.Perm (Fin (2 * m + 1))) : ℂ :=
  ∏ q : Fin m, mixedPairedFactor m A s σ q

def mixedPairedAlternatingSum (m : ℕ)
    (A : Fin (2 * m + 1) → Fin (2 * m + 1) → ℂ)
    (s : Finset (Fin m)) : ℂ :=
  ∑ σ : Equiv.Perm (Fin (2 * m + 1)),
    (((σ.sign : ℤ) : ℂ) * mixedPairedProduct m A s σ)

theorem mixedPairedFactor_erase_self (m : ℕ)
    (A : Fin (2 * m + 1) → Fin (2 * m + 1) → ℂ)
    (s : Finset (Fin m)) (r : Fin m) (σ : Equiv.Perm (Fin (2 * m + 1))) :
    mixedPairedFactor m A (s.erase r) σ r =
      A (σ (pairLeft m r)) (σ (pairRight m r)) := by
  simp [mixedPairedFactor]

theorem mixedPairedFactor_erase_of_ne (m : ℕ)
    (A : Fin (2 * m + 1) → Fin (2 * m + 1) → ℂ)
    (s : Finset (Fin m)) {q r : Fin m} (hqr : q ≠ r)
    (σ : Equiv.Perm (Fin (2 * m + 1))) :
    mixedPairedFactor m A (s.erase r) σ q = mixedPairedFactor m A s σ q := by
  by_cases hqs : q ∈ s <;> simp [mixedPairedFactor, hqr, hqs]

theorem mixedPairedFactor_swap_of_ne (m : ℕ)
    (A : Fin (2 * m + 1) → Fin (2 * m + 1) → ℂ)
    (s : Finset (Fin m)) {q r : Fin m} (hqr : q ≠ r)
    (σ : Equiv.Perm (Fin (2 * m + 1))) :
    mixedPairedFactor m A s (σ * pairSwap m r) q =
      mixedPairedFactor m A s σ q := by
  simp [mixedPairedFactor, Equiv.Perm.coe_mul, hqr]

theorem mixedPairedProduct_step_term (m : ℕ)
    (A : Fin (2 * m + 1) → Fin (2 * m + 1) → ℂ)
    (s : Finset (Fin m)) {r : Fin m} (hr : r ∈ s)
    (σ : Equiv.Perm (Fin (2 * m + 1))) :
    (((σ.sign : ℤ) : ℂ) * mixedPairedProduct m A s σ) =
      (((σ.sign : ℤ) : ℂ) * mixedPairedProduct m A (s.erase r) σ) +
      (((((σ * pairSwap m r).sign : ℤ) : ℂ)) *
        mixedPairedProduct m A (s.erase r) (σ * pairSwap m r)) := by
  have hmem : r ∈ (Finset.univ : Finset (Fin m)) := Finset.mem_univ r
  have hs : mixedPairedProduct m A s σ =
      mixedPairedFactor m A s σ r *
        ∏ q ∈ (Finset.univ.erase r), mixedPairedFactor m A s σ q := by
    exact (Finset.mul_prod_erase Finset.univ
      (mixedPairedFactor m A s σ) hmem).symm
  have he : mixedPairedProduct m A (s.erase r) σ =
      mixedPairedFactor m A (s.erase r) σ r *
        ∏ q ∈ (Finset.univ.erase r),
          mixedPairedFactor m A (s.erase r) σ q := by
    exact (Finset.mul_prod_erase Finset.univ
      (mixedPairedFactor m A (s.erase r) σ) hmem).symm
  have heSwap : mixedPairedProduct m A (s.erase r) (σ * pairSwap m r) =
      mixedPairedFactor m A (s.erase r) (σ * pairSwap m r) r *
        ∏ q ∈ (Finset.univ.erase r),
          mixedPairedFactor m A (s.erase r) (σ * pairSwap m r) q := by
    exact (Finset.mul_prod_erase Finset.univ
      (mixedPairedFactor m A (s.erase r) (σ * pairSwap m r)) hmem).symm
  have hrestErase :
      (∏ q ∈ (Finset.univ.erase r), mixedPairedFactor m A s σ q) =
      ∏ q ∈ (Finset.univ.erase r),
        mixedPairedFactor m A (s.erase r) σ q := by
    apply Finset.prod_congr rfl
    intro q hq
    exact (mixedPairedFactor_erase_of_ne m A s (Finset.ne_of_mem_erase hq) σ).symm
  have hrestSwap :
      (∏ q ∈ (Finset.univ.erase r),
        mixedPairedFactor m A (s.erase r) (σ * pairSwap m r) q) =
      ∏ q ∈ (Finset.univ.erase r),
        mixedPairedFactor m A (s.erase r) σ q := by
    apply Finset.prod_congr rfl
    intro q hq
    exact mixedPairedFactor_swap_of_ne m A (s.erase r)
      (Finset.ne_of_mem_erase hq) σ
  rw [hs, he, heSwap, hrestErase, hrestSwap]
  simp only [mixedPairedFactor, hr, if_true, Finset.mem_erase,
    ne_eq, not_true_eq_false, false_and, if_false, Equiv.Perm.sign_mul,
    pairSwap_sign, Equiv.Perm.coe_mul, Function.comp_apply,
    pairSwap_left, pairSwap_right]
  push_cast
  ring

theorem mixedPairedAlternatingSum_erase (m : ℕ)
    (A : Fin (2 * m + 1) → Fin (2 * m + 1) → ℂ)
    (s : Finset (Fin m)) {r : Fin m} (hr : r ∈ s) :
    mixedPairedAlternatingSum m A s =
      2 * mixedPairedAlternatingSum m A (s.erase r) := by
  unfold mixedPairedAlternatingSum
  simp_rw [mixedPairedProduct_step_term m A s hr]
  rw [Finset.sum_add_distrib]
  have hreindex :
      (∑ x : Equiv.Perm (Fin (2 * m + 1)),
        (((((x * pairSwap m r).sign : ℤ) : ℂ)) *
          mixedPairedProduct m A (s.erase r) (x * pairSwap m r))) =
      ∑ x : Equiv.Perm (Fin (2 * m + 1)),
        (((x.sign : ℤ) : ℂ) * mixedPairedProduct m A (s.erase r) x) :=
    by
      simpa only [Equiv.coe_mulRight] using
        (Equiv.sum_comp (Equiv.mulRight (pairSwap m r))
          (fun x : Equiv.Perm (Fin (2 * m + 1)) =>
            ((((x.sign : ℤ) : ℂ)) * mixedPairedProduct m A (s.erase r) x)))
  rw [hreindex]
  ring

theorem mixedPairedAlternatingSum_eq_pow_card (m : ℕ)
    (A : Fin (2 * m + 1) → Fin (2 * m + 1) → ℂ)
    (s : Finset (Fin m)) :
    mixedPairedAlternatingSum m A s =
      (2 : ℂ) ^ s.card * mixedPairedAlternatingSum m A ∅ := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert r s hrs ih =>
      rw [mixedPairedAlternatingSum_erase m A (insert r s)
        (Finset.mem_insert_self r s)]
      rw [Finset.erase_insert hrs, ih, Finset.card_insert_of_notMem hrs, pow_succ]
      ring

theorem mixedPairedAlternatingSum_empty (m : ℕ)
    (A : Fin (2 * m + 1) → Fin (2 * m + 1) → ℂ) :
    mixedPairedAlternatingSum m A ∅ = pairedAlternatingSum m A := by
  unfold mixedPairedAlternatingSum mixedPairedProduct pairedAlternatingSum
  simp [mixedPairedFactor]

theorem mixedPairedAlternatingSum_univ (m : ℕ)
    (A : Fin (2 * m + 1) → Fin (2 * m + 1) → ℂ) :
    mixedPairedAlternatingSum m A Finset.univ =
      pairedAlternatingSum m (fun i j => A i j - A j i) := by
  unfold mixedPairedAlternatingSum mixedPairedProduct pairedAlternatingSum
  simp [mixedPairedFactor]

theorem pairedAlternatingSum_skewPart_full (m : ℕ)
    (A : Fin (2 * m + 1) → Fin (2 * m + 1) → ℂ) :
    pairedAlternatingSum m (fun i j => A i j - A j i) =
      (2 : ℂ) ^ m * pairedAlternatingSum m A := by
  rw [← mixedPairedAlternatingSum_univ]
  rw [mixedPairedAlternatingSum_eq_pow_card]
  rw [mixedPairedAlternatingSum_empty, Finset.card_univ, Fintype.card_fin]

end LogarithmicMorrisFull
