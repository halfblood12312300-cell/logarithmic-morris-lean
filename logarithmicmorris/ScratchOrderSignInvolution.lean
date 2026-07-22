import logarithmicmorris.ScratchPfaffSaw

noncomputable section

set_option maxHeartbeats 800000

open scoped BigOperators

namespace LogarithmicMorrisFull

local instance (p : Prop) : Decidable p := Classical.propDecidable p

def PairOriented (m : ℕ) (σ : Equiv.Perm (Fin (2 * m + 1))) : Prop :=
  ∀ r : Fin m, σ (pairLeft m r) < σ (pairRight m r)

def upperOne {N : ℕ} (i j : Fin N) : ℂ :=
  if i < j then 1 else 0

theorem upperOne_skewPart (m : ℕ) (i j : Fin (2 * m + 1)) :
    upperOne i j - upperOne j i = orderSign i j := by
  rcases lt_trichotomy i j with hij | hij | hij
  · simp [upperOne, orderSign, hij, not_lt_of_ge hij.le]
  · subst j
    simp [upperOne, orderSign]
  · simp [upperOne, orderSign, hij, not_lt_of_ge hij.le]

theorem pairedAlternatingSum_orderSign_eq_upperOne (m : ℕ) :
    pairedAlternatingSum m (orderSign :
      Fin (2 * m + 1) → Fin (2 * m + 1) → ℂ) =
      (2 : ℂ) ^ m * pairedAlternatingSum m upperOne := by
  rw [← pairedAlternatingSum_skewPart_full m upperOne]
  congr 1
  funext i j
  exact (upperOne_skewPart m i j).symm

theorem upperOne_pair_product (m : ℕ)
    (σ : Equiv.Perm (Fin (2 * m + 1))) :
    (∏ r : Fin m,
      upperOne (σ (pairLeft m r)) (σ (pairRight m r))) =
      if PairOriented m σ then 1 else 0 := by
  simp only [upperOne]
  by_cases h : PairOriented m σ
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro r hr
    simp [h r]
  · rw [if_neg h]
    change ¬ ∀ r : Fin m,
      σ (pairLeft m r) < σ (pairRight m r) at h
    push_neg at h
    obtain ⟨r, hr⟩ := h
    apply Finset.prod_eq_zero (Finset.mem_univ r)
    simp [hr]

def BlockSurvivor (m : ℕ) (σ : Equiv.Perm (Fin (2 * m + 1))) : Prop :=
  ∀ j : Fin m, ∃ r : Fin m,
    σ (pairLeft m r) = pairLeft m j ∧
      σ (pairRight m r) = pairRight m j

def OutputPairPresent (m : ℕ) (σ : Equiv.Perm (Fin (2 * m + 1)))
    (j : Fin m) : Prop :=
  ∃ r : Fin m,
    σ (pairLeft m r) = pairLeft m j ∧
      σ (pairRight m r) = pairRight m j

theorem blockSurvivor_iff (m : ℕ)
    (σ : Equiv.Perm (Fin (2 * m + 1))) :
    BlockSurvivor m σ ↔ ∀ j : Fin m, OutputPairPresent m σ j := by
  rfl

def badOutputPairs (m : ℕ) (σ : Equiv.Perm (Fin (2 * m + 1))) :
    Finset (Fin m) :=
  Finset.univ.filter fun j => ¬OutputPairPresent m σ j

theorem badOutputPairs_nonempty (m : ℕ)
    (σ : Equiv.Perm (Fin (2 * m + 1)))
    (hσ : ¬BlockSurvivor m σ) : (badOutputPairs m σ).Nonempty := by
  rw [blockSurvivor_iff] at hσ
  push_neg at hσ
  obtain ⟨j, hj⟩ := hσ
  exact ⟨j, by simp [badOutputPairs, hj]⟩

def firstBadOutputPair (m : ℕ) (σ : Equiv.Perm (Fin (2 * m + 1)))
    (hσ : ¬BlockSurvivor m σ) : Fin m :=
  (badOutputPairs m σ).min' (badOutputPairs_nonempty m σ hσ)

theorem firstBadOutputPair_not_present (m : ℕ)
    (σ : Equiv.Perm (Fin (2 * m + 1)))
    (hσ : ¬BlockSurvivor m σ) :
    ¬OutputPairPresent m σ (firstBadOutputPair m σ hσ) := by
  have hmem := Finset.min'_mem (badOutputPairs m σ)
    (badOutputPairs_nonempty m σ hσ)
  simpa [badOutputPairs] using hmem

def outputPairSwap (m : ℕ) (j : Fin m) :
    Equiv.Perm (Fin (2 * m + 1)) :=
  Equiv.swap (pairLeft m j) (pairRight m j)

@[simp] theorem outputPairSwap_sign (m : ℕ) (j : Fin m) :
    (outputPairSwap m j).sign = -1 := by
  exact Equiv.Perm.sign_swap (pairLeft_ne_pairRight m j)

@[simp] theorem outputPairSwap_left (m : ℕ) (j : Fin m) :
    outputPairSwap m j (pairLeft m j) = pairRight m j := by
  simp [outputPairSwap, pairLeft_ne_pairRight]

@[simp] theorem outputPairSwap_right (m : ℕ) (j : Fin m) :
    outputPairSwap m j (pairRight m j) = pairLeft m j := by
  simp [outputPairSwap, pairLeft_ne_pairRight]

@[simp] theorem outputPairSwap_involutive (m : ℕ) (j : Fin m)
    (σ : Equiv.Perm (Fin (2 * m + 1))) :
    outputPairSwap m j * (outputPairSwap m j * σ) = σ := by
  rw [← mul_assoc]
  simp [outputPairSwap]

theorem outputPairSwap_apply_of_ne (m : ℕ) (j : Fin m)
    {x : Fin (2 * m + 1)}
    (hxl : x ≠ pairLeft m j) (hxr : x ≠ pairRight m j) :
    outputPairSwap m j x = x := by
  exact Equiv.swap_apply_of_ne_of_ne hxl hxr

theorem outputPairSwap_preserves_lt (m : ℕ) (j : Fin m)
    {x y : Fin (2 * m + 1)} (hxy : x < y)
    (hnot : ¬(x = pairLeft m j ∧ y = pairRight m j)) :
    outputPairSwap m j x < outputPairSwap m j y := by
  by_cases hxl : x = pairLeft m j
  · subst x
    have hyr : y ≠ pairRight m j := by
      intro h
      exact hnot ⟨rfl, h⟩
    have hyl : y ≠ pairLeft m j := ne_of_gt hxy
    rw [outputPairSwap_left,
      outputPairSwap_apply_of_ne m j hyl hyr]
    apply Fin.mk_lt_mk.mpr
    have hv := Fin.mk_lt_mk.mp hxy
    simp only [pairLeft, pairRight] at hv ⊢
    have hyne : y.val ≠ 2 * j.val + 1 := by
      intro hy
      apply hyr
      apply Fin.ext
      simpa [pairRight] using hy
    omega
  · by_cases hxr : x = pairRight m j
    · subst x
      have hyl : y ≠ pairLeft m j := by
        intro h
        have hv := congrArg Fin.val h
        have hxyv := Fin.mk_lt_mk.mp hxy
        simp only [pairLeft, pairRight] at hv hxyv
        omega
      have hyr : y ≠ pairRight m j := ne_of_gt hxy
      rw [outputPairSwap_right,
        outputPairSwap_apply_of_ne m j hyl hyr]
      apply Fin.mk_lt_mk.mpr
      have hv := Fin.mk_lt_mk.mp hxy
      simp only [pairLeft, pairRight] at hv ⊢
      omega
    · rw [outputPairSwap_apply_of_ne m j hxl hxr]
      by_cases hyl : y = pairLeft m j
      · subst y
        rw [outputPairSwap_left]
        apply Fin.mk_lt_mk.mpr
        have hv := Fin.mk_lt_mk.mp hxy
        simp only [pairLeft, pairRight] at hv ⊢
        omega
      · by_cases hyr : y = pairRight m j
        · subst y
          rw [outputPairSwap_right]
          apply Fin.mk_lt_mk.mpr
          have hv := Fin.mk_lt_mk.mp hxy
          have hxne : x.val ≠ 2 * j.val := by
            intro hx
            apply hxl
            apply Fin.ext
            simpa [pairLeft] using hx
          simp only [pairLeft, pairRight] at hv ⊢
          omega
        · rw [outputPairSwap_apply_of_ne m j hyl hyr]
          exact hxy

theorem outputPairPresent_swap_of_ne (m : ℕ)
    (σ : Equiv.Perm (Fin (2 * m + 1))) {j l : Fin m} (hjl : j ≠ l) :
    OutputPairPresent m (outputPairSwap m j * σ) l ↔
      OutputPairPresent m σ l := by
  simp only [OutputPairPresent, Equiv.Perm.coe_mul, Function.comp_apply]
  have hll : pairLeft m l ≠ pairLeft m j := pairLeft_ne_of_ne m hjl.symm
  have hlr : pairLeft m l ≠ pairRight m j :=
    pairLeft_ne_pairRight_of_ne m hjl.symm
  have hrl : pairRight m l ≠ pairLeft m j :=
    pairRight_ne_pairLeft_of_ne m hjl.symm
  have hrr : pairRight m l ≠ pairRight m j := pairRight_ne_of_ne m hjl.symm
  have hfixL : outputPairSwap m j (pairLeft m l) = pairLeft m l :=
    outputPairSwap_apply_of_ne m j hll hlr
  have hfixR : outputPairSwap m j (pairRight m l) = pairRight m l :=
    outputPairSwap_apply_of_ne m j hrl hrr
  constructor
  · rintro ⟨r, hrL, hrR⟩
    refine ⟨r, ?_, ?_⟩
    · apply (outputPairSwap m j).injective
      rw [hrL, hfixL]
    · apply (outputPairSwap m j).injective
      rw [hrR, hfixR]
  · rintro ⟨r, hrL, hrR⟩
    exact ⟨r, by rw [hrL, hfixL], by rw [hrR, hfixR]⟩

theorem pairOriented_swap_of_not_present (m : ℕ)
    (σ : Equiv.Perm (Fin (2 * m + 1))) (j : Fin m)
    (hor : PairOriented m σ) (hbad : ¬OutputPairPresent m σ j) :
    PairOriented m (outputPairSwap m j * σ) := by
  intro r
  simp only [Equiv.Perm.coe_mul, Function.comp_apply]
  apply outputPairSwap_preserves_lt m j (hor r)
  intro h
  exact hbad ⟨r, h.1, h.2⟩

theorem outputPairPresent_self_false_after_swap (m : ℕ)
    (σ : Equiv.Perm (Fin (2 * m + 1))) (j : Fin m)
    (hor : PairOriented m σ) (hbad : ¬OutputPairPresent m σ j) :
    ¬OutputPairPresent m (outputPairSwap m j * σ) j := by
  rintro ⟨r, hrL, hrR⟩
  simp only [Equiv.Perm.coe_mul, Function.comp_apply] at hrL hrR
  have hpreL : σ (pairLeft m r) = pairRight m j := by
    apply (outputPairSwap m j).injective
    rw [hrL, outputPairSwap_right]
  have hpreR : σ (pairRight m r) = pairLeft m j := by
    apply (outputPairSwap m j).injective
    rw [hrR, outputPairSwap_left]
  have h := hor r
  rw [hpreL, hpreR] at h
  exact (not_lt_of_ge (show pairLeft m j ≤ pairRight m j by
    apply Fin.mk_le_mk.mpr
    simp [pairLeft, pairRight])) h

theorem badOutputPairs_swap_eq (m : ℕ)
    (σ : Equiv.Perm (Fin (2 * m + 1))) (j : Fin m)
    (hor : PairOriented m σ) (hbad : ¬OutputPairPresent m σ j) :
    badOutputPairs m (outputPairSwap m j * σ) = badOutputPairs m σ := by
  ext l
  simp only [badOutputPairs, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hjl : j = l
  · subst l
    exact iff_of_true
      (outputPairPresent_self_false_after_swap m σ j hor hbad) hbad
  · exact not_congr (outputPairPresent_swap_of_ne m σ hjl)

theorem blockSurvivor_false_after_swap (m : ℕ)
    (σ : Equiv.Perm (Fin (2 * m + 1))) (j : Fin m)
    (hor : PairOriented m σ) (hbad : ¬OutputPairPresent m σ j) :
    ¬BlockSurvivor m (outputPairSwap m j * σ) := by
  rw [blockSurvivor_iff]
  push_neg
  exact ⟨j, outputPairPresent_self_false_after_swap m σ j hor hbad⟩

theorem firstBadOutputPair_after_swap (m : ℕ)
    (σ : Equiv.Perm (Fin (2 * m + 1)))
    (hns : ¬BlockSurvivor m σ) (hor : PairOriented m σ) :
    let j := firstBadOutputPair m σ hns
    let τ := outputPairSwap m j * σ
    let hnτ : ¬BlockSurvivor m τ :=
      blockSurvivor_false_after_swap m σ j hor
        (firstBadOutputPair_not_present m σ hns)
    firstBadOutputPair m τ hnτ = j := by
  dsimp only
  let S := badOutputPairs m
    (outputPairSwap m (firstBadOutputPair m σ hns) * σ)
  let T := badOutputPairs m σ
  have hsets : S = T := badOutputPairs_swap_eq m σ
    (firstBadOutputPair m σ hns) hor
    (firstBadOutputPair_not_present m σ hns)
  change S.min' _ = T.min' _
  refine (Finset.min'_eq_iff S _ (T.min' _)).2 ?_
  constructor
  · rw [hsets]
    exact Finset.min'_mem T _
  · intro b hb
    have hbT : b ∈ T := by
      rw [← hsets]
      exact hb
    exact Finset.min'_le T b hbT

def badOrientedPerms (m : ℕ) :
    Finset (Equiv.Perm (Fin (2 * m + 1))) :=
  Finset.univ.filter fun σ => PairOriented m σ ∧ ¬BlockSurvivor m σ

theorem badOrientedPerms_oriented (m : ℕ)
    {σ : Equiv.Perm (Fin (2 * m + 1))} (hσ : σ ∈ badOrientedPerms m) :
    PairOriented m σ := by
  simpa [badOrientedPerms] using (Finset.mem_filter.mp hσ).2.1

theorem badOrientedPerms_not_survivor (m : ℕ)
    {σ : Equiv.Perm (Fin (2 * m + 1))} (hσ : σ ∈ badOrientedPerms m) :
    ¬BlockSurvivor m σ := by
  simpa [badOrientedPerms] using (Finset.mem_filter.mp hσ).2.2

def badOrientedMate (m : ℕ)
    (σ : Equiv.Perm (Fin (2 * m + 1))) (hσ : σ ∈ badOrientedPerms m) :
    Equiv.Perm (Fin (2 * m + 1)) :=
  outputPairSwap m
      (firstBadOutputPair m σ (badOrientedPerms_not_survivor m hσ)) * σ

theorem badOrientedMate_mem (m : ℕ)
    (σ : Equiv.Perm (Fin (2 * m + 1))) (hσ : σ ∈ badOrientedPerms m) :
    badOrientedMate m σ hσ ∈ badOrientedPerms m := by
  let hns := badOrientedPerms_not_survivor m hσ
  let hor := badOrientedPerms_oriented m hσ
  let j := firstBadOutputPair m σ hns
  have hbad : ¬OutputPairPresent m σ j :=
    firstBadOutputPair_not_present m σ hns
  rw [badOrientedPerms, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_, ?_⟩
  · exact pairOriented_swap_of_not_present m σ j hor hbad
  · exact blockSurvivor_false_after_swap m σ j hor hbad

theorem badOrientedMate_sign (m : ℕ)
    (σ : Equiv.Perm (Fin (2 * m + 1))) (hσ : σ ∈ badOrientedPerms m) :
    (badOrientedMate m σ hσ).sign = -σ.sign := by
  simp [badOrientedMate, Equiv.Perm.sign_mul]

theorem badOrientedMate_ne (m : ℕ)
    (σ : Equiv.Perm (Fin (2 * m + 1))) (hσ : σ ∈ badOrientedPerms m) :
    badOrientedMate m σ hσ ≠ σ := by
  intro heq
  have hs := congrArg Equiv.Perm.sign heq
  rw [badOrientedMate_sign] at hs
  have hs' := congrArg (fun u : ℤˣ => u * σ.sign) hs
  simpa [Int.units_mul_self] using hs'

theorem badOrientedMate_involutive (m : ℕ)
    (σ : Equiv.Perm (Fin (2 * m + 1))) (hσ : σ ∈ badOrientedPerms m) :
    badOrientedMate m (badOrientedMate m σ hσ)
        (badOrientedMate_mem m σ hσ) = σ := by
  let hns := badOrientedPerms_not_survivor m hσ
  let hor := badOrientedPerms_oriented m hσ
  let j := firstBadOutputPair m σ hns
  let τ := outputPairSwap m j * σ
  have hbad : ¬OutputPairPresent m σ j :=
    firstBadOutputPair_not_present m σ hns
  let hnτ : ¬BlockSurvivor m τ :=
    blockSurvivor_false_after_swap m σ j hor hbad
  have hj : firstBadOutputPair m τ hnτ = j :=
    firstBadOutputPair_after_swap m σ hns hor
  change outputPairSwap m
      (firstBadOutputPair m τ
        (badOrientedPerms_not_survivor m (badOrientedMate_mem m σ hσ))) * τ = σ
  have hproof : badOrientedPerms_not_survivor m
      (badOrientedMate_mem m σ hσ) = hnτ := Subsingleton.elim _ _
  rw [hproof, hj]
  exact outputPairSwap_involutive m j σ

theorem sum_sign_badOrientedPerms (m : ℕ) :
    (∑ σ ∈ badOrientedPerms m, ((σ.sign : ℤ) : ℂ)) = 0 := by
  apply Finset.sum_involution
      (fun σ hσ => badOrientedMate m σ hσ)
  · intro σ hσ
    rw [badOrientedMate_sign]
    push_cast
    ring
  · intro σ hσ hf
    exact badOrientedMate_ne m σ hσ
  · intro σ hσ
    exact badOrientedMate_involutive m σ hσ

def pairBlockEquiv (m : ℕ) :
    ((Fin m × Fin 2) ⊕ Fin 1) ≃ Fin (2 * m + 1) :=
  ((finProdFinEquiv.sumCongr (Equiv.refl (Fin 1))).trans
    finSumFinEquiv).trans (finCongr (by omega))

@[simp] theorem pairBlockEquiv_left (m : ℕ) (r : Fin m) :
    pairBlockEquiv m (Sum.inl (r, 0)) = pairLeft m r := by
  apply Fin.ext
  simp [pairBlockEquiv, pairLeft, finProdFinEquiv, finSumFinEquiv]

@[simp] theorem pairBlockEquiv_right (m : ℕ) (r : Fin m) :
    pairBlockEquiv m (Sum.inl (r, 1)) = pairRight m r := by
  apply Fin.ext
  simp [pairBlockEquiv, pairRight, finProdFinEquiv, finSumFinEquiv]
  omega

@[simp] theorem pairBlockEquiv_unmatched (m : ℕ) :
    pairBlockEquiv m (Sum.inr 0) = pairUnmatched m := by
  apply Fin.ext
  simp [pairBlockEquiv, pairUnmatched, finProdFinEquiv, finSumFinEquiv]

@[simp] theorem pairBlockEquiv_symm_left (m : ℕ) (r : Fin m) :
    (pairBlockEquiv m).symm (pairLeft m r) = Sum.inl (r, 0) := by
  apply (pairBlockEquiv m).injective
  simp

@[simp] theorem pairBlockEquiv_symm_right (m : ℕ) (r : Fin m) :
    (pairBlockEquiv m).symm (pairRight m r) = Sum.inl (r, 1) := by
  apply (pairBlockEquiv m).injective
  simp

@[simp] theorem pairBlockEquiv_symm_unmatched (m : ℕ) :
    (pairBlockEquiv m).symm (pairUnmatched m) = Sum.inr 0 := by
  apply (pairBlockEquiv m).injective
  simp

def blockPerm (m : ℕ) (τ : Equiv.Perm (Fin m)) :
    Equiv.Perm (Fin (2 * m + 1)) :=
  (pairBlockEquiv m).permCongr
    ((τ.prodCongr (Equiv.refl (Fin 2))).sumCongr (Equiv.refl (Fin 1)))

@[simp] theorem blockPerm_left (m : ℕ) (τ : Equiv.Perm (Fin m))
    (r : Fin m) :
    blockPerm m τ (pairLeft m r) = pairLeft m (τ r) := by
  simp [blockPerm]

@[simp] theorem blockPerm_right (m : ℕ) (τ : Equiv.Perm (Fin m))
    (r : Fin m) :
    blockPerm m τ (pairRight m r) = pairRight m (τ r) := by
  simp [blockPerm]

@[simp] theorem blockPerm_unmatched (m : ℕ) (τ : Equiv.Perm (Fin m)) :
    blockPerm m τ (pairUnmatched m) = pairUnmatched m := by
  simp [blockPerm]

theorem blockPerm_oriented (m : ℕ) (τ : Equiv.Perm (Fin m)) :
    PairOriented m (blockPerm m τ) := by
  intro r
  simp only [blockPerm_left, blockPerm_right]
  apply Fin.mk_lt_mk.mpr
  simp [pairLeft, pairRight]

theorem blockPerm_survivor (m : ℕ) (τ : Equiv.Perm (Fin m)) :
    BlockSurvivor m (blockPerm m τ) := by
  intro j
  refine ⟨τ.symm j, ?_, ?_⟩ <;> simp

theorem blockPerm_sign (m : ℕ) (τ : Equiv.Perm (Fin m)) :
    (blockPerm m τ).sign = 1 := by
  rw [blockPerm, Equiv.Perm.sign_permCongr, Equiv.Perm.sign_sumCongr]
  rw [Equiv.prodCongr_refl_right]
  rw [Equiv.Perm.sign_prodCongrLeft]
  simp only [Equiv.Perm.sign_refl, mul_one]
  have hsq : τ.sign * τ.sign = 1 := by
    exact Int.units_mul_self τ.sign
  simpa [Fin.prod_univ_two] using hsq

theorem blockPerm_injective (m : ℕ) : Function.Injective (blockPerm m) := by
  intro τ υ h
  ext r
  have hr := congrArg (fun σ : Equiv.Perm (Fin (2 * m + 1)) =>
    σ (pairLeft m r)) h
  simp only [blockPerm_left] at hr
  have hv := congrArg Fin.val hr
  simp only [pairLeft] at hv
  omega

def survivorPreimage (m : ℕ)
    (σ : Equiv.Perm (Fin (2 * m + 1))) (hσ : BlockSurvivor m σ)
    (j : Fin m) : Fin m :=
  Classical.choose (hσ j)

theorem survivorPreimage_left (m : ℕ)
    (σ : Equiv.Perm (Fin (2 * m + 1))) (hσ : BlockSurvivor m σ)
    (j : Fin m) :
    σ (pairLeft m (survivorPreimage m σ hσ j)) = pairLeft m j := by
  exact (Classical.choose_spec (hσ j)).1

theorem survivorPreimage_right (m : ℕ)
    (σ : Equiv.Perm (Fin (2 * m + 1))) (hσ : BlockSurvivor m σ)
    (j : Fin m) :
    σ (pairRight m (survivorPreimage m σ hσ j)) = pairRight m j := by
  exact (Classical.choose_spec (hσ j)).2

theorem survivorPreimage_injective (m : ℕ)
    (σ : Equiv.Perm (Fin (2 * m + 1))) (hσ : BlockSurvivor m σ) :
    Function.Injective (survivorPreimage m σ hσ) := by
  intro j l h
  have hj := survivorPreimage_left m σ hσ j
  have hl := survivorPreimage_left m σ hσ l
  rw [h] at hj
  have : pairLeft m j = pairLeft m l := hj.symm.trans hl
  apply Fin.ext
  have hv := congrArg Fin.val this
  simp only [pairLeft] at hv
  omega

def survivorBlockPerm (m : ℕ)
    (σ : Equiv.Perm (Fin (2 * m + 1))) (hσ : BlockSurvivor m σ) :
    Equiv.Perm (Fin m) :=
  (Equiv.ofBijective (survivorPreimage m σ hσ)
    ⟨survivorPreimage_injective m σ hσ,
      Finite.injective_iff_surjective.mp
        (survivorPreimage_injective m σ hσ)⟩).symm

theorem survivorBlockPerm_preimage (m : ℕ)
    (σ : Equiv.Perm (Fin (2 * m + 1))) (hσ : BlockSurvivor m σ)
    (j : Fin m) :
    survivorBlockPerm m σ hσ (survivorPreimage m σ hσ j) = j := by
  exact (Equiv.ofBijective (survivorPreimage m σ hσ)
    ⟨survivorPreimage_injective m σ hσ,
      Finite.injective_iff_surjective.mp
        (survivorPreimage_injective m σ hσ)⟩).symm_apply_apply j

theorem survivor_maps_unmatched (m : ℕ)
    (σ : Equiv.Perm (Fin (2 * m + 1))) (hσ : BlockSurvivor m σ) :
    σ (pairUnmatched m) = pairUnmatched m := by
  let y := σ (pairUnmatched m)
  obtain ⟨z, hz⟩ := (pairBlockEquiv m).surjective y
  rcases z with z | u
  · rcases z with ⟨j, b⟩
    have hb : b = 0 ∨ b = 1 := by
      have hbv : b.val = 0 ∨ b.val = 1 := by omega
      rcases hbv with hbv | hbv
      · left
        apply Fin.ext
        exact hbv
      · right
        apply Fin.ext
        exact hbv
    rcases hb with rfl | rfl
    · have hz' : pairLeft m j = y := by
        simpa using hz
      let r := survivorPreimage m σ hσ j
      have hr := survivorPreimage_left m σ hσ j
      have heq : pairUnmatched m = pairLeft m r := by
        apply σ.injective
        rw [hr, hz']
      exact (pairLeft_ne_unmatched m r heq.symm).elim
    · have hz' : pairRight m j = y := by
        simpa using hz
      let r := survivorPreimage m σ hσ j
      have hr := survivorPreimage_right m σ hσ j
      have heq : pairUnmatched m = pairRight m r := by
        apply σ.injective
        rw [hr, hz']
      exact (pairRight_ne_unmatched m r heq.symm).elim
  · have hu : u = 0 := Subsingleton.elim _ _
    subst u
    have hz' : pairUnmatched m = y := by simpa using hz
    exact hz'.symm

theorem blockPerm_survivorBlockPerm (m : ℕ)
    (σ : Equiv.Perm (Fin (2 * m + 1))) (hσ : BlockSurvivor m σ) :
    blockPerm m (survivorBlockPerm m σ hσ) = σ := by
  apply Equiv.ext
  intro x
  obtain ⟨z, rfl⟩ := (pairBlockEquiv m).surjective x
  rcases z with z | u
  · rcases z with ⟨r, b⟩
    have hb : b = 0 ∨ b = 1 := by
      have hbv : b.val = 0 ∨ b.val = 1 := by omega
      rcases hbv with hbv | hbv
      · left
        apply Fin.ext
        exact hbv
      · right
        apply Fin.ext
        exact hbv
    rcases hb with rfl | rfl
    · have hx : pairBlockEquiv m (Sum.inl (r, (0 : Fin 2))) =
          pairLeft m r := pairBlockEquiv_left m r
      rw [hx]
      have hsur : Function.Surjective (survivorPreimage m σ hσ) :=
        Finite.injective_iff_surjective.mp
          (survivorPreimage_injective m σ hσ)
      obtain ⟨j, hj⟩ := hsur r
      rw [← hj, blockPerm_left, survivorBlockPerm_preimage,
        survivorPreimage_left]
    · have hx : pairBlockEquiv m (Sum.inl (r, (1 : Fin 2))) =
          pairRight m r := pairBlockEquiv_right m r
      rw [hx]
      have hsur : Function.Surjective (survivorPreimage m σ hσ) :=
        Finite.injective_iff_surjective.mp
          (survivorPreimage_injective m σ hσ)
      obtain ⟨j, hj⟩ := hsur r
      rw [← hj, blockPerm_right, survivorBlockPerm_preimage,
        survivorPreimage_right]
  · have hu : u = 0 := Subsingleton.elim _ _
    subst u
    have hx : pairBlockEquiv m (Sum.inr (0 : Fin 1)) =
        pairUnmatched m := pairBlockEquiv_unmatched m
    rw [hx, blockPerm_unmatched,
      survivor_maps_unmatched m σ hσ]

def orientedSurvivorPerms (m : ℕ) :
    Finset (Equiv.Perm (Fin (2 * m + 1))) :=
  Finset.univ.filter fun σ => PairOriented m σ ∧ BlockSurvivor m σ

theorem orientedSurvivorPerms_eq_image (m : ℕ) :
    orientedSurvivorPerms m =
      Finset.univ.image (blockPerm m) := by
  ext σ
  constructor
  · intro hσ
    have hs : BlockSurvivor m σ :=
      (Finset.mem_filter.mp hσ).2.2
    rw [Finset.mem_image]
    exact ⟨survivorBlockPerm m σ hs, Finset.mem_univ _,
      blockPerm_survivorBlockPerm m σ hs⟩
  · intro hσ
    rw [Finset.mem_image] at hσ
    obtain ⟨τ, hτ, rfl⟩ := hσ
    rw [orientedSurvivorPerms, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, blockPerm_oriented m τ,
      blockPerm_survivor m τ⟩

theorem card_orientedSurvivorPerms (m : ℕ) :
    (orientedSurvivorPerms m).card = m.factorial := by
  rw [orientedSurvivorPerms_eq_image, Finset.card_image_iff.mpr
    (fun _ _ _ _ h => blockPerm_injective m h), Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin]

theorem orientedSurvivorPerms_sign_one (m : ℕ)
    {σ : Equiv.Perm (Fin (2 * m + 1))}
    (hσ : σ ∈ orientedSurvivorPerms m) : σ.sign = 1 := by
  rw [orientedSurvivorPerms_eq_image, Finset.mem_image] at hσ
  obtain ⟨τ, hτ, rfl⟩ := hσ
  exact blockPerm_sign m τ

theorem sum_sign_orientedSurvivorPerms (m : ℕ) :
    (∑ σ ∈ orientedSurvivorPerms m, ((σ.sign : ℤ) : ℂ)) =
      (m.factorial : ℂ) := by
  calc
    _ = ∑ _σ ∈ orientedSurvivorPerms m, (1 : ℂ) := by
      apply Finset.sum_congr rfl
      intro σ hσ
      rw [orientedSurvivorPerms_sign_one m hσ]
      norm_num
    _ = (m.factorial : ℂ) := by
      simp [card_orientedSurvivorPerms]

def orientedPerms (m : ℕ) :
    Finset (Equiv.Perm (Fin (2 * m + 1))) :=
  Finset.univ.filter fun σ => PairOriented m σ

theorem orientedPerms_filter_survivor (m : ℕ) :
    (orientedPerms m).filter (BlockSurvivor m) =
      orientedSurvivorPerms m := by
  ext σ
  simp [orientedPerms, orientedSurvivorPerms]

theorem orientedPerms_filter_not_survivor (m : ℕ) :
    (orientedPerms m).filter (fun σ => ¬BlockSurvivor m σ) =
      badOrientedPerms m := by
  ext σ
  simp [orientedPerms, badOrientedPerms]

theorem pairedAlternatingSum_upperOne (m : ℕ) :
    pairedAlternatingSum m upperOne = (m.factorial : ℂ) := by
  classical
  unfold pairedAlternatingSum
  simp_rw [upperOne_pair_product]
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  change (∑ σ ∈ orientedPerms m, ((σ.sign : ℤ) : ℂ)) = _
  have hpartition := Finset.sum_filter_add_sum_filter_not
    (orientedPerms m) (BlockSurvivor m)
    (fun σ => ((σ.sign : ℤ) : ℂ))
  rw [orientedPerms_filter_survivor,
    orientedPerms_filter_not_survivor] at hpartition
  rw [← hpartition, sum_sign_orientedSurvivorPerms,
    sum_sign_badOrientedPerms, add_zero]

theorem pairedAlternatingSum_orderSign (m : ℕ) :
    pairedAlternatingSum m (orderSign :
      Fin (2 * m + 1) → Fin (2 * m + 1) → ℂ) =
      (2 : ℂ) ^ m * (m.factorial : ℂ) := by
  rw [pairedAlternatingSum_orderSign_eq_upperOne,
    pairedAlternatingSum_upperOne]

theorem pairedAlternatingSum_const_mul (m : ℕ) (c : ℂ)
    (A : Fin (2 * m + 1) → Fin (2 * m + 1) → ℂ) :
    pairedAlternatingSum m (fun i j => c * A i j) =
      c ^ m * pairedAlternatingSum m A := by
  unfold pairedAlternatingSum
  calc
    (∑ σ : Equiv.Perm (Fin (2 * m + 1)),
        ((σ.sign : ℤ) : ℂ) *
          ∏ r : Fin m, c * A (σ (pairLeft m r)) (σ (pairRight m r))) =
        ∑ σ : Equiv.Perm (Fin (2 * m + 1)),
          ((σ.sign : ℤ) : ℂ) *
            (c ^ m * ∏ r : Fin m,
              A (σ (pairLeft m r)) (σ (pairRight m r))) := by
          apply Finset.sum_congr rfl
          intro σ hσ
          rw [Finset.prod_mul_distrib, Finset.prod_const,
            Finset.card_univ, Fintype.card_fin]
    _ = c ^ m * ∑ σ : Equiv.Perm (Fin (2 * m + 1)),
          ((σ.sign : ℤ) : ℂ) *
            ∏ r : Fin m, A (σ (pairLeft m r)) (σ (pairRight m r)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro σ hσ
          ring

theorem pairedAlternatingSum_sawMatrix_complete (m : ℕ) (c : ℂ)
    (y : Fin (2 * m + 1) → ℂ) :
    pairedAlternatingSum m (sawMatrix m c y) =
      ((2 : ℂ) ^ m * (m.factorial : ℂ)) * c ^ m := by
  rw [pairedAlternatingSum_sawMatrix_reduce,
    pairedAlternatingSum_const_mul, pairedAlternatingSum_orderSign]
  ring

end LogarithmicMorrisFull
