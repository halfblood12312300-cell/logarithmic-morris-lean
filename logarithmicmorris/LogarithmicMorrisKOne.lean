import logarithmicmorris.LogarithmicMorrisDysonBaseReduction
import logarithmicmorris.ScratchOrderSignInvolution
import logarithmicmorris.ScratchPermutation
import Mathlib.LinearAlgebra.Vandermonde

/-! The finite `K = 1`, `a = b = 0` logarithmic Morris evaluation. -/

noncomputable section

open scoped BigOperators

namespace LogarithmicMorrisFull

local instance (p : Prop) : Decidable p := Classical.propDecidable p

lemma standardLogCT_sum {I : Type*} (S : Setup) (s : Finset I)
    (F : I → Laurent ℚ S.n) :
    standardLogCT S (∑ i ∈ s, F i) = ∑ i ∈ s, standardLogCT S (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [standardLogCT_eq_finsupp_sum]
  | @insert i s hi ih => simp [hi, standardLogCT_add, ih]

lemma prod_increasingPairs_eq_prod_Ioi_generic {R : Type*} [CommMonoid R]
    {n : ℕ} (f : Fin n → Fin n → R) :
    (∏ p ∈ increasingPairs n, f p.1 p.2) =
      ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, f i j := by
  simp only [increasingPairs, Finset.prod_filter]
  simp_rw [← Finset.filter_lt_eq_Ioi, Finset.prod_filter]
  exact (Finset.prod_product _ _ _).trans rfl

lemma vandermonde_eq_sign_det (m : ℕ) :
    (vandermonde (R := ℚ) (2 * m + 1)) =
      (-1 : Laurent ℚ (2 * m + 1)) ^ (m * (2 * m + 1)) *
        (Matrix.vandermonde
          (fun i : Fin (2 * m + 1) =>
            MultiLaurent.var (R := ℚ) i)).det := by
  rw [vandermonde, Matrix.det_vandermonde]
  rw [← prod_increasingPairs_eq_prod_Ioi_generic]
  rw [← card_increasingPairs_odd m]
  simp only [← Finset.prod_const, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  ring

def centeredExponent (m : ℕ)
    (σ : Equiv.Perm (Fin (2 * m + 1))) : Exponent (2 * m + 1) :=
  ∑ i : Fin (2 * m + 1),
    Finsupp.single (σ i) ((i : ℤ) - (m : ℤ))

@[simp] lemma centeredExponent_apply (m : ℕ)
    (σ : Equiv.Perm (Fin (2 * m + 1))) (j : Fin (2 * m + 1)) :
    centeredExponent m σ j = ((σ.symm j : Fin (2 * m + 1)) : ℤ) - (m : ℤ) := by
  classical
  unfold centeredExponent
  change (∑ i ∈ (Finset.univ : Finset (Fin (2 * m + 1))),
      (Finsupp.single (σ i) ((i : ℤ) - (m : ℤ)) :
        Exponent (2 * m + 1))) j = _
  rw [Finsupp.finset_sum_apply]
  simp only [Finsupp.single_apply]
  rw [Finset.sum_eq_single (σ.symm j)]
  · simp
  · intro i hi hne_i
    have hne : σ i ≠ j := by
      intro h
      apply hne_i
      exact σ.injective (by simpa using h)
    simp [hne]
  · simp

lemma detTerm_mul_center_eq (m : ℕ)
    (σ : Equiv.Perm (Fin (2 * m + 1))) :
    (∏ i : Fin (2 * m + 1),
        MultiLaurent.var (R := ℚ) (σ i) ^ (i : ℕ)) *
        (∏ j : Fin (2 * m + 1),
          MultiLaurent.varInv (R := ℚ) j ^ m) =
      MultiLaurent.X (R := ℚ) (centeredExponent m σ) := by
  rw [← Equiv.prod_comp σ (fun j : Fin (2 * m + 1) =>
    MultiLaurent.varInv (R := ℚ) j ^ m)]
  rw [← Finset.prod_mul_distrib]
  simp_rw [MultiLaurent.var, MultiLaurent.varInv, MultiLaurent.X_pow,
    MultiLaurent.X_mul_X]
  simp only [MultiLaurent.X, MultiLaurent.prod_monomial,
    Finset.prod_const_one]
  apply congrArg (fun e : Exponent (2 * m + 1) =>
    MultiLaurent.monomial e (1 : ℚ))
  ext j
  simp [centeredExponent, Finsupp.single_apply]
  rw [Finset.sum_add_distrib]
  rw [Finset.sum_neg_distrib]
  ring

def kOneSetup (m : ℕ) : Setup where
  n := 2 * m + 1
  m := m
  k := 0
  a := 0
  b := 0
  odd_rank := rfl

lemma dysonSetup_zero_eq (S : Setup) :
    dysonSetup S 0 = kOneSetup S.m := by
  cases S with
  | mk n m k a b h =>
      simp only [dysonSetup, kOneSetup]
      subst n
      rfl

lemma morrisKernel_kOne_simp (m : ℕ) :
    morrisKernel (kOneSetup m) =
      vandermonde (R := ℚ) (2 * m + 1) *
        ∏ i : Fin (2 * m + 1), MultiLaurent.varInv (R := ℚ) i ^ m := by
  simp [morrisKernel, kOneSetup]

lemma morrisKernel_kOne_expansion (m : ℕ) :
    morrisKernel (kOneSetup m) =
      ∑ σ : Equiv.Perm (Fin (2 * m + 1)),
        MultiLaurent.monomial (centeredExponent m σ)
          ((-1 : ℚ) ^ (m * (2 * m + 1)) * ((σ.sign : ℤ) : ℚ)) := by
  rw [morrisKernel_kOne_simp, vandermonde_eq_sign_det,
    Matrix.det_apply']
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [show
    (-1 : Laurent ℚ (2 * m + 1)) ^ (m * (2 * m + 1)) *
          (((σ.sign : ℤ) : Laurent ℚ (2 * m + 1)) *
            ∏ i : Fin (2 * m + 1),
              Matrix.vandermonde
                  (fun i : Fin (2 * m + 1) =>
                    MultiLaurent.var (R := ℚ) i)
                  (σ i) i) *
          ∏ i : Fin (2 * m + 1),
            MultiLaurent.varInv (R := ℚ) i ^ m =
        ((-1 : Laurent ℚ (2 * m + 1)) ^ (m * (2 * m + 1)) *
          ((σ.sign : ℤ) : Laurent ℚ (2 * m + 1))) *
          ((∏ i : Fin (2 * m + 1),
              MultiLaurent.var (R := ℚ) (σ i) ^ (i : ℕ)) *
            ∏ i : Fin (2 * m + 1),
              MultiLaurent.varInv (R := ℚ) i ^ m) by
      simp only [Matrix.vandermonde_apply]
      ring]
  rw [detTerm_mul_center_eq]
  rw [show
      (-1 : Laurent ℚ (2 * m + 1)) ^ (m * (2 * m + 1)) *
          ((σ.sign : ℤ) : Laurent ℚ (2 * m + 1)) =
        MultiLaurent.monomial 0
          ((-1 : ℚ) ^ (m * (2 * m + 1)) * ((σ.sign : ℤ) : ℚ)) by
      have hpow (q : ℚ) (N : ℕ) :
          (AddMonoidAlgebra.single (0 : Exponent (2 * m + 1)) q) ^ N =
            AddMonoidAlgebra.single 0 (q ^ N) := by
        induction N with
        | zero => simp [AddMonoidAlgebra.one_def]
        | succ N ih =>
            rw [pow_succ, ih, AddMonoidAlgebra.single_mul_single]
            simp [pow_succ]
      have hneg : (-1 : Laurent ℚ (2 * m + 1)) =
          AddMonoidAlgebra.single 0 (-1 : ℚ) := by
        simp [AddMonoidAlgebra.one_def, ← AddMonoidAlgebra.single_neg]
      rw [hneg, hpow, AddMonoidAlgebra.intCast_def,
        AddMonoidAlgebra.single_mul_single]
      rfl]
  rw [MultiLaurent.X, MultiLaurent.monomial_mul_monomial]
  simp

/-- The ordering of the centered Fourier modes
`1,-1,2,-2,…,m,-m,0`, expressed in the standard `Fin (2m+1)` labels. -/
def mirrorBlockMap (m : ℕ) :
    (Fin m × Fin 2) ⊕ Fin 1 → Fin (2 * m + 1)
  | Sum.inl (r, b) =>
      if b = 0 then
        ⟨m + 1 + r.1, by omega⟩
      else
        ⟨m - 1 - r.1, by omega⟩
  | Sum.inr _ => ⟨m, by omega⟩

lemma mirrorBlockMap_injective (m : ℕ) :
    Function.Injective (mirrorBlockMap m) := by
  intro x y hxy
  rcases x with ⟨r, b⟩ | u <;> rcases y with ⟨s, c⟩ | v
  · have hb : b = 0 ∨ b = 1 := by
      have : b.1 = 0 ∨ b.1 = 1 := by omega
      rcases this with h | h
      · left; apply Fin.ext; exact h
      · right; apply Fin.ext; exact h
    have hc : c = 0 ∨ c = 1 := by
      have : c.1 = 0 ∨ c.1 = 1 := by omega
      rcases this with h | h
      · left; apply Fin.ext; exact h
      · right; apply Fin.ext; exact h
    rcases hb with rfl | rfl <;> rcases hc with rfl | rfl
    · have hv := congrArg Fin.val hxy
      simp [mirrorBlockMap] at hv
      have hrs : r = s := by
        apply Fin.ext
        omega
      subst s
      rfl
    · have hv := congrArg Fin.val hxy
      simp [mirrorBlockMap] at hv
      omega
    · have hv := congrArg Fin.val hxy
      simp [mirrorBlockMap] at hv
      omega
    · have hv := congrArg Fin.val hxy
      simp [mirrorBlockMap] at hv
      have hrs : r = s := by
        apply Fin.ext
        omega
      subst s
      rfl
  · have hb : b = 0 ∨ b = 1 := by
      have : b.1 = 0 ∨ b.1 = 1 := by omega
      rcases this with h | h
      · left; apply Fin.ext; exact h
      · right; apply Fin.ext; exact h
    rcases hb with rfl | rfl <;>
      have hv := congrArg Fin.val hxy <;>
      simp [mirrorBlockMap] at hv <;> omega
  · have hc : c = 0 ∨ c = 1 := by
      have : c.1 = 0 ∨ c.1 = 1 := by omega
      rcases this with h | h
      · left; apply Fin.ext; exact h
      · right; apply Fin.ext; exact h
    rcases hc with rfl | rfl <;>
      have hv := congrArg Fin.val hxy <;>
      simp [mirrorBlockMap] at hv <;> omega
  · have huv : u = v := Subsingleton.elim _ _
    subst v
    rfl

def mirrorBlockEquiv (m : ℕ) :
    (Fin m × Fin 2) ⊕ Fin 1 ≃ Fin (2 * m + 1) :=
  Equiv.ofBijective (mirrorBlockMap m)
    ⟨mirrorBlockMap_injective m,
      (mirrorBlockMap_injective m).surjective_of_finite (pairBlockEquiv m)⟩

def mirrorPerm (m : ℕ) : Equiv.Perm (Fin (2 * m + 1)) :=
  (pairBlockEquiv m).symm.trans (mirrorBlockEquiv m)

@[simp] lemma mirrorPerm_left (m : ℕ) (r : Fin m) :
    mirrorPerm m (pairLeft m r) = ⟨m + 1 + r.1, by omega⟩ := by
  simp [mirrorPerm, mirrorBlockEquiv, mirrorBlockMap]

@[simp] lemma mirrorPerm_right (m : ℕ) (r : Fin m) :
    mirrorPerm m (pairRight m r) = ⟨m - 1 - r.1, by omega⟩ := by
  simp [mirrorPerm, mirrorBlockEquiv, mirrorBlockMap]

@[simp] lemma mirrorPerm_unmatched (m : ℕ) :
    mirrorPerm m (pairUnmatched m) = ⟨m, by omega⟩ := by
  simp [mirrorPerm, mirrorBlockEquiv, mirrorBlockMap]

lemma sum_over_standard_pairs {A : Type*} [AddCommMonoid A]
    (m : ℕ) (f : Fin (2 * m + 1) → A) :
    (∑ i, f i) =
      (∑ r : Fin m, (f (pairLeft m r) + f (pairRight m r))) +
        f (pairUnmatched m) := by
  rw [← Equiv.sum_comp (pairBlockEquiv m) f,
    Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp_rw [Fin.sum_univ_two]
  simp [pairBlockEquiv_left, pairBlockEquiv_right,
    pairBlockEquiv_unmatched]

lemma centeredExponent_sum (m : ℕ)
    (σ : Equiv.Perm (Fin (2 * m + 1))) :
    ∑ j, centeredExponent m σ j = 0 := by
  simp_rw [centeredExponent_apply]
  rw [Equiv.sum_comp σ.symm (fun i : Fin (2 * m + 1) =>
    ((i : ℤ) - (m : ℤ)))]
  let f : Fin (2 * m + 1) → ℤ := fun i => (i : ℤ) - (m : ℤ)
  have hpoint (i : Fin (2 * m + 1)) : f (Fin.revPerm i) = -f i := by
    change ((i.rev : Fin (2 * m + 1)) : ℤ) - (m : ℤ) =
      -((i : ℤ) - (m : ℤ))
    rw [Fin.val_rev]
    omega
  have hneg : (∑ i, f i) = -(∑ i, f i) := by
    calc
      (∑ i, f i) = ∑ i, f (Fin.revPerm i) :=
        (Equiv.sum_comp Fin.revPerm f).symm
      _ = ∑ i, -f i := by simp_rw [hpoint]
      _ = -(∑ i, f i) := by
        simpa using Finset.sum_neg_distrib (s := Finset.univ) f
  change (∑ i, f i) = 0
  omega

def kOnePairWeight (m : ℕ)
    (i j : Fin (2 * m + 1)) : ℚ :=
  if 0 < (i : ℤ) - (m : ℤ) ∧
      (j : ℤ) - (m : ℤ) = -((i : ℤ) - (m : ℤ)) then
    (-1 : ℚ) / (((i : ℤ) - (m : ℤ) : ℤ) : ℚ)
  else 0

lemma standardLogWeight_centeredExponent (m : ℕ)
    (σ : Equiv.Perm (Fin (2 * m + 1))) :
    standardLogWeight (kOneSetup m) (centeredExponent m σ) =
      ∏ r : Fin m,
        kOnePairWeight m (σ.symm (pairLeft m r))
          (σ.symm (pairRight m r)) := by
  let e := centeredExponent m σ
  let P : Fin m → Prop := fun r =>
    0 < e (pairLeft m r) ∧
      e (pairRight m r) = -e (pairLeft m r)
  by_cases hpairs : ∀ r, P r
  · have hpairsZero :
        ∑ r : Fin m, (e (pairLeft m r) + e (pairRight m r)) = 0 := by
      apply Finset.sum_eq_zero
      intro r hr
      rw [(hpairs r).2]
      simp
    have hsum := centeredExponent_sum m σ
    rw [sum_over_standard_pairs m e, hpairsZero, zero_add] at hsum
    have hlast : e (pairUnmatched m) = 0 := hsum
    have hadm : StandardLogAdmissible (kOneSetup m) e := by
      constructor
      · intro r
        simpa [P, e, kOneSetup, Setup.leftVertex, Setup.rightVertex,
          pairLeft, pairRight] using hpairs r
      · simpa [e, kOneSetup, Setup.lastVertex, pairUnmatched] using hlast
    rw [standardLogWeight]
    rw [if_pos hadm]
    apply Finset.prod_congr rfl
    intro r hr
    have hpr := hpairs r
    simp only [P, e] at hpr
    change (-1 : ℚ) / (e (pairLeft m r) : ℚ) =
      kOnePairWeight m (σ.symm (pairLeft m r))
        (σ.symm (pairRight m r))
    rw [kOnePairWeight, if_pos]
    · simp [e, centeredExponent_apply]
    · simpa [e, centeredExponent_apply] using hpr
  · have hadm : ¬StandardLogAdmissible (kOneSetup m) e := by
      intro h
      apply hpairs
      intro r
      simpa [P, e, kOneSetup, Setup.leftVertex, Setup.rightVertex,
        pairLeft, pairRight] using h.1 r
    rw [standardLogWeight]
    rw [if_neg hadm]
    push_neg at hpairs
    obtain ⟨r, hr⟩ := hpairs
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ r)
    simp only [kOnePairWeight, centeredExponent_apply]
    rw [if_neg]
    simpa [P, e, centeredExponent_apply] using hr

lemma standardLogCT_fintype_sum {I : Type*} [Fintype I]
    (S : Setup) (F : I → Laurent ℚ S.n) :
    standardLogCT S (∑ i, F i) = ∑ i, standardLogCT S (F i) := by
  simpa using standardLogCT_sum S (Finset.univ : Finset I) F

lemma logarithmicMorrisLHS_kOne_as_sum (m : ℕ) :
    logarithmicMorrisLHS (kOneSetup m) =
      ∑ σ : Equiv.Perm (Fin (2 * m + 1)),
        ((-1 : ℚ) ^ (m * (2 * m + 1)) * ((σ.sign : ℤ) : ℚ)) *
          ∏ r : Fin m,
            kOnePairWeight m (σ.symm (pairLeft m r))
              (σ.symm (pairRight m r)) := by
  rw [logarithmicMorrisLHS, morrisKernel_kOne_expansion,
    standardLogCT_fintype_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [standardLogCT_monomial, standardLogWeight_centeredExponent]

def pairedAlternatingSumQ (m : ℕ)
    (A : Fin (2 * m + 1) → Fin (2 * m + 1) → ℚ) : ℚ :=
  ∑ σ : Equiv.Perm (Fin (2 * m + 1)),
    ((σ.sign : ℤ) : ℚ) *
      ∏ r : Fin m, A (σ (pairLeft m r)) (σ (pairRight m r))

lemma logarithmicMorrisLHS_kOne_eq_paired (m : ℕ) :
    logarithmicMorrisLHS (kOneSetup m) =
      (-1 : ℚ) ^ (m * (2 * m + 1)) *
        pairedAlternatingSumQ m (kOnePairWeight m) := by
  rw [logarithmicMorrisLHS_kOne_as_sum]
  unfold pairedAlternatingSumQ
  let g : Equiv.Perm (Fin (2 * m + 1)) → ℚ := fun τ =>
    (((τ.sign : ℤ) : ℚ) *
      ∏ r : Fin m,
        kOnePairWeight m (τ (pairLeft m r)) (τ (pairRight m r)))
  have hinv := Equiv.sum_comp
    (Equiv.inv (Equiv.Perm (Fin (2 * m + 1)))) g
  have hinv' :
      (∑ σ : Equiv.Perm (Fin (2 * m + 1)),
          (((σ.sign : ℤ) : ℚ) *
            ∏ r : Fin m,
              kOnePairWeight m (σ.symm (pairLeft m r))
                (σ.symm (pairRight m r)))) =
        ∑ σ : Equiv.Perm (Fin (2 * m + 1)), g σ := by
    simpa [g, Equiv.Perm.sign_symm] using hinv
  rw [← hinv']
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  ring

lemma pairedAlternatingSumQ_cast (m : ℕ)
    (A : Fin (2 * m + 1) → Fin (2 * m + 1) → ℚ) :
    ((pairedAlternatingSumQ m A : ℚ) : ℂ) =
      pairedAlternatingSum m (fun i j => (A i j : ℂ)) := by
  unfold pairedAlternatingSumQ pairedAlternatingSum
  push_cast
  rfl

def blockPairWeightQ (m : ℕ)
    (i j : Fin (2 * m + 1)) : ℚ := by
  classical
  exact if h : ∃ r : Fin m,
      i = pairLeft m r ∧ j = pairRight m r then
    (-1 : ℚ) / ((Classical.choose h).1 + 1 : ℚ)
  else 0

lemma pairLeft_injective (m : ℕ) :
    Function.Injective (pairLeft m) := by
  intro r s h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [pairLeft] at hv
  omega

lemma blockPairWeightQ_of_pair (m : ℕ) (r : Fin m) :
    blockPairWeightQ m (pairLeft m r) (pairRight m r) =
      (-1 : ℚ) / ((r.1 + 1 : ℕ) : ℚ) := by
  rw [blockPairWeightQ]
  split_ifs with h
  · have hr : Classical.choose h = r := by
      apply pairLeft_injective m
      exact (Classical.choose_spec h).1.symm
    rw [hr]
    push_cast
    congr 1
  · exact (h ⟨r, rfl, rfl⟩).elim

lemma blockPairWeightQ_ne_zero_iff (m : ℕ)
    (i j : Fin (2 * m + 1)) :
    blockPairWeightQ m i j ≠ 0 ↔
      ∃ r : Fin m, i = pairLeft m r ∧ j = pairRight m r := by
  rw [blockPairWeightQ]
  split_ifs with h
  · refine ⟨fun _ => h, fun _ => ?_⟩
    apply div_ne_zero
    · norm_num
    · positivity
  · simp [h]

def PairBlockMapped (m : ℕ)
    (σ : Equiv.Perm (Fin (2 * m + 1))) : Prop :=
  ∀ r : Fin m, ∃ j : Fin m,
    σ (pairLeft m r) = pairLeft m j ∧
      σ (pairRight m r) = pairRight m j

lemma pairBlockMapped_of_blockSurvivor (m : ℕ)
    (σ : Equiv.Perm (Fin (2 * m + 1)))
    (hσ : BlockSurvivor m σ) : PairBlockMapped m σ := by
  rw [← blockPerm_survivorBlockPerm m σ hσ]
  intro r
  exact ⟨survivorBlockPerm m σ hσ r, by simp, by simp⟩

lemma blockSurvivor_of_pairBlockMapped (m : ℕ)
    (σ : Equiv.Perm (Fin (2 * m + 1)))
    (hσ : PairBlockMapped m σ) : BlockSurvivor m σ := by
  let φ : Fin m → Fin m := fun r => Classical.choose (hσ r)
  have hφ (r : Fin m) :
      σ (pairLeft m r) = pairLeft m (φ r) ∧
        σ (pairRight m r) = pairRight m (φ r) :=
    Classical.choose_spec (hσ r)
  have hinj : Function.Injective φ := by
    intro r s hrs
    apply pairLeft_injective m
    apply σ.injective
    rw [(hφ r).1, (hφ s).1, hrs]
  have hsurj : Function.Surjective φ := Finite.surjective_of_injective hinj
  intro j
  obtain ⟨r, hr⟩ := hsurj j
  exact ⟨r, by simpa [hr] using (hφ r).1,
    by simpa [hr] using (hφ r).2⟩

lemma pairBlockMapped_iff_blockSurvivor (m : ℕ)
    (σ : Equiv.Perm (Fin (2 * m + 1))) :
    PairBlockMapped m σ ↔ BlockSurvivor m σ :=
  ⟨blockSurvivor_of_pairBlockMapped m σ,
    pairBlockMapped_of_blockSurvivor m σ⟩

lemma blockPairWeightQ_prod_base (m : ℕ) :
    (∏ r : Fin m,
      blockPairWeightQ m (pairLeft m r) (pairRight m r)) =
        (-1 : ℚ) ^ m / (m.factorial : ℚ) := by
  simp_rw [blockPairWeightQ_of_pair]
  rw [Finset.prod_div_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  rw [Finset.prod_fin_eq_prod_range]
  have hprod :
      (∏ i ∈ Finset.range m,
          if h : i < m then (((⟨i, h⟩ : Fin m).1 + 1 : ℕ) : ℚ) else 1) =
        ∏ i ∈ Finset.range m, ((i + 1 : ℕ) : ℚ) := by
    apply Finset.prod_congr rfl
    intro i hi
    simp [Finset.mem_range.mp hi]
  rw [hprod, ← Nat.cast_prod]
  rw [← Nat.factorial_eq_prod_range_add_one]

lemma blockPairWeightQ_pair_product (m : ℕ)
    (σ : Equiv.Perm (Fin (2 * m + 1))) :
    (∏ r : Fin m,
      blockPairWeightQ m (σ (pairLeft m r)) (σ (pairRight m r))) =
        if BlockSurvivor m σ then
          (-1 : ℚ) ^ m / (m.factorial : ℚ)
        else 0 := by
  classical
  by_cases hσ : BlockSurvivor m σ
  · rw [if_pos hσ]
    let τ := survivorBlockPerm m σ hσ
    have heq := blockPerm_survivorBlockPerm m σ hσ
    rw [← heq]
    simp_rw [blockPerm_left, blockPerm_right, blockPairWeightQ_of_pair]
    rw [Equiv.prod_comp τ (fun r : Fin m =>
      (-1 : ℚ) / ((r.1 + 1 : ℕ) : ℚ))]
    simpa only [blockPairWeightQ_of_pair] using blockPairWeightQ_prod_base m
  · rw [if_neg hσ]
    have hmap : ¬PairBlockMapped m σ := by
      simpa [pairBlockMapped_iff_blockSurvivor] using hσ
    unfold PairBlockMapped at hmap
    push_neg at hmap
    obtain ⟨r, hr⟩ := hmap
    apply Finset.prod_eq_zero (Finset.mem_univ r)
    by_contra hn
    obtain ⟨j, hj⟩ :=
      (blockPairWeightQ_ne_zero_iff m
        (σ (pairLeft m r)) (σ (pairRight m r))).mp hn
    exact hr j hj.1 hj.2

lemma pairOriented_of_blockSurvivor (m : ℕ)
    (σ : Equiv.Perm (Fin (2 * m + 1)))
    (hσ : BlockSurvivor m σ) : PairOriented m σ := by
  have hmap := pairBlockMapped_of_blockSurvivor m σ hσ
  intro r
  obtain ⟨j, hj⟩ := hmap r
  rw [hj.1, hj.2]
  apply Fin.mk_lt_mk.mpr
  simp [pairLeft, pairRight]

lemma filter_blockSurvivor_eq_orientedSurvivorPerms (m : ℕ) :
    (Finset.univ : Finset (Equiv.Perm (Fin (2 * m + 1)))).filter
        (BlockSurvivor m) = orientedSurvivorPerms m := by
  ext σ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    orientedSurvivorPerms]
  constructor
  · intro h
    exact ⟨pairOriented_of_blockSurvivor m σ h, h⟩
  · intro h
    exact h.2

lemma sum_sign_blockSurvivor_Q (m : ℕ) :
    (∑ σ ∈ (Finset.univ :
        Finset (Equiv.Perm (Fin (2 * m + 1)))).filter (BlockSurvivor m),
      ((σ.sign : ℤ) : ℚ)) = (m.factorial : ℚ) := by
  rw [filter_blockSurvivor_eq_orientedSurvivorPerms]
  calc
    (∑ σ ∈ orientedSurvivorPerms m, ((σ.sign : ℤ) : ℚ)) =
        ∑ _σ ∈ orientedSurvivorPerms m, (1 : ℚ) := by
      apply Finset.sum_congr rfl
      intro σ hσ
      rw [orientedSurvivorPerms_sign_one m hσ]
      norm_num
    _ = (m.factorial : ℚ) := by
      simp [card_orientedSurvivorPerms]

lemma pairedAlternatingSumQ_blockPairWeightQ (m : ℕ) :
    pairedAlternatingSumQ m (blockPairWeightQ m) = (-1 : ℚ) ^ m := by
  classical
  unfold pairedAlternatingSumQ
  simp_rw [blockPairWeightQ_pair_product]
  simp only [mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  rw [← Finset.sum_mul]
  rw [sum_sign_blockSurvivor_Q]
  have hfac : (m.factorial : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero m
  field_simp [hfac]

lemma pairRight_injective (m : ℕ) :
    Function.Injective (pairRight m) := by
  intro r s h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [pairRight] at hv
  omega

lemma blockPairWeightQ_left_right (m : ℕ) (r s : Fin m) :
    blockPairWeightQ m (pairLeft m r) (pairRight m s) =
      if r = s then (-1 : ℚ) / ((r.1 + 1 : ℕ) : ℚ) else 0 := by
  by_cases hrs : r = s
  · subst s
    rw [if_pos rfl, blockPairWeightQ_of_pair]
  · rw [if_neg hrs, blockPairWeightQ]
    split_ifs with h
    · have hr := (pairLeft_injective m) (Classical.choose_spec h).1
      have hs := (pairRight_injective m) (Classical.choose_spec h).2
      exact (hrs (hr.trans hs.symm)).elim
    · rfl

lemma blockPairWeightQ_right_zero (m : ℕ) (r : Fin m)
    (y : Fin (2 * m + 1)) :
    blockPairWeightQ m (pairRight m r) y = 0 := by
  rw [blockPairWeightQ]
  split_ifs with h
  · have hv := congrArg Fin.val (Classical.choose_spec h).1
    simp only [pairLeft, pairRight] at hv
    omega
  · rfl

lemma blockPairWeightQ_unmatched_left_zero (m : ℕ)
    (y : Fin (2 * m + 1)) :
    blockPairWeightQ m (pairUnmatched m) y = 0 := by
  rw [blockPairWeightQ]
  split_ifs with h
  · exact (pairLeft_ne_unmatched m (Classical.choose h)
      (Classical.choose_spec h).1.symm).elim
  · rfl

lemma blockPairWeightQ_left_as_right_zero (m : ℕ)
    (x : Fin (2 * m + 1)) (s : Fin m) :
    blockPairWeightQ m x (pairLeft m s) = 0 := by
  rw [blockPairWeightQ]
  split_ifs with h
  · have hv := congrArg Fin.val (Classical.choose_spec h).2
    simp only [pairLeft, pairRight] at hv
    omega
  · rfl

lemma blockPairWeightQ_unmatched_right_zero (m : ℕ)
    (x : Fin (2 * m + 1)) :
    blockPairWeightQ m x (pairUnmatched m) = 0 := by
  rw [blockPairWeightQ]
  split_ifs with h
  · exact (pairRight_ne_unmatched m (Classical.choose h)
      (Classical.choose_spec h).2.symm).elim
  · rfl

lemma fin_eq_pairLeft_or_pairRight_or_unmatched (m : ℕ)
    (x : Fin (2 * m + 1)) :
    (∃ r : Fin m, x = pairLeft m r) ∨
      (∃ r : Fin m, x = pairRight m r) ∨
        x = pairUnmatched m := by
  obtain ⟨z, rfl⟩ := (pairBlockEquiv m).surjective x
  rcases z with ⟨r, b⟩ | u
  · have hb : b = 0 ∨ b = 1 := by
      have : b.1 = 0 ∨ b.1 = 1 := by omega
      rcases this with h | h
      · left; apply Fin.ext; exact h
      · right; apply Fin.ext; exact h
    rcases hb with rfl | rfl
    · left
      exact ⟨r, pairBlockEquiv_left m r⟩
    · right; left
      exact ⟨r, pairBlockEquiv_right m r⟩
  · right; right
    have hu : u = 0 := Subsingleton.elim _ _
    subst u
    exact pairBlockEquiv_unmatched m

@[simp] lemma mirrorPerm_left_centered (m : ℕ) (r : Fin m) :
    ((mirrorPerm m (pairLeft m r) : Fin (2 * m + 1)) : ℤ) - (m : ℤ) =
      (r.1 + 1 : ℕ) := by
  rw [mirrorPerm_left]
  push_cast
  ring

@[simp] lemma mirrorPerm_right_centered (m : ℕ) (r : Fin m) :
    ((mirrorPerm m (pairRight m r) : Fin (2 * m + 1)) : ℤ) - (m : ℤ) =
      -((r.1 + 1 : ℕ) : ℤ) := by
  rw [mirrorPerm_right]
  have hmr : r.1 < m := r.isLt
  have hm : 1 ≤ m := by omega
  have hr : r.1 ≤ m - 1 := by omega
  rw [Nat.cast_sub hr, Nat.cast_sub hm]
  push_cast
  ring

@[simp] lemma mirrorPerm_unmatched_centered (m : ℕ) :
    ((mirrorPerm m (pairUnmatched m) : Fin (2 * m + 1)) : ℤ) - (m : ℤ) = 0 := by
  rw [mirrorPerm_unmatched]
  simp

lemma kOnePairWeight_mirrorPerm (m : ℕ)
    (x y : Fin (2 * m + 1)) :
    kOnePairWeight m (mirrorPerm m x) (mirrorPerm m y) =
      blockPairWeightQ m x y := by
  rcases fin_eq_pairLeft_or_pairRight_or_unmatched m x with
    ⟨r, rfl⟩ | ⟨r, rfl⟩ | rfl <;>
  rcases fin_eq_pairLeft_or_pairRight_or_unmatched m y with
    ⟨s, rfl⟩ | ⟨s, rfl⟩ | rfl
  · rw [blockPairWeightQ_left_as_right_zero]
    rw [kOnePairWeight, mirrorPerm_left_centered, mirrorPerm_left_centered]
    simp
    omega
  · rw [blockPairWeightQ_left_right]
    rw [kOnePairWeight, mirrorPerm_left_centered, mirrorPerm_right_centered]
    simp [Fin.ext_iff, eq_comm]
  · rw [blockPairWeightQ_unmatched_right_zero]
    rw [kOnePairWeight, mirrorPerm_left_centered,
      mirrorPerm_unmatched_centered]
    simp
    omega
  · rw [blockPairWeightQ_right_zero]
    rw [kOnePairWeight, mirrorPerm_right_centered,
      mirrorPerm_left_centered]
    simp
  · rw [blockPairWeightQ_right_zero]
    rw [kOnePairWeight, mirrorPerm_right_centered,
      mirrorPerm_right_centered]
    simp
  · rw [blockPairWeightQ_right_zero]
    rw [kOnePairWeight, mirrorPerm_right_centered,
      mirrorPerm_unmatched_centered]
    simp
  · rw [blockPairWeightQ_unmatched_left_zero]
    rw [kOnePairWeight, mirrorPerm_unmatched_centered,
      mirrorPerm_left_centered]
    simp
  · rw [blockPairWeightQ_unmatched_left_zero]
    rw [kOnePairWeight, mirrorPerm_unmatched_centered,
      mirrorPerm_right_centered]
    simp
  · rw [blockPairWeightQ_unmatched_left_zero]
    rw [kOnePairWeight, mirrorPerm_unmatched_centered]
    simp

lemma kOnePairWeight_eq_relabel (m : ℕ)
    (i j : Fin (2 * m + 1)) :
    kOnePairWeight m i j =
      blockPairWeightQ m ((mirrorPerm m).symm i) ((mirrorPerm m).symm j) := by
  have h := kOnePairWeight_mirrorPerm m
    ((mirrorPerm m).symm i) ((mirrorPerm m).symm j)
  simpa using h

lemma pairedAlternatingSumQ_relabel (m : ℕ)
    (ρ : Equiv.Perm (Fin (2 * m + 1)))
    (A : Fin (2 * m + 1) → Fin (2 * m + 1) → ℚ) :
    pairedAlternatingSumQ m
        (fun i j => A (ρ.symm i) (ρ.symm j)) =
      (((ρ.sign : ℤ) : ℚ) * pairedAlternatingSumQ m A) := by
  unfold pairedAlternatingSumQ
  let F : Equiv.Perm (Fin (2 * m + 1)) → ℚ := fun σ =>
    (((σ.sign : ℤ) : ℚ) *
      ∏ r : Fin m,
        A (ρ.symm (σ (pairLeft m r)))
          (ρ.symm (σ (pairRight m r))))
  have hreindex := Equiv.sum_comp (Equiv.mulLeft ρ) F
  change (∑ σ, F σ) = _
  rw [← hreindex]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  simp only [F]
  rw [show (Equiv.mulLeft ρ) σ = ρ * σ by rfl]
  rw [Equiv.Perm.sign_mul]
  simp only [Equiv.Perm.coe_mul, Function.comp_apply,
    Equiv.symm_apply_apply]
  push_cast
  ring

lemma pairedAlternatingSumQ_kOnePairWeight (m : ℕ) :
    pairedAlternatingSumQ m (kOnePairWeight m) =
      (((mirrorPerm m).sign : ℤ) : ℚ) * (-1 : ℚ) ^ m := by
  rw [show kOnePairWeight m = fun i j =>
      blockPairWeightQ m ((mirrorPerm m).symm i)
        ((mirrorPerm m).symm j) by
    funext i j
    exact kOnePairWeight_eq_relabel m i j]
  rw [pairedAlternatingSumQ_relabel,
    pairedAlternatingSumQ_blockPairWeightQ]

def mirrorSignFactor (m : ℕ)
    (i j : Fin (2 * m + 1)) : ℤˣ :=
  if mirrorPerm m i < mirrorPerm m j then 1 else -1

lemma mirrorSignFactor_left_right (m : ℕ) (r : Fin m) :
    mirrorSignFactor m (pairLeft m r) (pairRight m r) = -1 := by
  rw [mirrorSignFactor, if_neg]
  simp only [mirrorPerm_left, mirrorPerm_right, not_lt]
  apply Fin.mk_le_mk.mpr
  omega

lemma mirrorSignFactor_pair_mul (m : ℕ) (r : Fin m)
    (j : Fin (2 * m + 1)) (h : pairRight m r < j) :
    mirrorSignFactor m (pairLeft m r) j *
        mirrorSignFactor m (pairRight m r) j =
      if j = pairUnmatched m then -1 else 1 := by
  rcases fin_eq_pairLeft_or_pairRight_or_unmatched m j with
    ⟨s, rfl⟩ | ⟨s, rfl⟩ | rfl
  · have hrs : r < s := by
      apply Fin.mk_lt_mk.mpr
      have hv := Fin.mk_lt_mk.mp h
      simp only [pairLeft, pairRight] at hv
      omega
    rw [if_neg (pairLeft_ne_unmatched m s)]
    unfold mirrorSignFactor
    rw [if_pos, if_pos]
    · norm_num
    · simp only [mirrorPerm_right, mirrorPerm_left]
      apply Fin.mk_lt_mk.mpr
      omega
    · simp only [mirrorPerm_left]
      apply Fin.mk_lt_mk.mpr
      omega
  · have hrs : r < s := by
      apply Fin.mk_lt_mk.mpr
      have hv := Fin.mk_lt_mk.mp h
      simp only [pairRight] at hv
      omega
    rw [if_neg (pairRight_ne_unmatched m s)]
    unfold mirrorSignFactor
    rw [if_neg, if_neg]
    · norm_num
    · simp only [mirrorPerm_right, not_lt]
      apply Fin.mk_le_mk.mpr
      omega
    · simp only [mirrorPerm_left, mirrorPerm_right, not_lt]
      apply Fin.mk_le_mk.mpr
      omega
  · rw [if_pos rfl]
    unfold mirrorSignFactor
    rw [if_neg, if_pos]
    · norm_num
    · simp only [mirrorPerm_right, mirrorPerm_unmatched]
      apply Fin.mk_lt_mk.mpr
      omega
    · simp only [mirrorPerm_left, mirrorPerm_unmatched, not_lt]
      apply Fin.mk_le_mk.mpr
      omega

lemma mirrorSignFactor_inner_pair (m : ℕ) (r : Fin m) :
    (∏ j ∈ Finset.Ioi (pairLeft m r),
        mirrorSignFactor m (pairLeft m r) j) *
      (∏ j ∈ Finset.Ioi (pairRight m r),
        mirrorSignFactor m (pairRight m r) j) = 1 := by
  have hIoi : Finset.Ioi (pairLeft m r) =
      insert (pairRight m r) (Finset.Ioi (pairRight m r)) := by
    ext j
    simp only [Finset.mem_Ioi, Finset.mem_insert]
    constructor
    · intro h
      by_cases hj : j = pairRight m r
      · exact Or.inl hj
      · right
        apply Fin.mk_lt_mk.mpr
        have hv := Fin.mk_lt_mk.mp h
        have hjv : j.1 ≠ 2 * r.1 + 1 := by
          intro heq
          apply hj
          apply Fin.ext
          simpa [pairRight] using heq
        simp only [pairLeft] at hv
        omega
    · intro h
      rcases h with rfl | h
      · apply Fin.mk_lt_mk.mpr
        simp [pairLeft, pairRight]
      · exact lt_trans (by
          apply Fin.mk_lt_mk.mpr
          simp [pairLeft, pairRight]) h
  rw [hIoi, Finset.prod_insert (by simp)]
  rw [mul_assoc, ← Finset.prod_mul_distrib]
  rw [mirrorSignFactor_left_right]
  have hprod :
      (∏ j ∈ Finset.Ioi (pairRight m r),
        mirrorSignFactor m (pairLeft m r) j *
          mirrorSignFactor m (pairRight m r) j) = -1 := by
    calc
      _ = ∏ j ∈ Finset.Ioi (pairRight m r),
          if j = pairUnmatched m then (-1 : ℤˣ) else 1 := by
        apply Finset.prod_congr rfl
        intro j hj
        exact mirrorSignFactor_pair_mul m r j (Finset.mem_Ioi.mp hj)
      _ = -1 := by
        rw [Finset.prod_ite_eq' _ (pairUnmatched m)
          (fun _ => (-1 : ℤˣ))]
        simp only [Finset.mem_Ioi]
        rw [if_pos]
        apply Fin.mk_lt_mk.mpr
        change 2 * r.1 + 1 < 2 * m
        omega
  rw [hprod]
  norm_num

lemma prod_over_standard_pairs {A : Type*} [CommMonoid A]
    (m : ℕ) (f : Fin (2 * m + 1) → A) :
    (∏ i, f i) =
      (∏ r : Fin m, (f (pairLeft m r) * f (pairRight m r))) *
        f (pairUnmatched m) := by
  rw [← Equiv.prod_comp (pairBlockEquiv m) f,
    Fintype.prod_sum_type, Fintype.prod_prod_type]
  simp_rw [Fin.prod_univ_two]
  simp [pairBlockEquiv_left, pairBlockEquiv_right,
    pairBlockEquiv_unmatched]

lemma mirrorPerm_sign (m : ℕ) : (mirrorPerm m).sign = 1 := by
  rw [Equiv.Perm.sign_eq_prod_prod_Ioi]
  let f : Fin (2 * m + 1) → ℤˣ := fun i =>
    ∏ j ∈ Finset.Ioi i, mirrorSignFactor m i j
  change (∏ i, f i) = 1
  rw [prod_over_standard_pairs m f]
  have hpairs :
      ∏ r : Fin m, (f (pairLeft m r) * f (pairRight m r)) = 1 := by
    apply Finset.prod_eq_one
    intro r hr
    exact mirrorSignFactor_inner_pair m r
  rw [hpairs, one_mul]
  have hlast : Finset.Ioi (pairUnmatched m) = ∅ := by
    ext j
    simp only [Finset.mem_Ioi, Finset.notMem_empty, iff_false]
    apply not_lt_of_ge
    apply Fin.mk_le_mk.mpr
    have hj := j.isLt
    change j.1 ≤ 2 * m
    omega
  simp [f, hlast]

lemma pairedAlternatingSumQ_kOnePairWeight_eq (m : ℕ) :
    pairedAlternatingSumQ m (kOnePairWeight m) = (-1 : ℚ) ^ m := by
  rw [pairedAlternatingSumQ_kOnePairWeight, mirrorPerm_sign]
  norm_num

theorem logarithmicMorrisLHS_kOne (m : ℕ) :
    logarithmicMorrisLHS (kOneSetup m) = 1 := by
  rw [logarithmicMorrisLHS_kOne_eq_paired,
    pairedAlternatingSumQ_kOnePairWeight_eq, ← pow_add]
  apply Even.neg_one_pow
  refine ⟨m * (m + 1), ?_⟩
  ring

theorem logarithmicMorrisLHS_dyson_zero_proved (S : Setup) :
    logarithmicMorrisLHS (dysonSetup S 0) = 1 := by
  rw [dysonSetup_zero_eq]
  exact logarithmicMorrisLHS_kOne S.m

theorem circularMorrisIntegral_dyson_zero_proved (S : Setup) :
    circularMorrisIntegral (dysonSetup S 0) =
      gammaPochhammerPart (dysonSetup S 0) (dysonSetup S 0).K := by
  exact circularMorrisIntegral_dyson_zero_of_lhs_one S
    (logarithmicMorrisLHS_dyson_zero_proved S)

end LogarithmicMorrisFull
