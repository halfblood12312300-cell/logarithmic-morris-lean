import logarithmicmorris.ScratchCircleLogFourier
import logarithmicmorris.ScratchPairedLogIntegrable

noncomputable section

set_option maxHeartbeats 800000

open scoped BigOperators
open MeasureTheory

namespace LogarithmicMorrisFull

theorem integral_fourier_eq_ite (q : ℤ) :
    (∫ t : UnitAddCircle, fourier q t) = if q = 0 then 1 else 0 := by
  rw [unitVolume_eq_haar]
  have h := congrFun (fourierCoeff_fourier (T := (1 : ℝ)) q) 0
  rw [fourierCoeff] at h
  simpa [Pi.single_apply, eq_comm] using h

theorem fourier_add_argument (q : ℤ) (x y : UnitAddCircle) :
    fourier q (x + y) = fourier q x * fourier q y := by
  simp only [fourier_apply, smul_add, AddCircle.toCircle_add, Circle.coe_mul]

theorem pairLog_fourierIntegral (a b : ℤ) :
    (∫ z : UnitAddCircle × UnitAddCircle,
      fourier a z.1 * fourier b z.2 * circleLog (z.2 - z.1)) =
      if 0 < a ∧ b = -a then -(1 : ℂ) / (a : ℂ) else 0 := by
  let g : UnitAddCircle × UnitAddCircle → ℂ := fun z =>
    fourier a z.1 * fourier b z.2 * circleLog (z.2 - z.1)
  have hemb : MeasurableEmbedding
      (fun z : UnitAddCircle × UnitAddCircle => (z.1, z.2 + z.1)) :=
    by
      simpa [add_comm] using
        (MeasurableEquiv.shearAddRight UnitAddCircle).measurableEmbedding
  have hchange := (measurePreserving_prod_add_right
    (volume : Measure UnitAddCircle) (volume : Measure UnitAddCircle)).integral_comp
      hemb g
  rw [← MeasureTheory.Measure.volume_eq_prod] at hchange
  have hpoint : (fun z : UnitAddCircle × UnitAddCircle =>
      g (z.1, z.2 + z.1)) = fun z =>
        fourier (a + b) z.1 * (fourier b z.2 * circleLog z.2) := by
    funext z
    simp only [g, add_sub_cancel_right]
    rw [fourier_add_argument, fourier_add]
    ring
  have hfactor :
      (∫ z : UnitAddCircle × UnitAddCircle,
          fourier (a + b) z.1 * (fourier b z.2 * circleLog z.2)) =
        (∫ x : UnitAddCircle, fourier (a + b) x) *
          ∫ y : UnitAddCircle, fourier b y * circleLog y := by
    exact integral_prod_mul
      (fun x : UnitAddCircle => fourier (a + b) x)
      (fun y : UnitAddCircle => fourier b y * circleLog y)
  rw [hpoint, hfactor] at hchange
  rw [integral_fourier_eq_ite, circleLog_fourierIntegral] at hchange
  rw [← hchange]
  by_cases hab : a + b = 0
  · have hb : b = -a := by omega
    subst b
    by_cases ha : 0 < a
    · have hneg : -a < 0 := by omega
      simp [ha, hneg]
      push_cast
      ring
    · have hnneg : ¬(-a < 0) := by omega
      simp [ha, hnneg]
  · simp only [hab, if_false, zero_mul]
    by_cases hpair : 0 < a ∧ b = -a
    · exact (hab (by omega)).elim
    · simp [hpair]

def finFourierProduct (q : ℕ) (d : Fin q → ℤ)
    (t : UnitAddTorus (Fin q)) : ℂ :=
  ∏ i : Fin q, fourier (d i) (t i)

def finPairedFourierWeight (m : ℕ) (d : Fin (2 * m) → ℤ) : ℂ :=
  ∏ r : Fin m,
    if 0 < d (finPairLeft m r) ∧
        d (finPairRight m r) = -d (finPairLeft m r) then
      -(1 : ℂ) / (d (finPairLeft m r) : ℂ)
    else 0

theorem finFourierProduct_cons_cons (m : ℕ) (d : Fin (2 * m + 2) → ℤ)
    (x y : UnitAddCircle) (t : UnitAddTorus (Fin (2 * m))) :
    finFourierProduct (2 * m + 2) d (Fin.cons x (Fin.cons y t)) =
      fourier (d 0) x * fourier (d 1) y *
        finFourierProduct (2 * m) (fun i => d i.succ.succ) t := by
  unfold finFourierProduct
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  have hs : Fin.succ (0 : Fin (2 * m + 1)) = (1 : Fin (2 * m + 2)) := by
    ext
    rfl
  rw [hs]
  ring

theorem finPairedFourierWeight_succ (m : ℕ)
    (d : Fin (2 * (m + 1)) → ℤ) :
    finPairedFourierWeight (m + 1) d =
      (if 0 < d 0 ∧ d 1 = -d 0 then -(1 : ℂ) / (d 0 : ℂ) else 0) *
        finPairedFourierWeight m (fun i => d i.succ.succ) := by
  simp only [finPairedFourierWeight, Fin.prod_univ_succ]
  congr 1

theorem finPairedFourierIntegral (m : ℕ) (d : Fin (2 * m) → ℤ) :
    (∫ t : UnitAddTorus (Fin (2 * m)),
      finFourierProduct (2 * m) d t * finPairedLog m t) =
      finPairedFourierWeight m d := by
  induction m with
  | zero =>
      simp only [finFourierProduct, finPairedLog, finPairedFourierWeight,
        Finset.univ_eq_empty, Finset.prod_empty, mul_one]
      change (∫ _ : UnitAddTorus (Fin 0), (1 : ℂ)) = 1
      rw [MeasureTheory.Measure.volume_pi_eq_dirac]
      simp
  | succ m ih =>
      let tail : Fin (2 * m) → ℤ := fun i => d i.succ.succ
      let G : UnitAddCircle ×
          (UnitAddCircle × UnitAddTorus (Fin (2 * m))) → ℂ := fun z =>
        (fourier (d 0) z.1 * fourier (d 1) z.2.1 *
          circleLog (z.2.1 - z.1)) *
        (finFourierProduct (2 * m) tail z.2.2 * finPairedLog m z.2.2)
      have hchange := (splitTwoEquiv_measurePreserving (2 * m)).integral_comp'
        G
      have heq : (fun t : UnitAddTorus (Fin (2 * (m + 1))) =>
          G (splitTwoEquiv (2 * m) t)) = fun t =>
          finFourierProduct (2 * (m + 1)) d t * finPairedLog (m + 1) t := by
        funext t
        obtain ⟨z, rfl⟩ := (splitTwoEquiv (2 * m)).symm.surjective t
        rcases z with ⟨x, y, u⟩
        rw [(splitTwoEquiv (2 * m)).apply_symm_apply]
        have hinv : (splitTwoEquiv (2 * m)).symm (x, y, u) =
            Fin.cons x (Fin.cons y u) := by
          change (MeasurableEquiv.piFinSuccAbove
              (fun _ : Fin (2 * m + 2) => UnitAddCircle) 0).symm
              (x, (MeasurableEquiv.piFinSuccAbove
                (fun _ : Fin (2 * m + 1) => UnitAddCircle) 0).symm (y, u)) =
            Fin.cons x (Fin.cons y u)
          simp only [MeasurableEquiv.piFinSuccAbove_symm_apply,
            Fin.insertNthEquiv, Fin.insertNth_zero]
          simp
        rw [hinv]
        have hfourier :
            finFourierProduct (2 * (m + 1)) d (Fin.cons x (Fin.cons y u)) =
              fourier (d 0) x * fourier (d 1) y *
                finFourierProduct (2 * m) (fun i => d i.succ.succ) u := by
          let d' : Fin (2 * m + 2) → ℤ := fun i => d ⟨i.1, by omega⟩
          simpa [d', Nat.mul_add] using
            (finFourierProduct_cons_cons m d' x y u)
        rw [hfourier, finPairedLog_cons_cons]
        simp only [G, tail]
        ring
      have hchange' :
          (∫ t : UnitAddTorus (Fin (2 * (m + 1))),
            finFourierProduct (2 * (m + 1)) d t * finPairedLog (m + 1) t) =
            ∫ z : UnitAddCircle ×
              (UnitAddCircle × UnitAddTorus (Fin (2 * m))), G z := by
        rw [← heq]
        exact hchange
      have hfactor : (∫ z : UnitAddCircle ×
            (UnitAddCircle × UnitAddTorus (Fin (2 * m))), G z) =
          (∫ z : UnitAddCircle × UnitAddCircle,
            fourier (d 0) z.1 * fourier (d 1) z.2 *
              circleLog (z.2 - z.1)) *
          (∫ t : UnitAddTorus (Fin (2 * m)),
            finFourierProduct (2 * m) tail t * finPairedLog m t) := by
        let pairPart : UnitAddCircle × UnitAddCircle → ℂ := fun z =>
          fourier (d 0) z.1 * fourier (d 1) z.2 * circleLog (z.2 - z.1)
        let tailPart : UnitAddTorus (Fin (2 * m)) → ℂ := fun t =>
          finFourierProduct (2 * m) tail t * finPairedLog m t
        let Gleft : (UnitAddCircle × UnitAddCircle) ×
            UnitAddTorus (Fin (2 * m)) → ℂ := fun z =>
          pairPart z.1 * tailPart z.2
        have hassoc :
            (∫ z : UnitAddCircle ×
                (UnitAddCircle × UnitAddTorus (Fin (2 * m))), G z) =
              ∫ z : (UnitAddCircle × UnitAddCircle) ×
                UnitAddTorus (Fin (2 * m)), Gleft z := by
          have h := (measurePreserving_prodAssoc
            (volume : Measure UnitAddCircle)
            (volume : Measure UnitAddCircle)
            (volume : Measure (UnitAddTorus (Fin (2 * m))))).integral_comp'
              (fun z : UnitAddCircle ×
                (UnitAddCircle × UnitAddTorus (Fin (2 * m))) => G z)
          simpa [Gleft, pairPart, tailPart, G,
            MeasureTheory.Measure.volume_eq_prod] using h.symm
        rw [hassoc]
        exact integral_prod_mul
          (fun z : UnitAddCircle × UnitAddCircle =>
            fourier (d 0) z.1 * fourier (d 1) z.2 * circleLog (z.2 - z.1))
          (fun t : UnitAddTorus (Fin (2 * m)) =>
            finFourierProduct (2 * m) tail t * finPairedLog m t)
      rw [hfactor, pairLog_fourierIntegral, ih] at hchange'
      rw [finPairedFourierWeight_succ]
      exact hchange'

theorem setup_mFourier_standardPairedLog_integral (S : Setup)
    (d : Exponent S.n) :
    (∫ t : UnitAddTorus (Fin S.n),
      UnitAddTorus.mFourier (fun i => d i) t * standardPairedLog S t) =
      ((standardLogWeight S d : ℚ) : ℂ) := by
  rcases S with ⟨n, m, k, a, b, hn⟩
  subst n
  let e := MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (2 * m + 1) => UnitAddCircle) (Fin.last (2 * m))
  let tail : Fin (2 * m) → ℤ := fun i => d i.castSucc
  let G : UnitAddCircle × UnitAddTorus (Fin (2 * m)) → ℂ := fun z =>
    fourier (d (Fin.last (2 * m))) z.1 *
      (finFourierProduct (2 * m) tail z.2 * finPairedLog m z.2)
  have hchange := (volume_preserving_piFinSuccAbove
    (fun _ : Fin (2 * m + 1) => UnitAddCircle) (Fin.last (2 * m))).integral_comp'
      G
  have heq : (fun t : UnitAddTorus (Fin (2 * m + 1)) => G (e t)) =
      fun t => UnitAddTorus.mFourier (fun i => d i) t *
        standardPairedLog
          ⟨2 * m + 1, m, k, a, b, rfl⟩ t := by
    funext t
    obtain ⟨z, rfl⟩ := e.symm.surjective t
    rcases z with ⟨x, u⟩
    rw [e.apply_symm_apply]
    have hinv : e.symm (x, u) = Fin.snoc u x := by
      change (MeasurableEquiv.piFinSuccAbove
          (fun _ : Fin (2 * m + 1) => UnitAddCircle)
          (Fin.last (2 * m))).symm (x, u) = Fin.snoc u x
      simp only [MeasurableEquiv.piFinSuccAbove_symm_apply,
        Fin.insertNthEquiv]
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp
      · simp
    rw [hinv]
    have hlog : standardPairedLog
        ⟨2 * m + 1, m, k, a, b, rfl⟩ (Fin.snoc u x) = finPairedLog m u := by
      simp only [standardPairedLog, finPairedLog]
      apply Finset.prod_congr rfl
      intro r hr
      congr 2
      · change (Fin.snoc u x : Fin (2 * m + 1) → UnitAddCircle)
          (finPairRight m r).castSucc = u (finPairRight m r)
        exact Fin.snoc_castSucc _ _ _
      · change (Fin.snoc u x : Fin (2 * m + 1) → UnitAddCircle)
          (finPairLeft m r).castSucc = u (finPairLeft m r)
        exact Fin.snoc_castSucc _ _ _
    simp only [G, tail, UnitAddTorus.mFourier, ContinuousMap.coe_mk,
      finFourierProduct, hlog]
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.snoc_last, Fin.snoc_castSucc]
    ring
  have hchange' :
      (∫ t : UnitAddTorus (Fin (2 * m + 1)),
        UnitAddTorus.mFourier (fun i => d i) t *
          standardPairedLog ⟨2 * m + 1, m, k, a, b, rfl⟩ t) =
        ∫ z : UnitAddCircle × UnitAddTorus (Fin (2 * m)), G z := by
    rw [← heq]
    exact hchange
  have hfactor :
      (∫ z : UnitAddCircle × UnitAddTorus (Fin (2 * m)), G z) =
        (∫ x : UnitAddCircle, fourier (d (Fin.last (2 * m))) x) *
        (∫ t : UnitAddTorus (Fin (2 * m)),
          finFourierProduct (2 * m) tail t * finPairedLog m t) := by
    exact integral_prod_mul
      (fun x : UnitAddCircle => fourier (d (Fin.last (2 * m))) x)
      (fun t : UnitAddTorus (Fin (2 * m)) =>
        finFourierProduct (2 * m) tail t * finPairedLog m t)
  rw [hfactor, integral_fourier_eq_ite, finPairedFourierIntegral] at hchange'
  rw [hchange']
  classical
  let S : Setup := ⟨2 * m + 1, m, k, a, b, rfl⟩
  by_cases hadm : StandardLogAdmissible S d
  · rcases hadm with ⟨hpairs, hlastS⟩
    have hadm' : StandardLogAdmissible S d := ⟨hpairs, hlastS⟩
    have hlast : d (Fin.last (2 * m)) = 0 := by
      simpa [S, Setup.lastVertex] using hlastS
    have hpairsTail : ∀ r : Fin m,
        0 < tail (finPairLeft m r) ∧
          tail (finPairRight m r) = -tail (finPairLeft m r) := by
      intro r
      simpa [S, Setup.leftVertex, Setup.rightVertex, tail,
        finPairLeft, finPairRight] using hpairs r
    simp only [hlast, if_pos, one_mul, finPairedFourierWeight]
    simp_rw [if_pos (hpairsTail _)]
    rw [show standardLogWeight S d =
        ∏ r : Fin m, (-1 : ℚ) / (d (S.leftVertex r) : ℚ) by
      simp [standardLogWeight, hadm', S]]
    push_cast
    apply Finset.prod_congr rfl
    intro r hr
    simp [S, Setup.leftVertex, tail, finPairLeft]
  · have hweight : standardLogWeight S d = 0 := by
      simp [standardLogWeight, hadm]
    rw [hweight]
    simp only [Rat.cast_zero]
    by_cases hlast : d (Fin.last (2 * m)) = 0
    · simp only [hlast, if_pos, one_mul]
      have hlastS : d S.lastVertex = 0 := by
        simpa [S, Setup.lastVertex] using hlast
      have hpairsNot : ¬∀ r : Fin m,
          0 < d (S.leftVertex r) ∧
            d (S.rightVertex r) = -d (S.leftVertex r) := by
        intro hpairs
        exact hadm ⟨hpairs, hlastS⟩
      obtain ⟨r, hr⟩ := not_forall.mp hpairsNot
      have hbadTail : ¬(0 < tail (finPairLeft m r) ∧
          tail (finPairRight m r) = -tail (finPairLeft m r)) := by
        simpa [S, Setup.leftVertex, Setup.rightVertex, tail,
          finPairLeft, finPairRight] using hr
      rw [finPairedFourierWeight]
      apply Finset.prod_eq_zero (Finset.mem_univ r)
      simp [hbadTail]
    · simp [hlast]

theorem standardLogCT_eq_finsupp_sum (S : Setup) (F : Laurent ℚ S.n) :
    standardLogCT S F = F.sum (fun e c => c * standardLogWeight S e) := by
  rfl

theorem standardLogCT_zero (S : Setup) :
    standardLogCT S (0 : Laurent ℚ S.n) = 0 := by
  rw [standardLogCT_eq_finsupp_sum]
  simp

theorem standardLogCT_add (S : Setup) (F G : Laurent ℚ S.n) :
    standardLogCT S (F + G) = standardLogCT S F + standardLogCT S G := by
  simp only [standardLogCT_eq_finsupp_sum]
  rw [Finsupp.sum_add_index']
  · intro e
    simp
  · intro e x y
    ring

theorem standardLogCT_monomial (S : Setup) (d : Exponent S.n) (c : ℚ) :
    standardLogCT S (MultiLaurent.monomial d c) =
      c * standardLogWeight S d := by
  rw [standardLogCT_eq_finsupp_sum]
  simp [MultiLaurent.monomial]

theorem torusEval_mul_standardPairedLog_integrable (S : Setup)
    (F : Laurent ℚ S.n) :
    Integrable (fun t : UnitAddTorus (Fin S.n) =>
      torusEval F t * standardPairedLog S t) := by
  let f : C(UnitAddTorus (Fin S.n), ℂ) :=
    ⟨torusEval F, continuous_torusEval F⟩
  apply (standardPairedLog_integrable S).bdd_mul
  · exact (continuous_torusEval F).measurable.aestronglyMeasurable
  · filter_upwards [] with t
    exact f.norm_coe_le_norm t

theorem standardLogCT_eq_torusIntegral_proved (S : Setup)
    (F : Laurent ℚ S.n) :
    ((standardLogCT S F : ℚ) : ℂ) =
      ∫ t : UnitAddTorus (Fin S.n),
        torusEval F t * standardPairedLog S t := by
  classical
  induction F using MultiLaurent.induction_on with
  | h0 => simp [standardLogCT_zero, torusEval]
  | hadd F G hF hG =>
      rw [standardLogCT_add]
      push_cast
      rw [hF, hG]
      have heq : (fun t : UnitAddTorus (Fin S.n) =>
          torusEval (F + G) t * standardPairedLog S t) = fun t =>
          torusEval F t * standardPairedLog S t +
            torusEval G t * standardPairedLog S t := by
        funext t
        simp only [torusEval, map_add, Pi.add_apply]
        ring
      rw [heq, integral_add]
      · exact torusEval_mul_standardPairedLog_integrable S F
      · exact torusEval_mul_standardPairedLog_integrable S G
  | hmono d c =>
      rw [standardLogCT_monomial]
      push_cast
      rw [show (fun t : UnitAddTorus (Fin S.n) =>
          torusEval (MultiLaurent.monomial d c) t * standardPairedLog S t) =
          fun t => (c : ℂ) *
            (UnitAddTorus.mFourier (fun i => d i) t * standardPairedLog S t) by
        funext t
        rw [torusEval_monomial]
        ring]
      rw [integral_const_mul, setup_mFourier_standardPairedLog_integral]

end LogarithmicMorrisFull
