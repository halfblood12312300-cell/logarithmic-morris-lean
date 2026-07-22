import logarithmicmorris.LogarithmicMorrisKOne

noncomputable section

open scoped BigOperators

namespace LogarithmicMorrisFull

open MeasureTheory

def Setup.swapAB (S : Setup) : Setup where
  n := S.n
  m := S.m
  k := S.k
  a := S.b
  b := S.a
  odd_rank := S.odd_rank

lemma fourier_neg_inv (x : AddCircle (1 : ℝ)) :
    fourier 1 (-x) = (fourier 1 x)⁻¹ := by
  rw [fourier_one, fourier_one, AddCircle.toCircle_neg]
  rw [Circle.coe_inv_eq_conj, Complex.inv_eq_conj]
  simp

lemma norm_fourier_neg_sub (x y : AddCircle (1 : ℝ)) :
    ‖fourier 1 (-x) - fourier 1 (-y)‖ =
      ‖fourier 1 x - fourier 1 y‖ := by
  rw [fourier_neg_inv, fourier_neg_inv]
  have hx : ‖fourier 1 x‖ = 1 := by simp
  have hy : ‖fourier 1 y‖ = 1 := by simp
  have hx0 : fourier 1 x ≠ 0 := by
    exact norm_ne_zero_iff.mp (by simp [hx])
  have hy0 : fourier 1 y ≠ 0 := by
    exact norm_ne_zero_iff.mp (by simp [hy])
  rw [inv_sub_inv hx0 hy0]
  rw [norm_div, norm_mul, hx, hy]
  norm_num [norm_sub_rev]

lemma norm_fourier_inv_sub (x y : AddCircle (1 : ℝ)) :
    ‖(fourier 1 x)⁻¹ - (fourier 1 y)⁻¹‖ =
      ‖fourier 1 x - fourier 1 y‖ := by
  rw [← fourier_neg_inv, ← fourier_neg_inv]
  exact norm_fourier_neg_sub x y

lemma circularMorrisIntegrand_swapAB_neg (S : Setup)
    (t : UnitAddTorus (Fin S.n)) :
    circularMorrisIntegrand S (-t) =
      circularMorrisIntegrand S.swapAB t := by
  unfold circularMorrisIntegrand Setup.swapAB
  simp only [Pi.neg_apply, fourier_neg_inv]
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi
    rw [inv_inv]
    ring
  · apply Finset.prod_congr rfl
    intro p hp
    change ((‖(fourier 1 (t p.1))⁻¹ - (fourier 1 (t p.2))⁻¹‖ : ℝ) : ℂ) ^ S.K = _
    rw [norm_fourier_inv_sub]
    rfl

lemma circularMorrisIntegral_swapAB (S : Setup) :
    circularMorrisIntegral S = circularMorrisIntegral S.swapAB := by
  unfold circularMorrisIntegral
  rw [show (volume : Measure (UnitAddTorus (Fin S.n))) =
      Measure.pi (fun _ : Fin S.n => AddCircle.haarAddCircle) by
    rw [MeasureTheory.volume_pi]
    congr 1
    funext i
    exact unitVolume_eq_haar]
  have hneg : MeasurePreserving
      (fun t : UnitAddTorus (Fin S.n) => -t)
      (Measure.pi fun _ : Fin S.n => AddCircle.haarAddCircle)
      (Measure.pi fun _ : Fin S.n => AddCircle.haarAddCircle) :=
    measurePreserving_pi _ _
      (fun _ => Measure.measurePreserving_neg AddCircle.haarAddCircle)
  rw [← hneg.integral_comp measurableEmbedding_neg
    (fun t : UnitAddTorus (Fin S.n) => circularMorrisIntegrand S t)]
  apply integral_congr_ae
  filter_upwards [] with t
  exact circularMorrisIntegrand_swapAB_neg S t

theorem logarithmicMorrisLHS_swapAB (S : Setup) :
    logarithmicMorrisLHS S = logarithmicMorrisLHS S.swapAB := by
  have hbaseS := morrisKernel_standardPairedLog_integrable S
  have hbaseT := morrisKernel_standardPairedLog_integrable S.swapAB
  have hS : ((logarithmicMorrisLHS S : ℚ) : ℂ) =
      (((S.m.factorial : ℂ) * (Real.pi : ℂ) ^ S.m) /
          (S.n.factorial : ℂ)) * circularMorrisIntegral S := by
    calc
      ((logarithmicMorrisLHS S : ℚ) : ℂ) =
          ∫ t : UnitAddTorus (Fin S.n),
            torusEval (morrisKernel S) t * standardPairedLog S t :=
        standardLogCT_eq_torusIntegral S (morrisKernel S)
      _ = (((S.m.factorial : ℂ) * (Real.pi : ℂ) ^ S.m) /
          (S.n.factorial : ℂ)) * circularMorrisIntegral S :=
        torusLogIntegral_eq_circular S hbaseS
  have hT : ((logarithmicMorrisLHS S.swapAB : ℚ) : ℂ) =
      (((S.m.factorial : ℂ) * (Real.pi : ℂ) ^ S.m) /
          (S.n.factorial : ℂ)) * circularMorrisIntegral S.swapAB := by
    simpa [Setup.swapAB] using
      (show ((logarithmicMorrisLHS S.swapAB : ℚ) : ℂ) =
          ((((S.swapAB).m.factorial : ℂ) * (Real.pi : ℂ) ^ (S.swapAB).m) /
            ((S.swapAB).n.factorial : ℂ)) * circularMorrisIntegral S.swapAB by
        calc
          ((logarithmicMorrisLHS S.swapAB : ℚ) : ℂ) =
              ∫ t : UnitAddTorus (Fin (S.swapAB).n),
                torusEval (morrisKernel S.swapAB) t *
                  standardPairedLog S.swapAB t :=
            standardLogCT_eq_torusIntegral S.swapAB (morrisKernel S.swapAB)
          _ = ((((S.swapAB).m.factorial : ℂ) *
                (Real.pi : ℂ) ^ (S.swapAB).m) /
              ((S.swapAB).n.factorial : ℂ)) *
                circularMorrisIntegral S.swapAB :=
            torusLogIntegral_eq_circular S.swapAB hbaseT)
  have hc : ((logarithmicMorrisLHS S : ℚ) : ℂ) =
      ((logarithmicMorrisLHS S.swapAB : ℚ) : ℂ) := by
    rw [hS, hT, circularMorrisIntegral_swapAB]
  exact_mod_cast hc

@[simp] theorem logarithmicMorrisRHS_swapAB (S : Setup) :
    logarithmicMorrisRHS S = logarithmicMorrisRHS S.swapAB := by
  unfold logarithmicMorrisRHS rhsFactor
  simp only [Setup.swapAB, Setup.K]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  congr 2
  · congr 2
    omega
  · rw [mul_comm]

end LogarithmicMorrisFull
