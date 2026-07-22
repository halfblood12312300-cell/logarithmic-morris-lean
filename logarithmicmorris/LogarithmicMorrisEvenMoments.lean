import logarithmicmorris.LogarithmicMorrisDysonMomentDefinitions

/-! # Integer moments of the squared circular discriminant -/

noncomputable section

open scoped BigOperators

namespace LogarithmicMorrisFull

open MeasureTheory

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

lemma torusEval_evenDysonLaurent (n q : ℕ)
    (t : UnitAddTorus (Fin n)) :
    torusEval (evenDysonLaurent n q) t =
      ((circularDiscriminantSq n t) ^ q : ℝ) := by
  unfold evenDysonLaurent circularDiscriminantSq torusEval
  simp only [map_prod, map_mul, map_pow, map_sub, map_one]
  have hratio (i j : Fin n) :
      evalLaurent (fun i => addCircleUnit (t i))
          (ratio i j : Laurent ℚ n) =
        fourier 1 (t i) / fourier 1 (t j) := by
    simp [ratio, addCircleUnit_coe, div_eq_mul_inv]
  simp_rw [hratio]
  push_cast
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro p hp
  rw [← mul_pow, one_sub_div_mul_reverse]
  all_goals simp [fourier_apply]

theorem integral_circularDiscriminantSq_pow (n q : ℕ) :
    (∫ t : UnitAddTorus (Fin n), (circularDiscriminantSq n t) ^ q) =
      (((n * q).factorial : ℝ) / (q.factorial : ℝ) ^ n) := by
  have h := integral_torusEval (evenDysonLaurent n q)
  rw [constantTerm_evenDysonLaurent] at h
  have hc : (((∫ t : UnitAddTorus (Fin n),
      (circularDiscriminantSq n t) ^ q) : ℝ) : ℂ) =
      ((((n * q).factorial : ℚ) / (q.factorial : ℚ) ^ n : ℚ) : ℂ) := by
    calc
      (((∫ t : UnitAddTorus (Fin n),
          (circularDiscriminantSq n t) ^ q) : ℝ) : ℂ) =
          ∫ t : UnitAddTorus (Fin n),
            (((circularDiscriminantSq n t) ^ q : ℝ) : ℂ) :=
        (integral_ofReal (f := fun t : UnitAddTorus (Fin n) =>
          (circularDiscriminantSq n t) ^ q)).symm
      _ = ∫ t : UnitAddTorus (Fin n),
          torusEval (evenDysonLaurent n q) t := by
        apply integral_congr_ae
        filter_upwards with t
        exact (torusEval_evenDysonLaurent n q t).symm
      _ = _ := h
  have hcR : (∫ t : UnitAddTorus (Fin n),
      (circularDiscriminantSq n t) ^ q) =
      (((((n * q).factorial : ℚ) / (q.factorial : ℚ) ^ n : ℚ) : ℝ)) := by
    exact_mod_cast hc
  calc
    _ = (((((n * q).factorial : ℚ) /
        (q.factorial : ℚ) ^ n : ℚ) : ℝ)) := hcR
    _ = (((n * q).factorial : ℝ) / (q.factorial : ℝ) ^ n) := by
      norm_num [Rat.cast_div]

end LogarithmicMorrisFull
