import Mathlib.MeasureTheory.Group.Prod
import logarithmicmorris.ScratchCircleLogIntegrable

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace LogarithmicMorrisFull

#check MeasurableEquiv.piFinSuccAbove
#check MeasurableEquiv.prodCongr
#check MeasurableEquiv.refl
#check volume_preserving_piFinSuccAbove
#check MeasurePreserving.prod
#check MeasurePreserving.comp
#check MeasurableEquiv.piFinSuccAbove_symm_apply
#check Fin.insertNth_zero

def finPairLeft (m : ℕ) (r : Fin m) : Fin (2 * m) :=
  ⟨2 * r.1, by omega⟩

def finPairRight (m : ℕ) (r : Fin m) : Fin (2 * m) :=
  ⟨2 * r.1 + 1, by omega⟩

def finPairedLog (m : ℕ) (t : UnitAddTorus (Fin (2 * m))) : ℂ :=
  ∏ r : Fin m, circleLog (t (finPairRight m r) - t (finPairLeft m r))

theorem pairCircleLog_integrable : Integrable
    (fun z : UnitAddCircle × UnitAddCircle => circleLog (z.2 - z.1)) := by
  have hbase : Integrable
      (fun z : UnitAddCircle × UnitAddCircle => (1 : ℂ) * circleLog z.2) :=
    (integrable_const (1 : ℂ)).mul_prod circleLog_integrable
  have hcomp := (measurePreserving_prod_sub
    (volume : Measure UnitAddCircle) (volume : Measure UnitAddCircle)).integrable_comp_of_integrable
      hbase
  simpa only [Function.comp_apply, one_mul] using hcomp

def splitTwoEquiv (q : ℕ) :
    (Fin (q + 2) → UnitAddCircle) ≃ᵐ
      UnitAddCircle × (UnitAddCircle × (Fin q → UnitAddCircle)) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (q + 2) => UnitAddCircle) 0).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl UnitAddCircle)
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (q + 1) => UnitAddCircle) 0))

theorem splitTwoEquiv_measurePreserving (q : ℕ) :
    MeasurePreserving (splitTwoEquiv q) := by
  have hleft := volume_preserving_piFinSuccAbove
    (fun _ : Fin (q + 2) => UnitAddCircle) 0
  have hright := (MeasurePreserving.id (volume : Measure UnitAddCircle)).prod
    (volume_preserving_piFinSuccAbove
      (fun _ : Fin (q + 1) => UnitAddCircle) 0)
  have hcomp := hright.comp hleft
  simpa only [splitTwoEquiv, MeasurableEquiv.coe_trans,
    Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.refl_apply,
    Prod.map_apply, id_eq] using hcomp

theorem finPairedLog_cons_cons (m : ℕ) (x y : UnitAddCircle)
    (t : Fin (2 * m) → UnitAddCircle) :
    finPairedLog (m + 1) (Fin.cons x (Fin.cons y t)) =
      circleLog (y - x) * finPairedLog m t := by
  simp only [finPairedLog, Fin.prod_univ_succ]
  congr 1

theorem finPairedLog_integrable (m : ℕ) :
    Integrable (finPairedLog m) := by
  induction m with
  | zero =>
      simpa [finPairedLog] using
        (integrable_const (1 : ℂ) : Integrable
          (fun _ : UnitAddTorus (Fin (2 * 0)) => (1 : ℂ)))
  | succ m ih =>
      have hprod : Integrable
          (fun z : (UnitAddCircle × UnitAddCircle) ×
              UnitAddTorus (Fin (2 * m)) =>
            circleLog (z.1.2 - z.1.1) * finPairedLog m z.2) :=
        pairCircleLog_integrable.mul_prod ih
      have hassoc : Integrable
          (fun z : UnitAddCircle ×
              (UnitAddCircle × UnitAddTorus (Fin (2 * m))) =>
            circleLog (z.2.1 - z.1) * finPairedLog m z.2.2) := by
        apply (volume_preserving_prodAssoc.integrable_comp_emb
          MeasurableEquiv.prodAssoc.measurableEmbedding).mp
        simpa only [Function.comp_apply, Equiv.prodAssoc_apply] using hprod
      have hsplit := (splitTwoEquiv_measurePreserving (2 * m)).integrable_comp_emb
        (splitTwoEquiv (2 * m)).measurableEmbedding |>.mpr hassoc
      have heq : ((fun z : UnitAddCircle ×
              (UnitAddCircle × UnitAddTorus (Fin (2 * m))) =>
            circleLog (z.2.1 - z.1) * finPairedLog m z.2.2) ∘
          (splitTwoEquiv (2 * m))) = finPairedLog (m + 1) := by
        funext t
        obtain ⟨z, rfl⟩ := (splitTwoEquiv (2 * m)).symm.surjective t
        rcases z with ⟨x, y, u⟩
        simp only [Function.comp_apply]
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
        change circleLog (y - x) * finPairedLog m u =
          finPairedLog (m + 1) (Fin.cons x (Fin.cons y u))
        rw [finPairedLog_cons_cons]
      rw [heq] at hsplit
      simpa only [Nat.succ_eq_add_one] using hsplit

theorem standardPairedLog_integrable (S : Setup) :
    Integrable (standardPairedLog S) := by
  rcases S with ⟨n, m, k, a, b, hn⟩
  subst n
  let e := MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (2 * m + 1) => UnitAddCircle) (Fin.last (2 * m))
  have hprod : Integrable
      (fun z : UnitAddCircle × UnitAddTorus (Fin (2 * m)) =>
        (1 : ℂ) * finPairedLog m z.2) :=
    (integrable_const (1 : ℂ)).mul_prod (finPairedLog_integrable m)
  have hcomp := (volume_preserving_piFinSuccAbove
    (fun _ : Fin (2 * m + 1) => UnitAddCircle) (Fin.last (2 * m))).integrable_comp_of_integrable
      hprod
  convert hcomp using 1
  funext t
  simp only [Function.comp_apply, one_mul, standardPairedLog, finPairedLog]
  apply Finset.prod_congr rfl
  intro r hr
  change (Fin (2 * m + 1) → UnitAddCircle) at t
  congr 2
  · simp [Setup.rightVertex, finPairRight, MeasurableEquiv.piFinSuccAbove,
      Fin.insertNthEquiv, Fin.succAbove_last, Fin.init]
  · simp [Setup.leftVertex, finPairLeft, MeasurableEquiv.piFinSuccAbove,
      Fin.insertNthEquiv, Fin.succAbove_last, Fin.init]

theorem morrisKernel_standardPairedLog_integrable (S : Setup) :
    Integrable (fun t : UnitAddTorus (Fin S.n) =>
      torusEval (morrisKernel S) t * standardPairedLog S t) := by
  let f : C(UnitAddTorus (Fin S.n), ℂ) :=
    ⟨torusEval (morrisKernel S), continuous_torusEval (morrisKernel S)⟩
  apply (standardPairedLog_integrable S).bdd_mul
  · exact (continuous_torusEval (morrisKernel S)).measurable.aestronglyMeasurable
  · filter_upwards [] with t
    exact f.norm_coe_le_norm t

end LogarithmicMorrisFull
