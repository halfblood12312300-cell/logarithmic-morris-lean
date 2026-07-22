import logarithmicmorris.ScratchPermutation
import Mathlib.MeasureTheory.Integral.Pi

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace LogarithmicMorrisFull

#check volume_measurePreserving_piCongrLeft
#check MeasureTheory.integral_finset_sum
#check MeasureTheory.integral_const_mul
#check Fintype.card_perm
#check MeasureTheory.MeasurePreserving.integrable_comp_emb
#check MeasureTheory.MeasurePreserving.integrable_comp

theorem piCongrLeft_eq_permuteTorus {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (t : UnitAddTorus (Fin n)) :
    (Equiv.piCongrLeft (fun _ : Fin n => UnitAddCircle) σ.symm) t =
      permuteTorus σ t := by
  funext i
  simp [Equiv.piCongrLeft_apply, permuteTorus]

theorem integral_permuteTorus {n : ℕ} (σ : Equiv.Perm (Fin n))
    (f : UnitAddTorus (Fin n) → ℂ) :
    (∫ t, f (permuteTorus σ t)) = ∫ t, f t := by
  simpa only [Function.comp_apply, MeasurableEquiv.coe_piCongrLeft,
      piCongrLeft_eq_permuteTorus] using
    (volume_measurePreserving_piCongrLeft
      (fun _ : Fin n => UnitAddCircle) σ.symm).integral_comp' f

theorem integrable_comp_permuteTorus_iff {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (f : UnitAddTorus (Fin n) → ℂ) :
    Integrable (fun t => f (permuteTorus σ t)) ↔ Integrable f := by
  let e := MeasurableEquiv.piCongrLeft
    (fun _ : Fin n => UnitAddCircle) σ.symm
  have he : (f ∘ (e : UnitAddTorus (Fin n) → UnitAddTorus (Fin n))) =
      (fun t => f (permuteTorus σ t)) := by
    funext t
    change f ((Equiv.piCongrLeft
      (fun _ : Fin n => UnitAddCircle) σ.symm) t) = _
    rw [piCongrLeft_eq_permuteTorus]
  rw [← he]
  exact (volume_measurePreserving_piCongrLeft
    (fun _ : Fin n => UnitAddCircle) σ.symm).integrable_comp_emb (g := f)
      e.measurableEmbedding

def permAlternatingSum {n : ℕ} (L : UnitAddTorus (Fin n) → ℂ)
    (t : UnitAddTorus (Fin n)) : ℂ :=
  ∑ σ : Equiv.Perm (Fin n),
    ((σ.sign : ℤ) : ℂ) * L (permuteTorus σ t)

theorem permSign_sq_complex {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    ((σ.sign : ℤ) : ℂ) * ((σ.sign : ℤ) : ℂ) = 1 := by
  norm_cast
  change (σ.sign : ℤ) * (σ.sign : ℤ) = 1
  rw [← Units.val_mul]
  congr 1
  rw [← Int.units_inv_eq_self σ.sign]
  simp

theorem permuteTorus_mul {n : ℕ} (σ τ : Equiv.Perm (Fin n))
    (t : UnitAddTorus (Fin n)) :
    permuteTorus τ (permuteTorus σ t) = permuteTorus (σ * τ) t := by
  funext i
  simp [permuteTorus, Equiv.Perm.coe_mul]

theorem permAlternatingSum_permute {n : ℕ}
    (L : UnitAddTorus (Fin n) → ℂ) (σ : Equiv.Perm (Fin n))
    (t : UnitAddTorus (Fin n)) :
    permAlternatingSum L (permuteTorus σ t) =
      ((σ.sign : ℤ) : ℂ) * permAlternatingSum L t := by
  unfold permAlternatingSum
  simp_rw [permuteTorus_mul]
  calc
    (∑ τ : Equiv.Perm (Fin n),
        ((τ.sign : ℤ) : ℂ) * L (permuteTorus (σ * τ) t)) =
      ((σ.sign : ℤ) : ℂ) *
        ∑ τ : Equiv.Perm (Fin n),
          ((((σ * τ).sign : ℤ) : ℂ) *
            L (permuteTorus (σ * τ) t)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro τ hτ
      rw [Equiv.Perm.sign_mul]
      push_cast
      calc
        ((τ.sign : ℤ) : ℂ) * L (permuteTorus (σ * τ) t) =
            1 * (((τ.sign : ℤ) : ℂ) *
              L (permuteTorus (σ * τ) t)) := by simp
        _ = (((σ.sign : ℤ) : ℂ) * ((σ.sign : ℤ) : ℂ)) *
              (((τ.sign : ℤ) : ℂ) *
                L (permuteTorus (σ * τ) t)) := by
          rw [permSign_sq_complex]
        _ = ((σ.sign : ℤ) : ℂ) *
              (((σ.sign : ℤ) : ℂ) * ((τ.sign : ℤ) : ℂ) *
                L (permuteTorus (σ * τ) t)) := by ring
    _ = ((σ.sign : ℤ) : ℂ) *
        ∑ ρ : Equiv.Perm (Fin n),
          ((ρ.sign : ℤ) : ℂ) * L (permuteTorus ρ t) := by
      congr 1
      exact Equiv.sum_comp (Equiv.mulLeft σ)
        (fun ρ : Equiv.Perm (Fin n) =>
          ((ρ.sign : ℤ) : ℂ) * L (permuteTorus ρ t))

theorem integrable_alternating_mul_permute {n : ℕ}
    (F L : UnitAddTorus (Fin n) → ℂ)
    (hF : ∀ (σ : Equiv.Perm (Fin n)) t,
      F (permuteTorus σ t) = ((σ.sign : ℤ) : ℂ) * F t)
    (hbase : Integrable (fun t => F t * L t))
    (σ : Equiv.Perm (Fin n)) :
    Integrable (fun t => F t * L (permuteTorus σ t)) := by
  have hcomp : Integrable (fun t =>
      F (permuteTorus σ t) * L (permuteTorus σ t)) :=
    (integrable_comp_permuteTorus_iff σ (fun t => F t * L t)).2 hbase
  have hscaled := hcomp.const_mul (((σ.sign : ℤ) : ℂ))
  convert hscaled using 1
  funext t
  rw [hF]
  have hs := permSign_sq_complex σ
  ring_nf at hs ⊢
  rw [hs]
  ring

theorem integral_mul_permAlternatingSum {n : ℕ}
    (F L : UnitAddTorus (Fin n) → ℂ)
    (hF : ∀ (σ : Equiv.Perm (Fin n)) t,
      F (permuteTorus σ t) = ((σ.sign : ℤ) : ℂ) * F t)
    (hInt : ∀ σ : Equiv.Perm (Fin n),
      Integrable (fun t => F t * L (permuteTorus σ t))) :
    (∫ t, F t * permAlternatingSum L t) =
      (n.factorial : ℂ) * ∫ t, F t * L t := by
  have h_each (σ : Equiv.Perm (Fin n)) :
      ((σ.sign : ℤ) : ℂ) *
          (∫ t, F t * L (permuteTorus σ t)) =
        ∫ t, F t * L t := by
    calc
      ((σ.sign : ℤ) : ℂ) *
            (∫ t, F t * L (permuteTorus σ t)) =
          ∫ t, ((σ.sign : ℤ) : ℂ) *
            (F t * L (permuteTorus σ t)) := by
              rw [integral_const_mul]
      _ = ∫ t, F (permuteTorus σ t) *
            L (permuteTorus σ t) := by
          apply integral_congr_ae
          filter_upwards [] with t
          rw [hF]
          ring
      _ = ∫ t, F t * L t :=
        integral_permuteTorus σ (fun t => F t * L t)
  calc
    (∫ t, F t * permAlternatingSum L t) =
        ∫ t, ∑ σ : Equiv.Perm (Fin n),
          ((σ.sign : ℤ) : ℂ) *
            (F t * L (permuteTorus σ t)) := by
      apply integral_congr_ae
      filter_upwards [] with t
      simp only [permAlternatingSum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ hσ
      ring
    _ = ∑ σ : Equiv.Perm (Fin n),
          ∫ t, ((σ.sign : ℤ) : ℂ) *
            (F t * L (permuteTorus σ t)) := by
      apply integral_finset_sum
      intro σ hσ
      exact (hInt σ).const_mul _
    _ = ∑ _σ : Equiv.Perm (Fin n),
          ∫ t, F t * L t := by
      apply Finset.sum_congr rfl
      intro σ hσ
      rw [integral_const_mul]
      exact h_each σ
    _ = (n.factorial : ℂ) * ∫ t, F t * L t := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm,
        Fintype.card_fin]
      simp

end LogarithmicMorrisFull
