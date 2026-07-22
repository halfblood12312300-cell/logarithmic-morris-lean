import logarithmicmorris.ScratchBridge
import logarithmicmorris.ScratchPermutationIntegral
import logarithmicmorris.LogarithmicMorrisPfaffian
import Mathlib.Data.Fin.Tuple.Sort

noncomputable section

open scoped BigOperators

namespace LogarithmicMorrisFull

def circleRepresentative (t : UnitAddCircle) : ℝ :=
  (AddCircle.equivIco (1 : ℝ) 0 t : ℝ)

def circleAngle (t : UnitAddCircle) : ℝ :=
  2 * Real.pi * circleRepresentative t

theorem circleRepresentative_mem (t : UnitAddCircle) :
    circleRepresentative t ∈ Set.Ico (0 : ℝ) 1 := by
  simpa only [circleRepresentative, zero_add] using
    (AddCircle.equivIco (1 : ℝ) 0 t).property

theorem coe_circleRepresentative (t : UnitAddCircle) :
    ((circleRepresentative t : ℝ) : UnitAddCircle) = t := by
  change (((AddCircle.equivIco (1 : ℝ) 0 t : Set.Ico (0 : ℝ) (0 + 1)) : ℝ) :
      UnitAddCircle) = t
  exact (AddCircle.equivIco (1 : ℝ) 0).symm_apply_apply t

theorem circleRepresentative_injective : Function.Injective circleRepresentative := by
  intro x y h
  rw [← coe_circleRepresentative x, ← coe_circleRepresentative y, h]

theorem angleTorus_circleAngle {n : ℕ} (t : UnitAddTorus (Fin n)) :
    angleTorus (fun i => circleAngle (t i)) = t := by
  funext i
  rw [angleTorus]
  change (((circleAngle (t i) / (2 * Real.pi) : ℝ)) : UnitAddCircle) = t i
  rw [show circleAngle (t i) / (2 * Real.pi) =
      circleRepresentative (t i) by
    dsimp [circleAngle]
    field_simp [Real.pi_ne_zero]]
  exact coe_circleRepresentative (t i)

def sortingPerm {n : ℕ} (t : UnitAddTorus (Fin n)) : Equiv.Perm (Fin n) :=
  Tuple.sort (fun i => circleRepresentative (t i))

theorem sortingPerm_monotone {n : ℕ} (t : UnitAddTorus (Fin n)) :
    Monotone (fun i => circleRepresentative (t (sortingPerm t i))) := by
  exact Tuple.monotone_sort
    (fun i : Fin n => circleRepresentative (t i))

theorem sortingPerm_strictMono {n : ℕ} (t : UnitAddTorus (Fin n))
    (ht : Function.Injective t) :
    StrictMono (fun i => circleRepresentative (t (sortingPerm t i))) := by
  exact (sortingPerm_monotone t).strictMono_of_injective
    (circleRepresentative_injective.comp (ht.comp (sortingPerm t).injective))

def sortingAngles {n : ℕ} (t : UnitAddTorus (Fin n)) (i : Fin n) : ℝ :=
  circleAngle (t (sortingPerm t i))

theorem angleTorus_sortingAngles {n : ℕ} (t : UnitAddTorus (Fin n)) :
    angleTorus (sortingAngles t) = permuteTorus (sortingPerm t) t := by
  exact angleTorus_circleAngle
    (fun i => t (sortingPerm t i))

theorem sortingAngles_order {n : ℕ} (t : UnitAddTorus (Fin n))
    (ht : Function.Injective t) :
    ∀ i j, i < j → sortingAngles t i < sortingAngles t j := by
  intro i j hij
  have hrep := sortingPerm_strictMono t ht hij
  dsimp [sortingAngles, circleAngle]
  nlinarith [Real.pi_pos]

theorem sortingAngles_width {n : ℕ} (t : UnitAddTorus (Fin n)) :
    ∀ i j, i < j → sortingAngles t j - sortingAngles t i < 2 * Real.pi := by
  intro i j hij
  have hi := circleRepresentative_mem (t (sortingPerm t i))
  have hj := circleRepresentative_mem (t (sortingPerm t j))
  rcases hi with ⟨hi0, hi1⟩
  rcases hj with ⟨hj0, hj1⟩
  dsimp [sortingAngles, circleAngle]
  nlinarith [Real.pi_pos]

end LogarithmicMorrisFull
