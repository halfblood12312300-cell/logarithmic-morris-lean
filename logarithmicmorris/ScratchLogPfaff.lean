import logarithmicmorris.ScratchRepresentative
import logarithmicmorris.LogarithmicMorrisLogIntegral
import logarithmicmorris.AristotleSkewTask

noncomputable section

open scoped BigOperators

namespace LogarithmicMorrisFull

#check fourier_neg
#check Complex.exp_sub

def angleLogMatrix {n : ℕ} (θ : Fin n → ℝ) (i j : Fin n) : ℂ :=
  Complex.log (1 - Complex.exp ((θ j - θ i) * Complex.I))

theorem circleLog_angleTorus_sub {n : ℕ} (θ : Fin n → ℝ) (i j : Fin n) :
    circleLog (angleTorus θ j - angleTorus θ i) =
      angleLogMatrix θ i j := by
  simp only [circleLog, angleLogMatrix]
  congr 2
  simp only [angleTorus]
  rw [← QuotientAddGroup.mk_sub, fourier_coe_apply]
  congr 1
  push_cast
  field_simp [Real.pi_ne_zero]

theorem angleLogMatrix_skewPart_ordered {m : ℕ}
    (θ : Fin (2 * m + 1) → ℝ)
    (horder : ∀ i j, i < j → θ i < θ j)
    (hwidth : ∀ i j, i < j → θ j - θ i < 2 * Real.pi) :
    (fun i j => angleLogMatrix θ i j - angleLogMatrix θ j i) =
      sawMatrix m (-Real.pi * Complex.I) (fun i => θ i * Complex.I) := by
  funext i j
  rcases lt_trichotomy i j with hij | hij | hij
  · have hlog :
        angleLogMatrix θ i j - angleLogMatrix θ j i =
          (θ j - θ i - Real.pi) * Complex.I := by
      rw [angleLogMatrix, angleLogMatrix]
      convert log_one_sub_cexp_sub_reverse
        (sub_pos.mpr (horder i j hij)) (hwidth i j hij) using 1 <;>
        push_cast <;> ring
    rw [hlog]
    simp only [sawMatrix, hij, if_pos]
    push_cast
    ring
  · subst j
    simp [angleLogMatrix, sawMatrix]
  · have hlog :
        angleLogMatrix θ j i - angleLogMatrix θ i j =
          (θ i - θ j - Real.pi) * Complex.I := by
      rw [angleLogMatrix, angleLogMatrix]
      convert log_one_sub_cexp_sub_reverse
        (sub_pos.mpr (horder j i hij)) (hwidth j i hij) using 1 <;>
        push_cast <;> ring
    rw [show angleLogMatrix θ i j - angleLogMatrix θ j i =
      -(angleLogMatrix θ j i - angleLogMatrix θ i j) by ring, hlog]
    have hnot : ¬i < j := not_lt_of_ge hij.le
    simp only [sawMatrix, hnot, if_neg, hij, if_pos]
    push_cast
    ring

theorem standardPairedLog_permute_angleTorus (S : Setup)
    (θ : Fin S.n → ℝ) (σ : Equiv.Perm (Fin S.n)) :
    standardPairedLog S (permuteTorus σ (angleTorus θ)) =
      ∏ r : Fin S.m,
        angleLogMatrix θ (σ (S.leftVertex r)) (σ (S.rightVertex r)) := by
  unfold standardPairedLog
  apply Finset.prod_congr rfl
  intro r hr
  simp only [permuteTorus]
  exact circleLog_angleTorus_sub θ
    (σ (S.leftVertex r)) (σ (S.rightVertex r))

def Setup.oddEquiv (S : Setup) : Fin S.n ≃ Fin (2 * S.m + 1) :=
  finCongr S.odd_rank

theorem permAlternatingSum_standardPairedLog_angleTorus (S : Setup)
    (θ : Fin S.n → ℝ) :
    permAlternatingSum (standardPairedLog S) (angleTorus θ) =
      pairedAlternatingSum S.m
        (angleLogMatrix (fun i => θ (S.oddEquiv.symm i))) := by
  rcases S with ⟨n, m, k, a, b, hn⟩
  subst n
  simp only [Setup.oddEquiv] at θ ⊢
  unfold permAlternatingSum pairedAlternatingSum
  apply Finset.sum_congr rfl
  intro σ hσ
  congr 1
  rw [standardPairedLog_permute_angleTorus]
  apply Finset.prod_congr rfl
  intro r hr
  congr 3 <;> apply congrArg σ <;> apply Fin.ext <;> rfl

theorem pairedAlternatingSum_angleLogMatrix_ordered {m : ℕ}
    (θ : Fin (2 * m + 1) → ℝ)
    (horder : ∀ i j, i < j → θ i < θ j)
    (hwidth : ∀ i j, i < j → θ j - θ i < 2 * Real.pi) :
    pairedAlternatingSum m (angleLogMatrix θ) =
      (m.factorial : ℂ) * (-Real.pi * Complex.I) ^ m := by
  have hskew := pairedAlternatingSum_skewPart m (angleLogMatrix θ)
  rw [angleLogMatrix_skewPart_ordered θ horder hwidth,
    pairedAlternatingSum_sawMatrix] at hskew
  apply mul_left_cancel₀ (pow_ne_zero m (by norm_num : (2 : ℂ) ≠ 0))
  calc
    (2 : ℂ) ^ m * pairedAlternatingSum m (angleLogMatrix θ) =
        ((2 : ℂ) ^ m * (m.factorial : ℂ)) *
          (-Real.pi * Complex.I) ^ m := hskew.symm
    _ = (2 : ℂ) ^ m *
        ((m.factorial : ℂ) * (-Real.pi * Complex.I) ^ m) := by ring

theorem permAlternatingSum_standardPairedLog_ordered (S : Setup)
    (θ : Fin S.n → ℝ)
    (horder : ∀ i j, i < j → θ i < θ j)
    (hwidth : ∀ i j, i < j → θ j - θ i < 2 * Real.pi) :
    permAlternatingSum (standardPairedLog S) (angleTorus θ) =
      (S.m.factorial : ℂ) * (-Real.pi * Complex.I) ^ S.m := by
  rcases S with ⟨n, m, k, a, b, hn⟩
  subst n
  simp only [Setup.oddEquiv] at θ horder hwidth ⊢
  rw [permAlternatingSum_standardPairedLog_angleTorus]
  exact pairedAlternatingSum_angleLogMatrix_ordered θ horder hwidth

end LogarithmicMorrisFull
