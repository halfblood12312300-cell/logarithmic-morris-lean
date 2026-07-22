import Mathlib.Probability.Distributions.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

/-! # A normalized Gauss multiplication formula -/

noncomputable section

open scoped BigOperators
open Set

namespace ProbabilityTheory

/-- The normalized finite Gamma product used in Gauss multiplication. -/
def normalizedGammaProduct (n : ℕ) (x : ℝ) : ℝ :=
  (n : ℝ) ^ (x - 1) *
      (∏ r ∈ Finset.range n, Real.Gamma ((x + r) / n)) /
    ∏ r ∈ Finset.range n, Real.Gamma ((1 + r) / n)

lemma normalizedGammaProduct_add_one (n : ℕ) (hn : 0 < n) {x : ℝ} (hx : 0 < x) :
    normalizedGammaProduct n (x + 1) = x * normalizedGammaProduct n x := by
  unfold normalizedGammaProduct
  rw [← Nat.sub_add_cancel hn, Finset.prod_range_succ]
  simp +decide [Finset.prod_range_succ', hn, Nat.cast_sub hn]
  rw [show (x + n : ℝ) / n = x / n + 1 by
    rw [add_div, div_self (by positivity)]]
  rw [Real.Gamma_add_one (by positivity)]
  ring
  rw [Real.rpow_add (by positivity), Real.rpow_neg_one]
  ring

lemma normalizedGammaProduct_one (n : ℕ) (hn : 0 < n) :
    normalizedGammaProduct n 1 = 1 := by
  unfold normalizedGammaProduct
  norm_num [Finset.prod_eq_zero_iff, Real.Gamma_pos_of_pos, hn.ne']
  exact fun x hx => ne_of_gt <| Real.Gamma_pos_of_pos <| by positivity

lemma normalizedGammaProduct_pos (n : ℕ) (hn : 0 < n) {x : ℝ} (hx : 0 < x) :
    0 < normalizedGammaProduct n x := by
  exact div_pos
    (mul_pos (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _)
      (Finset.prod_pos fun _ _ => Real.Gamma_pos_of_pos (by positivity)))
    (Finset.prod_pos fun _ _ => Real.Gamma_pos_of_pos (by positivity))

lemma normalizedGammaProduct_log_convex (n : ℕ) (hn : 0 < n) :
    ConvexOn ℝ (Ioi 0) (Real.log ∘ normalizedGammaProduct n) := by
  have h_log_gamma_prod : ∀ x > 0,
      Real.log (normalizedGammaProduct n x) =
        (x - 1) * Real.log n +
          ∑ r ∈ Finset.range n, Real.log (Real.Gamma ((x + r) / n)) -
          ∑ r ∈ Finset.range n, Real.log (Real.Gamma ((1 + r) / n)) := by
    intro x hx
    rw [normalizedGammaProduct]
    rw [Real.log_div, Real.log_mul, Real.log_rpow] <;>
      norm_num [hn.ne', hx.ne']
    any_goals positivity
    · rw [Real.log_prod, Real.log_prod] <;>
        intros <;> exact ne_of_gt <| Real.Gamma_pos_of_pos <| by positivity
    · exact ⟨by positivity,
        Finset.prod_ne_zero_iff.mpr fun i hi => by positivity⟩
  refine ⟨convex_Ioi 0, fun x hx y hy a b ha hb hab => ?_⟩
  have h_convex_sum : ConvexOn ℝ (Set.Ioi 0)
      (fun x => ∑ r ∈ Finset.range n,
        Real.log (Real.Gamma ((x + r) / n))) := by
    have h_each : ∀ r ∈ Finset.range n,
        ConvexOn ℝ (Set.Ioi 0)
          (fun x => Real.log (Real.Gamma ((x + r) / n))) := by
      intro r hr
      have h := Real.convexOn_log_Gamma
      simp_all +decide [ConvexOn]
      intro x hx y hy a b ha hb hab
      convert h.2
        (show 0 < (x + r : ℝ) / n by positivity)
        (show 0 < (y + r : ℝ) / n by positivity) ha hb hab using 1
      ring
      rw [← eq_sub_iff_add_eq'] at hab
      subst_vars
      ring
    exact ⟨convex_Ioi 0, fun x hx y hy a b ha hb hab => by
      simpa [Finset.sum_add_distrib, Finset.mul_sum _ _ _,
        Finset.sum_mul, hab] using
        Finset.sum_le_sum fun i hi => (h_each i hi).2 hx hy ha hb hab⟩
  have h := h_convex_sum.2 hx hy ha hb hab
  simp_all +decide [mul_add, add_mul, mul_comm, mul_left_comm]
  rw [h_log_gamma_prod (x * a + y * b)
    (by cases lt_or_ge a b <;> nlinarith)]
  rw [← eq_sub_iff_add_eq'] at hab
  subst_vars
  nlinarith

lemma normalizedGammaProduct_eq_Gamma (n : ℕ) (hn : 0 < n)
    {x : ℝ} (hx : 0 < x) :
    normalizedGammaProduct n x = Real.Gamma x := by
  exact Real.eq_Gamma_of_log_convex
    (normalizedGammaProduct_log_convex n hn)
    (fun {y} hy => normalizedGammaProduct_add_one n hn hy)
    (fun {y} hy => normalizedGammaProduct_pos n hn hy)
    (normalizedGammaProduct_one n hn) hx

lemma gammaProduct_normalized (n : ℕ) (hn : 0 < n) (s : ℝ) (hs : 0 ≤ s) :
    (n : ℝ) ^ ((n : ℝ) * s) *
        ∏ r ∈ Finset.Icc 1 (n - 1),
          (Real.Gamma (s + (r : ℝ) / n) / Real.Gamma ((r : ℝ) / n)) =
      Real.Gamma (1 + (n : ℝ) * s) / Real.Gamma (1 + s) := by
  have h_eq : n ^ (n * s) *
      (∏ r ∈ Finset.range n, Real.Gamma (s + (r + 1) / n)) /
      (∏ r ∈ Finset.range n, Real.Gamma ((r + 1) / n)) =
        Real.Gamma (1 + n * s) := by
    convert normalizedGammaProduct_eq_Gamma n hn
      (show 0 < 1 + n * s by positivity) using 1
    unfold normalizedGammaProduct
    norm_num [add_comm, add_left_comm, add_assoc]
    exact congrArg₂ _
      (congrArg₂ _ rfl (Finset.prod_congr rfl fun _ _ => by
        rw [add_div']
        ring
        positivity)) rfl
  erw [Finset.prod_Ico_eq_prod_range]
  rcases n <;> simp_all +decide [add_comm, Finset.prod_range_succ]
  simp_all +decide [← h_eq, mul_div, mul_assoc, mul_comm,
    mul_left_comm, ne_of_gt (Nat.cast_add_one_pos _)]
  rw [← h_eq, eq_div_iff (by positivity)]
  ring

lemma betaQuotient_eq (n : ℕ) (hn : 0 < n) (s : ℝ) (hs : 0 ≤ s)
    {r : ℕ} (hr : r ∈ Finset.Icc 1 (n - 1)) :
    beta (s + (r : ℝ) / n) (1 - (r : ℝ) / n) /
        beta ((r : ℝ) / n) (1 - (r : ℝ) / n) =
      (Real.Gamma (s + (r : ℝ) / n) / Real.Gamma ((r : ℝ) / n)) /
        Real.Gamma (1 + s) := by
  convert congr_arg (fun x : ℝ => x / Real.Gamma (1 + s))
    (mul_div_mul_comm (Real.Gamma (s + r / n)) (Real.Gamma (1 - r / n))
      (Real.Gamma (r / n)) (Real.Gamma (1 - r / n))) using 1
  · rw [ProbabilityTheory.beta, ProbabilityTheory.beta]
    ring
    norm_num
  · rw [div_self <| ne_of_gt <| Real.Gamma_pos_of_pos <| sub_pos.mpr <| by
      rw [div_lt_iff₀ <| by positivity]
      norm_cast
      linarith [Finset.mem_Icc.mp hr, Nat.sub_add_cancel hn]]
    ring

lemma betaQuotientProduct_eq (n : ℕ) (hn : 0 < n) (s : ℝ) (hs : 0 ≤ s) :
    (∏ r ∈ Finset.Icc 1 (n - 1),
      beta (s + (r : ℝ) / n) (1 - (r : ℝ) / n) /
        beta ((r : ℝ) / n) (1 - (r : ℝ) / n)) =
      (∏ r ∈ Finset.Icc 1 (n - 1),
        (Real.Gamma (s + (r : ℝ) / n) / Real.Gamma ((r : ℝ) / n))) /
        Real.Gamma (1 + s) ^ (n - 1) := by
  rw [Finset.prod_congr rfl fun x hx => ?_]
  rotate_left
  use fun x => (Real.Gamma (s + x / n) / Real.Gamma (x / n)) /
    Real.Gamma (1 + s)
  · convert betaQuotient_eq n hn s hs hx using 1
  · norm_num

def betaMellinProduct (n : ℕ) (s : ℝ) : ℝ :=
  (n : ℝ) ^ ((n : ℝ) * s) *
    ∏ r ∈ Finset.Icc 1 (n - 1),
      beta (s + (r : ℝ) / n) (1 - (r : ℝ) / n) /
        beta ((r : ℝ) / n) (1 - (r : ℝ) / n)

/-- Gauss multiplication in normalized beta-product form. -/
theorem betaMellinProduct_eq_gammaRatio (n : ℕ) (hn : 0 < n)
    (s : ℝ) (hs : 0 ≤ s) :
    betaMellinProduct n s =
      Real.Gamma (1 + (n : ℝ) * s) / Real.Gamma (1 + s) ^ n := by
  convert congr_arg (fun x : ℝ => x / Real.Gamma (1 + s) ^ (n - 1))
    (gammaProduct_normalized n hn s hs) using 1
  · convert congr_arg (fun x : ℝ => (n : ℝ) ^ (n * s) * x)
      (betaQuotientProduct_eq n hn s hs) using 1
    ring
  · rw [div_div, ← pow_succ', Nat.sub_add_cancel hn]

end ProbabilityTheory
