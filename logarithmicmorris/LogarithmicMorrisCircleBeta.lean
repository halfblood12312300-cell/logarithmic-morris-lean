import logarithmicmorris.ScratchLogCTBridge

/-!
# The one-dimensional circular beta integral

This is the rank-one base case of the circular Morris integral.  The
constant coefficient is evaluated by an explicit binomial expansion and
Vandermonde convolution.
-/

noncomputable section

open scoped BigOperators

namespace LogarithmicMorrisFull

open MeasureTheory

/-- The Laurent kernel occurring in the one-dimensional circular beta integral. -/
def circleBetaLaurent (a b : ℕ) : Laurent ℚ 1 :=
  (1 - MultiLaurent.var (0 : Fin 1)) ^ a *
    (1 - MultiLaurent.varInv (0 : Fin 1)) ^ b

set_option maxHeartbeats 800000 in
lemma constantTerm_circleBetaLaurent (a b : ℕ) :
    MultiLaurent.constantTerm (circleBetaLaurent a b) =
      (Nat.choose (a + b) a : ℚ) := by
  unfold circleBetaLaurent
  have h_binom :
      (1 - MultiLaurent.var 0) ^ a =
          ∑ i ∈ Finset.range (a + 1),
            (-1 : Laurent ℚ 1) ^ i *
              MultiLaurent.monomial (i • Finsupp.single 0 1)
                (Nat.choose a i : ℚ) ∧
      (1 - MultiLaurent.varInv 0) ^ b =
          ∑ j ∈ Finset.range (b + 1),
            (-1 : Laurent ℚ 1) ^ j *
              MultiLaurent.monomial (j • Finsupp.single 0 (-1))
                (Nat.choose b j : ℚ) := by
    constructor <;> rw [sub_eq_add_neg, add_comm, add_pow] <;> norm_num
    · refine Finset.sum_congr rfl fun x hx => ?_
      rw [neg_pow]
      simp +decide [mul_assoc, MultiLaurent.X_pow]
      erw [MultiLaurent.X_pow]
      erw [MultiLaurent.monomial_mul_monomial]
      aesop
    · refine Finset.sum_congr rfl fun x hx => ?_
      rw [neg_pow]
      simp +decide [MultiLaurent.varInv, MultiLaurent.X,
        MultiLaurent.monomial]
      erw [mul_assoc]
      erw [AddMonoidAlgebra.single_mul_single]
      aesop
  have h_const_term : ∀ i j : ℕ,
      MultiLaurent.constantTerm
          ((-1 : Laurent ℚ 1) ^ i *
              MultiLaurent.monomial (i • Finsupp.single 0 1)
                (Nat.choose a i : ℚ) *
            ((-1 : Laurent ℚ 1) ^ j *
              MultiLaurent.monomial (j • Finsupp.single 0 (-1))
                (Nat.choose b j : ℚ))) =
        if i = j then
          (-1 : ℚ) ^ (i + j) * (Nat.choose a i : ℚ) *
            (Nat.choose b j : ℚ)
        else 0 := by
    intro i j
    split_ifs <;>
      simp_all +decide [pow_add, mul_assoc, mul_left_comm, mul_comm]
    · simp +decide [← mul_assoc, ← pow_add, MultiLaurent.monomial]
    · simp +decide [← mul_assoc, ← pow_add, MultiLaurent.monomial]
      by_cases hi : Even (i + j) <;>
        simp_all +decide [Finsupp.single_apply, Finsupp.add_apply,
          Finsupp.neg_apply]
      · intro h
        replace h := congr_arg (fun f => f 0) h
        simp_all +decide [Finsupp.single_apply]
        grind
      · intro h
        replace h := congr_arg (fun f => f 0) h
        simp_all +decide [Finsupp.single_apply]
        grind
  simp_all +decide [Finset.sum_mul _ _ _, Finset.mul_sum]
  have h_vandermonde :
      ∑ x ∈ Finset.range (a + 1),
          (Nat.choose a x : ℚ) * (Nat.choose b x : ℚ) =
        (Nat.choose (a + b) a : ℚ) := by
    rw_mod_cast [Nat.add_choose_eq]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      fun i j => Nat.choose a i * Nat.choose b j]
    rw [← Finset.sum_flip]
    exact Finset.sum_congr rfl fun x hx => by
      rw [Nat.choose_symm (Finset.mem_range_succ_iff.mp hx)]
  convert h_vandermonde using 2
  split_ifs <;> simp_all +decide [Nat.choose_eq_zero_of_lt]

/-- The normalized one-dimensional circle integral. -/
lemma integral_circleBetaLaurent (a b : ℕ) :
    (∫ t : UnitAddTorus (Fin 1), torusEval (circleBetaLaurent a b) t) =
      (Nat.choose (a + b) a : ℂ) := by
  classical
  rw [show (volume : Measure (UnitAddTorus (Fin 1))) =
      Measure.pi (fun _ : Fin 1 => AddCircle.haarAddCircle) by
    rw [MeasureTheory.volume_pi]
    congr 1
    funext i
    exact unitVolume_eq_haar]
  convert integral_torusEval (circleBetaLaurent a b) using 1
  rw [constantTerm_circleBetaLaurent]
  norm_cast

end LogarithmicMorrisFull
