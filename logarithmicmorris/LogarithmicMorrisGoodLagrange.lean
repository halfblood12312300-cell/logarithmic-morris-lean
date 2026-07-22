import logarithmicmorris.LogarithmicMorrisCircleBeta
import Mathlib.LinearAlgebra.Lagrange

/-! # The Lagrange identity in Good's proof of the Dyson constant term -/

noncomputable section

open scoped BigOperators

namespace LogarithmicMorrisFull

set_option maxHeartbeats 1000000

lemma laurent_var_injective (n : ℕ) :
    Function.Injective (fun i : Fin n => (MultiLaurent.var i : Laurent ℚ n)) := by
  intro i j h
  apply Finsupp.single_left_injective (one_ne_zero : (1 : ℤ) ≠ 0)
  apply Finsupp.single_left_injective (one_ne_zero : (1 : ℚ) ≠ 0)
  simpa [MultiLaurent.var, MultiLaurent.X, MultiLaurent.monomial] using h

/-- The row factor `P_i = ∏_{j ≠ i} (1 - x_i/x_j)`. -/
def goodRow (n : ℕ) (i : Fin n) : Laurent ℚ n :=
  ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, (1 - ratio i j)

lemma goodRow_ne_zero (n : ℕ) (i : Fin n) : goodRow n i ≠ 0 := by
  unfold goodRow
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  intro h
  have hv : (MultiLaurent.var i : Laurent ℚ n) = MultiLaurent.var j := by
    have hr : (MultiLaurent.var i : Laurent ℚ n) *
        MultiLaurent.varInv j = 1 := by
      simpa [ratio] using (sub_eq_zero.mp h).symm
    calc
      MultiLaurent.var i = MultiLaurent.var i * 1 := by rw [mul_one]
      _ = MultiLaurent.var i *
          (MultiLaurent.varInv j * MultiLaurent.var j) := by
        rw [mul_comm (MultiLaurent.varInv j) (MultiLaurent.var j),
          MultiLaurent.var_mul_varInv]
      _ = (MultiLaurent.var i * MultiLaurent.varInv j) *
          MultiLaurent.var j := by rw [mul_assoc]
      _ = MultiLaurent.var j := by rw [hr]; simp
  exact hji ((laurent_var_injective n hv).symm)

/-- Good's denominator-cleared Lagrange identity. -/
lemma goodRow_product_identity (n : ℕ) (hn : 0 < n) :
    (∏ i : Fin n, goodRow n i) =
      ∑ i : Fin n, ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, goodRow n j := by
  let R := Laurent ℚ n
  let F := FractionRing R
  let ι : R →+* F := algebraMap R F
  let v : Fin n → F := fun i => ι (MultiLaurent.var i)
  have hv_inj : Function.Injective v := by
    intro i j h
    apply laurent_var_injective n
    exact IsFractionRing.injective R F h
  have huniv : (Finset.univ : Finset (Fin n)).Nonempty := by
    exact Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hn)
  have hlag := Lagrange.sum_basis
    (s := (Finset.univ : Finset (Fin n)))
    (v := v) hv_inj.injOn huniv
  have heval := congrArg (Polynomial.eval (0 : F)) hlag
  simp at heval
  have hrecip :
      (∑ i : Fin n, (ι (goodRow n i))⁻¹) = 1 := by
    calc
      (∑ i : Fin n, (ι (goodRow n i))⁻¹) =
          ∑ i : Fin n, Polynomial.eval 0
            (Lagrange.basis Finset.univ v i) := by
        apply Finset.sum_congr rfl
        intro i hi
        unfold goodRow
        rw [map_prod]
        simp only [map_sub, map_one, map_mul, ratio]
        simp only [Lagrange.basis, Polynomial.eval_prod,
          Lagrange.basisDivisor, Polynomial.eval_mul, Polynomial.eval_sub,
          Polynomial.eval_X, Polynomial.eval_C, zero_sub]
        rw [← Finset.prod_inv_distrib]
        apply Finset.prod_congr rfl
        intro j hj
        have hvj : v j ≠ 0 := by
          intro hzero
          have : (MultiLaurent.var j : R) = 0 :=
            IsFractionRing.injective R F (by simpa [v, ι] using hzero)
          have hm := congrArg (fun p : R => p * MultiLaurent.varInv j) this
          dsimp at hm
          simp only [zero_mul] at hm
          change (MultiLaurent.var j : R) * MultiLaurent.varInv j = 0 at hm
          rw [MultiLaurent.var_mul_varInv] at hm
          simp at hm
        have hdiff : v i - v j ≠ 0 :=
          sub_ne_zero.mpr (hv_inj.ne (Finset.mem_erase.mp hj).1.symm)
        have hvinv : ι (MultiLaurent.varInv j) = (v j)⁻¹ := by
          apply eq_inv_of_mul_eq_one_left
          change ι (MultiLaurent.varInv j) * ι (MultiLaurent.var j) = 1
          rw [mul_comm, ← map_mul, MultiLaurent.var_mul_varInv, map_one]
        rw [hvinv]
        have hbase : 1 - v i * (v j)⁻¹ = -(v i - v j) * (v j)⁻¹ := by
          calc
            1 - v i * (v j)⁻¹ = v j * (v j)⁻¹ - v i * (v j)⁻¹ := by
              rw [mul_inv_cancel₀ hvj]
            _ = -(v i - v j) * (v j)⁻¹ := by ring
        rw [hbase]
        rw [mul_inv_rev, inv_inv]
        have hneg : (-(v i - v j))⁻¹ = -((v i - v j)⁻¹) := by
          rw [show -(v i - v j) = (-1 : F) * (v i - v j) by ring,
            mul_inv_rev]
          norm_num
          ring
        rw [hneg]
        ring
      _ = Polynomial.eval 0
          (∑ i : Fin n, Lagrange.basis Finset.univ v i) := by
        exact (map_sum (Polynomial.evalRingHom (0 : F))
          (fun i : Fin n => Lagrange.basis Finset.univ v i) Finset.univ).symm
      _ = 1 := heval
  apply IsFractionRing.injective R F
  simp only [map_prod, map_sum, map_mul]
  have hrowmap : ∀ i : Fin n, ι (goodRow n i) ≠ 0 := fun i => by
    simpa [ι] using (IsFractionRing.injective R F).ne (goodRow_ne_zero n i)
  calc
    (∏ i : Fin n, ι (goodRow n i)) =
        (∏ i : Fin n, ι (goodRow n i)) * 1 := by ring
    _ = (∏ i : Fin n, ι (goodRow n i)) *
        (∑ i : Fin n, (ι (goodRow n i))⁻¹) := by rw [hrecip]
    _ = ∑ i : Fin n, (∏ j : Fin n, ι (goodRow n j)) *
        (ι (goodRow n i))⁻¹ := by rw [Finset.mul_sum]
    _ = ∑ i : Fin n,
        ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i,
          ι (goodRow n j) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.prod_eq_mul_prod_diff_singleton hi]
      rw [mul_comm (ι (goodRow n i)), mul_assoc,
        mul_inv_cancel₀ (hrowmap i), mul_one]
      simp [Finset.erase_eq]

end LogarithmicMorrisFull
