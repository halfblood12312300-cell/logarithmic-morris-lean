import logarithmicmorris.ScratchKernelEval

noncomputable section

open scoped BigOperators

namespace LogarithmicMorrisFull

def permuteTorus {n : ℕ} (σ : Equiv.Perm (Fin n))
    (t : UnitAddTorus (Fin n)) : UnitAddTorus (Fin n) :=
  fun i => t (σ i)

theorem prod_increasingPairs_eq_prod_Ioi {n : ℕ}
    (f : Fin n → Fin n → ℂ) :
    (∏ p ∈ increasingPairs n, f p.1 p.2) =
      ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, f i j := by
  simp only [increasingPairs, Finset.prod_filter]
  simp_rw [← Finset.filter_lt_eq_Ioi, Finset.prod_filter]
  exact (Finset.prod_product _ _ _).trans rfl

theorem vandermondeProduct_permute {n : ℕ} (σ : Equiv.Perm (Fin n))
    (x : Fin n → ℂ) :
    (∏ p ∈ increasingPairs n, (x (σ p.1) - x (σ p.2))) =
      ((σ.sign : ℤ) : ℂ) *
        ∏ p ∈ increasingPairs n, (x p.1 - x p.2) := by
  rw [prod_increasingPairs_eq_prod_Ioi
        (fun i j => x (σ i) - x (σ j)),
      prod_increasingPairs_eq_prod_Ioi (fun i j => x i - x j)]
  exact σ.prod_Ioi_comp_eq_sign_mul_prod
    (f := fun i j => x i - x j) (fun i j => by ring)

theorem prod_orderedPairs_permute {n : ℕ} (σ : Equiv.Perm (Fin n))
    (f : Fin n → Fin n → ℂ) :
    (∏ p ∈ orderedPairs n, f (σ p.1) (σ p.2)) =
      ∏ p ∈ orderedPairs n, f p.1 p.2 := by
  classical
  symm
  refine Finset.prod_equiv (Equiv.prodCongr σ.symm σ.symm) ?_ ?_
  · intro p
    simp [orderedPairs]
  · intro p hp
    simp

theorem torusEval_morrisKernel_permute (S : Setup)
    (σ : Equiv.Perm (Fin S.n)) (t : UnitAddTorus (Fin S.n)) :
    torusEval (morrisKernel S) (permuteTorus σ t) =
      ((σ.sign : ℤ) : ℂ) * torusEval (morrisKernel S) t := by
  rw [torusEval_morrisKernel, torusEval_morrisKernel]
  simp only [permuteTorus]
  rw [vandermondeProduct_permute σ (fun i => fourier 1 (t i))]
  have hcenter :
      (∏ i : Fin S.n,
        (fourier 1 (t (σ i)))⁻¹ ^ S.m *
          (1 - fourier 1 (t (σ i))) ^ S.a *
          (1 - (fourier 1 (t (σ i)))⁻¹) ^ S.b) =
      ∏ i : Fin S.n,
        (fourier 1 (t i))⁻¹ ^ S.m *
          (1 - fourier 1 (t i)) ^ S.a *
          (1 - (fourier 1 (t i))⁻¹) ^ S.b := by
    exact Equiv.prod_comp σ (fun i : Fin S.n =>
      (fourier 1 (t i))⁻¹ ^ S.m *
        (1 - fourier 1 (t i)) ^ S.a *
        (1 - (fourier 1 (t i))⁻¹) ^ S.b)
  rw [hcenter, prod_orderedPairs_permute σ
    (fun i j => (1 - fourier 1 (t i) / fourier 1 (t j)) ^ S.k)]
  ring

end LogarithmicMorrisFull
