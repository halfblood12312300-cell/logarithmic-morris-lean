import logarithmicmorris.LogarithmicMorrisFullArithmetic

/-!
# Arithmetic for the odd Dyson specialization

This file contains no integral evaluation.  It only verifies that the proposed
closed form obeys the exact `k ↦ k+1` multiplier used by the shift task.
-/

noncomputable section

open scoped BigOperators

namespace LogarithmicMorrisFull

/-- Keep the odd rank and replace the interaction parameter, setting the two
endpoint parameters to zero. -/
def dysonSetup (S : Setup) (k : ℕ) : Setup where
  n := S.n
  m := S.m
  k := k
  a := 0
  b := 0
  odd_rank := S.odd_rank

@[simp] theorem dysonSetup_n (S : Setup) (k : ℕ) :
    (dysonSetup S k).n = S.n := rfl

@[simp] theorem dysonSetup_m (S : Setup) (k : ℕ) :
    (dysonSetup S k).m = S.m := rfl

@[simp] theorem dysonSetup_k (S : Setup) (k : ℕ) :
    (dysonSetup S k).k = k := rfl

@[simp] theorem dysonSetup_a (S : Setup) (k : ℕ) :
    (dysonSetup S k).a = 0 := rfl

@[simp] theorem dysonSetup_b (S : Setup) (k : ℕ) :
    (dysonSetup S k).b = 0 := rfl

@[simp] theorem dysonSetup_K (S : Setup) (k : ℕ) :
    (dysonSetup S k).K = 2 * k + 1 := rfl

/-- The Gamma/Pochhammer expression has no Pochhammer contribution at
`a=b=0`; at an odd exponent it is a double-factorial quotient. -/
theorem gammaPochhammerPart_dyson (S : Setup) (k : ℕ) :
    gammaPochhammerPart (dysonSetup S k) (dysonSetup S k).K =
      (2 / (Real.pi : ℂ)) ^ S.m *
        (doubleFactorial (S.n * (2 * k + 1)) : ℂ) /
          (doubleFactorial (2 * k + 1) : ℂ) ^ S.n := by
  simpa [gammaPochhammerPart, complexGammaRatio] using
    (complexGammaRatio_at_K (dysonSetup S k))

/-- The rational multiplier in the odd Dyson shift. -/
def dysonShiftMultiplier (S : Setup) (k : ℕ) : ℂ :=
  (∏ j ∈ Finset.range S.n,
      (((S.n * (2 * k + 1) + 2 + 2 * j : ℕ) : ℂ))) /
    (((2 * k + 3 : ℕ) : ℂ) ^ S.n)

theorem gammaPochhammerPart_dyson_shift (S : Setup) (k : ℕ) :
    gammaPochhammerPart (dysonSetup S (k + 1))
        (dysonSetup S (k + 1)).K =
      gammaPochhammerPart (dysonSetup S k) (dysonSetup S k).K *
        dysonShiftMultiplier S k := by
  rw [gammaPochhammerPart_dyson, gammaPochhammerPart_dyson]
  unfold dysonShiftMultiplier
  have hnumNat := doubleFactorial_add_two_mul (S.n * (2 * k + 1)) S.n
  have hnumIndex :
      S.n * (2 * (k + 1) + 1) = S.n * (2 * k + 1) + 2 * S.n := by
    ring
  have hdenIndex : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by ring
  rw [hnumIndex, hdenIndex, doubleFactorial_succ_succ]
  rw [hnumNat]
  have hprod :
      (∏ j ∈ Finset.range S.n,
          ((S.n * (2 * k + 1) + 2 * (j + 1) : ℕ) : ℂ)) =
        ∏ j ∈ Finset.range S.n,
          ((S.n * (2 * k + 1) + 2 + 2 * j : ℕ) : ℂ) := by
    apply Finset.prod_congr rfl
    intro j hj
    congr 1
    ring
  push_cast at hprod ⊢
  rw [hprod]
  have hdf : (doubleFactorial (2 * k + 1) : ℂ) ≠ 0 := by
    exact_mod_cast doubleFactorial_ne_zero (2 * k + 1)
  have hstep : (2 * (k : ℂ) + 1 + 2) = 2 * (k : ℂ) + 3 := by
    ring
  have hk : (2 * (k : ℂ) + 3) ≠ 0 := by
    exact_mod_cast (show 2 * k + 3 ≠ 0 by omega)
  rw [hstep]
  field_simp [hdf, hk]
  ring_nf
  have hfactor :
      (k : ℂ) * (doubleFactorial (1 + k * 2) : ℂ) * 2 +
          (doubleFactorial (1 + k * 2) : ℂ) * 3 =
        (doubleFactorial (1 + k * 2) : ℂ) * (3 + (k : ℂ) * 2) := by
    ring
  rw [hfactor, mul_pow]
  ring

end LogarithmicMorrisFull
