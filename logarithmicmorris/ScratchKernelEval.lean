import logarithmicmorris.LogarithmicMorrisEvaluation

noncomputable section

open scoped BigOperators ComplexConjugate

namespace LogarithmicMorrisFull

theorem one_sub_div_mul_reverse {x y : ℂ} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    (1 - x / y) * (1 - y / x) = (‖x - y‖ : ℂ) ^ 2 := by
  have hx0 : x ≠ 0 := by
    intro h
    simp [h] at hx
  have hy0 : y ≠ 0 := by
    intro h
    simp [h] at hy
  have hnx : Complex.normSq x = 1 := by
    rw [Complex.normSq_eq_norm_sq, hx]
    norm_num
  have hny : Complex.normSq y = 1 := by
    rw [Complex.normSq_eq_norm_sq, hy]
    norm_num
  have hcx : conj x * x = 1 := by
    rw [← Complex.normSq_eq_conj_mul_self, hnx]
    norm_num
  have hcy : conj y * y = 1 := by
    rw [← Complex.normSq_eq_conj_mul_self, hny]
    norm_num
  have hrhs : (‖x - y‖ : ℂ) ^ 2 = (Complex.normSq (x - y) : ℂ) := by
    rw [Complex.normSq_eq_norm_sq]
    push_cast
    rfl
  simp_rw [div_eq_mul_inv, Complex.inv_def, hnx, hny]
  norm_num
  rw [hrhs, Complex.normSq_eq_conj_mul_self, map_sub]
  ring_nf at hcx hcy ⊢
  linear_combination (((starRingEnd ℂ) x * x) - 2) * hcy + hcy

def decreasingPairs (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun p => p.2 < p.1

theorem orderedPairs_eq_union (n : ℕ) :
    orderedPairs n = increasingPairs n ∪ decreasingPairs n := by
  ext p
  simp only [orderedPairs, increasingPairs, decreasingPairs,
    Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
  omega

theorem disjoint_increasing_decreasing (n : ℕ) :
    Disjoint (increasingPairs n) (decreasingPairs n) := by
  rw [Finset.disjoint_left]
  intro p hp hq
  simp only [increasingPairs, decreasingPairs, Finset.mem_filter,
    Finset.mem_univ, true_and] at hp hq
  omega

theorem image_swap_increasingPairs (n : ℕ) :
    (increasingPairs n).image (fun p : Fin n × Fin n => (p.2, p.1)) =
      decreasingPairs n := by
  ext p
  simp only [Finset.mem_image, increasingPairs, decreasingPairs,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact hq
  · intro hp
    exact ⟨(p.2, p.1), hp, by simp⟩

theorem card_decreasingPairs_eq (n : ℕ) :
    (decreasingPairs n).card = (increasingPairs n).card := by
  rw [← image_swap_increasingPairs]
  apply Finset.card_image_of_injective
  intro p q h
  simpa using congrArg (fun z : Fin n × Fin n => (z.2, z.1)) h

theorem orderedPairs_eq_offDiag (n : ℕ) :
    orderedPairs n = (Finset.univ : Finset (Fin n)).offDiag := by
  ext p
  simp [orderedPairs, Finset.mem_offDiag]

theorem card_increasingPairs_odd (m : ℕ) :
    (increasingPairs (2 * m + 1)).card = m * (2 * m + 1) := by
  let n := 2 * m + 1
  have hu := congrArg Finset.card (orderedPairs_eq_union n)
  rw [Finset.card_union_of_disjoint (disjoint_increasing_decreasing n),
    card_decreasingPairs_eq] at hu
  have hoff := congrArg Finset.card (orderedPairs_eq_offDiag n)
  simp only [Finset.offDiag_card, Finset.card_univ, Fintype.card_fin] at hoff
  dsimp [n] at hu hoff ⊢
  have hcalc :
      (2 * m + 1) * (2 * m + 1) - (2 * m + 1) =
        2 * (m * (2 * m + 1)) := by
    conv_lhs =>
      rhs
      rw [← Nat.mul_one (2 * m + 1)]
    rw [← Nat.mul_sub_left_distrib]
    simp
    ring
  rw [hcalc] at hoff
  omega

theorem sum_decreasingPairs (n : ℕ) (f : Fin n × Fin n → ℂ) :
    (∑ p ∈ decreasingPairs n, f p) =
      ∑ p ∈ increasingPairs n, f (p.2, p.1) := by
  let swap : Fin n × Fin n → Fin n × Fin n := fun p => (p.2, p.1)
  have himage : (increasingPairs n).image swap = decreasingPairs n := by
    exact image_swap_increasingPairs n
  rw [← himage, Finset.sum_image]
  intro p hp q hq heq
  simpa [swap] using congrArg swap heq

theorem sum_orderedPairs_symmetric (n : ℕ) (f : Fin n → ℂ) :
    (∑ p ∈ orderedPairs n, (f p.1 + f p.2)) =
      2 * ∑ p ∈ increasingPairs n, (f p.1 + f p.2) := by
  rw [orderedPairs_eq_union,
    Finset.sum_union (disjoint_increasing_decreasing n),
    sum_decreasingPairs]
  have hswap :
      (∑ p ∈ increasingPairs n, (f p.2 + f p.1)) =
        ∑ p ∈ increasingPairs n, (f p.1 + f p.2) := by
    apply Finset.sum_congr rfl
    intro p hp
    ring
  rw [hswap]
  ring

theorem sum_orderedPairs (n : ℕ) (f : Fin n → ℂ) :
    (∑ p ∈ orderedPairs n, (f p.1 + f p.2)) =
      2 * (n - 1 : ℕ) * ∑ i : Fin n, f i := by
  cases n with
  | zero => simp [orderedPairs]
  | succ n =>
    rw [orderedPairs_eq_offDiag]
    have hparts := congrArg
      (fun s : Finset (Fin (n + 1) × Fin (n + 1)) =>
        ∑ p ∈ s, (f p.1 + f p.2))
      (Finset.diag_union_offDiag (Finset.univ : Finset (Fin (n + 1))))
    change
      (∑ p ∈ (Finset.univ : Finset (Fin (n + 1))).diag ∪
          (Finset.univ : Finset (Fin (n + 1))).offDiag,
          (f p.1 + f p.2)) =
        ∑ p ∈ (Finset.univ : Finset (Fin (n + 1))) ×ˢ
          (Finset.univ : Finset (Fin (n + 1))), (f p.1 + f p.2) at hparts
    rw [Finset.sum_union
      (Finset.disjoint_diag_offDiag
        (s := (Finset.univ : Finset (Fin (n + 1)))))] at hparts
    simp only [Finset.sum_diag, Finset.univ_product_univ,
      Finset.sum_add_distrib] at hparts
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type] at hparts
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at hparts
    have hn : (((n + 1 : ℕ) : ℂ) - 1) = ((n + 1 - 1 : ℕ) : ℂ) := by
      push_cast
      ring
    rw [Finset.sum_add_distrib]
    rw [← Finset.mul_sum] at hparts
    linear_combination hparts + (2 * ∑ i : Fin (n + 1), f i) * hn

theorem sum_increasingPairs (n : ℕ) (f : Fin n → ℂ) :
    (∑ p ∈ increasingPairs n, (f p.1 + f p.2)) =
      (n - 1 : ℕ) * ∑ i : Fin n, f i := by
  have hsym := sum_orderedPairs_symmetric n f
  have hord := sum_orderedPairs n f
  have htwo :
      2 * (∑ p ∈ increasingPairs n, (f p.1 + f p.2)) =
        2 * ((n - 1 : ℕ) * ∑ i : Fin n, f i) := by
    calc
      _ = ∑ p ∈ orderedPairs n, (f p.1 + f p.2) := hsym.symm
      _ = _ := by simpa [mul_assoc] using hord
  calc
    _ = (2 : ℂ)⁻¹ *
        (2 * ∑ p ∈ increasingPairs n, (f p.1 + f p.2)) := by
          ring
    _ = (2 : ℂ)⁻¹ *
        (2 * ((n - 1 : ℕ) * ∑ i : Fin n, f i)) := by rw [htwo]
    _ = _ := by ring

theorem prod_decreasingPairs (n : ℕ) (f : Fin n × Fin n → ℂ) :
    (∏ p ∈ decreasingPairs n, f p) =
      ∏ p ∈ increasingPairs n, f (p.2, p.1) := by
  let swap : Fin n × Fin n → Fin n × Fin n := fun p => (p.2, p.1)
  have himage : (increasingPairs n).image swap = decreasingPairs n := by
    exact image_swap_increasingPairs n
  rw [← himage, Finset.prod_image]
  intro p hp q hq heq
  simpa [swap] using congrArg swap heq

theorem prod_orderedPairs (n : ℕ) (f : Fin n × Fin n → ℂ) :
    (∏ p ∈ orderedPairs n, f p) =
      ∏ p ∈ increasingPairs n, f p * f (p.2, p.1) := by
  rw [orderedPairs_eq_union, Finset.prod_union
    (disjoint_increasing_decreasing n), prod_decreasingPairs]
  rw [← Finset.prod_mul_distrib]

theorem orderedRatioProduct_eq_norm (S : Setup)
    (t : UnitAddTorus (Fin S.n)) :
    (∏ p ∈ orderedPairs S.n,
        (1 - fourier 1 (t p.1) / fourier 1 (t p.2)) ^ S.k) =
      ∏ p ∈ increasingPairs S.n,
        (‖fourier 1 (t p.1) - fourier 1 (t p.2)‖ : ℂ) ^ (2 * S.k) := by
  rw [prod_orderedPairs]
  apply Finset.prod_congr rfl
  intro p hp
  rw [← mul_pow, one_sub_div_mul_reverse]
  · rw [pow_mul]
  · simp [fourier_apply]
  · simp [fourier_apply]

theorem torusEval_vandermonde (S : Setup)
    (t : UnitAddTorus (Fin S.n)) :
    torusEval (vandermonde S.n) t =
      ∏ p ∈ increasingPairs S.n,
        (fourier 1 (t p.1) - fourier 1 (t p.2)) := by
  simp [torusEval, vandermonde, addCircleUnit_coe]

theorem torusEval_morrisKernel (S : Setup)
    (t : UnitAddTorus (Fin S.n)) :
    torusEval (morrisKernel S) t =
      (∏ p ∈ increasingPairs S.n,
        (fourier 1 (t p.1) - fourier 1 (t p.2))) *
      (∏ i : Fin S.n,
        (fourier 1 (t i))⁻¹ ^ S.m *
          (1 - fourier 1 (t i)) ^ S.a *
          (1 - (fourier 1 (t i))⁻¹) ^ S.b) *
      (∏ p ∈ orderedPairs S.n,
        (1 - fourier 1 (t p.1) / fourier 1 (t p.2)) ^ S.k) := by
  simp [torusEval, morrisKernel, vandermonde, ratio,
    addCircleUnit_coe, div_eq_mul_inv]

end LogarithmicMorrisFull
