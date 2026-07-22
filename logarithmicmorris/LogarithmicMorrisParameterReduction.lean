import logarithmicmorris.AristotleShiftRecurrenceFresh
import logarithmicmorris.ScratchCircularSwap

/-! # Reduction of endpoint parameters to the Dyson specialization -/

noncomputable section

open scoped BigOperators

namespace LogarithmicMorrisFull

set_option maxHeartbeats 1000000

@[simp] theorem shiftFamily_zero (S : Setup) (a b : ℕ) :
    shiftFamily S a b 0 = logarithmicMorrisLHS (S.withAB a b) := by
  unfold shiftFamily logarithmicMorrisLHS signedElementary
  simp +decide [Finset.sum_filter, Finset.prod_filter]

/-- Summing all signed elementary insertions multiplies the kernel by
`prod_i (1-x_i)` and hence increments `a`. -/
theorem shiftFamily_sum_eq_succ_a (S : Setup) (a b : ℕ) :
    (∑ r ∈ Finset.range (S.n + 1), shiftFamily S a b r) =
      logarithmicMorrisLHS (S.withAB (a + 1) b) := by
  unfold shiftFamily
  have h_sum :
      ∑ r ∈ Finset.range (S.n + 1),
          morrisKernel (S.withAB a b) * signedElementary (S.withAB a b).n r =
        morrisKernel (S.withAB (a + 1) b) := by
    have h_elem :
        ∑ r ∈ Finset.range (S.n + 1),
            signedElementary (S.withAB a b).n r =
          ∏ i : Fin (S.withAB a b).n, (1 - MultiLaurent.var i) := by
      simp +decide [sub_eq_neg_add, Finset.prod_add,
        Finset.prod_mul_distrib, Finset.sum_mul, signedElementary]
      rw [Finset.sum_sigma']
      refine Finset.sum_bij (fun x hx => x.snd) ?_ ?_ ?_ ?_ <;>
        simp +decide
      · grind
      · exact fun x => le_trans (Finset.card_le_univ _)
          (by simp +decide [Setup.withAB])
    rw [← Finset.mul_sum _ _ _, h_elem]
    unfold morrisKernel
    simp +decide [mul_assoc, Finset.prod_mul_distrib, pow_succ, Setup.withAB]
    exact Or.inl <| Or.inl <| Or.inl <| by ring
  rw [← standardLogCT_finset_sum_clean]
  exact congrArg (standardLogCT (S.withAB a b)) h_sum

/-- Finite Chu--Vandermonde in the exact product form required by the
parameter recurrence. -/
theorem finite_vandermonde_product
    (n : ℕ) (A B K : ℚ)
    (hden : ∀ i < n, A + (i : ℚ) * K ≠ 0) :
    (∑ r ∈ Finset.range (n + 1),
      (Nat.choose n r : ℚ) *
        (∏ j ∈ Finset.range r, (B + (j : ℚ) * K)) /
        (∏ j ∈ Finset.range r,
          (A + ((n - 1 - j : ℕ) : ℚ) * K))) =
      ∏ i ∈ Finset.range n,
        (A + B + (i : ℚ) * K) / (A + (i : ℚ) * K) := by
  revert n A B K hden
  intro n A B K hden
  have h_eq :
      (∑ r ∈ Finset.range (n + 1),
        (Nat.choose n r : ℚ) *
          (∏ j ∈ Finset.range r, (B + j * K)) *
          (∏ j ∈ Finset.range (n - r), (A + j * K))) =
        ∏ i ∈ Finset.range n, (A + B + i * K) := by
    induction' n with n ih generalizing A B K
    · norm_num
    · have h_split :
          ∑ r ∈ Finset.range (n + 2),
              (Nat.choose (n + 1) r : ℚ) *
                (∏ j ∈ Finset.range r, (B + j * K)) *
                (∏ j ∈ Finset.range (n + 1 - r), (A + j * K)) =
            (∑ r ∈ Finset.range (n + 1),
              (Nat.choose n r : ℚ) *
                (∏ j ∈ Finset.range r, (B + j * K)) *
                (∏ j ∈ Finset.range (n + 1 - r), (A + j * K))) +
            (∑ r ∈ Finset.range (n + 1),
              (Nat.choose n r : ℚ) *
                (∏ j ∈ Finset.range (r + 1), (B + j * K)) *
                (∏ j ∈ Finset.range (n - r), (A + j * K))) := by
          rw [Finset.sum_range_succ']
          rw [Finset.sum_range_succ]
          simp +decide [Nat.choose_succ_succ, add_mul, mul_add,
            Finset.sum_add_distrib]
          ring
          rw [add_comm 1 n, Finset.sum_range_succ']
          simp +decide [add_comm, add_left_comm, add_assoc,
            Finset.sum_range_succ]
          ring
      simp_all +decide [Finset.prod_range_succ]
      rw [← ih A B K fun i hi => hden i (Nat.le_of_lt hi)]
      rw [Finset.sum_mul _ _ _]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Nat.sub_add_comm (Finset.mem_range_succ_iff.mp hi)]
      ring
      rw [add_comm 1, Finset.prod_range_succ]
      ring
      rw [Nat.cast_sub (Finset.mem_range_succ_iff.mp hi)]
      ring
  convert congr_arg (fun x : ℚ => x /
      ∏ i ∈ Finset.range n, (A + i * K)) h_eq using 1
  · rw [Finset.sum_div _ _ _]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [div_eq_div_iff]
    · rw [show (Finset.range n : Finset ℕ) =
          Finset.range (n - i) ∪
            Finset.image (fun j => n - 1 - j) (Finset.range i) from ?_,
        Finset.prod_union]
      · rw [Finset.prod_image] <;> norm_num [mul_assoc]
        exact fun x hx y hy hxy => by
          rw [tsub_right_inj] at hxy <;>
            linarith [Finset.mem_range.mp hi,
              Nat.sub_add_cancel (show 1 ≤ n from Nat.pos_of_ne_zero (by aesop_cat)),
              hx.out, hy.out]
      · norm_num [Finset.disjoint_right]
        exact fun a ha => by omega
      · ext j
        simp +zetaDelta at *
        exact ⟨fun hj => or_iff_not_imp_left.mpr fun h =>
          ⟨n - 1 - j, by omega, by omega⟩,
          fun hj => hj.elim (fun hj => by omega)
            fun ⟨a, ha, hj⟩ => by omega⟩
    · exact Finset.prod_ne_zero_iff.mpr fun j hj =>
        hden _ <| by norm_num at *; omega
    · exact Finset.prod_ne_zero_iff.mpr fun i hi =>
        hden i (Finset.mem_range.mp hi)
  · rw [Finset.prod_div_distrib]

/-- One step of endpoint reduction in `a`. -/
theorem logarithmicMorrisLHS_succ_a (S : Setup) (a b : ℕ) :
    logarithmicMorrisLHS (S.withAB (a + 1) b) =
      logarithmicMorrisLHS (S.withAB a b) *
        ∏ i ∈ Finset.range S.n,
          ((2 * a + 2 * b + 2 + i * S.K : ℕ) : ℚ) /
            ((2 * a + 2 + i * S.K : ℕ) : ℚ) := by
  rw [← shiftFamily_sum_eq_succ_a]
  have h_recurrence : ∀ r ∈ Finset.range (S.n + 1),
      shiftFamily S a b r =
        (Nat.choose S.n r : ℚ) *
          (∏ j ∈ Finset.range r, (2 * b + j * S.K : ℚ)) /
          (∏ j ∈ Finset.range r,
            (2 * a + 2 + (S.n - 1 - j) * S.K : ℚ)) *
          logarithmicMorrisLHS (S.withAB a b) := by
    intro r hr
    induction' r with r ih <;>
      simp_all +decide [Nat.choose_succ_succ, Finset.prod_range_succ]
    have h_step :
        shiftFamily S a b (r + 1) =
          ((S.n - r : ℚ) * (2 * b + r * S.K) /
            ((r + 1 : ℚ) *
              (2 * a + 2 + (S.n - r - 1) * S.K))) *
            shiftFamily S a b r := by
      have h := shift_recurrence_fresh S a b r hr
      rw [div_mul_eq_mul_div, eq_div_iff] <;>
        norm_cast at * <;>
        simp_all +decide [Nat.sub_sub]
      · rw [Nat.cast_sub hr.le] at *
        linear_combination' h.symm
      · norm_cast
        rw [Int.subNatNat_eq_coe]
        norm_num
        nlinarith [show (S.K : ℤ) > 0 from mod_cast S.K_pos,
          show (r : ℤ) + 1 ≤ S.n from mod_cast hr]
    rw [h_step, ih (Nat.le_of_lt hr)]
    rw [Nat.cast_choose, Nat.cast_choose] <;> try linarith
    field_simp
    rw [show (S.n - r : ℕ) = (S.n - (r + 1)) + 1 by omega]
    push_cast [Nat.factorial_succ]
    ring
    rw [Nat.cast_sub (by linarith)]
    push_cast
    ring
  convert congr_arg
      (fun x : ℚ => x * logarithmicMorrisLHS (S.withAB a b))
      (finite_vandermonde_product S.n (2 * a + 2) (2 * b) S.K ?_)
      using 1
  · rw [Finset.sum_mul _ _ _]
    refine Finset.sum_congr rfl fun r hr => ?_
    convert h_recurrence r hr using 3
    refine Finset.prod_congr rfl fun x hx => ?_
    rw [Nat.cast_sub <| Nat.le_sub_one_of_lt <| by
      linarith [Finset.mem_range.mp hx, Finset.mem_range.mp hr]]
    rw [Nat.cast_sub <| by
      linarith [Finset.mem_range.mp hx, Finset.mem_range.mp hr]]
    push_cast
    ring
  · grind +locals
  · exact fun i hi => by positivity

/-- The explicit right-hand side obeys the same `a`-shift. -/
theorem logarithmicMorrisRHS_succ_a (S : Setup) (a b : ℕ) :
    logarithmicMorrisRHS (S.withAB (a + 1) b) =
      logarithmicMorrisRHS (S.withAB a b) *
        ∏ i ∈ Finset.range S.n,
          ((2 * a + 2 * b + 2 + i * S.K : ℕ) : ℚ) /
            ((2 * a + 2 + i * S.K : ℕ) : ℚ) := by
  unfold logarithmicMorrisRHS rhsFactor
  simp +decide [mul_assoc]
  rw [div_mul_div_comm, ← Finset.prod_div_distrib]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  rw [← Finset.prod_div_distrib]
  refine Or.inl <| Finset.prod_congr rfl fun x hx => ?_
  rw [div_eq_div_iff] <;> norm_cast <;>
    simp +decide [*, Nat.mul_succ, Nat.add_mul_div_left]
  ring
  · rw [show 2 + a * 2 + b * 2 + x * S.K =
        (a * 2 + b * 2 + x * S.K) + 2 by ring,
      show 2 + a * 2 + x * S.K = (a * 2 + x * S.K) + 2 by ring]
    rw [doubleFactorial_succ_succ, doubleFactorial_succ_succ]
    ring
  · exact ⟨doubleFactorial_ne_zero _, doubleFactorial_ne_zero _,
      doubleFactorial_ne_zero _⟩
  · exact ⟨doubleFactorial_ne_zero _, doubleFactorial_ne_zero _,
      doubleFactorial_ne_zero _⟩

/-- Endpoint exchange for the concrete logarithmic constant term. -/
theorem logarithmicMorrisLHS_swap_ab (S : Setup) (a b : ℕ) :
    logarithmicMorrisLHS (S.withAB a b) =
      logarithmicMorrisLHS (S.withAB b a) := by
  have h := logarithmicMorrisLHS_swapAB (S.withAB a b)
  have heq : (S.withAB a b).swapAB = S.withAB b a := rfl
  simpa only [heq] using h

theorem logarithmicMorrisRHS_swap_ab (S : Setup) (a b : ℕ) :
    logarithmicMorrisRHS (S.withAB a b) =
      logarithmicMorrisRHS (S.withAB b a) := by
  have h := logarithmicMorrisRHS_swapAB (S.withAB a b)
  have heq : (S.withAB a b).swapAB = S.withAB b a := rfl
  simpa only [heq] using h

/-- The full identity follows from its `a=b=0` specialization. -/
theorem logarithmicMorris_parameter_reduction (S : Setup)
    (hbase : LogarithmicMorrisStatement (S.withAB 0 0)) :
    LogarithmicMorrisStatement S := by
  have ha0 : ∀ a : ℕ,
      LogarithmicMorrisStatement (S.withAB a 0) := by
    intro a
    induction' a with a ih
    · exact hbase
    · unfold LogarithmicMorrisStatement at *
      rw [logarithmicMorrisLHS_succ_a,
        logarithmicMorrisRHS_succ_a, ih]
  have h0b : ∀ b : ℕ,
      LogarithmicMorrisStatement (S.withAB 0 b) := by
    intro b
    unfold LogarithmicMorrisStatement at *
    rw [logarithmicMorrisLHS_swap_ab S 0 b,
      logarithmicMorrisRHS_swap_ab S 0 b]
    exact ha0 b
  have hab : ∀ a b : ℕ,
      LogarithmicMorrisStatement (S.withAB a b) := by
    intro a b
    induction' a with a ih
    · exact h0b b
    · unfold LogarithmicMorrisStatement at *
      rw [logarithmicMorrisLHS_succ_a,
        logarithmicMorrisRHS_succ_a, ih]
  convert hab S.a S.b using 1

end LogarithmicMorrisFull
