import logarithmicmorris.LogarithmicMorrisFullBasic

noncomputable section

open scoped BigOperators

namespace LogarithmicMorrisFull

lemma standardLogCT_eq_finsupp_sum (S : Setup) (F : Laurent ℚ S.n) :
    standardLogCT S F = F.sum fun e c => c * standardLogWeight S e := by
  classical
  simp [standardLogCT, Finsupp.sum]

lemma standardLogCT_add_clean (S : Setup) (F G : Laurent ℚ S.n) :
    standardLogCT S (F + G) = standardLogCT S F + standardLogCT S G := by
  classical
  simp only [standardLogCT_eq_finsupp_sum]
  rw [Finsupp.sum_add_index (h_zero := fun e => by simp)
    (h_add := fun e he c d => by ring)]

lemma standardLogCT_finset_sum_clean (S : Setup) {I : Type*} (s : Finset I)
    (F : I → Laurent ℚ S.n) :
    standardLogCT S (∑ i ∈ s, F i) = ∑ i ∈ s, standardLogCT S (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [standardLogCT_eq_finsupp_sum]
  | @insert i s hi ih =>
      simp [hi, standardLogCT_add_clean, ih]

end LogarithmicMorrisFull
