module

public import SKConstants.SKSparseFields
public import SKConstants.HeatBathBoundary

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set WithLp
open scoped ENNReal NNReal Topology BigOperators RealInnerProductSpace Classical Matrix Matrix.Norms.L2Operator
set_option backward.isDefEq.respectTransparency false

namespace SKConstants

theorem exists_sparseFieldDirection_abs_sum {n r : ℕ} (h : Fin n → ℝ)
    (I : Finset (Fin n)) (hI : I.card ≤ r) :
    ∃ p ∈ sparseFieldDirections n r,
      (∑ i ∈ I, |h i|) = ∑ i, sparseFieldDirection p i * h i := by
  let pos : Spin n := fun i => decide (i ∈ I ∧ 0 ≤ h i)
  let neg : Spin n := fun i => decide (i ∈ I ∧ h i < 0)
  have hpos : pos ∈ spinHammingBall (fun _ => false) r := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    change (spinDifferenceSet (fun _ => false) pos).card ≤ r
    apply (Finset.card_le_card (show spinDifferenceSet (fun _ => false) pos ⊆ I from ?_)).trans hI
    intro i hi
    have hi' : decide (i ∈ I ∧ 0 ≤ h i) ≠ false := by
      simpa only [spinDifferenceSet, Finset.mem_filter, Finset.mem_univ, true_and, pos, ne_comm] using hi
    exact (of_decide_eq_true (Bool.eq_true_of_ne_false hi')).1
  have hneg : neg ∈ spinHammingBall (fun _ => false) r := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    change (spinDifferenceSet (fun _ => false) neg).card ≤ r
    apply (Finset.card_le_card (show spinDifferenceSet (fun _ => false) neg ⊆ I from ?_)).trans hI
    intro i hi
    have hi' : decide (i ∈ I ∧ h i < 0) ≠ false := by
      simpa only [spinDifferenceSet, Finset.mem_filter, Finset.mem_univ, true_and, neg, ne_comm] using hi
    exact (of_decide_eq_true (Bool.eq_true_of_ne_false hi')).1
  refine ⟨(pos, neg), Finset.mem_product.mpr ⟨hpos, hneg⟩, ?_⟩
  have hout (i : Fin n) (hi : i ∉ I) : sparseFieldDirection (pos, neg) i = 0 := by
    simp [sparseFieldDirection, signedSpin, pos, neg, hi]
  rw [← Finset.sum_subset (Finset.subset_univ I)
    (fun i hiU hiI => by rw [hout i hiI, zero_mul])]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hh : 0 ≤ h i
  · simp [sparseFieldDirection, signedSpin, pos, neg, hi, hh,
      not_lt.mpr hh, abs_of_nonneg hh]
  · have hh' := lt_of_not_ge hh
    simp only [sparseFieldDirection, signedSpin, pos, neg, hi, hh, hh', abs_of_neg hh',
      true_and, decide_true, decide_false, Bool.false_eq_true, ite_false, ite_true]
    ring

theorem sparseFieldBadSet_controls_absolute_sums {n r : ℕ} (x : Spin n)
    (A : ℝ) (z : EuclideanSpace ℝ (Fin n × Fin n))
    (hz : z ∉ sparseFieldBadSet x r A) (I : Finset (Fin n)) (hI : I.card ≤ r) :
    (∑ i ∈ I, |∑ j, GaussianProposal.goeMatrix (1 / Real.sqrt (2 * (n : ℝ))) z i j *
      signedSpin x j|) < A := by
  obtain ⟨p, hp, he⟩ := exists_sparseFieldDirection_abs_sum
    (fun i => ∑ j, GaussianProposal.goeMatrix (1 / Real.sqrt (2 * (n : ℝ))) z i j *
      signedSpin x j) I hI
  rw [he]
  change goeSignedSpinField (1 / Real.sqrt (2 * (n : ℝ))) x (sparseFieldDirection p) z < A
  apply lt_of_not_ge
  intro hge
  apply hz
  exact mem_iUnion.mpr ⟨p, mem_iUnion.mpr ⟨hp, hge⟩⟩

end SKConstants
