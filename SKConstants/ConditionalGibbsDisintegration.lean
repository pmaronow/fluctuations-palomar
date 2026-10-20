module

public import SKConstants.GaussianConditionalReverse

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal NNReal Topology Classical
set_option backward.isDefEq.respectTransparency false

namespace SKConstants

theorem conditionalGibbsSpinMass_sum {n : ℕ} (beta sigma : ℝ) :
    ∑ x : Spin n, conditionalGibbsSpinMass beta sigma x = 1 := by
  unfold conditionalGibbsSpinMass
  rw [← integral_finsetSum _ (fun x _ => goeGibbsProbability_integrable beta sigma x)]
  simp_rw [gibbsProbability_sum]
  simp

def conditionalGibbsSpinLaw (n : ℕ) (beta sigma : ℝ) : Measure (Spin n) :=
  finiteWeightMeasure (conditionalGibbsSpinMass beta sigma)

instance conditionalGibbsSpinLaw_isProbability (n : ℕ) (beta sigma : ℝ) :
    IsProbabilityMeasure (conditionalGibbsSpinLaw n beta sigma) :=
  finiteWeightMeasure_probability _ (fun x => (conditionalGibbsSpinMass_pos beta sigma x).le)
    (conditionalGibbsSpinMass_sum beta sigma)

instance primitiveJointGibbsLaw_isProbability (n : ℕ) (beta sigma : ℝ) :
    IsProbabilityMeasure (primitiveJointGibbsLaw n beta sigma) := by
  unfold primitiveJointGibbsLaw
  infer_instance

theorem measure_prod_finite_right {X V : Type*} [MeasurableSpace X] [MeasurableSpace V]
    [Fintype V] [MeasurableSingletonClass V] (μ : Measure (X × V))
    (B : Set X) (hB : MeasurableSet B) (A : Set V) :
    μ (B ×ˢ A) = ∑ x : V, if x ∈ A then μ (B ×ˢ {x}) else 0 := by
  classical
  let s := A.toFinset
  have hset : B ×ˢ A = ⋃ x ∈ s, B ×ˢ {x} := by
    ext p
    simp [s]
  rw [hset, measure_biUnion_finset (fun x hx y hy hxy => by
    apply Set.disjoint_left.mpr
    intro p hp hq
    exact hxy ((mem_singleton_iff.mp hp.2).symm.trans (mem_singleton_iff.mp hq.2)))
      (fun x hx => hB.prod (measurableSet_singleton x))]
  have hs : s = Finset.univ.filter (fun x => x ∈ A) := by ext x; simp [s]
  rw [hs, Finset.sum_filter]

theorem primitiveJointGibbsLaw_disintegrated (n : ℕ) (beta sigma : ℝ) :
    (primitiveJointGibbsLaw n beta sigma).map Prod.swap =
      conditionalGibbsSpinLaw n beta sigma ⊗ₘ conditionalGibbsGaussianKernel n beta sigma := by
  classical
  apply Measure.ext_prod
  intro A B hA hB
  rw [Measure.map_apply measurable_swap (hA.prod hB)]
  rw [Set.preimage_swap_prod]
  rw [measure_prod_finite_right _ B hB A,
    Measure.compProd_apply_prod hA hB, ← lintegral_indicator hA]
  simp_rw [primitiveJointGibbsLaw_spin_fiber beta sigma _ B hB]
  simp only [conditionalGibbsSpinLaw, finiteWeightMeasure, lintegral_finsetSum_measure,
    lintegral_smul_measure, lintegral_dirac, Set.indicator_apply, conditionalGibbsGaussianKernel]
  apply Finset.sum_congr rfl
  intro x hx
  split_ifs <;> simp

theorem conditionalGibbsSpinLaw_sk (n : ℕ) (beta : ℝ) :
    conditionalGibbsSpinLaw n beta (1 / Real.sqrt (2 * (n : ℝ))) =
      finiteWeightMeasure (fun _ : Spin n => 1 / (2 : ℝ) ^ n) := by
  unfold conditionalGibbsSpinLaw
  congr 1
  funext x
  exact conditionalGibbsSpinMass_sk beta x

theorem primitiveJointGibbs_reverse_smoothing_KL (n : ℕ) (beta sigma : ℝ)
    (proposal : Kernel (Spin n) (EuclideanSpace ℝ (Fin n × Fin n))) [IsMarkovKernel proposal]
    (c : ℝ) (hc : c ≠ 0) (v : ℝ≥0) (hv : v ≠ 0) :
    klDiv (conditionalGibbsSpinLaw n beta sigma ⊗ₘ
      (gaussianEuclideanSmoothingKernel c v ∘ₖ conditionalGibbsGaussianKernel n beta sigma))
      (conditionalGibbsSpinLaw n beta sigma ⊗ₘ (gaussianEuclideanSmoothingKernel c v ∘ₖ proposal)) ≤
      ENNReal.ofReal (c ^ 2 / (v : ℝ)) *
        klDiv (conditionalGibbsSpinLaw n beta sigma ⊗ₘ proposal)
          ((primitiveJointGibbsLaw n beta sigma).map Prod.swap) := by
  rw [primitiveJointGibbsLaw_disintegrated]
  exact conditionalGibbs_common_spin_reverse_smoothing_KL n beta sigma _ proposal c hc v hv

end SKConstants
