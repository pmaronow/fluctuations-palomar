module

public import SKConstants.ConditionalGibbsDisintegration
public import SKConstants.SKSparseFields

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators Classical
set_option backward.isDefEq.respectTransparency false

namespace SKConstants

theorem measurableSet_spin_dependent_event {X V : Type*} [MeasurableSpace X]
    [MeasurableSpace V] [Fintype V] [MeasurableSingletonClass V]
    (A : V → Set X) (hA : ∀ x, MeasurableSet (A x)) :
    MeasurableSet {p : X × V | p.1 ∈ A p.2} := by
  have he : {p : X × V | p.1 ∈ A p.2} = ⋃ x : V, A x ×ˢ {x} := by
    ext p
    simp
  rw [he]
  exact MeasurableSet.iUnion (fun x => (hA x).prod (measurableSet_singleton x))

theorem primitiveJointGibbsLaw_probability_eq_conditional_average {n : ℕ}
    (beta sigma : ℝ) (A : Spin n → Set (EuclideanSpace ℝ (Fin n × Fin n)))
    (hA : ∀ x, MeasurableSet (A x)) :
    (primitiveJointGibbsLaw n beta sigma).real {p | p.1 ∈ A p.2} =
      ∑ x, conditionalGibbsSpinMass beta sigma x *
        (conditionalGibbsGaussianLaw beta sigma x).real (A x) := by
  have hs : MeasurableSet {p : Spin n × EuclideanSpace ℝ (Fin n × Fin n) | p.2 ∈ A p.1} := by
    exact (measurableSet_spin_dependent_event A hA).preimage measurable_swap
  have hm : primitiveJointGibbsLaw n beta sigma {p | p.1 ∈ A p.2} =
      ∑ x, ENNReal.ofReal (conditionalGibbsSpinMass beta sigma x) *
        conditionalGibbsGaussianLaw beta sigma x (A x) := by
    calc
      _ = (conditionalGibbsSpinLaw n beta sigma ⊗ₘ
          conditionalGibbsGaussianKernel n beta sigma) {p | p.2 ∈ A p.1} := by
        rw [← primitiveJointGibbsLaw_disintegrated, Measure.map_apply measurable_swap hs]
        rfl
      _ = ∫⁻ x, conditionalGibbsGaussianLaw beta sigma x (A x)
          ∂conditionalGibbsSpinLaw n beta sigma := by
        rw [Measure.compProd_apply hs]
        rfl
      _ = _ := by
        simp [conditionalGibbsSpinLaw, finiteWeightMeasure, lintegral_finsetSum_measure,
          lintegral_smul_measure, lintegral_dirac]
  unfold Measure.real
  rw [hm, ENNReal.toReal_sum (fun x hx => ENNReal.mul_ne_top
    ENNReal.ofReal_ne_top (measure_ne_top _ _))]
  apply Finset.sum_congr rfl
  intro x hx
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (conditionalGibbsSpinMass_pos beta sigma x).le]

theorem primitiveJointGibbsLaw_probability_le_of_conditional_bound {n : ℕ}
    (beta sigma : ℝ) (A : Spin n → Set (EuclideanSpace ℝ (Fin n × Fin n)))
    (hA : ∀ x, MeasurableSet (A x)) (B : ℝ)
    (hB : ∀ x, (conditionalGibbsGaussianLaw beta sigma x).real (A x) ≤ B) :
    (primitiveJointGibbsLaw n beta sigma).real {p | p.1 ∈ A p.2} ≤ B := by
  rw [primitiveJointGibbsLaw_probability_eq_conditional_average beta sigma A hA]
  calc
    _ ≤ ∑ x, conditionalGibbsSpinMass beta sigma x * B := by
      apply Finset.sum_le_sum
      intro x hx
      exact mul_le_mul_of_nonneg_left (hB x) (conditionalGibbsSpinMass_pos beta sigma x).le
    _ = B := by rw [← Finset.sum_mul, conditionalGibbsSpinMass_sum, one_mul]

theorem primitiveJointGibbsLaw_sk_probability_eq_uniform_conditional_average {n : ℕ}
    (beta : ℝ) (A : Spin n → Set (EuclideanSpace ℝ (Fin n × Fin n)))
    (hA : ∀ x, MeasurableSet (A x)) :
    (primitiveJointGibbsLaw n beta (1 / Real.sqrt (2 * (n : ℝ)))).real
      {p | p.1 ∈ A p.2} =
      1 / (2 : ℝ) ^ n * ∑ x, (conditionalGibbsGaussianLaw beta
        (1 / Real.sqrt (2 * (n : ℝ))) x).real (A x) := by
  rw [primitiveJointGibbsLaw_probability_eq_conditional_average beta _ A hA]
  simp_rw [conditionalGibbsSpinMass_sk]
  rw [Finset.mul_sum]

def annealedSparseFieldBadSet (n r : ℕ) (A : ℝ) :
    Set (EuclideanSpace ℝ (Fin n × Fin n) × Spin n) :=
  {p | p.1 ∈ sparseFieldBadSet p.2 r A}

theorem measurableSet_annealedSparseFieldBadSet (n r : ℕ) (A : ℝ) :
    MeasurableSet (annealedSparseFieldBadSet n r A) :=
  measurableSet_spin_dependent_event _ (fun x => measurableSet_sparseFieldBadSet x r A)

theorem primitiveJointGibbs_sparseFieldBadSet_tail {n r : ℕ} (hn : 0 < n)
    (hr : 0 < r) (beta A : ℝ) (hA : 4 * |beta| * (r : ℝ) ≤ A) :
    (primitiveJointGibbsLaw n beta (1 / Real.sqrt (2 * (n : ℝ)))).real
      (annealedSparseFieldBadSet n r A) ≤
      (((r + 1) * (n + 1)^r : ℕ)^2 : ℝ) *
        Real.exp (-(A - 4 * |beta| * (r : ℝ))^2 / (8 * (r : ℝ))) := by
  exact primitiveJointGibbsLaw_probability_le_of_conditional_bound beta _
    (fun x => sparseFieldBadSet x r A) (fun x => measurableSet_sparseFieldBadSet x r A) _
    (fun x => conditionalGibbs_sparseFieldBadSet_tail hn hr beta x A hA)

end SKConstants
