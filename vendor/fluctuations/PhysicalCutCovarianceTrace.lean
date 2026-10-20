module

public import PhysicalBAtCutFourthMoment
public import BoundaryCapMassCellSum

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

theorem physicalSpinTraceCovSq_le_one (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ}
    (ha : OrderedSteps a steps) (x : FeatureIndex n → ℝ) :
    physicalSpinTraceCovSq n steps x ≤ 1 := by
  have h := posSemidef_entry_squares_le_one (physicalSourceCovarianceHessian_psd n steps ha x).1
    (physicalSourceCovarianceMatrix_trace_le_one n steps ha x)
  rw [physicalSourceCovarianceMatrix_eq_entries] at h
  exact h

def physicalCutSpinTraceCovSq (n : ℕ) :
    (steps : List (GaussianStep (FeatureIndex n))) → {P : Type} →
      (P → FeatureIndex n → ℝ) → ℕ → PhysicalPathState P n steps → ℝ
  | steps, _, x, 0, p => physicalSpinTraceCovSq n steps (x p.1)
  | [], _, _, _+1, _ => 0
  | _::steps, _, x, k+1, p => physicalCutSpinTraceCovSq n steps
      (fun q => x q.1+q.2) k ((p.1,p.2.1),p.2.2)

theorem physicalCutSpinTraceCovSq_measurable (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ} (ha : OrderedSteps a steps)
    {P : Type} [MeasurableSpace P] (x : P → FeatureIndex n → ℝ) (hx : Measurable x)
    (k : ℕ) : Measurable (physicalCutSpinTraceCovSq n steps x k) := by
  induction steps generalizing a P k with
  | nil => cases k with
    | zero => exact (physicalSpinTraceCovSq_smooth n [] ha).continuous.measurable.comp (hx.comp measurable_fst)
    | succ k => exact measurable_const
  | cons st steps ih => cases k with
    | zero => exact (physicalSpinTraceCovSq_smooth n (st::steps) ha).continuous.measurable.comp (hx.comp measurable_fst)
    | succ k =>
      exact (ih ha.2.2.2 (fun q : P × (FeatureIndex n → ℝ) => x q.1+q.2)
        ((hx.comp measurable_fst).add measurable_snd) k).comp
        ((measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
          (measurable_snd.comp measurable_snd))

theorem physicalCutSpinTraceCovSq_mem_Icc (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ} (ha : OrderedSteps a steps)
    {P : Type} (x : P → FeatureIndex n → ℝ) (k : ℕ)
    (p : PhysicalPathState P n steps) : physicalCutSpinTraceCovSq n steps x k p ∈ Icc (0:ℝ) 1 := by
  induction steps generalizing a P k with
  | nil => cases k with
    | zero =>
      change physicalSpinTraceCovSq n [] (x p.1) ∈ Icc (0:ℝ) 1
      exact ⟨Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _,physicalSpinTraceCovSq_le_one n [] ha _⟩
    | succ k => norm_num [physicalCutSpinTraceCovSq]
  | cons st steps ih => cases k with
    | zero =>
      change physicalSpinTraceCovSq n (st::steps) (x p.1) ∈ Icc (0:ℝ) 1
      exact ⟨Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _,physicalSpinTraceCovSq_le_one n (st::steps) ha _⟩
    | succ k =>
      exact ih ha.2.2.2 (fun q : P × (FeatureIndex n → ℝ) => x q.1+q.2)
        k ((p.1,p.2.1),p.2.2)

theorem physicalCutSpinTraceCovSq_integrable (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ} (ha : OrderedSteps a steps)
    {P : Type} [MeasurableSpace P] (μ : Measure P) [IsFiniteMeasure μ]
    (x : P → FeatureIndex n → ℝ) (hx : Measurable x) (k : ℕ) :
    Integrable (physicalCutSpinTraceCovSq n steps x k)
      (μ ⊗ₘ (hierarchyPathKernel (uniformWeight n) (finiteFeature n) steps).comap x hx) := by
  have := hierarchyPathKernel_markov (uniformWeight_pos n) (finiteFeature n) steps ha
  apply (integrable_const (1:ℝ)).mono'
    (physicalCutSpinTraceCovSq_measurable n steps ha x hx k).aestronglyMeasurable
  exact Eventually.of_forall fun p => by
    rw [Real.norm_eq_abs,abs_of_nonneg (physicalCutSpinTraceCovSq_mem_Icc n steps ha x k p).1]
    exact (physicalCutSpinTraceCovSq_mem_Icc n steps ha x k p).2

theorem physicalCutSpinTraceCovSq_eq_actualCut (n : ℕ)
    (pre tail : List (GaussianStep (FeatureIndex n))) {P : Type}
    (x : P → FeatureIndex n → ℝ) (p : PhysicalPathState P n (pre++tail)) :
    physicalCutSpinTraceCovSq n (pre++tail) x pre.length p =
      physicalSpinTraceCovSq n tail (actualCutField (S := Spin n) pre tail (x p.1) p.2) := by
  induction pre generalizing P with
  | nil => cases tail <;> rfl
  | cons st pre ih => exact ih (fun q : P × (FeatureIndex n → ℝ) => x q.1+q.2) ((p.1,p.2.1),p.2.2)

theorem physicalCutSpinTraceCovSq_le_square_of_cutMass (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {c a : ℝ} (hc : OrderedSteps c steps)
    (ha0 : 0 < a) {P : Type} (x : P → FeatureIndex n → ℝ) (k : ℕ)
    (hacut : a ≤ physicalCutMass c steps k) (p : PhysicalPathState P n steps) :
    physicalCutSpinTraceCovSq n steps x k p ≤ physicalCutSourceSquareTrace n steps x k p / a^2 := by
  induction steps generalizing c P k with
  | nil => cases k with
    | zero => exact physicalSpinTraceCovSq_le_sourceHessian n [] (hc.lower ha0.le hacut) ha0 _
    | succ k => simp [physicalCutSpinTraceCovSq,physicalCutSourceSquareTrace]
  | cons st steps ih => cases k with
    | zero => exact physicalSpinTraceCovSq_le_sourceHessian n (st::steps) (hc.lower ha0.le hacut) ha0 _
    | succ k =>
      exact ih hc.2.2.2 (fun q : P × (FeatureIndex n → ℝ) => x q.1+q.2)
        k hacut ((p.1,p.2.1),p.2.2)

theorem physicalCutSpinTraceCovSq_integral_le_square_of_cutMass (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {c a : ℝ} (hc : OrderedSteps c steps)
    (ha0 : 0 < a) {P : Type} [MeasurableSpace P] (μ : Measure P) [IsFiniteMeasure μ]
    (x : P → FeatureIndex n → ℝ) (hx : Measurable x) (k : ℕ)
    (hacut : a ≤ physicalCutMass c steps k) :
    (∫ p, physicalCutSpinTraceCovSq n steps x k p
      ∂μ ⊗ₘ (hierarchyPathKernel (uniformWeight n) (finiteFeature n) steps).comap x hx) ≤
    (∫ p, physicalCutSourceSquareTrace n steps x k p
      ∂μ ⊗ₘ (hierarchyPathKernel (uniformWeight n) (finiteFeature n) steps).comap x hx)/a^2 := by
  rw [← integral_div]
  exact integral_mono (physicalCutSpinTraceCovSq_integrable n steps hc μ x hx k)
    ((physicalCutSourceSquareTrace_integrable n steps hc μ x hx k).div_const _)
    (fun p => physicalCutSpinTraceCovSq_le_square_of_cutMass n steps hc ha0 x k hacut p)

theorem physicalCutSpinTraceCovSq_massCellSum_le_square (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {c a start : ℝ}
    (hc : OrderedSteps c steps) (ha0 : 0 < a) (q₀ : FeatureIndex n → ℝ≥0)
    (band : List PositiveMass) (hband : MassOrdered start band) (offset : ℕ)
    (hcut : ∀ j < band.length, a ≤ physicalCutMass c steps (offset+j)) :
    massCellSum band start (fun j =>
      ∫ p, physicalCutSpinTraceCovSq n steps id (offset+j) p
        ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ steps) ≤
    (massCellSum band start (fun j =>
      ∫ p, physicalCutSourceSquareTrace n steps id (offset+j) p
        ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ steps))/a^2 := by
  calc
    _ ≤ massCellSum band start (fun j =>
        (∫ p, physicalCutSourceSquareTrace n steps id (offset+j) p
          ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ steps)/a^2) := by
      apply massCellSum_mono band hband
      intro j hj
      simpa only [rootedHierarchyPathLaw,Kernel.comap_id] using
        physicalCutSpinTraceCovSq_integral_le_square_of_cutMass n steps hc ha0
          (Measure.pi fun i => gaussianReal 0 (q₀ i)) id measurable_id (offset+j) (hcut j hj)
    _ = _ := by
      simp only [div_eq_mul_inv,mul_comm _ ((a^2)⁻¹)]
      rw [massCellSum_const_mul]

end OAI.SKFluctuations.LaplaceWindowFormalization
