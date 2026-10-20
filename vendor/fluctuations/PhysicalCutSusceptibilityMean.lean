module

public import PhysicalSusceptibilityExpectations
public import PhysicalOverlapClockDerivative
public import SKFluctuationsOAI.Probability.SKFluctuations.PhysicalCommonCutSwap

@[expose] public section

noncomputable section

namespace OAI.SKFluctuations

open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

def physicalSourceMixedTrace (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (x : FeatureIndex n → ℝ) : ℝ :=
  (LaplaceWindowFormalization.hierarchySourceHessianMatrix
    (uniformWeight n) (finiteFeature n) (LaplaceWindowFormalization.physicalNormalizedSourceMap n)
    steps x * LaplaceWindowFormalization.hierarchySourceCovarianceMatrix
    (uniformWeight n) (finiteFeature n) (LaplaceWindowFormalization.physicalNormalizedSourceMap n)
    steps x).trace

theorem physicalSourceMixedTrace_measurable (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ}
    (ha : OrderedSteps a steps) : Measurable (physicalSourceMixedTrace n steps) := by
  have := hierarchyPathKernel_markov (uniformWeight_pos n) (finiteFeature n) steps ha
  have h := (physicalSusceptibility_measurable n steps ha id measurable_id).stronglyMeasurable
    |>.integral_kernel_prod_right' (κ := hierarchyPathKernel (uniformWeight n) (finiteFeature n) steps)
  have he : (fun x => ∫ p, physicalSusceptibility n steps x p
      ∂hierarchyPathKernel (uniformWeight n) (finiteFeature n) steps x) =
      physicalSourceMixedTrace n steps := by
    funext x
    exact physicalSusceptibility_integral_eq_trace n steps ha x
  change StronglyMeasurable (fun x => ∫ p, physicalSusceptibility n steps x p
    ∂hierarchyPathKernel (uniformWeight n) (finiteFeature n) steps x) at h
  rw [he] at h
  exact h.measurable

theorem physicalSourceMixedTrace_abs_le_four (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ}
    (ha : OrderedSteps a steps) (x : FeatureIndex n → ℝ) :
    |physicalSourceMixedTrace n steps x| ≤ 4 := by
  have := hierarchyPathKernel_markov (uniformWeight_pos n) (finiteFeature n) steps ha
  unfold physicalSourceMixedTrace
  rw [← physicalSusceptibility_integral_eq_trace n steps ha x]
  have h := norm_integral_le_of_norm_le_const (μ := hierarchyPathKernel
      (uniformWeight n) (finiteFeature n) steps x)
      (C := (4 : ℝ))
      (Eventually.of_forall fun p => by
        rw [Real.norm_eq_abs, abs_of_nonneg
          (gaussianHierarchyHessian_nonneg (uniformWeight_pos n) (finiteFeature n) steps ha x _)]
        exact physicalSusceptibility_le_four n steps ha x p)
  simpa [Real.norm_eq_abs, physicalSusceptibility] using h

def physicalCutSourceMixedTrace (n : ℕ) :
    (steps : List (GaussianStep (FeatureIndex n))) → {P : Type} →
    (P → FeatureIndex n → ℝ) → ℕ → PhysicalPathState P n steps → ℝ
  | steps, _, x, 0, p => physicalSourceMixedTrace n steps (x p.1)
  | [], _, _, _+1, _ => 0
  | _::steps, _, x, k+1, p => physicalCutSourceMixedTrace n steps
      (fun q => x q.1+q.2) k ((p.1,p.2.1),p.2.2)

theorem physicalCutSourceMixedTrace_measurable (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ} (ha : OrderedSteps a steps)
    {P : Type} [MeasurableSpace P] (x : P → FeatureIndex n → ℝ) (hx : Measurable x)
    (k : ℕ) : Measurable (physicalCutSourceMixedTrace n steps x k) := by
  induction steps generalizing a P k with
  | nil => cases k with
    | zero => exact (physicalSourceMixedTrace_measurable n [] ha).comp (hx.comp measurable_fst)
    | succ k => exact measurable_const
  | cons st steps ih => cases k with
    | zero =>
      exact (physicalSourceMixedTrace_measurable n (st::steps) ha).comp
        (hx.comp measurable_fst)
    | succ k =>
      exact (ih ha.2.2.2 (fun q : P × (FeatureIndex n → ℝ) => x q.1+q.2)
        ((hx.comp measurable_fst).add measurable_snd) k).comp
        ((measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
          (measurable_snd.comp measurable_snd))

theorem physicalCutSourceMixedTrace_abs_le_four (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ} (ha : OrderedSteps a steps)
    {P : Type} (x : P → FeatureIndex n → ℝ) (k : ℕ)
    (p : PhysicalPathState P n steps) : |physicalCutSourceMixedTrace n steps x k p| ≤ 4 := by
  induction steps generalizing a P k with
  | nil => cases k with
    | zero => exact physicalSourceMixedTrace_abs_le_four n [] ha _
    | succ k => norm_num [physicalCutSourceMixedTrace]
  | cons st steps ih => cases k with
    | zero => exact physicalSourceMixedTrace_abs_le_four n (st::steps) ha _
    | succ k =>
      exact ih ha.2.2.2 (fun q : P × (FeatureIndex n → ℝ) => x q.1+q.2)
        k ((p.1,p.2.1),p.2.2)

theorem physicalCutSourceMixedTrace_integrable (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ} (ha : OrderedSteps a steps)
    {P : Type} [MeasurableSpace P] (μ : Measure P) [IsFiniteMeasure μ]
    (x : P → FeatureIndex n → ℝ) (hx : Measurable x) (k : ℕ) :
    Integrable (physicalCutSourceMixedTrace n steps x k)
      (μ ⊗ₘ (hierarchyPathKernel (uniformWeight n) (finiteFeature n) steps).comap x hx) := by
  have := hierarchyPathKernel_markov (uniformWeight_pos n) (finiteFeature n) steps ha
  apply (integrable_const (4 : ℝ)).mono'
    (physicalCutSourceMixedTrace_measurable n steps ha x hx k).aestronglyMeasurable
  exact Eventually.of_forall fun p => by
    rw [Real.norm_eq_abs]
    exact physicalCutSourceMixedTrace_abs_le_four n steps ha x k p

theorem physicalCutSusceptibility_le_four (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ} (ha : OrderedSteps a steps)
    {P : Type} (x : P → FeatureIndex n → ℝ) (k : ℕ)
    (p : PhysicalPathState P n steps) : physicalCutSusceptibility n steps x k p ≤ 4 := by
  induction steps generalizing a P k with
  | nil => cases k with
    | zero => exact physicalSusceptibility_le_four n [] ha _ _
    | succ k => norm_num [physicalCutSusceptibility]
  | cons st steps ih => cases k with
    | zero => exact physicalSusceptibility_le_four n (st::steps) ha _ _
    | succ k =>
      exact ih ha.2.2.2 (fun q : P × (FeatureIndex n → ℝ) => x q.1+q.2)
        k ((p.1,p.2.1),p.2.2)

theorem physicalCutSusceptibility_integrable (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ} (ha : OrderedSteps a steps)
    {P : Type} [MeasurableSpace P] (μ : Measure P) [IsFiniteMeasure μ]
    (x : P → FeatureIndex n → ℝ) (hx : Measurable x) (k : ℕ) :
    Integrable (physicalCutSusceptibility n steps x k)
      (μ ⊗ₘ (hierarchyPathKernel (uniformWeight n) (finiteFeature n) steps).comap x hx) := by
  have := hierarchyPathKernel_markov (uniformWeight_pos n) (finiteFeature n) steps ha
  apply (integrable_const (4 : ℝ)).mono'
    (physicalCutSusceptibility_measurable n steps ha x hx k).aestronglyMeasurable
  exact Eventually.of_forall fun p => by
    rw [Real.norm_eq_abs, abs_of_nonneg (physicalCutSusceptibility_nonneg n steps ha x k p)]
    exact physicalCutSusceptibility_le_four n steps ha x k p

theorem physicalCutSusceptibility_integral_eq_trace (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ} (ha : OrderedSteps a steps)
    {P : Type} [MeasurableSpace P] (μ : Measure P) [IsFiniteMeasure μ]
    (x : P → FeatureIndex n → ℝ) (hx : Measurable x) (k : ℕ) :
    (∫ p, physicalCutSusceptibility n steps x k p
      ∂μ ⊗ₘ (hierarchyPathKernel (uniformWeight n) (finiteFeature n) steps).comap x hx) =
    (∫ p, physicalCutSourceMixedTrace n steps x k p
      ∂μ ⊗ₘ (hierarchyPathKernel (uniformWeight n) (finiteFeature n) steps).comap x hx) := by
  induction steps generalizing P a k with
  | nil => cases k with
    | zero =>
      have := hierarchyPathKernel_markov (uniformWeight_pos n) (finiteFeature n) [] ha
      rw [Measure.integral_compProd (physicalCutSusceptibility_integrable n [] ha μ x hx 0)]
      simp only [physicalCutSusceptibility, Kernel.comap_apply,
        physicalSusceptibility_integral_eq_trace n [] ha]
      rw [Measure.integral_compProd]
      · simp [physicalCutSourceMixedTrace, physicalSourceMixedTrace]
      · exact physicalCutSourceMixedTrace_integrable n [] ha μ x hx 0
    | succ k => rfl
  | cons st tail ih => cases k with
    | zero =>
      have := hierarchyPathKernel_markov (uniformWeight_pos n) (finiteFeature n) (st::tail) ha
      rw [Measure.integral_compProd
        (physicalCutSusceptibility_integrable n (st::tail) ha μ x hx 0)]
      simp only [physicalCutSusceptibility, Kernel.comap_apply,
        physicalSusceptibility_integral_eq_trace n (st::tail) ha]
      rw [Measure.integral_compProd]
      · simp [physicalCutSourceMixedTrace, physicalSourceMixedTrace]
      · exact physicalCutSourceMixedTrace_integrable n (st::tail) ha μ x hx 0
    | succ k =>
      rcases st with ⟨m,q⟩
      have := plantedStepKernel_markov (uniformWeight_pos n) (finiteFeature n) m q tail ha
      let ν := μ ⊗ₘ (hierarchyPathKernel (uniformWeight n) (finiteFeature n) ((m,q)::tail)).comap x hx
      let μ' := μ ⊗ₘ (plantedStepKernel (uniformWeight n) (finiteFeature n) m q tail).comap x hx
      let x' : P × (FeatureIndex n → ℝ) → FeatureIndex n → ℝ := fun p => x p.1+p.2
      have hx' : Measurable x' := (hx.comp measurable_fst).add measurable_snd
      let e : (PhysicalPathState P n ((m,q)::tail)) ≃ᵐ
          PhysicalPathState (P × (FeatureIndex n → ℝ)) n tail := MeasurableEquiv.prodAssoc.symm
      have hmap : ν.map e = μ' ⊗ₘ
          (hierarchyPathKernel (uniformWeight n) (finiteFeature n) tail).comap x' hx' :=
        hierarchyPathLaw_cons (uniformWeight_pos n) (finiteFeature n) m q tail ha μ x hx
      have he := ih ha.2.2.2 μ' x' hx' k
      rw [← hmap] at he
      have hl := integral_map (μ := ν) e.measurable.aemeasurable
        (physicalCutSusceptibility_measurable n tail ha.2.2.2 x' hx' k).aestronglyMeasurable
      have hr := integral_map (μ := ν) e.measurable.aemeasurable
        (physicalCutSourceMixedTrace_measurable n tail ha.2.2.2 x' hx' k).aestronglyMeasurable
      rw [hl,hr] at he
      exact he

def physicalSourceSquareTrace (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (x : FeatureIndex n → ℝ) : ℝ :=
  ∑ i, ∑ j, (LaplaceWindowFormalization.hierarchySourceHessianMatrix
    (uniformWeight n) (finiteFeature n) (LaplaceWindowFormalization.physicalNormalizedSourceMap n)
    steps x i j)^2

theorem physicalSourceSquareTrace_measurable (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ} (ha : OrderedSteps a steps) :
    Measurable (physicalSourceSquareTrace n steps) := by
  unfold physicalSourceSquareTrace
  apply Finset.measurable_sum
  intro i _
  apply Finset.measurable_sum
  intro j _
  have h := (gaussianHierarchyResponse_smooth (uniformWeight_pos n) (finiteFeature n)
    (fun σ => normalizedSpin n σ i)
    (LaplaceWindowFormalization.physicalNormalizedSourceMap n (Pi.single j 1)) steps ha 0).continuous.measurable
  simpa only [LaplaceWindowFormalization.physicalSourceHessian_eq_response] using h.pow_const 2

def physicalCutSourceSquareTrace (n : ℕ) :
    (steps : List (GaussianStep (FeatureIndex n))) → {P : Type} →
    (P → FeatureIndex n → ℝ) → ℕ → PhysicalPathState P n steps → ℝ
  | steps, _, x, 0, p => physicalSourceSquareTrace n steps (x p.1)
  | [], _, _, _+1, _ => 0
  | _::steps, _, x, k+1, p => physicalCutSourceSquareTrace n steps
      (fun q => x q.1+q.2) k ((p.1,p.2.1),p.2.2)

theorem physicalCutSourceSquareTrace_measurable (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ} (ha : OrderedSteps a steps)
    {P : Type} [MeasurableSpace P] (x : P → FeatureIndex n → ℝ) (hx : Measurable x)
    (k : ℕ) : Measurable (physicalCutSourceSquareTrace n steps x k) := by
  induction steps generalizing a P k with
  | nil => cases k with
    | zero => exact (physicalSourceSquareTrace_measurable n [] ha).comp (hx.comp measurable_fst)
    | succ k => exact measurable_const
  | cons st steps ih => cases k with
    | zero =>
      exact (physicalSourceSquareTrace_measurable n (st::steps) ha).comp (hx.comp measurable_fst)
    | succ k =>
      exact (ih ha.2.2.2 (fun q : P × (FeatureIndex n → ℝ) => x q.1+q.2)
        ((hx.comp measurable_fst).add measurable_snd) k).comp
        ((measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
          (measurable_snd.comp measurable_snd))

theorem physicalCutSourceSquareTrace_mem_Icc (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ} (ha : OrderedSteps a steps)
    {P : Type} (x : P → FeatureIndex n → ℝ) (k : ℕ)
    (p : PhysicalPathState P n steps) : physicalCutSourceSquareTrace n steps x k p ∈ Icc (0:ℝ) 1 := by
  induction steps generalizing a P k with
  | nil => cases k with
    | zero =>
      change physicalSourceSquareTrace n [] (x p.1) ∈ Icc (0:ℝ) 1
      exact ⟨Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _,
        LaplaceWindowFormalization.physicalSourceHessianMatrix_entry_squares_le_one n [] ha _⟩
    | succ k => norm_num [physicalCutSourceSquareTrace]
  | cons st steps ih => cases k with
    | zero =>
      change physicalSourceSquareTrace n (st::steps) (x p.1) ∈ Icc (0:ℝ) 1
      exact ⟨Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _,
        LaplaceWindowFormalization.physicalSourceHessianMatrix_entry_squares_le_one n (st::steps) ha _⟩
    | succ k =>
      exact ih ha.2.2.2 (fun q : P × (FeatureIndex n → ℝ) => x q.1+q.2)
        k ((p.1,p.2.1),p.2.2)

theorem physicalCutSourceMixedTrace_le_square (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ} (ha : OrderedSteps a steps)
    (ha0 : 0 < a) {P : Type} (x : P → FeatureIndex n → ℝ) (k : ℕ)
    (p : PhysicalPathState P n steps) :
    physicalCutSourceMixedTrace n steps x k p ≤ physicalCutSourceSquareTrace n steps x k p / a := by
  induction steps generalizing P k with
  | nil => cases k with
    | zero => exact (LaplaceWindowFormalization.physicalSourceCovarianceHessian_trace n [] ha ha0 _).1
    | succ k => simp [physicalCutSourceMixedTrace,physicalCutSourceSquareTrace]
  | cons st steps ih => cases k with
    | zero => exact (LaplaceWindowFormalization.physicalSourceCovarianceHessian_trace n (st::steps) ha ha0 _).1
    | succ k =>
      exact ih (OrderedSteps.suffix [st] steps ha)
        (fun q : P × (FeatureIndex n → ℝ) => x q.1+q.2) k ((p.1,p.2.1),p.2.2)

theorem physicalCutSourceSquareTrace_integrable (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ} (ha : OrderedSteps a steps)
    {P : Type} [MeasurableSpace P] (μ : Measure P) [IsFiniteMeasure μ]
    (x : P → FeatureIndex n → ℝ) (hx : Measurable x) (k : ℕ) :
    Integrable (physicalCutSourceSquareTrace n steps x k)
      (μ ⊗ₘ (hierarchyPathKernel (uniformWeight n) (finiteFeature n) steps).comap x hx) := by
  have := hierarchyPathKernel_markov (uniformWeight_pos n) (finiteFeature n) steps ha
  apply (integrable_const (1 : ℝ)).mono'
    (physicalCutSourceSquareTrace_measurable n steps ha x hx k).aestronglyMeasurable
  exact Eventually.of_forall fun p => by
    rw [Real.norm_eq_abs, abs_of_nonneg (physicalCutSourceSquareTrace_mem_Icc n steps ha x k p).1]
    exact (physicalCutSourceSquareTrace_mem_Icc n steps ha x k p).2

theorem physicalCutSusceptibility_integral_le_square (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ} (ha : OrderedSteps a steps)
    (ha0 : 0 < a) {P : Type} [MeasurableSpace P] (μ : Measure P) [IsFiniteMeasure μ]
    (x : P → FeatureIndex n → ℝ) (hx : Measurable x) (k : ℕ) :
    (∫ p, physicalCutSusceptibility n steps x k p
      ∂μ ⊗ₘ (hierarchyPathKernel (uniformWeight n) (finiteFeature n) steps).comap x hx) ≤
    (∫ p, physicalCutSourceSquareTrace n steps x k p
      ∂μ ⊗ₘ (hierarchyPathKernel (uniformWeight n) (finiteFeature n) steps).comap x hx) / a := by
  rw [physicalCutSusceptibility_integral_eq_trace n steps ha μ x hx k, ← integral_div]
  exact integral_mono (physicalCutSourceMixedTrace_integrable n steps ha μ x hx k)
    ((physicalCutSourceSquareTrace_integrable n steps ha μ x hx k).div_const a)
    (fun p => physicalCutSourceMixedTrace_le_square n steps ha ha0 x k p)

theorem physicalCutSourceMixedTrace_le_square_of_cutMass (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {c a : ℝ} (hc : OrderedSteps c steps)
    (ha0 : 0 < a) {P : Type} (x : P → FeatureIndex n → ℝ) (k : ℕ)
    (hacut : a ≤ physicalCutMass c steps k) (p : PhysicalPathState P n steps) :
    physicalCutSourceMixedTrace n steps x k p ≤ physicalCutSourceSquareTrace n steps x k p / a := by
  induction steps generalizing c P k with
  | nil => cases k with
    | zero =>
      exact (LaplaceWindowFormalization.physicalSourceCovarianceHessian_trace n []
        (hc.lower ha0.le hacut) ha0 _).1
    | succ k => simp [physicalCutSourceMixedTrace,physicalCutSourceSquareTrace]
  | cons st steps ih => cases k with
    | zero =>
      exact (LaplaceWindowFormalization.physicalSourceCovarianceHessian_trace n (st::steps)
        (hc.lower ha0.le hacut) ha0 _).1
    | succ k =>
      exact ih hc.2.2.2 (fun q : P × (FeatureIndex n → ℝ) => x q.1+q.2)
        k hacut ((p.1,p.2.1),p.2.2)

theorem physicalCutSusceptibility_integral_le_square_of_cutMass (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {c a : ℝ} (hc : OrderedSteps c steps)
    (ha0 : 0 < a) {P : Type} [MeasurableSpace P] (μ : Measure P) [IsFiniteMeasure μ]
    (x : P → FeatureIndex n → ℝ) (hx : Measurable x) (k : ℕ)
    (hacut : a ≤ physicalCutMass c steps k) :
    (∫ p, physicalCutSusceptibility n steps x k p
      ∂μ ⊗ₘ (hierarchyPathKernel (uniformWeight n) (finiteFeature n) steps).comap x hx) ≤
    (∫ p, physicalCutSourceSquareTrace n steps x k p
      ∂μ ⊗ₘ (hierarchyPathKernel (uniformWeight n) (finiteFeature n) steps).comap x hx) / a := by
  rw [physicalCutSusceptibility_integral_eq_trace n steps hc μ x hx k, ← integral_div]
  exact integral_mono (physicalCutSourceMixedTrace_integrable n steps hc μ x hx k)
    ((physicalCutSourceSquareTrace_integrable n steps hc μ x hx k).div_const a)
    (fun p => physicalCutSourceMixedTrace_le_square_of_cutMass n steps hc ha0 x k hacut p)

theorem physicalRadiusWindowSusceptibility_integral_eq_trace (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ} (ha : OrderedSteps a steps)
    {P : Type} [MeasurableSpace P] (μ : Measure P) [IsFiniteMeasure μ]
    (x : P → FeatureIndex n → ℝ) (hx : Measurable x)
    (J : Finset (Fin (steps.length+1))) (r : Fin (steps.length+2) → ℝ) (hr : Monotone r)
    (hc : ∀ j, physicalWindowCellMass steps a J j ≠ 0 → r j.castSucc < r j.succ) :
    (∫ p, physicalSusceptibilityMassIntegral n steps x
      (radiusCellMeasure (fun j => r j.castSucc) (fun j => r j.succ)
        (physicalWindowCellMass steps a J)) (radiusGridCut r) p
      ∂μ ⊗ₘ (hierarchyPathKernel (uniformWeight n) (finiteFeature n) steps).comap x hx) =
    ∑ j, physicalWindowCellMass steps a J j *
      (∫ p, physicalCutSourceMixedTrace n steps x j.val p
        ∂μ ⊗ₘ (hierarchyPathKernel (uniformWeight n) (finiteFeature n) steps).comap x hx) := by
  have he : physicalSusceptibilityMassIntegral n steps x
      (radiusCellMeasure (fun j => r j.castSucc) (fun j => r j.succ)
        (physicalWindowCellMass steps a J)) (radiusGridCut r) =
      fun p => ∑ j, physicalWindowCellMass steps a J j * physicalCutSusceptibility n steps x j.val p := by
    funext p
    unfold physicalSusceptibilityMassIntegral
    exact integral_radiusCellMeasure_allow_zero _ _ _ (fun j => or_iff_not_imp_left.mpr (hc j))
      (physicalWindowCellMass_nonneg steps ha J) _ _
      (fun j s hs => by rw [radiusGridCut_cell r hr j hs])
  rw [he,integral_finsetSum]
  · simp_rw [integral_const_mul,physicalCutSusceptibility_integral_eq_trace n steps ha μ x hx]
  · intro j _
    exact (physicalCutSusceptibility_integrable n steps ha μ x hx j.val).const_mul _

end OAI.SKFluctuations
