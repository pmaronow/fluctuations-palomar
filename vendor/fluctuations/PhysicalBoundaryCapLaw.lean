module

public import PhysicalCapBoundaryTrace
public import PhysicalCutSusceptibilityMean

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

def physicalPathBoundaryCapTrace (n : ℕ) : (durations : List ℝ≥0) →
    (pre tail : List (GaussianStep (FeatureIndex n))) →
    (FeatureIndex n → ℝ) → ForwardPath (FeatureIndex n → ℝ) (Spin n) (pre++tail).length → ℝ
  | [], _, _, _, _ => 0
  | _::_, [], _, _, _ => 0
  | w::durations, st::pre, tail, x, p =>
      w*physicalBoundarySourceTrace n ((st::pre)++tail) x +
      physicalPathBoundaryCapTrace n durations pre tail (x+p.1) p.2

theorem physicalPathBoundaryCapTrace_measurable_joint (n : ℕ) (durations : List ℝ≥0)
    (pre tail : List (GaussianStep (FeatureIndex n))) {a : ℝ}
    (ha : OrderedSteps a (pre++tail)) :
    Measurable (fun p : (FeatureIndex n → ℝ) ×
      ForwardPath (FeatureIndex n → ℝ) (Spin n) (pre++tail).length =>
      physicalPathBoundaryCapTrace n durations pre tail p.1 p.2) := by
  induction pre generalizing a durations with
  | nil => cases durations <;> exact measurable_const
  | cons st pre ih =>
    cases durations with
    | nil => exact measurable_const
    | cons w durations =>
      exact (((physicalBoundarySourceTrace_smooth n ((st::pre)++tail) ha).continuous.measurable.comp
        measurable_fst).const_mul w).add
        ((ih durations ha.2.2.2).comp
          ((measurable_fst.add (measurable_fst.comp measurable_snd)).prodMk
            (measurable_snd.comp measurable_snd)))

theorem physicalPathBoundaryCapTrace_mem_Icc (n : ℕ) (durations : List ℝ≥0)
    (pre tail : List (GaussianStep (FeatureIndex n))) {a : ℝ}
    (ha : OrderedSteps a (pre++tail)) (x : FeatureIndex n → ℝ)
    (p : ForwardPath (FeatureIndex n → ℝ) (Spin n) (pre++tail).length) :
    physicalPathBoundaryCapTrace n durations pre tail x p ∈ Icc (0:ℝ) (durations.sum:ℝ) := by
  induction pre generalizing a durations x with
  | nil => cases durations <;> exact ⟨le_rfl,NNReal.coe_nonneg _⟩
  | cons st pre ih =>
    cases durations with
    | nil => exact ⟨le_rfl,le_rfl⟩
    | cons w durations =>
      have hb : physicalBoundarySourceTrace n ((st::pre)++tail) x ∈ Icc (0:ℝ) 1 :=
        ⟨Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _,
          physicalSourceHessianMatrix_entry_squares_le_one n ((st::pre)++tail) ha x⟩
      have ht := ih durations ha.2.2.2 (x+p.1) p.2
      constructor
      · exact add_nonneg (mul_nonneg w.coe_nonneg hb.1) ht.1
      · change (w:ℝ)*physicalBoundarySourceTrace n ((st::pre)++tail) x + _ ≤ _
        simpa only [List.sum_cons,NNReal.coe_add,mul_one] using
          add_le_add (mul_le_mul_of_nonneg_left hb.2 w.coe_nonneg) ht.2

theorem physicalPathBoundaryCapTrace_integrable (n : ℕ) (durations : List ℝ≥0)
    (pre tail : List (GaussianStep (FeatureIndex n))) {a : ℝ}
    (ha : OrderedSteps a (pre++tail)) (x : FeatureIndex n → ℝ) :
    Integrable (physicalPathBoundaryCapTrace n durations pre tail x)
      (hierarchyPathKernel (uniformWeight n) (finiteFeature n) (pre++tail) x) := by
  have := hierarchyPathKernel_markov (uniformWeight_pos n) (finiteFeature n) (pre++tail) ha
  apply (integrable_const (durations.sum:ℝ)).mono'
    ((physicalPathBoundaryCapTrace_measurable_joint n durations pre tail ha).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  exact Eventually.of_forall fun p => by
    change ‖physicalPathBoundaryCapTrace n durations pre tail x p‖ ≤ (durations.sum:ℝ)
    rw [Real.norm_eq_abs,abs_of_nonneg (physicalPathBoundaryCapTrace_mem_Icc n durations pre tail ha x p).1]
    exact (physicalPathBoundaryCapTrace_mem_Icc n durations pre tail ha x p).2

theorem physicalPathBoundaryCapTrace_integral_eq_cap (n : ℕ) (durations : List ℝ≥0)
    (pre tail : List (GaussianStep (FeatureIndex n))) {a : ℝ}
    (ha : OrderedSteps a (pre++tail)) (x : FeatureIndex n → ℝ) :
    (∫ p, physicalPathBoundaryCapTrace n durations pre tail x p
      ∂hierarchyPathKernel (uniformWeight n) (finiteFeature n) (pre++tail) x) =
      physicalFiniteCapBoundaryTrace n durations pre tail ha x := by
  induction pre generalizing a durations x with
  | nil => cases durations <;> simp [physicalPathBoundaryCapTrace,physicalFiniteCapBoundaryTrace]
  | cons st pre ih =>
    cases durations with
    | nil => simp [physicalPathBoundaryCapTrace,physicalFiniteCapBoundaryTrace]
    | cons w durations =>
      rcases st with ⟨m,q⟩
      have := plantedStepKernel_markov (uniformWeight_pos n) (finiteFeature n) m q (pre++tail) ha
      have := hierarchyPathKernel_markov (uniformWeight_pos n) (finiteFeature n) (pre++tail) ha.2.2.2
      have hf := physicalPathBoundaryCapTrace_integrable n (w::durations) ((m,q)::pre) tail ha x
      change Integrable (fun p : (FeatureIndex n → ℝ) ×
        ForwardPath (FeatureIndex n → ℝ) (Spin n) (pre++tail).length =>
        (w:ℝ)*physicalBoundarySourceTrace n (((m,q)::pre)++tail) x +
          physicalPathBoundaryCapTrace n durations pre tail (x+p.1) p.2)
        ((plantedStepKernel (uniformWeight n) (finiteFeature n) m q (pre++tail) ⊗ₖ
          (hierarchyPathKernel (uniformWeight n) (finiteFeature n) (pre++tail)).comap
            (fun p => p.1+p.2) (measurable_fst.add measurable_snd)) x) at hf
      change (∫ p : (FeatureIndex n → ℝ) ×
        ForwardPath (FeatureIndex n → ℝ) (Spin n) (pre++tail).length,
        (w:ℝ)*physicalBoundarySourceTrace n (((m,q)::pre)++tail) x +
          physicalPathBoundaryCapTrace n durations pre tail (x+p.1) p.2 ∂
        ((plantedStepKernel (uniformWeight n) (finiteFeature n) m q (pre++tail) ⊗ₖ
          (hierarchyPathKernel (uniformWeight n) (finiteFeature n) (pre++tail)).comap
            (fun p => p.1+p.2) (measurable_fst.add measurable_snd)) x)) = _
      rw [ProbabilityTheory.integral_compProd hf]
      simp only [Kernel.comap_apply]
      simp_rw [integral_add (integrable_const _) (physicalPathBoundaryCapTrace_integrable n durations pre tail ha.2.2.2 _),
        integral_const,probReal_univ,one_smul,ih durations ha.2.2.2]
      rw [integral_add (integrable_const _)]
      · simp only [integral_const,probReal_univ,one_smul]
        rw [plantedStepKernel_eq_tilted (uniformWeight_pos n) (finiteFeature n) m q (pre++tail) ha x,
          integral_tiltedLaw (F := fun z => gaussianHierarchy (uniformWeight n) (finiteFeature n) (pre++tail) (x+z))
            ((gaussianHierarchy_continuous (uniformWeight_pos n) (finiteFeature n) (pre++tail) ha.2.2.2).comp
              (continuous_const.add continuous_id)).measurable
            (gaussianHierarchy_integrable (uniformWeight_pos n) (finiteFeature n) (pre++tail) ha.2.2.2 m q x)]
        rfl
      · exact (physicalFiniteCapBoundaryTrace_smooth n durations pre tail ha.2.2.2).integrable_comp_measurable
          (measurable_const.add measurable_id)

def physicalWeightedCutSum : List ℝ≥0 → (ℕ → ℝ) → ℝ
  | [], _ => 0
  | w::ws, C => w*C 0 + physicalWeightedCutSum ws (fun k => C (k+1))

theorem physicalPathBoundaryCapTrace_eq_weightedCutSum (n : ℕ) (durations : List ℝ≥0)
    (pre tail : List (GaussianStep (FeatureIndex n))) (hlength : durations.length ≤ pre.length)
    {P : Type} (x : P → FeatureIndex n → ℝ)
    (p : PhysicalPathState P n (pre++tail)) :
    physicalPathBoundaryCapTrace n durations pre tail (x p.1) p.2 =
      physicalWeightedCutSum durations (fun k => physicalCutSourceSquareTrace n (pre++tail) x k p) := by
  induction pre generalizing durations P with
  | nil =>
    have : durations=[] := List.eq_nil_of_length_eq_zero (by simpa using hlength)
    subst durations
    rfl
  | cons st pre ih =>
    cases durations with
    | nil => rfl
    | cons w ws =>
      have hlen : ws.length ≤ pre.length := by simpa only [List.length_cons,Nat.add_le_add_iff_right] using hlength
      simp only [physicalPathBoundaryCapTrace,physicalWeightedCutSum]
      rw [ih ws hlen (fun q : P × (FeatureIndex n → ℝ) => x q.1+q.2) ((p.1,p.2.1),p.2.2)]
      rfl

theorem physicalWeightedCutSum_integral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (durations : List ℝ≥0) (C : ℕ → Ω → ℝ)
    (hC : ∀ k, Integrable (C k) μ) :
    (∫ p, physicalWeightedCutSum durations (fun k => C k p) ∂μ) =
      physicalWeightedCutSum durations (fun k => ∫ p, C k p ∂μ) := by
  induction durations generalizing C with
  | nil => simp [physicalWeightedCutSum]
  | cons w ws ih =>
    have hrest : Integrable (fun p => physicalWeightedCutSum ws (fun k => C (k+1) p)) μ := by
      clear ih
      induction ws generalizing C with
      | nil => exact (integrable_const (0:ℝ) : Integrable (fun _ : Ω => (0:ℝ)) μ)
      | cons v vs hi =>
        exact ((hC 1).const_mul v).add (hi (fun k => C (k+1)) (fun k => hC (k+1)))
    simp only [physicalWeightedCutSum]
    rw [integral_add ((hC 0).const_mul w) hrest,integral_const_mul,ih _ (fun k => hC (k+1))]

theorem physicalFiniteCapBoundaryTrace_rooted_eq_weightedCuts (n : ℕ)
    (q₀ : FeatureIndex n → ℝ≥0) (durations : List ℝ≥0)
    (pre tail : List (GaussianStep (FeatureIndex n))) {a : ℝ}
    (ha : OrderedSteps a (pre++tail)) (hlength : durations.length ≤ pre.length) :
    zeroContinuation (Measure.pi fun k => gaussianReal 0 (q₀ k))
      (physicalFiniteCapBoundaryTrace n durations pre tail ha) 0 =
    physicalWeightedCutSum durations (fun k =>
      ∫ p, physicalCutSourceSquareTrace n (pre++tail) id k p
        ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ (pre++tail)) := by
  have := hierarchyPathKernel_markov (uniformWeight_pos n) (finiteFeature n) (pre++tail) ha
  have := rootedHierarchyPathLaw_probability (uniformWeight_pos n) (finiteFeature n) q₀ (pre++tail) ha
  have hI : Integrable (fun p : PhysicalPathState (FeatureIndex n → ℝ) n (pre++tail) =>
      physicalPathBoundaryCapTrace n durations pre tail p.1 p.2)
      (rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ (pre++tail)) := by
    apply (integrable_const (durations.sum:ℝ)).mono'
      (physicalPathBoundaryCapTrace_measurable_joint n durations pre tail ha).aestronglyMeasurable
    exact Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs,abs_of_nonneg (physicalPathBoundaryCapTrace_mem_Icc n durations pre tail ha p.1 p.2).1]
      exact (physicalPathBoundaryCapTrace_mem_Icc n durations pre tail ha p.1 p.2).2
  have hcond := Measure.integral_compProd hI
  simp_rw [physicalPathBoundaryCapTrace_integral_eq_cap n durations pre tail ha] at hcond
  have hCi (k : ℕ) : Integrable (physicalCutSourceSquareTrace n (pre++tail) id k)
      (rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ (pre++tail)) := by
    simpa only [rootedHierarchyPathLaw,Kernel.comap_id] using
      physicalCutSourceSquareTrace_integrable n (pre++tail) ha
        (Measure.pi fun i => gaussianReal 0 (q₀ i)) id measurable_id k
  have heq := physicalWeightedCutSum_integral
    (rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ (pre++tail)) durations
    (fun k => physicalCutSourceSquareTrace n (pre++tail) id k) hCi
  rw [← heq]
  calc
    _ = ∫ p, physicalPathBoundaryCapTrace n durations pre tail p.1 p.2
        ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ (pre++tail) := by
      simpa only [zeroContinuation,zero_add,rootedHierarchyPathLaw] using hcond.symm
    _ = _ := integral_congr_ae (Eventually.of_forall fun p =>
      physicalPathBoundaryCapTrace_eq_weightedCutSum n durations pre tail hlength id p)

theorem physicalWeightedCutSquareTrace_le_pathSecondMoment (n d : ℕ)
    (e : Fin (d+1) ≃ FeatureIndex (n+1)) (q₀ : FeatureIndex (n+1) → ℝ≥0)
    (durations : List ℝ≥0) (pre tail : List (GaussianStep (FeatureIndex (n+1))))
    {mesh g M : ℝ} (ha : OrderedSteps 0 (pre++tail))
    (hlength : durations.length ≤ pre.length) (hmesh0 : 0 ≤ mesh)
    (hmesh : ∀ w ∈ durations, (w:ℝ) ≤ mesh) (hg : 0 < g)
    (hfield : ∀ st ∈ pre, ∀ j, st.2 (Sum.inl j) = st.2 (Sum.inl 0))
    (hslope : List.Forall₂ (fun (w:ℝ≥0) (st:GaussianStep (FeatureIndex (n+1))) =>
      g*(w:ℝ) ≤ st.2 (Sum.inl 0)) durations pre)
    (hmean : physicalPathSecondMoment (n+1) (pre++tail) q₀ pre.length ≤ M) :
    physicalWeightedCutSum durations (fun k =>
      ∫ p, physicalCutSourceSquareTrace (n+1) (pre++tail) id k p
        ∂rootedHierarchyPathLaw (uniformWeight (n+1)) (finiteFeature (n+1)) q₀ (pre++tail)) ≤
      2*M/((n+1:ℝ)*g)+2*mesh*M := by
  rw [← physicalFiniteCapBoundaryTrace_rooted_eq_weightedCuts (n+1) q₀ durations pre tail ha hlength]
  exact physicalFiniteCapBoundaryTrace_rooted_le_pathSecondMoment n d e q₀ durations pre tail ha
    hmesh0 hmesh hg hfield hslope hmean

end OAI.SKFluctuations.LaplaceWindowFormalization
