module

public import CavityWeightedExteriorResampling

@[expose] public section

noncomputable section
set_option maxHeartbeats 8000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations
open Hierarchy

def physicalRootVectorTerminalResidual (n : ℕ) {P : Type}
    (V : P → EuclideanSpace ℝ (Fin n))
    (tail pre : List (GaussianStep (FeatureIndex n)))
    (x : P → FeatureIndex n → ℝ) (p : PhysicalPathState P n (pre++tail)) : ℝ :=
  ∑ i,V p.1 i*physicalTerminalIncrement n tail pre x p i

def physicalRootVectorResamplingMoment (n l : ℕ) {P : Type} [MeasurableSpace P]
    (V : P → EuclideanSpace ℝ (Fin n))
    (tail pre : List (GaussianStep (FeatureIndex n)))
    (μ : Measure P) (x : P → FeatureIndex n → ℝ) (hx : Measurable x) : ℝ :=
  ∫ p,conditionalForkTest (uniformWeight n) (finiteFeature n) (pre++tail) x pre.length
    (fun z=>|physicalRootVectorTerminalResidual n V tail pre x z.1-
      physicalRootVectorTerminalResidual n V tail pre x z.2|^(4*l)) p
    ∂physicalPathLaw μ n (pre++tail) x hx

theorem physical_root_vector_cut_center_cancels (n l : ℕ) {P : Type}
    (V : P → EuclideanSpace ℝ (Fin n))
    (tail pre : List (GaussianStep (FeatureIndex n)))
    (x : P → FeatureIndex n → ℝ) (p : PhysicalPathState P n (pre++tail)) :
    conditionalForkTest (uniformWeight n) (finiteFeature n) (pre++tail) x pre.length
      (fun z=>|∑ i,V z.1.1 i*normalizedSpin n (ForwardPath.spin (pre++tail).length z.1.2) i-
        ∑ i,V z.2.1 i*normalizedSpin n (ForwardPath.spin (pre++tail).length z.2.2) i|^(4*l)) p =
    conditionalForkTest (uniformWeight n) (finiteFeature n) (pre++tail) x pre.length
      (fun z=>|physicalRootVectorTerminalResidual n V tail pre x z.1-
        physicalRootVectorTerminalResidual n V tail pre x z.2|^(4*l)) p := by
  have hc := conditionalForkTest_sub_cut_center (uniformWeight n) (finiteFeature n) pre tail x
    (fun p σ=>∑ i,V p i*normalizedSpin n σ i)
    (fun p y=>∑ i,V p i*actualSpinMean n tail y i) (fun z=>|z|^(4*l)) p
  convert hc using 1
  congr 1
  funext z
  simp only [physicalRootVectorTerminalResidual,physicalTerminalIncrement,Pi.sub_apply,mul_sub,
    Finset.sum_sub_distrib]

theorem physicalRootVectorTerminalResidual_measurable (n : ℕ) {P : Type} [MeasurableSpace P]
    (V : P → EuclideanSpace ℝ (Fin n)) (hV : Measurable V)
    (tail pre : List (GaussianStep (FeatureIndex n))) {a : ℝ} (hs : OrderedSteps a (pre++tail))
    (x : P → FeatureIndex n → ℝ) (hx : Measurable x) :
    Measurable (physicalRootVectorTerminalResidual n V tail pre x) := by
  unfold physicalRootVectorTerminalResidual
  apply Finset.measurable_sum
  intro i _
  exact (((PiLp.continuous_apply 2 (fun _ : Fin n=>ℝ) i).measurable).comp
    (hV.comp measurable_fst)).mul
      ((measurable_pi_apply i).comp (physicalTerminalIncrement_measurable n tail pre hs hx))

theorem physical_root_vector_resampling_le_residual (n l : ℕ) (hl : 0 < l)
    {P : Type} [MeasurableSpace P] (V : P → EuclideanSpace ℝ (Fin n)) (hV : Measurable V)
    (R : ℝ) (hbound : ∀ p,‖V p‖ ≤ R)
    (tail pre : List (GaussianStep (FeatureIndex n))) {a : ℝ} (hs : OrderedSteps a (pre++tail))
    (μ : Measure P) [IsFiniteMeasure μ] (x : P → FeatureIndex n → ℝ) (hx : Measurable x) :
    physicalRootVectorResamplingMoment n l V tail pre μ x hx ≤
      (2:ℝ)^(4*l)*(∫ p,|physicalRootVectorTerminalResidual n V tail pre x p|^(4*l)
        ∂physicalPathLaw μ n (pre++tail) x hx) := by
  let E := physicalRootVectorTerminalResidual n V tail pre x
  have hE := physicalRootVectorTerminalResidual_measurable n V hV tail pre hs x hx
  have hb p : |E p| ≤ 2*R := by
    apply (abs_dot_physicalTerminalIncrement_le n (fun i=>V p.1 i) tail pre hs x p).trans
    rw [projectionEuclideanNorm_coe]
    exact mul_le_mul_of_nonneg_left (hbound p.1) (by norm_num)
  have hr := fork_add_power_le (uniformWeight_pos n) (finiteFeature n) (pre++tail) hs μ x hx pre.length
    (hE.comp measurable_fst) ((hE.comp measurable_snd).neg) (fun z=>hb z.1)
    (fun z=>by simpa only [Function.comp_apply,Pi.neg_apply,abs_neg] using hb z.2) (4*l) (by omega)
  have hf := integral_conditionalForkTest_fst (uniformWeight_pos n) (finiteFeature n)
    (pre++tail) hs μ x hx pre.length (fun p=>|E p|^(4*l))
  have hg := integral_conditionalForkTest_snd (uniformWeight_pos n) (finiteFeature n)
    (pre++tail) hs μ x hx pre.length (F:=fun p=>|E p|^(4*l)) (R:=(2*R)^(4*l))
    (hE.abs.pow_const _) (fun p=>by
      rw [abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hb p) _)
  simp only [Function.comp_apply,Pi.neg_apply,abs_neg,←sub_eq_add_neg] at hr
  rw [hf,hg] at hr
  apply hr.trans_eq
  have he : (2:ℝ)^(4*l-1)*2=(2:ℝ)^(4*l) := by rw [←pow_succ]; congr 1; omega
  dsimp only [E]
  unfold physicalPathLaw
  rw [←two_mul,←mul_assoc,he]

theorem eventually_physical_root_vector_resampling (k : ℕ) (B : ℝ) :
    ∀ᶠ n : ℕ in atTop,∀ (P : Type) [MeasurableSpace P]
      (V : P → EuclideanSpace ℝ (Fin n)) (hV : Measurable V)
      (R : ℝ), (∀ p,‖V p‖ ≤ R) →
      ∀ (tail pre skip : List (GaussianStep (FeatureIndex n))) (a a₀ D : ℝ),
      0 < a → 0 < D → D ≤ B → OrderedSteps a (pre++tail) →
      OrderedSteps a₀ ((skip++pre)++tail) →
      ∀ (μ : Measure P) [IsFiniteMeasure μ] (x : P → FeatureIndex n → ℝ) (hx : Measurable x)
      (d : Fin pre.length → ℝ), (∀ j,0 ≤ d j) → (∑ j,d j=D) →
      (∀ j i,(hierarchyClocks pre j (Sum.inl i):ℝ)=d j) →
      physicalRootVectorResamplingMoment n (k+1) V tail (skip++pre) μ x hx ≤
        (2*(projectionLpConstant (2*k+1)*(Real.log (n:ℝ))^2/
          (a*Real.sqrt ((n:ℝ)*D))))^(4*(k+1))*
          (∫ p,‖V p‖^(4*(k+1)) ∂μ) := by
  filter_upwards [eventually_physical_suffix_terminal_projection (2*k+1) B] with n hn
  intro P _ V hV R hbound tail pre skip a a₀ D ha hD hDB ho hs μ _ x hx d hd hdD hc
  have hV' : Measurable (fun p i=>V p i) := by
    exact (WithLp.measurable_ofLp 2 (Fin n → ℝ)).comp hV
  have hI : Integrable (fun p=>(projectionEuclideanNorm n (fun i=>V p i))^(2*(2*k+1)+2)) μ := by
    apply Integrable.of_bound (((projectionEuclideanNorm_measurable n).comp hV').pow_const _).aestronglyMeasurable
      (R^(2*(2*k+1)+2))
    apply Eventually.of_forall
    intro p
    simp only [Function.comp_apply]
    rw [projectionEuclideanNorm_coe,Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hbound p) _
  have hp := hn P tail pre skip a a₀ D ha hD hDB ho hs μ (fun p i=>V p i) hV' x hx hI
    (fun p=>alignedFieldClock_of_physical n pre d hd D hdD hc (fun i=>V p i))
  have he : 2*(2*k+1)+2=4*(k+1) := by omega
  simp only [he,projectionEuclideanNorm_coe] at hp
  apply (physical_root_vector_resampling_le_residual n (k+1) (by omega) V hV R hbound
    tail (skip++pre) hs μ x hx).trans
  apply (mul_le_mul_of_nonneg_left hp (by positivity : (0:ℝ) ≤ 2^(4*(k+1)))).trans_eq
  rw [mul_pow,mul_assoc]

end OAI.SKFluctuations
