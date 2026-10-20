module

public import CavityPhysicalWeightedExterior
public import CavityPhysicalResamplingTreeLaw

@[expose] public section

noncomputable section
set_option maxHeartbeats 1500000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations
open Hierarchy

def physicalWeightedTerminalResidual (n : ℕ)
    {ext : List (GaussianStep (FeatureIndex n))}
    (T : ReplicaTree (FeatureIndex n) (Spin n) ext) (H : T.Assignment → ℝ) (s : T.Slot)
    (tail pre : List (GaussianStep (FeatureIndex n))) {P : Type}
    (xₑ x : P → FeatureIndex n → ℝ) (p : PhysicalPathState P n (pre++tail)) : ℝ :=
  ∑ i, (physicalWeightedExteriorAnchor n T H s (xₑ p.1)) i*
    physicalTerminalIncrement n tail pre x p i

def physicalWeightedExteriorResamplingMoment (n l : ℕ)
    {ext : List (GaussianStep (FeatureIndex n))}
    (T : ReplicaTree (FeatureIndex n) (Spin n) ext) (H : T.Assignment → ℝ) (s : T.Slot)
    (tail pre : List (GaussianStep (FeatureIndex n))) {P : Type} [MeasurableSpace P]
    (μ : Measure P) (xₑ x : P → FeatureIndex n → ℝ) (hx : Measurable x) : ℝ :=
  ∫ p, conditionalForkTest (uniformWeight n) (finiteFeature n) (pre++tail) x pre.length
    (fun z=>|physicalWeightedTerminalResidual n T H s tail pre xₑ x z.1-
      physicalWeightedTerminalResidual n T H s tail pre xₑ x z.2|^(4*l)) p
    ∂physicalPathLaw μ n (pre++tail) x hx

theorem physical_weighted_resampling_cut_center_cancels (n l : ℕ)
    {ext : List (GaussianStep (FeatureIndex n))}
    (T : ReplicaTree (FeatureIndex n) (Spin n) ext) (H : T.Assignment → ℝ) (s : T.Slot)
    (tail pre : List (GaussianStep (FeatureIndex n))) {P : Type}
    (xₑ x : P → FeatureIndex n → ℝ) (p : PhysicalPathState P n (pre++tail)) :
    conditionalForkTest (uniformWeight n) (finiteFeature n) (pre++tail) x pre.length
      (fun z=>|∑ i, (physicalWeightedExteriorAnchor n T H s (xₑ z.1.1)) i*
        normalizedSpin n (ForwardPath.spin (pre++tail).length z.1.2) i-
        ∑ i, (physicalWeightedExteriorAnchor n T H s (xₑ z.2.1)) i*
          normalizedSpin n (ForwardPath.spin (pre++tail).length z.2.2) i|^(4*l)) p=
    conditionalForkTest (uniformWeight n) (finiteFeature n) (pre++tail) x pre.length
      (fun z=>|physicalWeightedTerminalResidual n T H s tail pre xₑ x z.1-
        physicalWeightedTerminalResidual n T H s tail pre xₑ x z.2|^(4*l)) p := by
  have hc := conditionalForkTest_sub_cut_center (uniformWeight n) (finiteFeature n) pre tail x
    (fun p σ=>∑ i, (physicalWeightedExteriorAnchor n T H s (xₑ p)) i*normalizedSpin n σ i)
    (fun p y=>∑ i, (physicalWeightedExteriorAnchor n T H s (xₑ p)) i*actualSpinMean n tail y i)
    (fun z=>|z|^(4*l)) p
  convert hc using 1
  congr 1
  funext z
  simp only [physicalWeightedTerminalResidual,physicalTerminalIncrement,Pi.sub_apply,mul_sub,Finset.sum_sub_distrib]

theorem physicalWeightedTerminalResidual_measurable (n : ℕ)
    {ext : List (GaussianStep (FeatureIndex n))}
    (T : ReplicaTree (FeatureIndex n) (Spin n) ext) {aₑ : ℝ} (hₑ : OrderedSteps aₑ ext)
    (H : T.Assignment → ℝ) (s : T.Slot)
    (tail pre : List (GaussianStep (FeatureIndex n))) {a : ℝ} (hs : OrderedSteps a (pre++tail))
    {P : Type} [MeasurableSpace P] (xₑ x : P → FeatureIndex n → ℝ)
    (hxₑ : Measurable xₑ) (hx : Measurable x) :
    Measurable (physicalWeightedTerminalResidual n T H s tail pre xₑ x) := by
  unfold physicalWeightedTerminalResidual
  apply Finset.measurable_sum
  intro i _
  have hA : Measurable (fun p : PhysicalPathState P n (pre++tail)=>
      physicalWeightedExteriorAnchor n T H s (xₑ p.1)) :=
    (physicalWeightedExteriorAnchor_continuous n T hₑ H s).measurable.comp (hxₑ.comp measurable_fst)
  exact (((PiLp.continuous_apply 2 (fun _ : Fin n=>ℝ) i).measurable).comp hA).mul
    ((measurable_pi_apply i).comp (physicalTerminalIncrement_measurable n tail pre hs hx))

theorem physical_weighted_exterior_resampling_le_residual (n l : ℕ) (hl : 0<l)
    {ext : List (GaussianStep (FeatureIndex n))}
    (T : ReplicaTree (FeatureIndex n) (Spin n) ext) {aₑ : ℝ} (hₑ : OrderedSteps aₑ ext)
    (H : T.Assignment → ℝ) (s : T.Slot)
    (tail pre : List (GaussianStep (FeatureIndex n))) {a : ℝ} (hs : OrderedSteps a (pre++tail))
    {P : Type} [MeasurableSpace P] (μ : Measure P) [IsFiniteMeasure μ]
    (xₑ x : P → FeatureIndex n → ℝ) (hxₑ : Measurable xₑ) (hx : Measurable x) :
    physicalWeightedExteriorResamplingMoment n l T H s tail pre μ xₑ x hx≤
      (2:ℝ)^(4*l)*(∫ p, |physicalWeightedTerminalResidual n T H s tail pre xₑ x p|^(4*l)
        ∂physicalPathLaw μ n (pre++tail) x hx) := by
  let E := physicalWeightedTerminalResidual n T H s tail pre xₑ x
  let R := 2*(∑ σ, |H σ| * ‖WithLp.toLp 2 (normalizedSpin n (T.atSlot σ s))‖)
  have hE := physicalWeightedTerminalResidual_measurable n T hₑ H s tail pre hs xₑ x hxₑ hx
  have hbound (p) : |E p|≤R := by
    apply (abs_dot_physicalTerminalIncrement_le n
      (fun i=>physicalWeightedExteriorAnchor n T H s (xₑ p.1) i) tail pre hs x p).trans
    rw [projectionEuclideanNorm_coe]
    exact mul_le_mul_of_nonneg_left (physicalWeightedExteriorAnchor_norm_le n T hₑ H s _) (by norm_num)
  have hr := fork_add_power_le (uniformWeight_pos n) (finiteFeature n) (pre++tail) hs μ x hx pre.length
    (hE.comp measurable_fst) ((hE.comp measurable_snd).neg) (fun z=>hbound z.1)
    (fun z=>by simpa only [Function.comp_apply,Pi.neg_apply,abs_neg] using hbound z.2) (4*l) (by omega)
  have hf := integral_conditionalForkTest_fst (uniformWeight_pos n) (finiteFeature n)
    (pre++tail) hs μ x hx pre.length (fun p=>|E p|^(4*l))
  have hg := integral_conditionalForkTest_snd (uniformWeight_pos n) (finiteFeature n)
    (pre++tail) hs μ x hx pre.length (F:=fun p=>|E p|^(4*l)) (R:=R^(4*l))
    (hE.abs.pow_const _) (fun p=>by
      rw [abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hbound p) _)
  simp only [Function.comp_apply,Pi.neg_apply,abs_neg,←sub_eq_add_neg] at hr
  rw [hf,hg] at hr
  apply hr.trans_eq
  have he : (2:ℝ)^(4*l-1)*2=(2:ℝ)^(4*l) := by rw [←pow_succ]; congr 1; omega
  dsimp only [E]
  unfold physicalPathLaw
  rw [←two_mul,←mul_assoc,he]

end OAI.SKFluctuations
