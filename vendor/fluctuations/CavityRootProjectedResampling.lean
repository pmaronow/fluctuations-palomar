module

public import CavityExteriorResamplingClock
public import CavityPhysicalFreshTooth

@[expose] public section

noncomputable section
set_option maxHeartbeats 1500000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations
open Hierarchy

def physicalRootProjectionResidual (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {P : Type}
    (x : P → FeatureIndex n → ℝ) (cut : ℕ) (p : PhysicalPathState P n steps) : ℝ :=
  inner ℝ (actualSpinPath n steps x 0 p)
    (physicalCutIncrement n steps x cut (steps.length+1) p)

def physicalRootProjectedResamplingMoment (n l : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {P : Type} [MeasurableSpace P]
    (μ : Measure P) (x : P → FeatureIndex n → ℝ) (hx : Measurable x) (cut : ℕ) : ℝ :=
  ∫ p, conditionalForkTest (uniformWeight n) (finiteFeature n) steps x cut
    (fun z=>|physicalRootProjectionResidual n steps x cut z.1-
      physicalRootProjectionResidual n steps x cut z.2|^(2*l)) p
    ∂physicalPathLaw μ n steps x hx

theorem physicalRootProjectionResidual_measurable (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {c : ℝ} (hs : OrderedSteps c steps)
    {P : Type} [MeasurableSpace P] (x : P → FeatureIndex n → ℝ) (hx : Measurable x)
    (cut : ℕ) : Measurable (physicalRootProjectionResidual n steps x cut) :=
  (actualSpinPath_measurable n steps hs x hx 0).inner
    (physicalCutIncrement_measurable n steps hs x hx cut (steps.length+1))

theorem physicalRootProjectionResidual_abs_le (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {c : ℝ} (hs : OrderedSteps c steps)
    {P : Type} (x : P → FeatureIndex n → ℝ) (cut : ℕ) (p : PhysicalPathState P n steps) :
    |physicalRootProjectionResidual n steps x cut p|≤2 := by
  have H := norm_inner_le_norm (𝕜:=ℝ) (actualSpinPath n steps x 0 p)
    (physicalCutIncrement n steps x cut (steps.length+1) p)
  rw [Real.norm_eq_abs] at H
  apply H.trans
  simpa only [one_mul] using mul_le_mul (actualSpinPath_norm_le n steps hs x 0 p)
    (physicalCutIncrement_norm_le n steps hs x cut (steps.length+1) p) (norm_nonneg _)
    (by norm_num : (0:ℝ)≤1)

theorem physical_root_residual_eq_core_power (n l : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {c : ℝ} (hs : OrderedSteps c steps)
    {P : Type} [MeasurableSpace P] (μ : Measure P) [IsFiniteMeasure μ]
    (x : P → FeatureIndex n → ℝ) (hx : Measurable x) (cut : ℕ) :
    (∫ p, |physicalRootProjectionResidual n steps x cut p|^(2*l)
      ∂physicalPathLaw μ n steps x hx)=
    ∫ p, physicalCoreLayerPower n l steps x 0 0 cut (steps.length+1) p
      ∂physicalPathLaw μ n steps x hx := by
  have hE := physicalRootProjectionResidual_measurable n steps hs x hx cut
  have H := integral_conditionalForkTest_snd (uniformWeight_pos n) (finiteFeature n)
    steps hs μ x hx 0 (hE.abs.pow_const (2*l))
    (fun p=>by
      rw [abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
      exact pow_le_pow_left₀ (abs_nonneg _) (physicalRootProjectionResidual_abs_le n steps hs x cut p) _)
  symm
  unfold physicalPathLaw
  convert H using 1
  congr 1
  funext p
  simp only [physicalCoreLayerPower,physicalRootProjectionResidual,conditionalForkTest,
    conditionalPathAverage,actualSpinPath_zero]

theorem physical_root_projected_resampling_le_core (n l : ℕ) (hl : 0<l)
    (steps : List (GaussianStep (FeatureIndex n))) {c : ℝ} (hs : OrderedSteps c steps)
    {P : Type} [MeasurableSpace P] (μ : Measure P) [IsFiniteMeasure μ]
    (x : P → FeatureIndex n → ℝ) (hx : Measurable x) (cut : ℕ) :
    physicalRootProjectedResamplingMoment n l steps μ x hx cut≤
      (2:ℝ)^(2*l)*(∫ p, physicalCoreLayerPower n l steps x 0 0 cut (steps.length+1) p
        ∂physicalPathLaw μ n steps x hx) := by
  let E := physicalRootProjectionResidual n steps x cut
  have hE := physicalRootProjectionResidual_measurable n steps hs x hx cut
  have hER := physicalRootProjectionResidual_abs_le n steps hs x cut
  have H := fork_add_power_le (uniformWeight_pos n) (finiteFeature n) steps hs μ x hx cut
    (hE.comp measurable_fst) ((hE.comp measurable_snd).neg) (fun z=>hER z.1)
    (fun z=>by simpa only [Function.comp_apply,Pi.neg_apply,abs_neg] using hER z.2) (2*l) (by omega)
  have hfst := integral_conditionalForkTest_fst (uniformWeight_pos n) (finiteFeature n)
    steps hs μ x hx cut (fun p=>|E p|^(2*l))
  have hsnd := integral_conditionalForkTest_snd (uniformWeight_pos n) (finiteFeature n)
    steps hs μ x hx cut (hE.abs.pow_const (2*l))
    (fun p=>by
      rw [abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hER p) _)
  simp only [Function.comp_apply,Pi.neg_apply,abs_neg,←sub_eq_add_neg] at H
  rw [hfst,hsnd] at H
  change physicalRootProjectedResamplingMoment n l steps μ x hx cut≤_ at H
  apply H.trans_eq
  rw [←physical_root_residual_eq_core_power n l steps hs μ x hx cut]
  dsimp only [E]
  unfold physicalPathLaw
  have he : (2:ℝ)^(2*l)=(2:ℝ)^(2*l-1)*2 := by rw [←pow_succ]; congr 1; omega
  rw [he]
  ring

theorem physical_root_projection_residual_at_cut (n : ℕ)
    (pre tail : List (GaussianStep (FeatureIndex n))) {P : Type}
    (x : P → FeatureIndex n → ℝ) (p : PhysicalPathState P n (pre++tail)) :
    physicalRootProjectionResidual n (pre++tail) x pre.length p=
      physicalProjectedBoundaryOverlap n (pre++tail)
        (ForwardPath.spin (pre++tail).length p.2) (x p.1)-
      ∑ i, actualSpinMean n (pre++tail) (x p.1) i*
        actualSpinMean n tail (actualCutField pre tail (x p.1) p.2) i := by
  have he : actualSpinPath n (pre++tail) x pre.length p=
      WithLp.toLp 2 (actualSpinMean n tail (actualCutField pre tail (x p.1) p.2)) := by
    ext i
    exact hierarchyMeanPath_at_cut _ _ _ pre tail x p
  rw [physicalRootProjectionResidual,physicalCutIncrement,inner_sub_right,
    actualSpinPath_zero,actualSpinPath_terminal,he]
  simp only [physicalProjectedBoundaryOverlap,PiLp.inner_apply,RCLike.inner_apply,conj_trivial]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem physical_root_projected_resampling_eq_boundary (n l : ℕ)
    (pre tail : List (GaussianStep (FeatureIndex n))) {P : Type} [MeasurableSpace P]
    (μ : Measure P) (x : P → FeatureIndex n → ℝ) (hx : Measurable x) :
    physicalRootProjectedResamplingMoment n l (pre++tail) μ x hx pre.length=
      ∫ p, conditionalForkTest (uniformWeight n) (finiteFeature n) (pre++tail) x pre.length
        (fun z=>|physicalProjectedBoundaryOverlap n (pre++tail)
          (ForwardPath.spin (pre++tail).length z.1.2) (x z.1.1)-
          physicalProjectedBoundaryOverlap n (pre++tail)
            (ForwardPath.spin (pre++tail).length z.2.2) (x z.2.1)|^(2*l)) p
        ∂physicalPathLaw μ n (pre++tail) x hx := by
  apply integral_congr_ae
  apply Eventually.of_forall
  intro p
  have H := conditionalForkTest_sub_cut_center (uniformWeight n) (finiteFeature n) pre tail x
    (fun p σ=>physicalProjectedBoundaryOverlap n (pre++tail) σ (x p))
    (fun p y=>∑ i, actualSpinMean n (pre++tail) (x p) i*actualSpinMean n tail y i)
    (fun t=>|t|^(2*l)) p
  symm
  convert H using 1
  congr 1
  funext z
  rw [physical_root_projection_residual_at_cut,physical_root_projection_residual_at_cut]

theorem eventually_physical_root_projected_clock_bound (k : ℕ) (B : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ (P : Type) [MeasurableSpace P]
      (steps : List (GaussianStep (FeatureIndex n))) (a c D D₀ xs H : ℝ),
      0<a → 0<D₀ → D₀≤D → D≤B → 0<xs → 0≤H → OrderedSteps c steps →
    ∀ (μ : Measure P) [IsProbabilityMeasure μ]
      (x : P → FeatureIndex n → ℝ) (hx : Measurable x) (cut : ℕ),
      PhysicalProjectionClock n steps 0 cut (steps.length+1) a D →
      xs+physicalCutMass c steps 0≤H*a^2 →
    physicalRootProjectedResamplingMoment n (k+1) steps μ x hx cut≤
      (2:ℝ)^(2*(k+1))*(4*(projectionLpConstant k)^2*(Real.log (n:ℝ))^4*
        (physicalRawRatio n (k+1) steps c xs μ x hx)^2*H/((n:ℝ)*D₀))^(k+1) := by
  filter_upwards [eventually_physical_clock_core_layer_full_moment k B,
    eventually_gt_atTop (0:ℕ)] with n hn hnpos
  intro P _ steps a c D D₀ xs H ha hD₀ hD hDB hxs hH hs μ _ x hx cut hc hscale
  have hN : 0<(n:ℝ) := by exact_mod_cast hnpos
  have hr := hn P steps a c D xs ha (hD₀.trans_le hD) hDB hxs hs μ x hx
    0 0 cut (steps.length+1) (by omega) hc
  have hS : 0≤xs+physicalCutMass c steps 0 :=
    add_nonneg hxs.le (physicalCutMass_mem steps hs 0).1
  have hQ := physicalRawRatio_one_le n (k+1) steps c xs μ x hx
  have H := projection_weight_scale_bound (C:=projectionLpConstant k) (z:=Real.log (n:ℝ))
    (Q:=physicalRawRatio n (k+1) steps c xs μ x hx) hN ha hD₀ hD (m:=1)
    (by norm_num) hS hH (by simpa only [one_mul] using hscale)
  simp only [one_mul] at H
  have hh : (projectionLpConstant k*Real.log (n:ℝ)^2/(a*Real.sqrt ((n:ℝ)*D)))^2*
      (physicalRawRatio n (k+1) steps c xs μ x hx)^2*(xs+physicalCutMass c steps 0)≤
      (projectionLpConstant k*Real.log (n:ℝ)^2/(a*Real.sqrt ((n:ℝ)*D)))^2*
      (2*physicalRawRatio n (k+1) steps c xs μ x hx)^2*(xs+physicalCutMass c steps 0) := by
    apply mul_le_mul_of_nonneg_right _ hS
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    nlinarith [sq_nonneg (physicalRawRatio n (k+1) steps c xs μ x hx)]
  have hp := pow_le_pow_left₀ (Real.rpow_nonneg
    (integral_nonneg fun p=>physicalCoreLayerPower_nonneg n (k+1) steps x 0 0 cut (steps.length+1) p) _)
    (hr.trans (hh.trans H)) (k+1)
  rw [Real.rpow_inv_natCast_pow
    (integral_nonneg fun p=>physicalCoreLayerPower_nonneg n (k+1) steps x 0 0 cut (steps.length+1) p)
    (Nat.succ_ne_zero k)] at hp
  exact (physical_root_projected_resampling_le_core n (k+1) (Nat.succ_pos k)
    steps hs μ x hx cut).trans (mul_le_mul_of_nonneg_left hp (by positivity))

end OAI.SKFluctuations
