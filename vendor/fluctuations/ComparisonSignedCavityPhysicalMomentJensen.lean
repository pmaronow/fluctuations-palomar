module

public import CavityCenteringMoments
public import SKFluctuationsOAI.Probability.SKFluctuations.FiniteRetainedGridReady
public import SKFluctuationsOAI.Probability.SKFluctuations.PhysicalTerminalPairLaw

@[expose] public section

noncomputable section
set_option maxHeartbeats 6000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations
open Hierarchy

namespace Hierarchy
variable {S ι : Type*} [Fintype S] [Nonempty S] [Fintype ι]

theorem hierarchy_pair_mean_even_power_le {w : S → ℝ} (hw : ∀σ,0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (P : S → S → ℝ)
    (tail : List (GaussianStep ι)) {a : ℝ} (ha : OrderedSteps a tail)
    (l : ℕ) (x : ι → ℝ) :
    (hierarchyPairMean w φ P tail x)^(2*l) ≤
      hierarchyPairMean w φ (fun σ τ=>|P σ τ|^(2*l)) tail x := by
  let q := fun σ=>hierarchyAtom w φ tail σ x
  have hq : ∀σ,0 ≤ q σ := fun σ=>hierarchyAtom_nonneg hw φ tail ha σ x
  have hmass : ∑σ,q σ=1 := hierarchyAtom_sum hw φ tail ha x
  have hpair : (∑z : S×S,q z.1*q z.2)=1 := by
    simp only [Fintype.sum_prod_type,←Finset.mul_sum,hmass,mul_one]
  have H := finite_weighted_mean_abs_pow_le (fun z : S×S=>q z.1*q z.2)
    (fun z=>P z.1 z.2) (fun z=>mul_nonneg (hq z.1) (hq z.2)) hpair (2*l)
  simpa only [Fintype.sum_prod_type,hierarchyPairMean,q,(even_two_mul l).pow_abs] using H

theorem step_power_disorder_even_le_pair {w : S → ℝ} (hw : ∀σ,0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (P : S → S → ℝ)
    (pre tail : List (GaussianStep ι)) {a : ℝ} (ha : OrderedSteps a (pre++tail))
    (q₀ : ι → ℝ≥0) (l : ℕ) (x : ι → ℝ) :
    stepPowerDisorder w φ q₀ pre tail P (2*l) x ≤
      stepPairDisorder w φ q₀ pre tail (fun σ τ=>|P σ τ|^(2*l)) x := by
  have htail := ha.suffix pre tail
  have hpre : ∀st∈pre,0<st.1 := fun st hst=>ha.mem_pos st (List.mem_append_left tail hst)
  obtain ⟨C,hF⟩ := gaussianHierarchy_lipschitz hw φ tail htail
  have hA : BddSmooth 0 (fun y=>(hierarchyPairMean w φ P tail y)^(2*l)) :=
    (hierarchyPairMean_smooth hw φ P tail htail 0).pow (2*l)
  have hB := hierarchyPairMean_smooth hw φ (fun σ τ=>|P σ τ|^(2*l)) tail htail 0
  have hAi := prefixTest_smooth0 hF hA pre hpre
  have hBi := prefixTest_smooth0 hF hB pre hpre
  have Hmono := prefixTest_mono hF hA hB
    (hierarchy_pair_mean_even_power_le hw φ P tail htail l) pre hpre
  unfold stepPowerDisorder stepPairDisorder zeroContinuation stepPowerMean stepPairMean
  simp_rw [←hierarchyPairMean_eq_nested hw φ P tail htail,
    ←hierarchyPairMean_eq_nested hw φ (fun σ τ=>|P σ τ|^(2*l)) tail htail]
  exact integral_mono (hAi.integrable_zero_shift x) (hBi.integrable_zero_shift x)
    (fun y=>Hmono (x+y))

end Hierarchy

theorem physical_norm_power_le_overlap_moment (n l : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q₀ : FeatureIndex n → ℝ≥0) (j : ℕ) (hj : j ≤ steps.length) :
    (∫p,‖actualSpinPath n steps id j p‖^(4*l)
      ∂physicalPathLaw (Measure.pi fun i=>gaussianReal 0 (q₀ i)) n steps id measurable_id) ≤
      physicalOverlapMoment n l steps (Measure.pi fun i=>gaussianReal 0 (q₀ i))
        id measurable_id j := by
  have hsplit : steps.take j++steps.drop j=steps := List.take_append_drop ..
  have ho : OrderedSteps 0 (steps.take j++steps.drop j) := by rwa [hsplit]
  have Hnorm := physicalPowerMoment_eq_stepPowerDisorder n (2*l)
    (steps.take j) (steps.drop j) ho q₀
  rw [rootedHierarchyPathLaw_eq_physical] at Hnorm
  have Hpair := physicalOverlapMoment_eq_stepPairDisorder n l
    (steps.take j) (steps.drop j) ho q₀
  have Hjensen := step_power_disorder_even_le_pair (uniformWeight_pos n) (finiteFeature n)
    (orderedOverlap n) (steps.take j) (steps.drop j) ho q₀ l 0
  have H := Hnorm.trans_le Hjensen
  rw [←Hpair] at H
  rw [List.length_take_of_le hj,hsplit] at H
  simpa only [show 2*(2*l)=4*l by omega] using H

end OAI.SKFluctuations
