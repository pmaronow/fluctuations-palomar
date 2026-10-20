module

public import PhysicalOverlapEnergyUpper

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 1000000

def physicalCapVarianceSum {n : ℕ} : List (GaussianStep (FeatureIndex n))→ℝ
  | []=>0
  | (_,q)::rest=>(∑ k,(q k:ℝ))+physicalCapVarianceSum rest

theorem physicalOverlapEnergyConstant_nonneg (n : ℕ) : 0 ≤ physicalOverlapEnergyConstant n :=
  mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)

theorem physicalFilledOverlapEnergy_integral_le_variance (n d : ℕ)
    (e : Fin (d+1) ≃ FeatureIndex n) (q : FeatureIndex n→ℝ≥0)
    (steps : List (GaussianStep (FeatureIndex n))) {m : ℝ}
    (ha : OrderedSteps m steps) (hm : 0 < m) (x : FeatureIndex n→ℝ) :
    (∫ t in 0..1,physicalFilledOverlapEnergy n d (physicalJointGaussianDriver n d e q)
      steps ha hm 1 t x) ≤ physicalOverlapEnergyConstant n*∑ k,(q k:ℝ) := by
  have hi : IntervalIntegrable (fun t=>physicalFilledOverlapEnergy n d
      (physicalJointGaussianDriver n d e q) steps ha hm 1 t x) volume 0 1 :=
    (physicalFilledOverlapEnergy_continuous n d _ steps ha hm 1 x).intervalIntegrable 0 1
  have hc : IntervalIntegrable (fun _ : ℝ=>physicalOverlapEnergyConstant n*∑ k,(q k:ℝ)) volume 0 1 :=
    intervalIntegrable_const
  have hh := intervalIntegral.integral_mono_on zero_le_one hi hc
    (fun t _=>physicalFilledOverlapEnergy_le_variance n d e q steps ha hm 1 t x)
  simpa only [intervalIntegral.integral_const,sub_zero,one_smul] using hh

theorem physicalFiniteCapEnergy_le_variance (n d : ℕ)
    (e : Fin (d+1) ≃ FeatureIndex n)
    (pre tail : List (GaussianStep (FeatureIndex n))) {a : ℝ}
    (ha : OrderedSteps a (pre++tail)) (x : FeatureIndex n→ℝ) :
    physicalFiniteCapEnergy n d e pre tail ha x ≤
      physicalOverlapEnergyConstant n*physicalCapVarianceSum pre := by
  induction pre generalizing a x with
  | nil=>simp [physicalFiniteCapEnergy,physicalCapVarianceSum]
  | cons st pre ih=>
    rcases st with ⟨m,q⟩
    have hfirst := physicalFilledOverlapEnergy_integral_le_variance n d e q (pre++tail)
      ha.2.2.2 ha.2.2.1 x
    have hi := gaussianHierarchy_integrable (uniformWeight_pos n) (finiteFeature n)
      (pre++tail) ha.2.2.2 m q x
    have hrest := shiftedMean_mono (physicalFiniteCapEnergy_smooth n d e pre tail ha.2.2.2)
      (BddSmooth.const 0 (physicalOverlapEnergyConstant n*physicalCapVarianceSum pre))
      (ih ha.2.2.2) hi
    rw [shiftedMean_const _ hi] at hrest
    simp only [physicalFiniteCapEnergy,physicalCapVarianceSum]
    nlinarith

theorem physicalCapVarianceSum_sample_eq (n : ℕ)
    (q : ℝ→FeatureIndex n→ℝ≥0)
    (hq : ∀k,MonotoneOn (fun u=>q u k) (Icc (0:ℝ) 1))
    {a : ℝ} (as : List PositiveMass) (ha : MassOrdered a as) :
    physicalCapVarianceSum (sampleClockSteps q a as)=
      ∑ k,((q (partitionEnd a as) k:ℝ)-(q a k:ℝ)) := by
  induction as generalizing a with
  | nil=>simp [physicalCapVarianceSum,sampleClockSteps,partitionEnd]
  | cons b bs ih=>
    have hb1 : b.val ≤ 1 := (massOrdered_bounds ha.2.2).2
    have ha1 : a ≤ 1 := ha.2.1.trans hb1
    have hqb (k : FeatureIndex n) : q a k ≤ q b.val k :=
      hq k ⟨ha.1,ha1⟩ ⟨b.property.le,hb1⟩ ha.2.1
    simp only [sampleClockSteps,physicalCapVarianceSum,partitionEnd,ih ha.2.2]
    simp_rw [NNReal.coe_sub (hqb _)]
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring

theorem physicalCapEnergy_band_rooted_le_variance (n d : ℕ)
    (e : Fin (d+1) ≃ FeatureIndex n) (q₀ : FeatureIndex n→ℝ≥0)
    (common mid tail : List (GaussianStep (FeatureIndex n)))
    (ha : OrderedSteps 0 ((common++mid)++tail)) :
    physicalPathSecondMoment n ((common++mid)++tail) q₀ (common++mid).length-
      physicalPathSecondMoment n ((common++mid)++tail) q₀ common.length ≤
      physicalOverlapEnergyConstant n*physicalCapVarianceSum mid := by
  let hfull : OrderedSteps 0 (common++(mid++tail)) := by
    simpa only [List.append_assoc] using ha
  let hmid := hfull.suffix common (mid++tail)
  obtain ⟨C,hF⟩ := gaussianHierarchy_lipschitz (uniformWeight_pos n) (finiteFeature n) (mid++tail) hmid
  have hpos : ∀st∈common,0 < st.1 := fun st hs=>hfull.mem_pos st (List.mem_append_left _ hs)
  have hh := rootedPrefixTest_le_const hF (physicalFiniteCapEnergy_smooth n d e mid tail hmid)
    common hpos (physicalFiniteCapEnergy_le_variance n d e mid tail hmid) q₀ 0
  rw [physicalFiniteCapEnergy_band_rooted_eq_path_increment n d e q₀ common mid tail ha] at hh
  exact hh

end OAI.SKFluctuations.LaplaceWindowFormalization
