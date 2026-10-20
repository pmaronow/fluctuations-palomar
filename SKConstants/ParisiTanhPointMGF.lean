module
public import SKConstants.ParisiPostWeightedMGF
public import SKConstants.ParisiFullMartingale

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace SKConstants
open SKConstantsOAI.ZeroTemperatureSK ParisiFullSupport
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {Ω : Type*} [MeasurableSpace Ω]
local instance ParisiTanhPointMGF_localInstance1 (W : BrownianSystem Ω) : IsProbabilityMeasure W.law := W.isProbability

theorem scalarTanhPicard_endpoint_mgf (W : BrownianSystem Ω) (z : ℝ) (v : ℝ≥0) (θ : ℝ) :
    (∫ w,Real.exp (θ*(Real.tanh (scalarForwardPicardPath scalarTanhDrift v
      (z,brownianFinitePath W v w) ⟨v,v.coe_nonneg,le_rfl⟩)-Real.tanh z)) ∂W.law)≤
      Real.exp ((v:ℝ)*θ^2/2) := by
  let q : ℕ → ℝ≥0 := fun k => if k=0 then 0 else v
  have hq : Monotone q := by
    intro a b hab
    by_cases ha : a=0
    · simp [q,ha]
    · have hb : b≠0 := by omega
      simp [q,ha,hb]
  have h := scalarTanhPicard_weighted_mgf W z q hq (fun _ => 1) 1 θ
  have hq0 : q 0=0 := by simp [q]
  have hq1 : q 1=v := by simp [q]
  have hp (p : ScalarContinuousPath v) : postPathWeighted q (fun _ => 1) 1 p =
      Real.tanh (p ⟨v,v.coe_nonneg,le_rfl⟩)-Real.tanh (p ⟨0,le_rfl,v.coe_nonneg⟩) := by
    simp only [postPathWeighted,Finset.sum_range_one,Nat.zero_add,hq0,hq1,one_mul,NNReal.coe_zero]
    change Real.tanh (p (projIcc 0 (v:ℝ) v.coe_nonneg (v:ℝ))) -
      Real.tanh (p (projIcc 0 (v:ℝ) v.coe_nonneg 0)) = _
    rw [projIcc_of_mem _ (show (v:ℝ)∈Icc (0:ℝ) v from ⟨v.coe_nonneg,le_rfl⟩),
      projIcc_of_mem _ (show (0:ℝ)∈Icc (0:ℝ) v from ⟨le_rfl,v.coe_nonneg⟩)]
  have hz : ∀ᵐ w ∂W.law,scalarForwardPicardPath scalarTanhDrift v
      (z,brownianFinitePath W v w) ⟨0,le_rfl,v.coe_nonneg⟩=z := by
    filter_upwards [brownianFinitePath_version W v,W.brownian.toIsPreBrownianReal.eval_zero_ae_eq_zero]
      with w hw hzero
    rw [scalarForwardPicardPath_integral_equation]
    rw [hw ⟨0,le_rfl,v.coe_nonneg⟩]
    simp only [intervalIntegral.integral_same,add_zero]
    change z+W.B 0 w=z
    rw [hzero,add_zero]
  have hproxy : preCDFWeightedProxy q (fun _ => 1) 1=v := by
    simp [preCDFWeightedProxy,q]
  rw [hproxy] at h
  change (∫ w,Real.exp (θ*postPathWeighted q (fun _ => 1) 1
    (scalarForwardPicardPath scalarTanhDrift v (z,brownianFinitePath W v w))) ∂W.law)≤_ at h
  refine (integral_congr_ae ?_).trans_le h
  filter_upwards [hz] with w hw
  rw [hp,hw]

theorem actualParisiFullRestart_post_mgf (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1<β) (a v : ℝ≥0) (ha : parisiEquilibriumPhysicalEndpoint β≤a)
    (past : ScalarContinuousPath a) (θ : ℝ) :
    (∫ w,Real.exp (θ*(actualParisiFullMagnetization β ((a+v:ℝ≥0):ℝ)
      (boundedDriftRestartCallback (actualParisiFullScalarDrift β) a v
        (past,brownianFinitePath W v w) ⟨v,v.coe_nonneg,le_rfl⟩)-
      actualParisiFullMagnetization β a (past ⟨a,a.coe_nonneg,le_rfl⟩))) ∂W.law)≤
      Real.exp ((v:ℝ)*θ^2/2) := by
  have hafter (t : ℝ≥0) (ht : parisiEquilibriumPhysicalEndpoint β≤t) :
      β^2*parisiEquilibriumSupportEndpoint β≤(t:ℝ) := by
    simpa only [parisiEquilibriumPhysicalEndpoint_coe β hβ] using NNReal.coe_le_coe.mpr ht
  rw [actualParisiFullMagnetization_eq_tanh_after_support β hβ _
    (hafter (a+v) (ha.trans (le_add_of_nonneg_right bot_le))),
    actualParisiFullMagnetization_eq_tanh_after_support β hβ _ (hafter a ha)]
  simp_rw [actualParisiRestartCallback_eq_tanh_after_support β hβ a v ha]
  exact scalarTanhPicard_endpoint_mgf W (past ⟨a,a.coe_nonneg,le_rfl⟩) v θ

end SKConstants
