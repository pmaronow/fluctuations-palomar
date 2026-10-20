module

public import ComparisonActualHighOnlyOmittedCapEnvelopes

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 10000000
theorem actual_shifted_omitted_quantile_cap_envelopes {c s r0 : ℝ} {k M : ℝ→ℝ}
    (_hr0 : 0 ≤ r0) (hr1 : r0 ≤ 1) (hs : s∈Icc (0:ℝ) 1) (hc : 0 < c) (hk : ContinuousOn k (Icc r0 1))
    (hkc : ∀r∈Icc r0 1,c  ≤  k r)
    (hMc : Continuous M) (hm : MonotoneOn M (Icc (0:ℝ) 1))
    (hMp : ∀u∈Icc (0:ℝ) 1,0 < M u)
    (alpha : inverseIntegralConstraints r0 s k M) {u : ℝ} (hu : u∈Icc s 1) :
    let q:=omittedSweepQuantile hr1 hs hc hk hkc hm (hMp 1 ⟨zero_le_one,le_rfl⟩).le alpha
    r0+inverseCapPrimitive M u-inverseCapPrimitive M s  ≤  q u ∧ q u  ≤  downwardBarrierEnvelope M u := by
  intro q
  have Hlip:=omittedSweepQuantile_lipschitz hr1 hs hc hk hkc hm
    (hMp 1 ⟨zero_le_one,le_rfl⟩).le alpha
  have HAC:AbsolutelyContinuousOnInterval q s 1:=by
    apply LipschitzOnWith.absolutelyContinuousOnInterval
    exact Hlip.lipschitzOnWith
  have HI:=inverseCapPrimitive_integrable hMc hm hMp
  have Hder:=omittedSweepQuantile_ae_slope hr1 hs hc hk hkc hm
    (hMp 1 ⟨zero_le_one,le_rfl⟩).le alpha hMc
    (fun v hv=>hMp v ⟨hs.1.trans hv.1,hv.2⟩)
  have Hgap {x y : ℝ} (hx : x∈Icc s 1) (hy : y∈Icc s 1) (hxy : x ≤ y) :
      inverseCapPrimitive M y-inverseCapPrimitive M x  ≤  q y-q x := by
    have Hsub:uIcc x y⊆uIcc s 1:=by
      rw [uIcc_of_le hxy,uIcc_of_le hs.2]
      exact Icc_subset_Icc hx.1 hy.2
    have HACxy:=HAC.mono Hsub
    have HIxy:=HI.mono_set (show uIcc x y⊆uIcc (0:ℝ) 1 by
      rw [uIcc_of_le hxy,uIcc_of_le zero_le_one]
      exact Icc_subset_Icc (hs.1.trans hx.1) hy.2)
    have Hmono:(fun v=>(M v)⁻¹)≤ᵐ[volume.restrict (Icc x y)] deriv q:=by
      change ∀ᵐv∂volume.restrict (Icc x y),(M v)⁻¹ ≤ deriv q v
      rw [ae_restrict_iff' measurableSet_Icc]
      filter_upwards [Hder] with v hv hvxy
      exact (hv ⟨hx.1.trans hvxy.1,hvxy.2.trans hy.2⟩).1
    have H:=intervalIntegral.integral_mono_ae_restrict hxy HIxy HACxy.intervalIntegrable_deriv Hmono
    rw [HACxy.integral_deriv_eq_sub] at H
    have HI0x:=HI.mono_set (show uIcc (0:ℝ) x⊆uIcc (0:ℝ) 1 by
      rw [uIcc_of_le (hs.1.trans hx.1),uIcc_of_le zero_le_one]
      exact Icc_subset_Icc le_rfl hx.2)
    have Hsum:=intervalIntegral.integral_add_adjacent_intervals HI0x HIxy
    dsimp only [inverseCapPrimitive]
    linarith
  have HL:=Hgap ⟨le_rfl,hs.2⟩ hu hu.1
  have HU:=Hgap hu ⟨hs.2,le_rfl⟩ hu.2
  have Hleft:q s=r0:=omittedSweepQuantile_left hr1 hs hc hk hkc hm
    (hMp 1 ⟨zero_le_one,le_rfl⟩).le alpha
  have Hone:q 1=1:=omittedSweepQuantile_one hr1 hs hc hk hkc hm
    (hMp 1 ⟨zero_le_one,le_rfl⟩).le alpha
  unfold downwardBarrierEnvelope
  constructor <;> linarith

theorem actual_shifted_omitted_quantile_low_origin {c s r0 : ℝ} {k M : ℝ→ℝ}
    (_hr0 : 0 ≤ r0) (hr1 : r0 ≤ 1) (hs : s∈Icc (0:ℝ) 1) (hc : 0 < c) (hk : ContinuousOn k (Icc r0 1))
    (hkc : ∀r∈Icc r0 1,c  ≤  k r) (hm : MonotoneOn M (Icc (0:ℝ) 1))
    (hM : 0 ≤ M 1) (alpha : inverseIntegralConstraints r0 s k M) {u : ℝ} (hu : u ≤ s) :
    omittedSweepQuantile hr1 hs hc hk hkc hm hM alpha u=r0 := by
  have H:=omittedSweepQuantile_monotone hr1 hs hc hk hkc hm hM alpha hu
  rw [omittedSweepQuantile_left hr1 hs hc hk hkc hm hM alpha] at H
  exact le_antisymm H (omittedSweepQuantile_bounds hr1 hs hc hk hkc hm hM alpha u).1

theorem actual_shifted_omitted_trial_quantile_eq {c s r0 : ℝ} {k M : ℝ→ℝ}
    (_hr0 : 0 ≤ r0) (hr1 : r0 ≤ 1) (hs : s∈Icc (0:ℝ) 1) (hc : 0 < c) (hk : ContinuousOn k (Icc r0 1))
    (hkc : ∀r∈Icc r0 1,c  ≤  k r) (hm : MonotoneOn M (Icc (0:ℝ) 1))
    (hM : 0 ≤ M 1) (gamma : inverseIntegralConstraints r0 s k M) (Rhat : ℝ→ℝ)
    (hb : ∀u∈Icc s 1,Rhat u∈Icc r0 1)
    (hgraph : ∀u∈Icc s 1,gamma.val.val (Rhat u)=u) {u : ℝ} (hu : u∈Icc s 1) :
    omittedSweepQuantile hr1 hs hc hk hkc hm hM gamma u=Rhat u := by
  calc
    _ = omittedSweepQuantile hr1 hs hc hk hkc hm hM gamma (gamma.val.val (Rhat u)):=by rw [hgraph u hu]
    _ = _:=omittedSweepQuantile_inverse hr1 hs hc hk hkc hm hM gamma (hb u hu)

end OAI.SKFluctuations.LaplaceWindowFormalization
