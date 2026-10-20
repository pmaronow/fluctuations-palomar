module

public import ComparisonNativeActualHighFlatOffFloorWeightedMass
public import ComparisonNativeActualWeightedCapTravelAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 18000000
namespace NativeOverlapMinimum

theorem actual_high_strength_off_floor_weighted_mass_saving_along
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (hdelta : 0 < delta) (hcl : 0 < cl) (hAz : 0 ≤ Az)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hlarge : Tendsto (fun n=>laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs/(M n).xs^2)
      atTop atTop)
    (C : ℝ) (hC : 0 ≤ C) :
    ∃eta : ℕ→ℝ,(∀n,0 ≤ eta n) ∧ Tendsto eta atTop (𝓝 0) ∧
      ∀ᶠn in atTop,∃p : (M n).Potential,∀v∈Icc (0:ℝ) 1,v ≤ C*(M n).xs →
        (∫u in 0..v,p.offFloorWeightedDiscrepancy u)/(M n).xs^4 ≤ eta n := by
  let eta n:=C*actualWeightedCapTravelRate delta dim n
  have heta n:0 ≤ eta n:=mul_nonneg hC (actual_weighted_cap_travel_rate_nonneg delta dim n)
  have HEta:Tendsto eta atTop (𝓝 0):=by
    simpa only [mul_zero] using (actual_weighted_cap_travel_rate_tendsto_zero_along hdelta dim hdim).const_mul C
  refine ⟨eta,heta,HEta,?_⟩
  filter_upwards [actual_high_strength_flat_weighted_point_along hdelta hcl hAz dim hdim M hlarge C hC,
    eventually_actual_cap_log_loss_le_along dim hdim M] with n hn hlog
  obtain ⟨p,hp⟩:=hn
  refine ⟨p,?_⟩
  intro v hv hvC
  have Hpoint:∀ᵐu,u∈Icc (0:ℝ) v → p.H ((M n).R u) ≤ 0 →
      |laplaceComparisonStrength (M n).context.d (M n).lam ((M n).R u)*
        (orderedPathS (dim n+1) (M n).bf (M n).hf u-(M n).R u)|/(M n).xs^3 ≤
        actualWeightedCapTravelRate delta dim n:=by
    filter_upwards [hp] with u hu hui hnonpos
    exact (hu ⟨hui.1,hui.2.trans hv.2⟩ (hui.2.trans hvC) hnonpos).trans hlog
  have H:=p.offFloorWeightedDiscrepancy_mass_le hv (actual_weighted_cap_travel_rate_nonneg delta dim n) Hpoint
  have HS:=mul_le_mul_of_nonneg_left hvC
    (mul_nonneg (actual_weighted_cap_travel_rate_nonneg delta dim n) (pow_pos (M n).hxs 3).le)
  apply (div_le_iff₀ (pow_pos (M n).hxs 4)).2
  apply H.trans
  convert HS using 1
  dsimp only [eta]
  ring

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
