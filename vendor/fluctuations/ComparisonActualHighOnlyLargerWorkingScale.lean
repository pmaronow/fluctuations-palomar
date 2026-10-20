module

public import ComparisonActualHighOnlyScalarUtilities
public import ComparisonActualHighOnlyInitialCharges

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 12000000
namespace ActualHighOnlyOverlapMinimum.HighOnlyActualComparableBandContext
variable {m delta cl cu Az C0 Ct D Bclock T : ℝ} {dim : ℕ→ℕ}
  {M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}

theorem omission_over_larger_scale_zero (G : HighOnlyActualComparableBandContext M T)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs≤W n) :
    Tendsto (fun n=>(M n).data.s/W n) atTop (𝓝 0) := by
  apply squeeze_zero (fun n=>div_nonneg (M n).data.hs.1 ((M n).hxs.trans_le (hxs n)).le)
    (fun n=>div_le_div_of_nonneg_left (M n).data.hs.1 (M n).hxs (hxs n)) G.omission_over_test_zero

theorem floor_and_omission_over_larger_scale_zero (G : HighOnlyActualComparableBandContext M T)
    (hC0 : 0<C0) (hroom : 0<3*m+delta)
    (hdim : Tendsto dim atTop atTop) (W : ℕ→ℝ) (hxs : ∀n,(M n).xs≤W n) :
    Tendsto (fun n=>((M n).data.s+(M n).context.N^(-delta)*(M n).context.U)/W n)
      atTop (𝓝 0) := by
  simpa only [add_div,zero_add] using (G.omission_over_larger_scale_zero W hxs).add
    (actual_floor_mass_ratio_tendsto_zero_along hC0 hroom dim hdim M W hxs)

theorem eventually_floor_and_omission_small (G : HighOnlyActualComparableBandContext M T)
    (hC0 : 0<C0) (hroom : 0<3*m+delta)
    (hdim : Tendsto dim atTop atTop) (W : ℕ→ℝ) (hxs : ∀n,(M n).xs≤W n)
    {epsilon : ℝ} (hepsilon : 0<epsilon) :
    ∀ᶠn in atTop,(M n).data.s+(M n).context.N^(-delta)*(M n).context.U≤epsilon*W n := by
  filter_upwards [(G.floor_and_omission_over_larger_scale_zero hC0 hroom hdim W hxs).eventually
    (eventually_le_nhds hepsilon)] with n hn
  exact (div_le_iff₀ ((M n).hxs.trans_le (hxs n))).mp hn

theorem positive_larger_bands_high (G : HighOnlyActualComparableBandContext M T)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs≤W n) {c : ℝ} (hc : 0<c) :
    ∀ᶠn in atTop,(M n).data.s≤c*W n := by
  filter_upwards [G.positive_bands_high c hc] with n hn
  exact hn.trans (mul_le_mul_of_nonneg_left (hxs n) hc.le)

end ActualHighOnlyOverlapMinimum.HighOnlyActualComparableBandContext
end OAI.SKFluctuations.LaplaceWindowFormalization
