module

public import SKProof.Port.OriginalQHighOnlyBridge
public import ComparisonActualHighWallThetaZeroContactTrace
public import ComparisonActualHighWallThetaZeroCapTravelCore
public import ComparisonContactDerivative
public import ComparisonCapIntervals

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 12000000

namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

end ActualThetaZeroOverlapMinimum

theorem eventually_actual_contact_derivative_original_q
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (hm : 0 < m) (hC0 : 0 < C0) :
    ∀ᶠ n : ℕ in atTop,
      ∀ a : ActualThetaZeroOverlapMinimum n m delta cl cu Az C0 Ct D Bclock,
      ∀ P : a.Potential,∀ᵐ r,r∈Icc a.data.rmin 1→P.H r=0→
        deriv (fun t => orderedPathS n a.sweepBf a.sweepHf (a.alpha.val.val t)) r≤9*Real.log a.data.N := by
  have hlog : ∀ᶠ n : ℕ in atTop,1≤Real.log (n:ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  filter_upwards [eventually_comparisonLowerScale_depth hC0 hm,hlog,
    eventually_ge_atTop (1:ℕ)] with n hdepth hnlog hn1
  obtain ⟨k, rfl⟩ : ∃ k, n = k+1 := ⟨n-1, by omega⟩
  intro a P
  have hs : comparisonLowerScale a.data.N a.data.E a.data.d≤a.data.d := by
    unfold comparisonLowerScale
    exact (div_le_iff₀ a.data.hd).mpr (by simpa only [pow_two] using a.hupper)
  exact P.contact_ae_deriv_le (by exact_mod_cast hn1) hnlog
    ((hdepth a.data.E a.data.d a.data.hE a.data.hd a.hlower).trans hs)

theorem eventually_actual_cap_travel_small_original_q
    {m delta cl cu Az C0 Ct D Bclock epsilon : ℝ}
    (hC0 : 0 < C0) (hroom : 0 < 3*m+delta) (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop,
      ∀ a : ActualThetaZeroOverlapMinimum n m delta cl cu Az C0 Ct D Bclock,
        a.cavityCapTravel≤epsilon*a.xs ∧
        ∀ (P : a.Potential) (l r : ℝ), a.data.rmin ≤ l → l ≤ r → r ≤ 1 →
          (∀ t ∈ Ioo l r, P.H t < 0) → r-l ≤ epsilon*a.xs := by
  filter_upwards [eventually_comparisonTravel_small (C:=C0) (D:=D)
    hC0 hroom hepsilon] with n hn
  intro a
  have hc : a.cavityCapTravel≤epsilon*a.xs := by
    exact (hn a.data.E a.data.d a.data.hE a.data.hd a.hdD a.hupper a.hlower).trans
      (mul_le_mul_of_nonneg_left a.hscale hepsilon.le)
  refine ⟨hc,?_⟩
  intro P l r hl hlr hr hnegative
  exact (P.cap_interval_travel a hl hlr hr hnegative).2.1.trans hc

end OAI.SKFluctuations.LaplaceWindowFormalization
