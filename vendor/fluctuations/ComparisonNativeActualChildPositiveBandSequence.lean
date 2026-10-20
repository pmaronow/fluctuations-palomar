module

public import ComparisonNativeActualChildPositiveBandClocks

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 15000000
namespace NativeOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock c0 : ℝ}

theorem actual_child_positive_band_increments_vanish
    (hdelta : 0 < delta) (hcl : 0 < cl) (hAz : 0 ≤ Az) (hC0 : 0 < C0)
    (hc0 : 0 < c0) (hc01 : c0 ≤ 1) (hmargin : 0 < 9*m-298*delta)
    (N : ℕ→ℕ) (hN : Tendsto N atTop atTop)
    (P : (n:ℕ)→NativeOverlapMinimum (N n+1) m delta cl cu Az C0 Ct D Bclock)
    (x : ℕ→ℝ) (hx : ∀n,0 < x n) (hxlim : Tendsto x atTop (𝓝 0))
    (htarget : ∀ᶠn in atTop,
      comparisonConditionalScale (P n).context.N delta (P n).context.E (P n).lam ≤ x n)
    (hcap : ∀ᶠn in atTop,(P n).z ≤ Az*x n)
    (hweak : Tendsto (fun n=>laplaceComparisonStrength (P n).context.d (P n).lam (x n)/(x n)^2)
      atTop (𝓝 0)) :
    ∀Cmass epsilon : ℝ,0 ≤ Cmass → 0 < epsilon → ∀ᶠn in atTop,
      ∀y : ℝ,actualChildCutoff (N n+1) delta c0 (P n).context.d (P n).lam (x n) ≤ y →
      ∀u∈Icc (0:ℝ) (min (Cmass*y) 1),
        laplaceComparisonStrength (P n).context.d (P n).lam ((P n).R u) ≤ epsilon*y^2 ∧
        laplaceComparisonStrength (P n).context.d (P n).lam ((P n).R u)*(P n).R u ≤ epsilon*y^3 := by
  intro Cmass epsilon hCmass heps
  let C:=max 1 (Az+Cmass/cl)
  let eta:=min 1 (epsilon/(C+1))
  have hC : 1 ≤ C:=le_max_left _ _
  have hC0' : 0 ≤ C:=zero_le_one.trans hC
  have heta : 0 < eta:=lt_min zero_lt_one (div_pos heps (by positivity))
  have heta1 : eta ≤ 1:=min_le_left _ _
  have Het : eta*(C+1) ≤ epsilon:=
    (le_div_iff₀ (by positivity : 0 < C+1)).mp (min_le_right _ _)
  have Het2 : eta^2 ≤ eta := by nlinarith
  have hsave : eta^2 ≤ epsilon ∧ C*eta^2 ≤ epsilon := by
    have H:=mul_le_mul_of_nonneg_left Het2 hC0'
    constructor <;> nlinarith only [Het,Het2,H,heta.le,hC,mul_nonneg heta.le hC0']
  have Hweak:=hweak.eventually (gt_mem_nhds (pow_pos (mul_pos heta hc0) 3))
  have Hunit:=hxlim.eventually (gt_mem_nhds zero_lt_one)
  filter_upwards [hN.eventually (eventually_actual_child_positive_band_increments (cu:=cu) (Ct:=Ct)
    (D:=D) (Bclock:=Bclock) hdelta hcl hAz hC0 hc0 hc01 heta heta1 hCmass hmargin),
    Hweak,Hunit,htarget,hcap] with n hn hnweak hnunit hntarget hncap
  intro y hay u hu
  have Hweak' : laplaceComparisonStrength (P n).context.d (P n).lam (x n) ≤ (eta*c0)^3*(x n)^2 :=
    (div_le_iff₀ (sq_pos_of_pos (hx n))).mp hnweak.le
  have H:=hn (P n) (x n) ⟨hx n,hnunit.le⟩ hntarget Hweak' hncap y hay u hu
  have hy : 0 < y:=
    (actual_child_cutoff_pos_le_radius (P n).context.hN hc0 (P n).hlam (hx n)).1.trans_le hay
  exact ⟨H.1.trans (mul_le_mul_of_nonneg_right hsave.1 (sq_nonneg y)),
    H.2.trans (mul_le_mul_of_nonneg_right hsave.2 (pow_nonneg hy.le 3))⟩

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
