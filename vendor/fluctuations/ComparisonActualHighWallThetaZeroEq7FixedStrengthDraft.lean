module

public import ComparisonActualHighWallThetaZeroSelectedRadius
public import ComparisonCanonicalPhysicalStrength

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter Hierarchy
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 12000000

namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
variable (Q : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)

theorem eq7_fixed_strength_at_mass_draft
    (hcl : 0 < cl) (hAz : 0 ≤ Az)
    (hN : 1 ≤ Q.data.N) (hdelta : 0 ≤ delta)
    (hcarrier : Q.xs =
      comparisonConditionalScale Q.data.N delta Q.data.E Q.lam)
    {u Cmass : ℝ} (hu : u ∈ Icc (0:ℝ) 1)
    (hCmass : 0 ≤ Cmass) (huA : u ≤ Cmass*Q.xs) :
    let K := max 1 ((Az+1/cl)*(1+Cmass))
    Q.data.N*(Q.data.N^(-delta)*Q.lam) ≤
      K*(Q.data.N*laplaceComparisonStrength Q.data.d Q.lam
        (Q.shiftedNativeModel.R u)) := by
  let K := max 1 ((Az+1/cl)*(1+Cmass))
  have hK : 1 ≤ K := le_max_left _ _
  have hcoeff : 0 ≤ Az+1/cl := by positivity
  have huplus : Q.xs+u ≤ (1+Cmass)*Q.xs := by
    nlinarith only [huA]
  have Hradius := Q.inverse_radius_le_source_mass hcl hAz hu
  have Hplus := mul_le_mul_of_nonneg_left huplus hcoeff
  have hKfactor : (Az+1/cl)*(1+Cmass) ≤ K := le_max_right _ _
  have Hmax := mul_le_mul_of_nonneg_right hKfactor Q.hxs.le
  have hrA : Q.shiftedNativeModel.R u ≤ K*
      comparisonConditionalScale Q.data.N delta Q.data.E Q.lam := by
    rw [←hcarrier]
    rw [Q.shiftedNativeModel_radius]
    nlinarith only [Hradius,Hplus,Hmax]
  have hRlo : Q.data.rmin ≤ Q.shiftedNativeModel.R u :=
    (omittedSweepQuantile_bounds Q.data.hr
      ⟨Q.data.hs.1.le,Q.data.hs1⟩ Q.data.hc Q.data.hk
      Q.data.hkc Q.data.hm Q.data.hM Q.alpha u).1
  have hR : 0 < Q.shiftedNativeModel.R u :=
    Q.data.hrbounds.1.trans_le hRlo
  exact comparison_canonical_inner_strength hN hdelta Q.data.hE
    Q.data.hd Q.hlam Q.hld Q.hupper hK hR hrA

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
