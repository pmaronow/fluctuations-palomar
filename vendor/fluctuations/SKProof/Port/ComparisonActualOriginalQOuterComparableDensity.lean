module

public import SKProof.Port.ComparisonActualOriginalQOuterCapDiameter
public import SKProof.Port.ComparisonActualOriginalQCapTraceNormalized
public import ComparisonNativeOuterComparableTrace

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 8000000
namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable {a : ActualThetaZeroOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}

theorem inverse_slice_mass {l z : ℝ} (hl : a.data.rmin ≤ l) (hlz : l ≤ z) (hz : z ≤ 1) :
    (∫r in Ioo l z,deriv a.alpha.val.val r)=a.alpha.val.val z-a.alpha.val.val l := by
  have hac : AbsolutelyContinuousOnInterval a.alpha.val.val l z := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval
    simpa only [uIcc_of_le hlz] using
      (inverseIntegralConstraints_lipschitz a.data.hm a.data.hM a.alpha.property).mono
        (Icc_subset_Icc hl hz)
  rw [←integral_Ioc_eq_integral_Ioo,←intervalIntegral.integral_of_le hlz,hac.integral_deriv_eq_sub]

namespace ShiftedCapInterval
variable {P : a.Potential} (c : ShiftedCapInterval a P)

theorem outer_slice_density_length_le
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (htravel : a.cavityCapTravel ≤ a.xs)
    (houter : 2*cu*(Az+1)*a.xs ≤ a.alpha.val.val c.right)
    {l z v ceiling : ℝ} (hl : c.left ≤ l) (hlz : l < z) (hz : z ≤ c.right)
    (hv : 0 < v) (hwidth : v ≤ ∫r in Ioo l z,deriv a.alpha.val.val r)
    (hceiling : ceiling∈Icc (0:ℝ) 1) (hceilingMass : a.alpha.val.val z ≤ ceiling)
    (hcomparable : ceiling ≤ 4*v) (hUv : a.data.U ≤ v) :
    a.data.M ceiling*(c.right-c.left) ≤
      nativeOuterComparableTraceConstant cl cu*(∫r in Ioo l z,deriv a.alpha.val.val r) := by
  let K:=max 1 (10*cu/cl)
  let kappa:=cl/(2*cu)
  have hK : 1 ≤ K:=le_max_left _ _
  have hk : 0 < kappa:=by dsimp [kappa];positivity
  have HA0 : 0 ≤ a.alpha.val.val c.left:=(a.alpha.val.property.1 _).1
  have Hfloor:=c.outer_mass_floor hcl hcu hAz htravel houter
  change kappa*a.alpha.val.val c.right ≤ a.alpha.val.val c.left at Hfloor
  have Hmass:=a.inverse_slice_mass (c.hleft.trans hl) hlz.le (hz.trans c.hright)
  have Hscale : v ≤ a.alpha.val.val c.right := by
    rw [Hmass] at hwidth
    have H0:=(a.alpha.val.property.1 l).1
    have Hmono:=a.alpha.val.property.2 hz
    linarith
  have HA : kappa*v ≤ a.alpha.val.val c.left:=
    (mul_le_mul_of_nonneg_left Hscale hk.le).trans Hfloor
  have HAhi : a.alpha.val.val c.left ≤ 4*v:=
    ((a.alpha.val.property.2 hl).trans (a.alpha.val.property.2 hlz.le)).trans
      (hceilingMass.trans hcomparable)
  have HZ : a.alpha.val.val c.right ≤ (8*cu/cl)*v:=by
    have H:=Hfloor.trans HAhi
    have HH : a.alpha.val.val c.right ≤ (4*v)/kappa:=
      (le_div_iff₀ hk).mpr (by simpa only [mul_comm] using H)
    convert HH using 1
    dsimp [kappa]
    field_simp; ring
  have HKk : (5:ℝ) ≤ K*kappa:=by
    have H:=mul_le_mul_of_nonneg_right (le_max_right (1:ℝ) (10*cu/cl)) hk.le
    have HE : (10*cu/cl)*kappa=5:=by dsimp [kappa];field_simp; ring
    rw [HE] at H
    exact H
  have Hband : ceiling+a.data.U ≤ K*(a.alpha.val.val c.left+a.data.U):=by
    have H1:=mul_le_mul_of_nonneg_left HA (zero_le_one.trans hK)
    have H2:=mul_le_mul_of_nonneg_right HKk hv.le
    have H3 : 0 ≤ K*a.data.U:=mul_nonneg (zero_le_one.trans hK) a.data.hU.le
    nlinarith
  have HR:=comparisonCap_common_mass_band_ratio (δ:=delta)
    a.data.hN a.data.hU a.data.hL a.data.hE a.data.hd.le HA0 hK Hband
    (u:=a.alpha.val.val c.left) (v:=ceiling) le_rfl le_rfl hceiling.1
  have HMa : 0 < a.data.M (a.alpha.val.val c.left):=
    (comparisonCap_first_term (δ:=delta) a.data.hN a.data.hU a.data.hL a.data.hE a.data.hd.le HA0).1
  have HR' : a.data.M ceiling ≤ K^2*a.data.M (a.alpha.val.val c.left):=by
    change a.data.M ceiling/a.data.M (a.alpha.val.val c.left) ≤ K^2 at HR
    simpa only [mul_comm] using (div_le_iff₀ HMa).mp HR
  have H1:=mul_le_mul_of_nonneg_right HR' (sub_nonneg.mpr c.hlt.le)
  have H2:=mul_le_mul_of_nonneg_left c.mass_lower (sq_nonneg K)
  have H3:=mul_le_mul_of_nonneg_left (HZ.trans
    (mul_le_mul_of_nonneg_left hwidth (by positivity : 0 ≤ 8*cu/cl))) (sq_nonneg K)
  unfold nativeOuterComparableTraceConstant
  dsimp only [K] at *
  nlinarith only [H1,H2,H3,HA0]

end ShiftedCapInterval
end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
