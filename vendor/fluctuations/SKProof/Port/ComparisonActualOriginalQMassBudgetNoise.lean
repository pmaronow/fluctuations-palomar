module

public import ComparisonNativeActualMassBudgetNormalization
public import SKProof.Port.ComparisonActualOriginalQMassBudgetScale

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 24000000
namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
theorem canonical_mass_diameter_nonneg
    (a : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (_hlog : 0 ≤ Real.log a.data.N) : 0 ≤ a.canonicalMassDiameter := by
  unfold canonicalMassDiameter cavityCapTravel
  have Hlog : 0 ≤ Real.log ((1+a.data.U)/a.data.U):=
    Real.log_nonneg ((one_le_div a.data.hU).mpr (by linarith))
  have hL:=a.data.hL.le
  have hN:=a.data.hN.le
  positivity

theorem canonical_mass_cut_error_le
    (a : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hC0 : 0<C0) (hm : 0 < m) (hN : 1 ≤ a.data.N) (hxs1 : a.xs ≤ 1)
    {v Q cut : ℝ} (hv : 0<v) (hv1 : v ≤ 1) (hcut : 0 ≤ cut) :
    18*((((Q^2*a.canonicalMassHeight v)^2*a.canonicalMassPower v*(16*v)^2)^((1:ℝ)/3))+2)*cut/a.xs^3 ≤
      (18*(3+1024*Q^4*D^2)*C0^3)*a.data.N^4*cut := by
  have hx:=a.hxs
  have hP:=(a.canonical_mass_power_pos v).le
  have Hy0 : 0 ≤ a.canonicalMassHeight v:=by unfold canonicalMassHeight;positivity
  have Hy : a.canonicalMassHeight v ≤ 2 := by
    unfold canonicalMassHeight
    have H:=min_le_right (16*v) (1:ℝ)
    linarith
  have HB : (16*v)^2 ≤ (16:ℝ)^2:=pow_le_pow_left₀ (by positivity) (by linarith) 2
  have HY : (Q^2*a.canonicalMassHeight v)^2 ≤ (2*Q^2)^2:=
    pow_le_pow_left₀ (by positivity) (by nlinarith [mul_nonneg (sq_nonneg Q) (sub_nonneg.mpr Hy)]) 2
  have HP:=a.canonical_mass_power_le v
  have Hinside : (Q^2*a.canonicalMassHeight v)^2*a.canonicalMassPower v*(16*v)^2 ≤
      (1+1024*Q^4*D^2)*a.data.N := by
    have H1:=mul_le_mul HY HP (a.canonical_mass_power_pos v).le (sq_nonneg _)
    have H2:=mul_le_mul H1 HB (sq_nonneg _) (by positivity : 0 ≤ (2*Q^2)^2*(a.data.N*D^2))
    nlinarith [H2,a.data.hN]
  have Hroot:=mass_root_third_le_linear (by positivity)
    (show 1 ≤ 1+1024*Q^4*D^2 by nlinarith [show 0 ≤ 1024*Q^4*D^2 by positivity]) hN Hinside
  have Hcoeff :
      18*((((Q^2*a.canonicalMassHeight v)^2*a.canonicalMassPower v*(16*v)^2)^((1:ℝ)/3))+2) ≤
      18*(3+1024*Q^4*D^2)*a.data.N := by nlinarith
  have Hinv:=a.canonical_mass_inverse_cube_le hC0 hm hN
  have Hmul:=mul_le_mul Hcoeff Hinv (by positivity : 0 ≤ 1/a.xs^3)
    (by positivity : 0 ≤ 18*(3+1024*Q^4*D^2)*a.data.N)
  have Hcut:=mul_le_mul_of_nonneg_right Hmul hcut
  convert Hcut using 1 <;> ring

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
