module

public import ComparisonActualHighWallThetaZeroStrongScaleGeometry
public import ComparisonNativeActualHighMassCriticalRates

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
  (Q : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)

theorem original_critical_energy_ratio (hC0 : 0 < C0) :
    Q.data.d^3/(Q.data.N^2*Q.data.E^3) ≤ C0^3*Q.data.N^(-3*m) := by
  have Hcube:=pow_le_pow_left₀
    (show 0 ≤ Q.data.N^(-(2:ℝ)/3+m)*Q.data.d by positivity [Q.data.hd]) Q.hlower 3
  have HE : (Q.data.N^(-(2:ℝ)/3+m)*Q.data.d)^3=
      Q.data.N^(-2+3*m)*Q.data.d^3:=by
    rw [mul_pow,←Real.rpow_mul_natCast Q.data.hN.le]
    congr 1
    congr 1
    ring
  rw [HE,mul_pow] at Hcube
  have H:=mul_le_mul_of_nonneg_left Hcube
    (show 0 ≤ Q.data.N^(-3*m)/Q.data.E^3 by positivity [Q.data.hE])
  have HEleft : (Q.data.N^(-3*m)/Q.data.E^3)*
      (Q.data.N^(-2+3*m)*Q.data.d^3)=Q.data.d^3/(Q.data.N^2*Q.data.E^3):=by
    rw [div_mul_eq_mul_div,←mul_assoc,←Real.rpow_add Q.data.hN,
      show -3*m+(-2+3*m)=(-2:ℝ) by ring,Real.rpow_neg Q.data.hN.le,Real.rpow_two]
    field_simp
  rw [HEleft] at H
  convert H using 1
  field_simp [Q.data.hE.ne']

theorem original_cap_length_target_star_bound {Cs : ℝ} (hCs : 0 ≤ Cs)
    (hstrong : Q.xs^2 ≤ Cs*laplaceComparisonStrength Q.data.d Q.lam Q.xs) :
    comparisonConstraintLength Q.data.N Q.data.E Q.data.d*
      Q.directTestWorkingScale/Q.xs^2 ≤ Cs+1 := by
  let a:=comparisonLowerScale Q.data.N Q.data.E Q.data.d
  let L:=comparisonConstraintLength Q.data.N Q.data.E Q.data.d
  have ha : 0 < a:=comparisonLowerScale_pos Q.data.hN Q.data.hE Q.data.hd
  have hax : a ≤ Q.xs:=Q.hscale
  have had : a ≤ Q.data.d:=by
    dsimp only [a,comparisonLowerScale]
    apply (div_le_iff₀ Q.data.hd).mpr
    simpa only [pow_two] using Q.hupper
  have hL : 0 ≤ L:=Q.data.hL.le
  have HL : L ≤ a^3/Q.data.d^2:=by
    dsimp only [L,comparisonConstraintLength,a]
    exact min_le_right _ _
  have HLmul : L*Q.data.d^2 ≤ a^3:=(le_div_iff₀ (sq_pos_of_pos Q.data.hd)).mp HL
  have Hasq:=pow_le_pow_left₀ ha.le hax 2
  have Hcube:=mul_le_mul_of_nonneg_right had (sq_nonneg a)
  have Hsq:=mul_le_mul_of_nonneg_left Hasq Q.data.hd.le
  have HLd : L*Q.data.d ≤ Q.xs^2:=by
    apply (mul_le_mul_iff_right₀ Q.data.hd).mp
    nlinarith only [HLmul,Hcube,Hsq]
  have HW:=((Q.strong_direct_test_working_geometry hCs hstrong).2.1).trans
    (mul_le_mul_of_nonneg_left Q.natural_strength_scale_le_original_taper (by linarith : 0 ≤ Cs+1))
  have H1:=mul_le_mul_of_nonneg_left HW hL
  have H2:=mul_le_mul_of_nonneg_left HLd (by linarith : 0 ≤ Cs+1)
  apply (div_le_iff₀ (sq_pos_of_pos Q.hxs)).mpr
  change L*Q.directTestWorkingScale ≤ (Cs+1)*Q.xs^2
  nlinarith only [H1,H2]

theorem original_cap_travel_target_star_bound {Cs : ℝ} (hCs : 0 ≤ Cs)
    (hstrong : Q.xs^2 ≤ Cs*laplaceComparisonStrength Q.data.d Q.lam Q.xs) :
    Q.cavityCapTravel*Q.directTestWorkingScale/Q.xs^2 ≤
      (Cs+1)*Real.log ((1+comparisonSmallMass Q.data.N Q.data.E)/
        comparisonSmallMass Q.data.N Q.data.E)/Q.data.N^delta := by
  have hU:=Q.data.hU
  have Hlog : 0 ≤ Real.log ((1+comparisonSmallMass Q.data.N Q.data.E)/
      comparisonSmallMass Q.data.N Q.data.E):=
    Real.log_nonneg ((one_le_div hU).mpr (by linarith))
  have H:=mul_le_mul_of_nonneg_left (Q.original_cap_length_target_star_bound hCs hstrong)
    (div_nonneg Hlog (Real.rpow_nonneg Q.data.hN.le delta))
  convert H using 1
  · dsimp only [cavityCapTravel]
    ring
  · ring

theorem original_floor_target_star_bound {Cs : ℝ} (hCs : 0 ≤ Cs)
    (hstrong : Q.xs^2 ≤ Cs*laplaceComparisonStrength Q.data.d Q.lam Q.xs) :
    comparisonSmallMass Q.data.N Q.data.E*Q.directTestWorkingScale/Q.xs^2 ≤
      (Cs+1)*Q.data.d^3/(Q.data.N^2*Q.data.E^3) := by
  let A:=comparisonSmallMass Q.data.N Q.data.E*Q.directTestWorkingScale/Q.xs^2
  let R:=Q.data.d^3/(Q.data.N^2*Q.data.E^3)
  have hA : 0 ≤ A:=by dsimp only [A];positivity [Q.direct_test_working_scale_pos,Q.data.hU]
  have hR : 0 ≤ R:=by dsimp only [R];positivity [Q.data.hd,Q.data.hE]
  have HW:=((Q.strong_direct_test_working_geometry hCs hstrong).2.1).trans
    (mul_le_mul_of_nonneg_left Q.natural_strength_scale_le_original_taper (by linarith : 0 ≤ Cs+1))
  have Hcap:=mass_cap_strong_normalization Q.data.hN Q.data.hE Q.data.hd Q.hxs
    Q.direct_test_working_scale_pos.le (show 0 ≤ Cs+1 by linarith) Q.hscale HW
  have HE : A^2=R*((Q.data.E/Q.data.d^3)*(Q.directTestWorkingScale^2/Q.xs^4)):=by
    dsimp only [A,R,comparisonSmallMass]
    field_simp [Q.data.hN.ne',Q.data.hE.ne',Q.data.hd.ne',Q.hxs.ne'] <;> ring
  have Hcap' : (Q.data.E/Q.data.d^3)*(Q.directTestWorkingScale^2/Q.xs^4) ≤
      (Cs+1)^2*R := by
    simpa only [R,mul_div_assoc] using Hcap
  have H:=mul_le_mul_of_nonneg_left Hcap' hR
  have Hsq : A^2 ≤ ((Cs+1)*R)^2:=by
    calc
      _ = R*((Q.data.E/Q.data.d^3)*(Q.directTestWorkingScale^2/Q.xs^4)) := HE
      _ ≤ R*((Cs+1)^2*R) := H
      _ = _ := by ring
  have hKR : 0 ≤ (Cs+1)*R:=mul_nonneg (by linarith) hR
  have HA : A ≤ (Cs+1)*R:=by nlinarith only [Hsq,hA,hKR]
  dsimp only [A,R] at HA
  convert HA using 1
  ring

theorem original_radius_target_star_bound {Cs : ℝ} (hCs : 0 ≤ Cs)
    (hstrong : Q.xs^2 ≤ Cs*laplaceComparisonStrength Q.data.d Q.lam Q.xs) :
    Q.data.rmin*Q.directTestWorkingScale/Q.xs^2 ≤
      ((Cs+1)*Q.data.d^3/(Q.data.N^2*Q.data.E^3))/(2*Q.data.N^delta) := by
  have Hcap:=concreteWallCap_ge (δ:=delta) Q.data.hN Q.data.hE Q.data.hd Q.data.hs.1.le
  have Hradius : Q.data.rmin ≤ comparisonSmallMass Q.data.N Q.data.E/(2*Q.data.N^delta):=by
    change comparisonSmallMass Q.data.N Q.data.E/(2*Q.data.M Q.data.s) ≤ _
    exact div_le_div_of_nonneg_left Q.data.hU.le
      (by positivity : 0 < 2*Q.data.N^delta)
      (mul_le_mul_of_nonneg_left Hcap (by norm_num : (0:ℝ) ≤ 2))
  have H1:=mul_le_mul_of_nonneg_right Hradius Q.direct_test_working_scale_pos.le
  have H2:=div_le_div_of_nonneg_right H1 (sq_nonneg Q.xs)
  have H3:=div_le_div_of_nonneg_right (Q.original_floor_target_star_bound hCs hstrong)
    (by positivity : 0 ≤ 2*Q.data.N^delta)
  apply H2.trans
  convert H3 using 1
  ring

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
