module

public import ComparisonNativeActualMassBandScale
public import ComparisonNativeActualBroadMassNormalization
public import ComparisonNativeActualMinimumLocalDiameterBudgets

@[expose] public section

noncomputable section
set_option maxHeartbeats 9000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators

def actualHighMassHeightConstant (c : ℝ) : ℝ := 1/c+16
def actualHighMassEndpointConstant (Az cl c : ℝ) : ℝ :=
  max (1/c) ((Az+1/cl)*actualHighMassHeightConstant c)
def actualHighMassStrengthConstant (Az cl Ct c : ℝ) : ℝ :=
  (Ct+1)*actualHighMassEndpointConstant Az cl c

theorem mass_strength_linear_test_scale {d lam x v z c C : ℝ}
    (hd : 0 < d) (hlam : 0 < lam) (hx : 0 < x) (hx1 : x ≤ 1)
    (hz : 0 ≤ z) (hz1 : z ≤ 1) (hc : 0 < c) (hvlo : c*x ≤ v)
    (hC : 1/c ≤ C) (hzv : z ≤ C*v) :
    laplaceComparisonStrength d lam x*x ≤ C*laplaceComparisonStrength d lam z*v := by
  have hmono:=laplaceComparisonStrength_monotonicities hd.ne' hlam (r₀:=0) le_rfl
  have hg:=(laplaceComparisonStrength_pos d hlam z).le
  have hv : 0 < v:= (mul_pos hc hx).trans_le hvlo
  have hcv : x ≤ (1/c)*v:=by
    have H : x ≤ v/c := (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hvlo)
    simpa only [one_div,mul_comm,div_eq_mul_inv,one_mul,mul_one] using H
  by_cases hzx : z ≤ x
  · have HG:=hmono.1 ⟨hz,hz1⟩ ⟨hx.le,hx1⟩ hzx
    have HX:=hcv.trans (mul_le_mul_of_nonneg_right hC hv.le)
    have H:=mul_le_mul HG HX hx.le hg
    convert H using 1; ring
  · have H:=hmono.2 ⟨hx.le,hx1⟩ ⟨hz,hz1⟩ (le_of_not_ge hzx)
    have HH:=mul_le_mul_of_nonneg_left hzv hg
    convert H.trans HH using 1; ring

namespace NativeOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem canonical_high_mass_height_le
    (a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {v c : ℝ} (hc : 0 < c) (hvlo : c*a.xs ≤ v) :
    a.canonicalMassHeight v ≤ actualHighMassHeightConstant c*v := by
  have HX : a.xs ≤ v/c:= (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hvlo)
  unfold canonicalMassHeight actualHighMassHeightConstant
  have HU:=min_le_left (16*v) 1
  calc
    _ ≤ v/c+16*v := add_le_add HX HU
    _ = _ := by ring

theorem canonical_high_mass_power_size
    (a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hcl : 0 < cl) (hAz : 0 ≤ Az) (hCt : 0 ≤ Ct) (hxs1 : a.xs ≤ 1)
    {v c : ℝ} (hc : 0 < c) (hvlo : c*a.xs ≤ v) :
    1/a.context.U^2 ≤ actualHighMassStrengthConstant Az cl Ct c*a.canonicalMassPower v*a.xs*v := by
  have hv : 0 < v:=(mul_pos hc a.hxs).trans_le hvlo
  let u:=min (16*v) 1
  have hu : u∈Icc (0:ℝ) 1:=⟨le_min (by positivity) zero_le_one,min_le_right _ _⟩
  have hR:=comparisonSweepQuantile_bounds a.context.hc a.context.hk a.context.hkc
    a.context.hm a.context.hM a.alpha u
  have hCf : 0 ≤ Az+1/cl:=by positivity
  have HR:=a.inverse_radius_le_source_mass hcl hAz hu
  have HZ : a.R u ≤ actualHighMassEndpointConstant Az cl c*v := by
    calc
      _ ≤ (Az+1/cl)*(a.xs+u) := HR
      _ ≤ (Az+1/cl)*(actualHighMassHeightConstant c*v) :=
        mul_le_mul_of_nonneg_left (a.canonical_high_mass_height_le hc hvlo) hCf
      _ ≤ actualHighMassEndpointConstant Az cl c*v := by
        rw [←mul_assoc]
        exact mul_le_mul_of_nonneg_right (le_max_right _ _) hv.le
  have HS:=mass_strength_linear_test_scale a.context.hd a.hlam a.hxs hxs1 hR.1 hR.2
    hc hvlo (le_max_left _ _) HZ
  have HK : 0 ≤ actualHighMassEndpointConstant Az cl c:=by
    exact (one_div_pos.mpr hc).le.trans (le_max_left _ _)
  have HgR : 0 ≤ laplaceComparisonStrength a.context.d a.lam (a.R u):=
    (laplaceComparisonStrength_pos _ a.hlam _).le
  have Hg : 0 ≤ actualHighMassEndpointConstant Az cl c*
      laplaceComparisonStrength a.context.d a.lam (a.R u)*a.xs*v:=
    mul_nonneg (mul_nonneg (mul_nonneg HK HgR) a.hxs.le) hv.le
  have HT : a.context.N*a.context.E^2 ≤ actualHighMassStrengthConstant Az cl Ct c*
      laplaceComparisonStrength a.context.d a.lam (a.R u)*a.xs*v := by
    have H:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left HS hCt) a.hxs.le
    have H' : Ct*laplaceComparisonStrength a.context.d a.lam a.xs*a.xs^2 ≤
        Ct*actualHighMassEndpointConstant Az cl c*
          laplaceComparisonStrength a.context.d a.lam (a.R u)*a.xs*v := by
      unfold actualHighMassEndpointConstant
      convert H using 1 <;> ring
    apply a.htest.trans H' |>.trans
    unfold actualHighMassStrengthConstant
    nlinarith only [Hg]
  calc
    1/a.context.U^2 = a.context.N*(a.context.N*a.context.E^2) := by
      unfold NativeOverlapContext.U comparisonSmallMass
      field_simp
    _ ≤ a.context.N*(actualHighMassStrengthConstant Az cl Ct c*
      laplaceComparisonStrength a.context.d a.lam (a.R u)*a.xs*v) :=
      mul_le_mul_of_nonneg_left HT a.context.hN.le
    _ = _ := by unfold canonicalMassPower;dsimp only [u];ring

end NativeOverlapMinimum

theorem mass_high_normalized_noise_le {P x U v K : ℝ}
    (hP : 0 < P) (hx : 0 < x) (hU : 0 < U) (hv : 0 < v)
    (hsize : 1/U^2 ≤ K*P*x*v) :
    1/(P*v^2*x^2) ≤ K*(U/x)^2*(x/v) := by
  have Hsize : 1 ≤ K*P*x*v*U^2:=(div_le_iff₀ (sq_pos_of_pos hU)).mp hsize
  apply (div_le_iff₀ (show 0 < P*v^2*x^2 by positivity)).mpr
  have HE : (K*(U/x)^2*(x/v))*(P*v^2*x^2)=K*P*x*v*U^2:=by field_simp
  rw [HE]
  exact Hsize

theorem mass_high_broad_loss_noise_le {x U v tau K c Cr tlog rlog : ℝ}
    (hx : 0 < x) (hU : 0 < U) (hv : 0 < v) (hK : 0 ≤ K) (hc : 0 < c)
    (hCr : 0 ≤ Cr) (hlog : 1 ≤ tlog) (ht : U/x ≤ 1) (hvlo : c*x ≤ v)
    (hrlog : 0 ≤ rlog) (hr : rlog ≤ Cr*tlog)
    (htau : tau ≤ K*(U/x)^2*(x/v)) :
    (1025+25*(1+v/U)*rlog)*tau ≤
      K*(1025/c+25*(1/c+1)*Cr)*tlog*(U/x) := by
  have ht0 : 0 ≤ U/x:=by positivity
  have hvx : x/v ≤ 1/c:=by
    apply (div_le_div_iff₀ hv hc).mpr
    simpa only [one_mul,mul_one,mul_comm] using hvlo
  have ht2 : (U/x)^2 ≤ U/x:=by nlinarith
  have Hbase : (U/x)^2*(x/v) ≤ (1/c)*(U/x):=by
    have H:=mul_le_mul ht2 hvx (div_nonneg hx.le hv.le) ht0
    nlinarith [H]
  have HE : (1+v/U)*(U/x)^2*(x/v)=(U/x)^2*(x/v)+U/x:=by field_simp
  have Hfactor : (1+v/U)*(U/x)^2*(x/v) ≤ (1/c+1)*(U/x):=by rw [HE];linarith
  have Hnoise:=mul_le_mul_of_nonneg_left htau
    (show 0 ≤ 1025+25*(1+v/U)*rlog by positivity)
  have Hrnoise:=mul_le_mul_of_nonneg_left hr
    (show 0 ≤ 25*K*((1+v/U)*(U/x)^2*(x/v)) by positivity)
  have Hfnoise:=mul_le_mul_of_nonneg_left Hfactor (show 0 ≤ 25*K*(Cr*tlog) by positivity)
  have Hbaselog:=mul_le_mul_of_nonneg_left
    (Hbase.trans (le_mul_of_one_le_left (show 0 ≤ (1/c)*(U/x) by positivity) hlog))
    (show 0 ≤ 1025*K by positivity)
  have HEout : K*(1025/c+25*(1/c+1)*Cr)*tlog*(U/x)=
      1025*K*(tlog*((1/c)*(U/x)))+25*K*(Cr*tlog)*((1/c+1)*(U/x)):=by ring
  rw [HEout]
  nlinarith only [Hnoise,Hrnoise,Hfnoise,Hbaselog]

end OAI.SKFluctuations.LaplaceWindowFormalization
