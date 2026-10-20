module

public import ComparisonNativeActualMinimumMassBudgets
public import ComparisonSignedCavityMinimumSourceClocks
public import ComparisonNativeCavityConcentrationRadiusLimit

@[expose] public section

noncomputable section
set_option maxHeartbeats 7000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators

theorem mass_strength_comparable_endpoint {d lam x z C : ℝ}
    (hd : 0<d) (hlam : 0<lam) (hx : 0<x) (hx1 : x ≤ 1)
    (hz : 0 ≤ z) (hz1 : z ≤ 1) (hC : 1 ≤ C) (hzx : z ≤ C*x) :
    laplaceComparisonStrength d lam x ≤ C*laplaceComparisonStrength d lam z := by
  have hmono:=laplaceComparisonStrength_monotonicities hd.ne' hlam (r₀:=0) le_rfl
  have hg:=(laplaceComparisonStrength_pos d hlam z).le
  by_cases hzx' : z ≤ x
  · exact (hmono.1 ⟨hz,hz1⟩ ⟨hx.le,hx1⟩ hzx').trans (by nlinarith)
  · have H:=hmono.2 ⟨hx.le,hx1⟩ ⟨hz,hz1⟩ (le_of_not_ge hzx')
    have H' : laplaceComparisonStrength d lam x*x ≤ (C*laplaceComparisonStrength d lam z)*x := by
      calc
        _ ≤ laplaceComparisonStrength d lam z*z := H
        _ ≤ laplaceComparisonStrength d lam z*(C*x) := mul_le_mul_of_nonneg_left hzx hg
        _ = _ := by ring
    exact (mul_le_mul_iff_right₀ hx).mp (by simpa only [mul_comm] using H')

def actualMassEndpointConstant (Az cl Cv : ℝ) : ℝ :=
  max 1 ((Az+1/cl)*(1+16*Cv))

def actualMassStrengthConstant (Az cl Ct Cv : ℝ) : ℝ :=
  (Ct+1)*actualMassEndpointConstant Az cl Cv

namespace NativeOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem canonical_mass_height_le
    (a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {v Cv : ℝ} (_hCv : 0 ≤ Cv) (hv : v ≤ Cv*a.xs) :
    a.canonicalMassHeight v ≤ (1+16*Cv)*a.xs := by
  unfold canonicalMassHeight
  have H : min (16*v) 1 ≤ 16*v:=min_le_left _ _
  nlinarith

theorem canonical_mass_power_pos
    (a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (v : ℝ) :
    0 < a.canonicalMassPower v:=
  mul_pos a.context.hN (laplaceComparisonStrength_pos a.context.d a.hlam _)

theorem canonical_mass_power_size
    (a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hcl : 0<cl) (hAz : 0 ≤ Az) (hCt : 0 ≤ Ct) (hxs1 : a.xs ≤ 1)
    {v Cv : ℝ} (hv : 0<v) (_hCv : 0 ≤ Cv) (hvsize : v ≤ Cv*a.xs) :
    1/a.context.U^2 ≤ actualMassStrengthConstant Az cl Ct Cv*a.canonicalMassPower v*a.xs^2 := by
  let u:=min (16*v) 1
  have hu : u∈Icc (0:ℝ) 1:=⟨le_min (by positivity) zero_le_one,min_le_right _ _⟩
  have hR:=comparisonSweepQuantile_bounds a.context.hc a.context.hk a.context.hkc
    a.context.hm a.context.hM a.alpha u
  have hCf : 0 ≤ Az+1/cl:=by positivity
  have HR:=a.inverse_radius_le_source_mass hcl hAz hu
  have Hu : a.xs+u ≤ (1+16*Cv)*a.xs:=by
    have H : u ≤ 16*v:=min_le_left _ _
    nlinarith
  have HZ : a.R u ≤ actualMassEndpointConstant Az cl Cv*a.xs := by
    calc
      _ ≤ (Az+1/cl)*(a.xs+u) := HR
      _ ≤ (Az+1/cl)*((1+16*Cv)*a.xs) := mul_le_mul_of_nonneg_left Hu hCf
      _ ≤ actualMassEndpointConstant Az cl Cv*a.xs := by
        rw [←mul_assoc]
        exact mul_le_mul_of_nonneg_right (le_max_right _ _) a.hxs.le
  have Hstrength:=mass_strength_comparable_endpoint a.context.hd a.hlam a.hxs hxs1
    hR.1 hR.2 (le_max_left _ _) HZ
  have Hg : 0 ≤ laplaceComparisonStrength a.context.d a.lam (a.R u)*a.xs^2:=
    mul_nonneg (laplaceComparisonStrength_pos _ a.hlam _).le (sq_nonneg _)
  have Htest : a.context.N*a.context.E^2 ≤
      actualMassStrengthConstant Az cl Ct Cv*laplaceComparisonStrength a.context.d a.lam (a.R u)*a.xs^2 := by
    change laplaceComparisonStrength a.context.d a.lam a.xs ≤
      actualMassEndpointConstant Az cl Cv*laplaceComparisonStrength a.context.d a.lam (a.R u) at Hstrength
    have H:=mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left Hstrength hCt) (sq_nonneg a.xs)
    have HZ0 : 0 ≤ actualMassEndpointConstant Az cl Cv:=zero_le_one.trans (le_max_left _ _)
    have HH:=mul_nonneg HZ0 Hg
    unfold actualMassStrengthConstant
    nlinarith [a.htest]
  calc
    1/a.context.U^2 = a.context.N*(a.context.N*a.context.E^2) := by
      unfold NativeOverlapContext.U comparisonSmallMass
      field_simp
    _ ≤ a.context.N*(actualMassStrengthConstant Az cl Ct Cv*
      laplaceComparisonStrength a.context.d a.lam (a.R u)*a.xs^2) :=
      mul_le_mul_of_nonneg_left Htest a.context.hN.le
    _ = _ := by unfold canonicalMassPower;dsimp only [u];ring

theorem canonical_mass_small_ratio
    (a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (hC0 : 0<C0) :
    a.context.U/a.xs ≤ C0^3*a.context.N^(-3*m) := by
  have hupper : a.context.E ≤ a.context.d^2/Real.sqrt a.context.N :=
    (le_div_iff₀ (Real.sqrt_pos.mpr a.context.hN)).mpr (by simpa only [mul_comm] using a.hupper)
  have hlower : (1/C0)*a.context.N^(-(2:ℝ)/3+m)*a.context.d ≤ a.context.E := by
    have H : (a.context.N^(-(2:ℝ)/3+m)*a.context.d)/C0 ≤ a.context.E:=
      (div_le_iff₀ hC0).mpr (by simpa only [mul_comm] using a.hlower)
    simpa only [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc,one_mul] using H
  have H:=comparison_radius_small_mass_ratio a.context.hN (one_div_pos.mpr hC0)
    a.context.hd hlower hupper a.hscale
  simpa only [one_div_div,one_pow,div_pow,div_one,NativeOverlapContext.U,NativeOverlapContext.N] using H

theorem canonical_mass_diameter_rate
    (a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hC0 : 0<C0) (hN : 1 ≤ a.context.N) (hlog : 1 ≤ Real.log a.context.N) :
    a.canonicalMassDiameter/a.xs ≤
      (9*C0^3*(1+Real.log (1+D^2)))*(Real.log a.context.N)^2*a.context.N^(-(3*m+delta)) := by
  have Htravel:=comparisonTravel_ratio_bound (δ:=delta) hN a.context.hE a.context.hd a.hdD hC0 a.hupper a.hlower
  have ht0 : 0 ≤ a.cavityCapTravel := by
    unfold cavityCapTravel
    have Hu:=a.context.hU
    have Hlog : 0 ≤ Real.log ((1+a.context.U)/a.context.U):=
      Real.log_nonneg ((one_le_div Hu).mpr (by linarith))
    exact mul_nonneg (div_nonneg a.context.hL.le (Real.rpow_nonneg a.context.hN.le _)) Hlog
  have Hscale : a.cavityCapTravel/a.xs ≤ a.cavityCapTravel/comparisonLowerScale a.context.N a.context.E a.context.d :=
    div_le_div_of_nonneg_left ht0 (comparisonLowerScale_pos a.context.hN a.context.hE a.context.hd) a.hscale
  have Htr : a.cavityCapTravel/a.xs ≤ C0^3*a.context.N^(-(3*m+delta))*
      (Real.log a.context.N+Real.log (1+D^2)) := Hscale.trans Htravel
  have HlogD : 0 ≤ Real.log (1+D^2):=Real.log_nonneg (by nlinarith [sq_nonneg D])
  have Hlogs : Real.log a.context.N+Real.log (1+D^2) ≤
      (1+Real.log (1+D^2))*Real.log a.context.N := by
    nlinarith [mul_nonneg HlogD (sub_nonneg.mpr hlog)]
  have Hmul:=mul_le_mul_of_nonneg_left Htr (show 0 ≤ 9*Real.log a.context.N by linarith)
  have HlogsMul:=mul_le_mul_of_nonneg_left Hlogs
    (show 0 ≤ 9*Real.log a.context.N*(C0^3*a.context.N^(-(3*m+delta))) by positivity)
  unfold canonicalMassDiameter
  have Hmul' : 9*Real.log a.context.N*a.cavityCapTravel/a.xs ≤
      9*Real.log a.context.N*(C0^3*a.context.N^(-(3*m+delta))*
        (Real.log a.context.N+Real.log (1+D^2))) := by
    simpa only [mul_div_assoc] using Hmul
  exact Hmul'.trans (by nlinarith [HlogsMul])

theorem canonical_mass_power_le
    (a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (v : ℝ) :
    a.canonicalMassPower v ≤ a.context.N*D^2 := by
  apply mul_le_mul_of_nonneg_left _ a.context.hN.le
  exact (laplaceComparisonStrength_le a.context.d a.hlam.le _).trans
    (a.hld.trans (pow_le_pow_left₀ a.context.hd.le a.hdD 2))

theorem canonical_mass_inverse_cube_le
    (a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hC0 : 0<C0) (hm : 0 < m) (hN : 1 ≤ a.context.N) :
    1/a.xs^3 ≤ C0^3*a.context.N^3 := by
  have hupper : a.context.E ≤ a.context.d^2/Real.sqrt a.context.N :=
    (le_div_iff₀ (Real.sqrt_pos.mpr a.context.hN)).mpr (by simpa only [mul_comm] using a.hupper)
  have hlower : (1/C0)*a.context.N^(-(2:ℝ)/3+m)*a.context.d ≤ a.context.E := by
    have H : (a.context.N^(-(2:ℝ)/3+m)*a.context.d)/C0 ≤ a.context.E:=
      (div_le_iff₀ hC0).mpr (by simpa only [mul_comm] using a.hlower)
    simpa only [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc,one_mul] using H
  have Hparent:=comparison_parent_scale_lower_bounds a.context.hN (one_div_pos.mpr hC0)
    a.context.hd hlower hupper
  have Hpow : a.context.N^(-(1:ℝ)) ≤ a.context.N^(-(1:ℝ)/6+m):=
    Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have Hx : 1/(C0*a.context.N) ≤ a.xs := by
    have H:=(mul_le_mul_of_nonneg_left Hpow (one_div_pos.mpr hC0).le).trans
      (Hparent.2.2.trans a.hscale)
    calc
      1/(C0*a.context.N) = (1/C0)*a.context.N^(-(1:ℝ)) := by
        rw [Real.rpow_neg a.context.hN.le,Real.rpow_one]
        ring
      _ ≤ a.xs := H
  have Hcube:=pow_le_pow_left₀ (by positivity : 0 ≤ 1/(C0*a.context.N)) Hx 3
  have Hinv:=one_div_le_one_div_of_le (by positivity : 0 < (1/(C0*a.context.N))^3) Hcube
  simpa only [one_div_div,div_pow,one_pow,mul_pow,div_one] using Hinv

end NativeOverlapMinimum

theorem mass_normalized_noise_le {P x U v K c : ℝ}
    (hP : 0<P) (hx : 0<x) (hU : 0<U) (hv : 0<v) (hK : 0 ≤ K) (hc : 0<c)
    (hsize : 1/U^2 ≤ K*P*x^2) (hscale : c*x ≤ v) :
    1/(P*(16*v)^2*x^2) ≤ (K/(256*c^2))*(U/x)^2 := by
  have Hsize : 1 ≤ K*P*x^2*U^2:=by
    exact (div_le_iff₀ (sq_pos_of_pos hU)).mp hsize
  have Hscale:=pow_le_pow_left₀ (mul_pos hc hx).le hscale 2
  have Hmul:=mul_le_mul_of_nonneg_left Hscale (show 0 ≤ K*P*U^2/c^2 by positivity)
  have HE : (K*P*U^2/c^2)*(c*x)^2=K*P*x^2*U^2 := by field_simp
  rw [HE] at Hmul
  apply (div_le_iff₀ (show 0<P*(16*v)^2*x^2 by positivity)).mpr
  have HE' : ((K/(256*c^2))*(U/x)^2)*(P*(16*v)^2*x^2)=(K*P*U^2/c^2)*v^2 := by
    field_simp
    ring
  rw [HE']
  exact Hsize.trans Hmul

end OAI.SKFluctuations.LaplaceWindowFormalization
