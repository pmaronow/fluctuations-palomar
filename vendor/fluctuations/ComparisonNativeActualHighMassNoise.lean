module

public import ComparisonNativeActualHighMassCriticalRates

@[expose] public section

noncomputable section
set_option maxHeartbeats 12000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators

theorem mass_high_variance_base_le {N P W v y Q Cy K : ℝ}
    (hN : 0 < N) (hP : 0 < P) (hW : 0 < W) (hv : 0 < v)
    (hCy : 0 ≤ Cy) (_hK : 0 ≤ K) (hy : y ≤ Cy*v) (hpower : N*W^3 ≤ K*P*v) :
    ((Q^2*y)/(P*(16*v)^2))*W^3 ≤ (Q^2*Cy*K/256)/N := by
  apply (le_div_iff₀ hN).mpr
  have HE : ((Q^2*y)/(P*(16*v)^2))*W^3*N=
      (Q^2*y*W^3*N)/(P*(16*v)^2):=by ring
  rw [HE]
  apply (div_le_iff₀ (show 0 < P*(16*v)^2 by positivity)).mpr
  have H1:=mul_le_mul_of_nonneg_left hy (show 0 ≤ Q^2*W^3*N by positivity)
  have H2:=mul_le_mul_of_nonneg_left hpower (show 0 ≤ Q^2*Cy*v by positivity)
  nlinarith only [H1,H2]

theorem mass_high_variance_noise_le {N P W v x y Q Cy K : ℝ}
    (hN : 0 < N) (hP : 0 < P) (hW : 0 < W) (hv : 0 < v) (hx : 0 < x)
    (hy0 : 0 ≤ y) (hCy : 0 ≤ Cy) (hK : 0 ≤ K) (hy : y ≤ Cy*v)
    (hpower : N*W^3 ≤ K*P*v) :
    ((Q^2*y)/(P*(16*v)^2))^((2:ℝ)/3)*(W^2/x^4) ≤
      (Q^2*Cy*K/256)^((2:ℝ)/3)/(N^((2:ℝ)/3)*x^4) := by
  have H:=Real.rpow_le_rpow
    (show 0 ≤ ((Q^2*y)/(P*(16*v)^2))*W^3 by positivity)
    (mass_high_variance_base_le hN hP hW hv hCy hK hy hpower) (by norm_num : 0 ≤ (2:ℝ)/3)
  rw [Real.mul_rpow (by positivity) (by positivity),Real.div_rpow (by positivity) hN.le] at H
  have HW : (W^3)^((2:ℝ)/3)=W^2:=by
    rw [←Real.rpow_natCast W 3,←Real.rpow_mul hW.le]
    norm_num
  rw [HW] at H
  have HH:=div_le_div_of_nonneg_right H (pow_nonneg hx.le 4)
  convert HH using 1 <;> ring

theorem mass_high_inverse_noise_le {N P W v x K c : ℝ}
    (hN : 0 < N) (hP : 0 < P) (hW : 0 < W) (hv : 0 < v) (hx : 0 < x)
    (_hK : 0 ≤ K) (hc : 0 < c) (hxW : x ≤ W) (hvlo : c*W ≤ v)
    (hpower : N*W^3 ≤ K*P*v) :
    (1/(P*(16*v)^2))*(W^2/x^4) ≤ (K/(256*c))*(1/(N*x^6)) := by
  have Hwv : c*x^2 ≤ W*v:=by
    have H1:=mul_le_mul_of_nonneg_left hvlo hW.le
    have H2:=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx.le hxW 2) hc.le
    nlinarith only [H1,H2]
  have HE : (1/(P*(16*v)^2))*(W^2/x^4)=W^2/(P*(16*v)^2*x^4):=by ring
  rw [HE,mul_one_div]
  apply (div_le_div_iff₀ (show 0 < P*(16*v)^2*x^4 by positivity)
    (show 0 < N*x^6 by positivity)).mpr
  have H3:=mul_le_mul_of_nonneg_left Hwv (show 0 ≤ N*W^2*x^4 by positivity)
  have H4:=mul_le_mul_of_nonneg_left hpower (show 0 ≤ v*x^4 by positivity)
  have HC : c*(N*W^2*x^6) ≤ K*P*v^2*x^4:=by
    nlinarith only [H3,H4]
  have HC':=mul_le_mul_of_nonneg_left HC (show 0 ≤ 1/c by positivity)
  convert HC' using 1 <;> field_simp; ring

theorem mass_high_point_noise_le {N P W v x K : ℝ}
    (hN : 0 < N) (hP : 0 < P) (hW : 0 < W) (hv : 0 < v) (hx : 0 < x)
    (hpower : N*W^3 ≤ K*P*v) :
    (W^2/x^4)/(P*v^2) ≤ K/(N*W*v*x^4) := by
  have HE : (W^2/x^4)/(P*v^2)=W^2/(P*v^2*x^4):=by ring
  rw [HE]
  apply (div_le_div_iff₀ (show 0 < P*v^2*x^4 by positivity)
    (show 0 < N*W*v*x^4 by positivity)).mpr
  have H:=mul_le_mul_of_nonneg_right hpower (show 0 ≤ v*x^4 by positivity)
  nlinarith only [H]

theorem mass_high_inverse_geometry_le {N W v x c : ℝ}
    (hN : 0 < N) (hW : 0 < W) (hv : 0 < v) (hx : 0 < x)
    (hc : 0 < c) (hxW : x ≤ W) (hvlo : c*W ≤ v) :
    1/(N*W*v*x^4) ≤ (1/c)*(1/(N*x^6)) := by
  have Hwv : c*x^2 ≤ W*v:=by
    have H1:=mul_le_mul_of_nonneg_left hvlo hW.le
    have H2:=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx.le hxW 2) hc.le
    nlinarith only [H1,H2]
  rw [mul_one_div]
  apply (div_le_div_iff₀ (show 0 < N*W*v*x^4 by positivity)
    (show 0 < N*x^6 by positivity)).mpr
  have H:=mul_le_mul_of_nonneg_left Hwv (show 0 ≤ N*x^4/c by positivity)
  convert H using 1 <;> field_simp

theorem mass_high_broad_trace_noise_le {N P W v x U E tau K c Cr Ce tlog rlog : ℝ}
    (hN : 0 < N) (hP : 0 < P) (hW : 0 < W) (hv : 0 < v) (hx : 0 < x)
    (hU : 0 < U) (hE : 0 < E) (hK : 0 ≤ K) (hc : 0 < c)
    (hCr : 0 ≤ Cr) (_hCe : 0 ≤ Ce) (hlog : 0 ≤ tlog) (hrlog : 0 ≤ rlog)
    (hxW : x ≤ W) (hvlo : c*W ≤ v) (hpower : N*W^3 ≤ K*P*v)
    (hUeq : U=1/(N*E)) (hr : rlog ≤ Cr*tlog)
    (htau : tau ≤ (W^2/x^4)/(P*v^2))
    (henergy : E/(W*x^4) ≤ Ce/(Real.sqrt N*x^3)) :
    (1025+25*(1+v/U)*rlog)*tau ≤
      K*(1025*((1/c)*(1/(N*x^6)))+
        25*(Cr*tlog)*((1/c)*(1/(N*x^6))+Ce/(Real.sqrt N*x^3))) := by
  have Htau:=htau.trans (mass_high_point_noise_le hN hP hW hv hx hpower)
  have Hgeom:=mass_high_inverse_geometry_le hN hW hv hx hc hxW hvlo
  have Hn:=mul_le_mul_of_nonneg_left Htau
    (show 0 ≤ 1025+25*(1+v/U)*rlog by positivity)
  have HE : (1025+25*(1+v/U)*rlog)*(K/(N*W*v*x^4))=
      K*(1025*(1/(N*W*v*x^4))+25*rlog*(1/(N*W*v*x^4)+E/(W*x^4))):=by
    rw [hUeq]
    field_simp
  rw [HE] at Hn
  apply Hn.trans
  gcongr

theorem mass_direct_test_energy_over_band {N E x W g Ct : ℝ}
    (hN : 0 < N) (_hE : 0 < E) (hx : 0 < x) (hW : 0 < W) (hCt : 0 ≤ Ct)
    (hTest : N*E^2 ≤ Ct*g*x^2) (hgW : g ≤ W^2) :
    E/(W*x^4) ≤ (Ct+1)/(Real.sqrt N*x^3) := by
  have HS : 0 < Real.sqrt N:=Real.sqrt_pos.mpr hN
  have H1:=mul_le_mul_of_nonneg_left hgW (show 0 ≤ Ct*x^2 by positivity)
  have H2 : (Real.sqrt N*E)^2 ≤ ((Ct+1)*W*x)^2:=by
    rw [mul_pow,Real.sq_sqrt hN.le]
    have Hc : Ct ≤ (Ct+1)^2:=by nlinarith
    have HC:=mul_le_mul_of_nonneg_right Hc (show 0 ≤ W^2*x^2 by positivity)
    nlinarith only [hTest,H1,HC]
  have HH : Real.sqrt N*E ≤ (Ct+1)*W*x:=by
    have Hpos : 0 ≤ (Ct+1)*W*x:=by positivity
    nlinarith [mul_pos HS _hE]
  apply (div_le_div_iff₀ (show 0 < W*x^4 by positivity)
    (show 0 < Real.sqrt N*x^3 by positivity)).mpr
  have H:=mul_le_mul_of_nonneg_right HH (pow_nonneg hx.le 3)
  nlinarith only [H]

namespace NativeOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem canonical_direct_test_energy_over_band
    (a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (hCt : 0 ≤ Ct) :
    a.context.E/(a.canonicalDirectTestBandScale*a.xs^4) ≤
      (Ct+1)/(Real.sqrt a.context.N*a.xs^3) := by
  have Hg : 0 ≤ laplaceComparisonStrength a.context.d a.lam a.xs:=
    (laplaceComparisonStrength_pos _ a.hlam _).le
  have HS:=pow_le_pow_left₀ (Real.sqrt_nonneg _) (le_max_right a.xs
    (Real.sqrt (laplaceComparisonStrength a.context.d a.lam a.xs))) 2
  rw [Real.sq_sqrt Hg] at HS
  exact mass_direct_test_energy_over_band a.context.hN a.context.hE a.hxs
    a.canonical_direct_test_band_pos hCt a.htest HS

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
