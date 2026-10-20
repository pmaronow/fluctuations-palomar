module

public import ComparisonNativeActualHighMassSharpScale

@[expose] public section

noncomputable section
set_option maxHeartbeats 10000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators

theorem mass_critical_inverse_power {N x C0 m : ℝ} (hN : 0 < N)
    (hx : 0 < x) (hC0 : 0 < C0)
    (hlow : (1/C0)*N^(-(1:ℝ)/6+m) ≤ x) (k : ℕ) :
    1/(N^((k:ℝ)/6)*x^k) ≤ C0^k*N^(-(k:ℝ)*m) := by
  have Hpow:=pow_le_pow_left₀ (by positivity : 0 ≤ (1/C0)*N^(-(1:ℝ)/6+m)) hlow k
  have Hmul:=mul_le_mul_of_nonneg_left Hpow
    (show 0 ≤ C0^k*N^(-(k:ℝ)*m)*N^((k:ℝ)/6) by positivity)
  have HE : (C0^k*N^(-(k:ℝ)*m)*N^((k:ℝ)/6))*
      ((1/C0)*N^(-(1:ℝ)/6+m))^k=1:=by
    rw [mul_pow,div_pow,one_pow,←Real.rpow_mul_natCast hN.le]
    calc
      _ = (N^(-(k:ℝ)*m)*N^((k:ℝ)/6))*N^((-(1:ℝ)/6+m)*(k:ℝ)) := by field_simp
      _ = N^((-(k:ℝ)*m+(k:ℝ)/6)+((-(1:ℝ)/6+m)*(k:ℝ))) := by
        rw [←Real.rpow_add hN,←Real.rpow_add hN]
      _ = 1 := by rw [show (-(k:ℝ)*m+(k:ℝ)/6)+((-(1:ℝ)/6+m)*(k:ℝ))=0 by ring,Real.rpow_zero]
  rw [HE] at Hmul
  apply (div_le_iff₀ (show 0 < N^((k:ℝ)/6)*x^k by positivity)).mpr
  simpa only [mul_assoc] using Hmul

theorem mass_cap_strong_normalization {N E d x W Cd : ℝ}
    (hN : 0 < N) (hE : 0 < E) (hd : 0 < d) (hx : 0 < x)
    (hW : 0 ≤ W) (_hCd : 0 ≤ Cd) (hscale : Real.sqrt N*E/d ≤ x)
    (hWd : W ≤ Cd*d) :
    (E/d^3)*(W^2/x^4) ≤ Cd^2*d^3/(N^2*E^3) := by
  have HX:=pow_le_pow_left₀ (by positivity : 0 ≤ Real.sqrt N*E/d) hscale 2
  have Hsq : N*E^2 ≤ d^2*x^2 := by
    have HH : (Real.sqrt N*E/d)^2=N*E^2/d^2:=by rw [div_pow,mul_pow,Real.sq_sqrt hN.le]
    rw [HH] at HX
    simpa only [mul_comm] using (div_le_iff₀ (sq_pos_of_pos hd)).mp HX
  have Hfour:=pow_le_pow_left₀ (show 0 ≤ N*E^2 by positivity) Hsq 2
  have HW:=pow_le_pow_left₀ hW hWd 2
  have HE : (E/d^3)*(W^2/x^4)=(E*W^2)/(d^3*x^4):=by ring
  rw [HE]
  apply (div_le_div_iff₀ (show 0 < d^3*x^4 by positivity) (show 0 < N^2*E^3 by positivity)).mpr
  have H1:=mul_le_mul_of_nonneg_right HW (show 0 ≤ N^2*E^4 by positivity)
  have H2:=mul_le_mul_of_nonneg_left Hfour (show 0 ≤ Cd^2*d^2 by positivity)
  nlinarith only [H1,H2]

namespace NativeOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem canonical_high_mass_scale_critical_lower
    (a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (hC0 : 0 < C0) :
    (1/C0)*a.context.N^(-(1:ℝ)/6+m) ≤ a.xs := by
  have Hupper : a.context.E ≤ a.context.d^2/Real.sqrt a.context.N :=
    (le_div_iff₀ (Real.sqrt_pos.mpr a.context.hN)).mpr (by simpa only [mul_comm] using a.hupper)
  have Hlower : (1/C0)*a.context.N^(-(2:ℝ)/3+m)*a.context.d ≤ a.context.E := by
    have H := (div_le_iff₀ hC0).mpr (by simpa only [mul_comm] using a.hlower)
    simpa only [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc,one_mul] using H
  exact (comparison_parent_scale_lower_bounds a.context.hN (one_div_pos.mpr hC0)
    a.context.hd Hlower Hupper).2.2.trans a.hscale

theorem canonical_high_mass_inverse_power
    (a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (hC0 : 0 < C0) (k : ℕ) :
    1/(a.context.N^((k:ℝ)/6)*a.xs^k) ≤ C0^k*a.context.N^(-(k:ℝ)*m) :=
  mass_critical_inverse_power a.context.hN a.hxs hC0 (a.canonical_high_mass_scale_critical_lower hC0) k

theorem canonical_direct_test_cap_strong_rate
    (a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hC0 : 0 < C0) {Cs : ℝ} (hCs : 0 ≤ Cs)
    (hsmall : a.xs^2 ≤ Cs*laplaceComparisonStrength a.context.d a.lam a.xs) :
    (a.context.E/a.context.d^3)*(a.canonicalDirectTestBandScale^2/a.xs^4) ≤
      (Cs+1)^2*C0^3*a.context.N^(-3*m) := by
  have H:=mass_cap_strong_normalization a.context.hN a.context.hE a.context.hd a.hxs
    a.canonical_direct_test_band_pos.le (show 0 ≤ Cs+1 by linarith) a.hscale
    (a.canonical_direct_test_band_geometry hCs hsmall).1
  apply H.trans
  have HH:=mul_le_mul_of_nonneg_left (a.canonical_high_mass_critical_ratio hC0) (sq_nonneg (Cs+1))
  simpa only [mul_div_assoc,mul_assoc] using HH

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
