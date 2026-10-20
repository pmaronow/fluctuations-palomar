module

public import ComparisonNativeActualMinimumLocalMassAssembly

@[expose] public section

noncomputable section
set_option maxHeartbeats 6000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators

theorem mass_wall_cubic_normalized_le {xs U W K : ℝ}
    (hxs : 0 < xs) (hxsW : xs ≤ W) (hU : 0 ≤ U) (hUW : U/W ≤ 1) (hK : 0 ≤ K) :
    8*K*(xs+8*U)^2*U/W^3 ≤ 648*K*(U/W) := by
  have hW : 0 < W := hxs.trans_le hxsW
  have Huw : U ≤ W := (div_le_one hW).mp hUW
  have Hs : xs+8*U ≤ 9*W := by linarith
  have Hsq := pow_le_pow_left₀ (by positivity : 0 ≤ xs+8*U) Hs 2
  have Hmul := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left Hsq (by positivity : 0 ≤ 8*K)) hU
  exact (div_le_div_of_nonneg_right Hmul (pow_nonneg hW.le 3)).trans_eq (by field_simp; ring)

theorem mass_floor_cubic_normalized_le {xs hi W K N delta Chi U : ℝ}
    (hxs : 0 < xs) (hxsW : xs ≤ W) (hhi : 0 ≤ hi) (hsize : hi ≤ Chi*W)
    (hK : 0 ≤ K) (hN : 0 ≤ N) (hU : 0 ≤ U) :
    K*(xs+hi)^2*N^(-delta)*U/W^3 ≤ K*(1+Chi)^2*N^(-delta)*(U/W) := by
  have hW : 0 < W := hxs.trans_le hxsW
  have Hs : xs+hi ≤ (1+Chi)*W := by nlinarith
  have Hsq := pow_le_pow_left₀ (by positivity : 0 ≤ xs+hi) Hs 2
  have Hmul := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left Hsq hK) (Real.rpow_nonneg hN (-delta))) hU
  exact (div_le_div_of_nonneg_right Hmul (pow_nonneg hW.le 3)).trans_eq (by field_simp)

namespace NativeOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem actual_mass_energy_le_Dsq
    (a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hN : 1 ≤ a.context.N) : a.context.E ≤ D^2 := by
  have Hsqrt : 1 ≤ Real.sqrt a.context.N := (Real.one_le_sqrt).mpr hN
  have HE : a.context.E ≤ a.context.d^2 := by nlinarith [a.hupper,a.context.hE]
  exact HE.trans (pow_le_pow_left₀ a.context.hd.le a.hdD 2)

theorem actual_mass_inverse_small_le
    (a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hN : 1 ≤ a.context.N) : 1/a.context.U ≤ a.context.N*(1+D^2) := by
  have HE := a.actual_mass_energy_le_Dsq hN
  have Hmul := mul_le_mul_of_nonneg_left HE a.context.hN.le
  have he : 1/a.context.U=a.context.N*a.context.E := by
    unfold NativeOverlapContext.U comparisonSmallMass
    field_simp
  rw [he]
  nlinarith [a.context.hN]

theorem actual_mass_log_count_le
    (a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hN : 1 ≤ a.context.N) (hlog : 1 ≤ Real.log a.context.N) (hU1 : a.context.U ≤ 1) :
    (Nat.ceil (Real.log (1/a.context.U)/Real.log 2):ℝ)+1 ≤
      (((1+Real.log (1+D^2))/Real.log 2)+2)*Real.log a.context.N := by
  have HlogD : 0 ≤ Real.log (1+D^2) := Real.log_nonneg (by nlinarith [sq_nonneg D])
  have HU : 1 ≤ 1/a.context.U := (one_le_div a.context.hU).mpr hU1
  have HL0 : 0 ≤ Real.log (1/a.context.U) := Real.log_nonneg HU
  have HL := Real.log_le_log (one_div_pos.mpr a.context.hU) (a.actual_mass_inverse_small_le hN)
  rw [Real.log_mul a.context.hN.ne' (by positivity : (1+D^2:ℝ)≠0)] at HL
  have Hlogs : Real.log a.context.N+Real.log (1+D^2) ≤
      (1+Real.log (1+D^2))*Real.log a.context.N := by
    nlinarith [mul_nonneg HlogD (sub_nonneg.mpr hlog)]
  have Hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have Hratio := div_le_div_of_nonneg_right (HL.trans Hlogs) Hlog2.le
  have Hceil := Nat.ceil_lt_add_one (div_nonneg HL0 Hlog2.le)
  have Htwo : (2:ℝ) ≤ 2*Real.log a.context.N := by linarith
  have He : ((1+Real.log (1+D^2))*Real.log a.context.N)/Real.log 2+2*Real.log a.context.N =
      (((1+Real.log (1+D^2))/Real.log 2)+2)*Real.log a.context.N := by ring
  rw [←He]
  linarith

end NativeOverlapMinimum

theorem eventually_actual_mass_polynomial_cut_feasible
    {m delta cl cu Az C0 Ct D Bclock : ℝ} :
    ∀ᶠn : ℕ in atTop,
      ∀a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        2*a.context.N^(-(10:ℝ)) < a.context.U := by
  have Hsmall := (tendsto_add_atTop_nat 1).eventually
    (eventually_coefficient_rpow_le (c:=2*(1+D^2)) (d:=(1:ℝ)/2) (q:=-(9:ℝ)) (r:=0)
      (by norm_num) (by norm_num))
  filter_upwards [Hsmall] with n hn
  intro a
  have hN : 1 ≤ a.context.N := by dsimp [NativeOverlapContext.N]; exact_mod_cast Nat.succ_pos n
  have Hinv := a.actual_mass_inverse_small_le hN
  have Hprod : (2*a.context.N^(-(10:ℝ)))/a.context.U ≤
      (2*(1+D^2))*a.context.N^(-(9:ℝ)) := by
    calc
      _ = (2*a.context.N^(-(10:ℝ)))*(1/a.context.U) := by ring
      _ ≤ (2*a.context.N^(-(10:ℝ)))*(a.context.N*(1+D^2)) :=
        mul_le_mul_of_nonneg_left Hinv (by positivity)
      _ = (2*(1+D^2))*a.context.N^(-(9:ℝ)) := by
        have He : a.context.N^(-(10:ℝ))*a.context.N=a.context.N^(-(9:ℝ)) := by
          calc
            _ = a.context.N^(-(10:ℝ))*a.context.N^(1:ℝ) := by rw [Real.rpow_one]
            _ = a.context.N^(-(10:ℝ)+1) := (Real.rpow_add a.context.hN _ _).symm
            _ = _ := by norm_num
        calc
          _ = (2*(1+D^2))*(a.context.N^(-(10:ℝ))*a.context.N) := by ring
          _ = _ := by rw [He]
  have Hhalf : (2*(1+D^2))*a.context.N^(-(9:ℝ)) ≤ (1:ℝ)/2 := by
    simpa only [NativeOverlapContext.N,Real.rpow_zero,mul_one] using hn
  exact (div_lt_one a.context.hU).mp ((Hprod.trans Hhalf).trans_lt (by norm_num))

end OAI.SKFluctuations.LaplaceWindowFormalization
