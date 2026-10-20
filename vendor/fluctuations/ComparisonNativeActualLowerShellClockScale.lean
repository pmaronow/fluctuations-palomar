module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import ComparisonActualChildMargins
public import ComparisonNativeActualWeakHistoryVaryingRoot

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 5000000
namespace NativeOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem actual_lower_shell_covariance_defect_bound {n : ℕ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (hC0 : 0 < C0) :
    M.context.N^(-(1:ℝ)/3)/
      (comparisonLowerScale M.context.N M.context.E M.context.d)^2 ≤
      C0^2*M.context.N^(-2*m) := by
  have hlo : (1/C0)*M.context.N^(-(2:ℝ)/3+m)*M.context.d ≤ M.context.E := by
    have H:=(div_le_iff₀ hC0).mpr (by simpa only [mul_comm] using M.hlower)
    simpa only [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc,one_mul] using H
  have hup : M.context.E ≤ M.context.d^2/Real.sqrt M.context.N :=
    (le_div_iff₀ (Real.sqrt_pos.mpr M.context.hN)).mpr
      (by simpa only [mul_comm] using M.hupper)
  have Hlow := (comparison_parent_scale_lower_bounds M.context.hN
    (one_div_pos.mpr hC0) M.context.hd hlo hup).2.2
  let a:=comparisonLowerScale M.context.N M.context.E M.context.d
  have ha : 0 < a := by
    dsimp only [a,comparisonLowerScale]
    exact div_pos (mul_pos (Real.sqrt_pos.mpr M.context.hN) M.context.hE) M.context.hd
  have HL : (1/C0)*M.context.N^(-(1:ℝ)/6+m) ≤ a:=Hlow
  have Hp:=pow_le_pow_left₀ (show 0 ≤ (1/C0)*M.context.N^(-(1:ℝ)/6+m) by positivity) HL 2
  have H:=mul_le_mul_of_nonneg_left Hp
    (show 0 ≤ C0^2*M.context.N^(-2*m) by positivity)
  have Heq : (C0^2*M.context.N^(-2*m))*((1/C0)*M.context.N^(-(1:ℝ)/6+m))^2=
      M.context.N^(-(1:ℝ)/3) := by
    calc
      _ = (C0*(1/C0))^2*
          (M.context.N^(-2*m)*(M.context.N^(-(1:ℝ)/6+m))^2) := by ring
      _ = _ := by
        rw [mul_one_div_cancel hC0.ne',one_pow,one_mul,
          ←Real.rpow_mul_natCast M.context.hN.le,←Real.rpow_add M.context.hN]
        congr 1
        ring
  rw [Heq] at H
  exact (div_le_iff₀ (sq_pos_of_pos ha)).mpr (by simpa only [a] using H)

theorem actual_lower_shell_covariance_defect_tendsto_zero
    (hm : 0 < m) (hC0 : 0 < C0) (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (root : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock) :
    Tendsto (fun n=>(root n).context.N^(-(1:ℝ)/3)/
      (comparisonLowerScale (root n).context.N (root n).context.E (root n).context.d)^2)
      atTop (𝓝 0) := by
  have HN : Tendsto (fun n=>((dim n+1:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hdim)
  have Hpow:= (tendsto_rpow_neg_atTop (by linarith : 0 < 2*m)).comp HN
  have Hlim : Tendsto (fun n=>C0^2*(root n).context.N^(-2*m)) atTop (𝓝 0) := by
    simpa only [mul_zero,NativeOverlapContext.N,Function.comp_def,neg_mul] using Hpow.const_mul (C0^2)
  exact squeeze_zero
    (fun n=>div_nonneg (Real.rpow_nonneg (root n).context.hN.le _) (sq_nonneg _))
    (fun n=>(root n).actual_lower_shell_covariance_defect_bound hC0) Hlim

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
