module

public import ComparisonNativeActualMassSlabScale
public import SKProof.Port.ComparisonActualOriginalQMassBudgetScale

@[expose] public section
noncomputable section
set_option maxHeartbeats 6000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators

namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem actual_mass_energy_le_Dsq
    (a : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hN : 1 ≤ a.data.N) : a.data.E ≤ D^2 := by
  have Hsqrt : 1 ≤ Real.sqrt a.data.N := (Real.one_le_sqrt).mpr hN
  have HE : a.data.E ≤ a.data.d^2 := by nlinarith [a.hupper,a.data.hE]
  exact HE.trans (pow_le_pow_left₀ a.data.hd.le a.hdD 2)

theorem actual_mass_inverse_small_le
    (a : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hN : 1 ≤ a.data.N) : 1/a.data.U ≤ a.data.N*(1+D^2) := by
  have HE := a.actual_mass_energy_le_Dsq hN
  have Hmul := mul_le_mul_of_nonneg_left HE a.data.hN.le
  have he : 1/a.data.U=a.data.N*a.data.E := by
    unfold ActualHighWallData.U comparisonSmallMass
    field_simp
  rw [he]
  nlinarith [a.data.hN]

theorem actual_mass_log_count_le
    (a : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hN : 1 ≤ a.data.N) (hlog : 1 ≤ Real.log a.data.N) (hU1 : a.data.U ≤ 1) :
    (Nat.ceil (Real.log (1/a.data.U)/Real.log 2):ℝ)+1 ≤
      (((1+Real.log (1+D^2))/Real.log 2)+2)*Real.log a.data.N := by
  have HlogD : 0 ≤ Real.log (1+D^2) := Real.log_nonneg (by nlinarith [sq_nonneg D])
  have HU : 1 ≤ 1/a.data.U := (one_le_div a.data.hU).mpr hU1
  have HL0 : 0 ≤ Real.log (1/a.data.U) := Real.log_nonneg HU
  have HL := Real.log_le_log (one_div_pos.mpr a.data.hU) (a.actual_mass_inverse_small_le hN)
  rw [Real.log_mul a.data.hN.ne' (by positivity : (1+D^2:ℝ)≠0)] at HL
  have Hlogs : Real.log a.data.N+Real.log (1+D^2) ≤
      (1+Real.log (1+D^2))*Real.log a.data.N := by
    nlinarith [mul_nonneg HlogD (sub_nonneg.mpr hlog)]
  have Hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have Hratio := div_le_div_of_nonneg_right (HL.trans Hlogs) Hlog2.le
  have Hceil := Nat.ceil_lt_add_one (div_nonneg HL0 Hlog2.le)
  have Htwo : (2:ℝ) ≤ 2*Real.log a.data.N := by linarith
  have He : ((1+Real.log (1+D^2))*Real.log a.data.N)/Real.log 2+2*Real.log a.data.N =
      (((1+Real.log (1+D^2))/Real.log 2)+2)*Real.log a.data.N := by ring
  rw [←He]
  linarith

end ActualThetaZeroOverlapMinimum

theorem eventually_actual_mass_polynomial_cut_feasible_original_q
    {m delta cl cu Az C0 Ct D Bclock : ℝ} :
    ∀ᶠn : ℕ in atTop,
      ∀a : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        2*a.data.N^(-(10:ℝ)) < a.data.U := by
  have Hsmall := (tendsto_add_atTop_nat 1).eventually
    (eventually_coefficient_rpow_le (c:=2*(1+D^2)) (d:=(1:ℝ)/2) (q:=-(9:ℝ)) (r:=0)
      (by norm_num) (by norm_num))
  filter_upwards [Hsmall] with n hn
  intro a
  have hN : 1 ≤ a.data.N := by dsimp [ActualHighWallData.N]; exact_mod_cast Nat.succ_pos n
  have Hinv := a.actual_mass_inverse_small_le hN
  have Hprod : (2*a.data.N^(-(10:ℝ)))/a.data.U ≤
      (2*(1+D^2))*a.data.N^(-(9:ℝ)) := by
    calc
      _ = (2*a.data.N^(-(10:ℝ)))*(1/a.data.U) := by ring
      _ ≤ (2*a.data.N^(-(10:ℝ)))*(a.data.N*(1+D^2)) :=
        mul_le_mul_of_nonneg_left Hinv (by positivity)
      _ = (2*(1+D^2))*a.data.N^(-(9:ℝ)) := by
        have He : a.data.N^(-(10:ℝ))*a.data.N=a.data.N^(-(9:ℝ)) := by
          calc
            _ = a.data.N^(-(10:ℝ))*a.data.N^(1:ℝ) := by rw [Real.rpow_one]
            _ = a.data.N^(-(10:ℝ)+1) := (Real.rpow_add a.data.hN _ _).symm
            _ = _ := by norm_num
        calc
          _ = (2*(1+D^2))*(a.data.N^(-(10:ℝ))*a.data.N) := by ring
          _ = _ := by rw [He]
  have Hhalf : (2*(1+D^2))*a.data.N^(-(9:ℝ)) ≤ (1:ℝ)/2 := by
    simpa only [ActualHighWallData.N,Real.rpow_zero,mul_one] using hn
  exact (div_lt_one a.data.hU).mp ((Hprod.trans Hhalf).trans_lt (by norm_num))

end OAI.SKFluctuations.LaplaceWindowFormalization
