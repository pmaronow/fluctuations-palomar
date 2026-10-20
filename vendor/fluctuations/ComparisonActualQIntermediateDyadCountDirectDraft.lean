module

public import ComparisonActualHighWallThetaZeroDyadicThermalAssembly

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 10000000

namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
  (Q : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)

theorem intermediate_mass_inverse_small_le (hN : 1≤Q.data.N) :
    1/comparisonSmallMass Q.data.N Q.data.E ≤ Q.data.N := by
  have Hsqrt : Real.sqrt Q.data.N≤Q.data.N := by
    have Hsq:=Real.sq_sqrt Q.data.hN.le
    have Hlow:=(Real.one_le_sqrt).mpr hN
    nlinarith only [Hsq,Hlow,hN]
  have hdSq : Q.data.d^2 ≤ 1 :=
    pow_le_one₀ Q.data.hd.le Q.data.hd1
  have HEnergy0 : Real.sqrt Q.data.N*Q.data.E ≤ 1 := Q.hupper.trans hdSq
  have HEnergy : Q.data.N*Q.data.E ≤ Real.sqrt Q.data.N := by
    calc
      Q.data.N*Q.data.E = (Real.sqrt Q.data.N)^2*Q.data.E := by
        rw [Real.sq_sqrt Q.data.hN.le]
      _ = Real.sqrt Q.data.N*(Real.sqrt Q.data.N*Q.data.E) := by ring
      _ ≤ Real.sqrt Q.data.N*1 :=
        mul_le_mul_of_nonneg_left HEnergy0 (Real.sqrt_nonneg _)
      _ = Real.sqrt Q.data.N := by ring
  have H:=HEnergy.trans Hsqrt
  have HE : 1/comparisonSmallMass Q.data.N Q.data.E=Q.data.N*Q.data.E := by
    unfold comparisonSmallMass
    field_simp [Q.data.hN.ne',Q.data.hE.ne']
  simpa only [HE] using H

theorem intermediate_mass_log_count_le (hN : 1≤Q.data.N)
    (hlog : 1≤Real.log Q.data.N) :
    (Nat.ceil (Real.log (1/comparisonSmallMass Q.data.N Q.data.E)/Real.log 2):ℝ)+1 ≤
      (1/Real.log 2+2)*Real.log Q.data.N := by
  have HU : 1≤1/comparisonSmallMass Q.data.N Q.data.E :=
    (one_le_div Q.data.hU).mpr (Q.data.hsmall.trans Q.data.hd1)
  have HL0 : 0≤Real.log (1/comparisonSmallMass Q.data.N Q.data.E) :=
    Real.log_nonneg HU
  have HL:=Real.log_le_log (one_div_pos.mpr Q.data.hU)
    (Q.intermediate_mass_inverse_small_le hN)
  have Hlog2 : 0<Real.log 2:=Real.log_pos (by norm_num)
  have Hratio:=div_le_div_of_nonneg_right HL Hlog2.le
  have Hceil:=Nat.ceil_lt_add_one (div_nonneg HL0 Hlog2.le)
  have Htwo : (2:ℝ)≤2*Real.log Q.data.N:=by linarith only [hlog]
  have HE : Real.log Q.data.N/Real.log 2+2*Real.log Q.data.N=
      (1/Real.log 2+2)*Real.log Q.data.N:=by ring
  rw [←HE]
  linarith only [Hratio,Hceil,Htwo]

theorem intermediate_local_dyad_card_le_log
    (hN : 1≤Q.data.N) (hlog : 1≤Real.log Q.data.N)
    (lo hi : ℝ) :
    (Fintype.card (LocalShiftedMassDyad Q lo hi):ℝ)≤
      (1/Real.log 2+2)*Real.log Q.data.N := by
  have H:=local_mass_dyad_card_le_log Q lo hi
  have HC : (Fintype.card (LocalShiftedMassDyad Q lo hi):ℝ)≤
      (Nat.ceil (Real.log (1/comparisonSmallMass Q.data.N Q.data.E)/Real.log 2):ℝ)+1 := by
    exact_mod_cast H
  exact HC.trans (Q.intermediate_mass_log_count_le hN hlog)

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
