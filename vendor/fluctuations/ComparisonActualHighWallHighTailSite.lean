module

public import ComparisonActualHighWallHighMassNumerics
public import ComparisonActualHighWallHighProfile
public import ComparisonNativeHighTailOmittedSite

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 16000000
namespace ActualHighWallOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem high_tail_site_normalized_le
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hC0 : 0< C0) (hxsD : M.xs≤ M.data.d) :
    (1/M.data.N)/M.data.d≤ C0^2*M.data.N^(-(2:ℝ)/3-2*m) := by
  have hN:=M.data.hN
  have hx:=M.hxs
  have hd:=M.data.hd
  have H:=M.high_mass_inverse_power hC0 2
  have H' : 1/(M.data.N^((1:ℝ)/3)*M.xs^2)≤ C0^2*M.data.N^(-2*m):=by
    simpa only [Nat.cast_ofNat,show (2:ℝ)/6=1/3 by norm_num] using H
  have HE : (1/M.data.N)/(M.xs^2/M.data.d)=
      M.data.d*(M.data.N^(-(2:ℝ)/3)*(1/(M.data.N^((1:ℝ)/3)*M.xs^2))):=by
    have HP : M.data.N^(-(2:ℝ)/3)*M.data.N=M.data.N^((1:ℝ)/3):=by
      calc
        _=M.data.N^(-(2:ℝ)/3)*M.data.N^(1:ℝ):=by rw [Real.rpow_one]
        _=M.data.N^(-(2:ℝ)/3+1):=(Real.rpow_add hN _ _).symm
        _=_:=by congr 1;norm_num
    rw [←HP]
    have Hne : M.data.N^(-(2:ℝ)/3)≠0:=(Real.rpow_pos_of_pos hN _).ne'
    field_simp [hN.ne',hx.ne',hd.ne',Hne]
  have HT : M.xs^2/M.data.d≤ M.data.d:=(div_le_iff₀ hd).mpr
    (by simpa only [pow_two] using pow_le_pow_left₀ hx.le hxsD 2)
  have HL : (1/M.data.N)/M.data.d≤(1/M.data.N)/(M.xs^2/M.data.d):=
    div_le_div_of_nonneg_left (by positivity) (by positivity) HT
  rw [HE] at HL
  have HS:=mul_le_mul_of_nonneg_left H' (Real.rpow_nonneg hN.le (-(2:ℝ)/3))
  have HF:=mul_le_of_le_one_left
    (show 0≤ M.data.N^(-(2:ℝ)/3)*(1/(M.data.N^((1:ℝ)/3)*M.xs^2)) by positivity) M.data.hd1
  have Hfinal : M.data.N^(-(2:ℝ)/3)*(C0^2*M.data.N^(-2*m))=
      C0^2*M.data.N^(-(2:ℝ)/3-2*m):=by
    rw [mul_left_comm,←Real.rpow_add hN,show (-(2:ℝ)/3)+(-2*m)=-(2:ℝ)/3-2*m by ring]
  exact HL.trans (HF.trans (HS.trans_eq Hfinal))

theorem highComparisonConstant_le
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) :
    M.data.highComparisonConstant≤ Cavity.actualLowErrorComparisonConstant (2*Bclock) Bclock := by
  have hT:=M.hT
  have hTp:=M.data.hTpos
  have hBclock : 0≤ Bclock:=hTp.le.trans hT
  unfold ActualHighWallData.highComparisonConstant Cavity.actualLowErrorComparisonConstant
  have HI : 2*Real.exp (220*(2*M.data.T))*(Real.exp (110*M.data.T)+1)≤
      2*Real.exp (220*(2*Bclock))*(Real.exp (110*Bclock)+1):=by
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (by nlinarith only [hT])) (by norm_num)
    · exact add_le_add
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hT (show (0:ℝ)≤110 by norm_num))) le_rfl
    · positivity
    · positivity
  exact mul_le_mul hT (Real.sqrt_le_sqrt HI) (Real.sqrt_nonneg _) hBclock

end ActualHighWallOverlapMinimum

theorem eventually_actual_high_wall_high_tail_site_le
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (hm : 0< m) (hdelta : 0< delta) (hC0 : 0< C0) :
    ∀ᶠn in atTop,∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      M.xs≤ M.data.d → 1/M.data.N≤ M.data.N^(-(actualMassSavingExponent m delta/16))*M.data.d := by
  let eta:=actualMassSavingExponent m delta
  have heta:=actualMassSavingExponent_pos hm hdelta
  have HE:=(actualMassSavingExponent_bounds m delta).1
  have HC:=(tendsto_add_atTop_nat 1).eventually
    (eventually_coefficient_rpow_le (c:=C0^2) (d:=1) (q:=-(2:ℝ)/3-2*m)
      (r:=-eta/16) zero_lt_one (by dsimp only [eta] at *;linarith))
  filter_upwards [HC] with n hc
  intro M hxsD
  have HH:=M.high_tail_site_normalized_le hC0 hxsD
  have HN : C0^2*M.data.N^(-(2:ℝ)/3-2*m)≤ M.data.N^(-eta/16):=by
    simpa only [ActualHighWallData.N,one_mul] using hc
  simpa only [eta,neg_div] using (div_le_iff₀ M.data.hd).mp (HH.trans HN)

end OAI.SKFluctuations.LaplaceWindowFormalization
