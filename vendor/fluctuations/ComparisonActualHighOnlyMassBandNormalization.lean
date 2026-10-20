module

public import ComparisonNativeActualMassBandNormalization
public import ComparisonActualHighOnlyMassBandScale

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 24000000
namespace ActualHighOnlyOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
theorem canonical_ordinary_mass_band_budget_normalized_le
    (a : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℝ) (hxsW : a.xs ≤ W)
    (ell : ℕ) (hell : 2<ell) (Q Ccut c Cv : ℝ)
    (hCcut : 0 ≤ Ccut) (hc : 0<c) (hCv : 0 ≤ Cv)
    (hm : 0 < m) (hcl : 0<cl) (hAz : 0 ≤ Az) (hCt : 0 ≤ Ct) (hC0 : 0<C0)
    (hxs1 : W ≤ 1) (hN : 1 ≤ a.data.N) (hlog : 1 ≤ Real.log a.data.N)
    {v cut : ℝ} (hv : 0<v) (hv1 : v ≤ 1) (hvlo : c*W ≤ v)
    (hvhi : v ≤ Cv*W) (hcut : 0 ≤ cut) :
    a.canonicalOrdinaryMassBudget ell Q (Ccut*Real.log a.data.N) cut v/W^3 ≤
      nativeMassBinLossConstant Ccut*(Real.log a.data.N)^4*(16*Cv)*
        nativeMassOrdinaryEnvelope ell Q Cv
          (actualMassStrengthConstant Az cl Ct Cv/(256*c^2))
          (a.data.U/W) (a.canonicalMassDiameter/W)+
      (18*(3+1024*Q^4*D^2)*C0^3)*a.data.N^4*cut := by
  let x:=W
  let y:=a.canonicalMassHeight v
  let P:=a.canonicalMassPower v
  let B:=16*v
  let Dm:=a.canonicalMassDiameter
  let R:=a.canonicalMassReverse ell Q v
  let F:=nativeBinScaleLoss (Ccut*Real.log a.data.N)
    (108*32^2*(Real.log a.data.N)^2) (54*32^2*(Real.log a.data.N)^2) B (v/4)
  let tau:=1/(P*B^2*x^2)
  let Cn:=actualMassStrengthConstant Az cl Ct Cv/(256*c^2)
  let t:=a.data.U/x
  let d:=Dm/x
  have hx : 0<x:=a.hxs.trans_le hxsW
  have hP : 0<P:=a.canonical_mass_power_pos v
  have hB : 0<B:=by dsimp [B];positivity
  have hy : 0 ≤ y:=by
    dsimp [y,canonicalMassHeight]
    exact add_nonneg a.hxs.le (le_min (by positivity) zero_le_one)
  have hd : 0 ≤ Dm:=a.canonical_mass_diameter_nonneg (by linarith)
  have ht : 0 ≤ t:=div_nonneg a.data.hU.le hx.le
  have hCy : 0 ≤ 1+16*Cv:=by positivity
  have hCn : 0 ≤ Cn:=by
    dsimp [Cn,actualMassStrengthConstant,actualMassEndpointConstant]
    positivity
  have hF : 0 ≤ F:=by
    dsimp [F,nativeBinScaleLoss]
    positivity
  have htau : 0 ≤ tau:=by dsimp [tau];positivity
  have Hy:=a.canonical_mass_band_height_le hxsW hvhi
  have Hyx : y/x ≤ 1+16*Cv:=(div_le_iff₀ hx).mpr (by simpa only [mul_comm] using Hy)
  have Htau : tau ≤ Cn*t^2:=mass_normalized_noise_le hP hx a.data.hU hv
    (show 0 ≤ actualMassStrengthConstant Az cl Ct Cv by
      unfold actualMassStrengthConstant actualMassEndpointConstant;positivity)
    hc (a.canonical_mass_band_power_size hcl hAz hCt hxsW hxs1 hv hvhi) hvlo
  have Hfirst:=mass_noise_two_thirds_le (Q:=Q) hCy hCn ht (div_nonneg hy hx.le) htau Hyx Htau
  have Hrev : R/x^2 ≤ nativeMassReverseConstant ell Q (1+16*Cv)*d^(((ell:ℝ)-2)/((ell:ℝ)-1)) :=
    mass_reverse_normalized_le hell hx hd hy hCy Hy
  have Hinside : 2*(Q^2*(y/x)*tau)^((2:ℝ)/3)+3*tau+d^2+R/x^2 ≤
      nativeMassOrdinaryEnvelope ell Q Cv Cn t d := by
    dsimp [nativeMassOrdinaryEnvelope]
    nlinarith [Hfirst,Htau,Hrev]
  have Hinside0 : 0 ≤ 2*(Q^2*(y/x)*tau)^((2:ℝ)/3)+3*tau+d^2+R/x^2 := by
    have hEven : 0 ≤ (2*Q)^(2*ell):=by rw [Nat.mul_comm 2 ell,pow_mul];exact sq_nonneg _
    have hR : 0 ≤ R:=by dsimp [R,canonicalMassReverse];positivity
    positivity
  have Hnorm:=mass_ordinary_cubic_normalization (x:=x) (P:=P) (B:=B) (y:=y)
    (D:=Dm) (R:=R) (F:=F) (Q:=Q) (cut:=cut) hx hP hB hy
  have HF:=native_mass_binScaleLoss_log_bound hCcut hlog hv
  have HBx : B/x ≤ 16*Cv:=(div_le_iff₀ hx).mpr (by dsimp [B];nlinarith)
  have Houter:=mul_le_mul
    (mul_le_mul HF HBx (div_nonneg hB.le hx.le)
      (show 0 ≤ nativeMassBinLossConstant Ccut*(Real.log a.data.N)^4 by
        exact mul_nonneg (native_mass_binScaleLoss_constant_nonneg hCcut) (pow_nonneg (by linarith) _)))
    Hinside Hinside0 (mul_nonneg
      (mul_nonneg (native_mass_binScaleLoss_constant_nonneg hCcut) (pow_nonneg (by linarith) _))
      (mul_nonneg (by norm_num) hCv))
  have HcutXs:=a.canonical_mass_cut_error_le (Q:=Q) hC0 hm hN (hxsW.trans hxs1) hv hv1 hcut
  have Hnum0 : 0 ≤ 18*(((Q^2*y)^2*P*B^2)^((1:ℝ)/3)+2)*cut := by positivity
  have Hcut : 18*(((Q^2*y)^2*P*B^2)^((1:ℝ)/3)+2)*cut/x^3 ≤
      (18*(3+1024*Q^4*D^2)*C0^3)*a.data.N^4*cut :=
    (div_le_div_of_nonneg_left Hnum0 (pow_pos a.hxs 3)
      (pow_le_pow_left₀ a.hxs.le hxsW 3)).trans HcutXs
  change a.canonicalOrdinaryMassBudget ell Q (Ccut*Real.log a.data.N) cut v/x^3 ≤ _
  change (F*B*(2*((Q^2*y)/(P*B^2))^((2:ℝ)/3)+3/(P*B^2)+Dm^2+R)+
    18*(((Q^2*y)^2*P*B^2)^((1:ℝ)/3)+2)*cut)/x^3 ≤ _
  rw [Hnorm]
  exact add_le_add Houter Hcut

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
