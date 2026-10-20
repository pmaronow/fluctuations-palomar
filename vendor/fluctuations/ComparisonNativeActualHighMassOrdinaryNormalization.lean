module

public import ComparisonNativeActualHighMassNoise
public import ComparisonNativeActualHighMassReverse

@[expose] public section

noncomputable section
set_option maxHeartbeats 10000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators

theorem mass_high_ordinary_normalization {x W v P y Q diam rev F cut : ℝ}
    (hx : 0 < x) (hW : 0 < W) (hv : 0 < v) :
    (F*(16*v)*(2*((Q^2*y)/(P*(16*v)^2))^((2:ℝ)/3)+
        3/(P*(16*v)^2)+diam^2+rev)+
      18*(((Q^2*y)^2*P*(16*v)^2)^((1:ℝ)/3)+2)*cut)/(x^4*v/W^2)=
    16*F*(2*(((Q^2*y)/(P*(16*v)^2))^((2:ℝ)/3)*(W^2/x^4))+
        3*((W^2/x^4)/(P*(16*v)^2))+diam^2*(W^2/x^4)+rev*(W^2/x^4))+
      (18*(((Q^2*y)^2*P*(16*v)^2)^((1:ℝ)/3)+2)*cut)*(W^2/(x^4*v)) := by
  field_simp

namespace NativeOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem canonical_high_mass_ordinary_budget_normalized_le
    (a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (ell : ℕ) (Q Ccut : ℝ) (hCcut : 0 ≤ Ccut)
    (hlog : 1 ≤ Real.log a.context.N) {v diam cut : ℝ}
    (hv : 0 < v) (hdiam : 0 ≤ diam) :
    a.canonicalOrdinaryMassBudgetAtDiameter ell Q (Ccut*Real.log a.context.N) cut v diam/
        (a.xs^4*v/a.canonicalDirectTestBandScale^2) ≤
      (16*nativeMassBinLossConstant Ccut)*(Real.log a.context.N)^4*
        (2*(((Q^2*a.canonicalMassHeight v)/(a.canonicalMassPower v*(16*v)^2))^((2:ℝ)/3)*
              (a.canonicalDirectTestBandScale^2/a.xs^4))+
          3*((a.canonicalDirectTestBandScale^2/a.xs^4)/(a.canonicalMassPower v*(16*v)^2))+
          diam^2*(a.canonicalDirectTestBandScale^2/a.xs^4)+
          a.canonicalMassReverseAtDiameter ell Q v diam*(a.canonicalDirectTestBandScale^2/a.xs^4))+
      (18*(((Q^2*a.canonicalMassHeight v)^2*a.canonicalMassPower v*(16*v)^2)^((1:ℝ)/3)+2)*cut)*
        (a.canonicalDirectTestBandScale^2/(a.xs^4*v)) := by
  have Hnorm:=mass_high_ordinary_normalization (P:=a.canonicalMassPower v)
    (y:=a.canonicalMassHeight v) (Q:=Q) (diam:=diam)
    (rev:=a.canonicalMassReverseAtDiameter ell Q v diam)
    (F:=nativeBinScaleLoss (Ccut*Real.log a.context.N) (108*32^2*(Real.log a.context.N)^2)
      (54*32^2*(Real.log a.context.N)^2) (16*v) (v/4)) (cut:=cut)
    a.hxs a.canonical_direct_test_band_pos hv
  unfold canonicalOrdinaryMassBudgetAtDiameter
  rw [Hnorm]
  have HF:=native_mass_binScaleLoss_log_bound hCcut hlog hv
  have hP:=a.canonical_mass_power_pos v
  have hxs:=a.hxs
  have hW:=a.canonical_direct_test_band_pos
  have hy : 0 ≤ a.canonicalMassHeight v:=by unfold canonicalMassHeight;positivity
  have hEven : 0 ≤ (2*Q)^(2*ell):=by rw [Nat.mul_comm 2 ell,pow_mul];exact sq_nonneg _
  have hR : 0 ≤ a.canonicalMassReverseAtDiameter ell Q v diam:=by
    unfold canonicalMassReverseAtDiameter
    exact mul_nonneg (Real.rpow_nonneg hdiam _)
      (Real.rpow_nonneg (mul_nonneg hEven (pow_nonneg hy ell)) _)
  have H:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left HF (by norm_num : (0:ℝ) ≤ 16))
    (show 0 ≤ 2*(((Q^2*a.canonicalMassHeight v)/(a.canonicalMassPower v*(16*v)^2))^((2:ℝ)/3)*
        (a.canonicalDirectTestBandScale^2/a.xs^4))+
      3*((a.canonicalDirectTestBandScale^2/a.xs^4)/(a.canonicalMassPower v*(16*v)^2))+
      diam^2*(a.canonicalDirectTestBandScale^2/a.xs^4)+
      a.canonicalMassReverseAtDiameter ell Q v diam*(a.canonicalDirectTestBandScale^2/a.xs^4) by positivity)
  nlinarith only [H]

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
