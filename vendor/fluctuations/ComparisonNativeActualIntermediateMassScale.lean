module

public import ComparisonNativeActualHighMassNoiseRates

@[expose] public section

noncomputable section
set_option maxHeartbeats 7000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators

def actualIntermediateMassEffectiveScale (W v : ℝ) : ℝ :=
  (W^2*v)^((1:ℝ)/3)

theorem actualIntermediateMassEffectiveScale_pos {W v : ℝ}
    (hW : 0 < W) (hv : 0 < v) : 0 < actualIntermediateMassEffectiveScale W v := by
  unfold actualIntermediateMassEffectiveScale
  positivity

theorem actualIntermediateMassEffectiveScale_cube {W v : ℝ}
    (_hW : 0 ≤ W) (hv : 0 ≤ v) :
    (actualIntermediateMassEffectiveScale W v)^3=W^2*v := by
  unfold actualIntermediateMassEffectiveScale
  rw [←Real.rpow_natCast _ 3,←Real.rpow_mul (by positivity : 0 ≤ W^2*v)]
  norm_num

theorem actualIntermediateMassEffectiveScale_upper {W v C : ℝ}
    (hW : 0 < W) (hv : 0 < v) (hvupper : v ≤ C*W) :
    actualIntermediateMassEffectiveScale W v ≤ max 1 C*W ∧
    (actualIntermediateMassEffectiveScale W v)^2 ≤ (max 1 C)^2*W^2 := by
  let K := max (1:ℝ) C
  have hK1 : 1 ≤ K := le_max_left _ _
  have hK : 0 < K := zero_lt_one.trans_le hK1
  have hC : C ≤ K := le_max_right _ _
  have HKcube : K ≤ K^3 := by
    have HH := mul_le_mul_of_nonneg_left (one_le_pow₀ hK1 (n:=2)) hK.le
    nlinarith only [HH]
  have Hupper : actualIntermediateMassEffectiveScale W v ≤ K*W := by
    apply (pow_le_pow_iff_left₀ (actualIntermediateMassEffectiveScale_pos hW hv).le
      (mul_pos hK hW).le (by norm_num : (3:ℕ) ≠ 0)).mp
    rw [actualIntermediateMassEffectiveScale_cube hW.le hv.le]
    have HH := mul_le_mul_of_nonneg_left (hvupper.trans
      (mul_le_mul_of_nonneg_right (hC.trans HKcube) hW.le)) (sq_nonneg W)
    nlinarith only [HH]
  refine ⟨Hupper,?_⟩
  simpa only [mul_pow] using pow_le_pow_left₀
    (actualIntermediateMassEffectiveScale_pos hW hv).le Hupper 2

theorem actualIntermediateMassEffectiveScale_lower_product {W v x c : ℝ}
    (hx : 0 < x) (hxW : x ≤ W) (hc : 0 < c) (hvlower : c*x ≤ v) :
    (min 1 c)^2*x^2 ≤ actualIntermediateMassEffectiveScale W v*v := by
  let k := min (1:ℝ) c
  have hk : 0 < k := lt_min zero_lt_one hc
  have hk1 : k ≤ 1 := min_le_left _ _
  have hkc : k ≤ c := min_le_right _ _
  have hW : 0 < W := hx.trans_le hxW
  have hv : 0 < v := (mul_pos hc hx).trans_le hvlower
  have Hkcube : k^3 ≤ c := by
    have HH := mul_le_mul_of_nonneg_left (pow_le_one₀ hk.le hk1 (n:=2)) hk.le
    nlinarith only [HH,hkc]
  have Hlower : k*x ≤ actualIntermediateMassEffectiveScale W v := by
    apply (pow_le_pow_iff_left₀ (mul_pos hk hx).le
      (actualIntermediateMassEffectiveScale_pos hW hv).le (by norm_num : (3:ℕ) ≠ 0)).mp
    rw [actualIntermediateMassEffectiveScale_cube hW.le hv.le]
    have H1 := mul_le_mul_of_nonneg_left hvlower (sq_nonneg x)
    have H2 := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx.le hxW 2) hv.le
    have H3 := mul_le_mul_of_nonneg_right Hkcube (pow_pos hx 3).le
    nlinarith only [H1,H2,H3]
  have Hvlower : k*x ≤ v := (mul_le_mul_of_nonneg_right hkc hx.le).trans hvlower
  have HH := mul_le_mul Hlower Hvlower (mul_pos hk hx).le
    (actualIntermediateMassEffectiveScale_pos hW hv).le
  nlinarith only [HH]

end OAI.SKFluctuations.LaplaceWindowFormalization
