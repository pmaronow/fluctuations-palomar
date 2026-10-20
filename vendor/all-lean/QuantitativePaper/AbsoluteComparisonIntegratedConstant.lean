module

public import QuantitativePaper.AbsoluteComparisonAbsorption

@[expose] public section

/-! Collection of the integrated rates into one model-only constant. -/
noncomputable section
namespace QuantitativePaper
set_option maxHeartbeats 1000000

def absoluteComparisonIntegrationConstant (A B D : ℝ) : ℝ := 5+4*A+66*B*(D+1)

theorem absoluteComparisonIntegrationConstant_pos (A B D : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D) :
    0<absoluteComparisonIntegrationConstant A B D := by unfold absoluteComparisonIntegrationConstant;positivity

theorem absoluteComparison_integrated_budget (N lam e η A B D : ℝ)
    (hN : 1 ≤ N) (hlam : 0<lam) (he : 0 ≤ e) (hη : 0 ≤ η)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hbudget : 4*e ≤ 4/N+Real.log (2+N)/(N*lam)+4*A*N^(-3/4:ℝ)*lam^(-1/2:ℝ)+
      66*B*N^(-2/3:ℝ)*(D+lam^(-1/3:ℝ)*η^(1/11:ℝ))) :
    e ≤ absoluteComparisonIntegrationConstant A B D*
      (N^(-2/3:ℝ)+N^(-3/4:ℝ)*lam^(-1/2:ℝ)+Real.log (2+N)/(N*lam)+
        (N^(-2/3:ℝ)*lam^(-1/3:ℝ))*η^(1/11:ℝ)) := by
  let X:=N^(-2/3:ℝ)
  let Y:=N^(-3/4:ℝ)*lam^(-1/2:ℝ)
  let Z:=Real.log (2+N)/(N*lam)
  let w:=lam^(-1/3:ℝ)*η^(1/11:ℝ)
  let S:=X+Y+Z+X*w
  have hNp : 0<N:=zero_lt_one.trans_le hN
  have hX : 0 ≤ X:=Real.rpow_nonneg hNp.le _
  have hY : 0 ≤ Y:=by dsimp [Y];positivity
  have hZ : 0 ≤ Z:=div_nonneg (Real.log_nonneg (by linarith)) (mul_nonneg hNp.le hlam.le)
  have hw : 0 ≤ w:=by dsimp [w];positivity
  have hXw:=mul_nonneg hX hw
  have hXS : X ≤ S:=by dsimp [S];linarith
  have hYS : Y ≤ S:=by dsimp [S];linarith
  have hZS : Z ≤ S:=by dsimp [S];linarith
  have hwS : X*w ≤ S:=by dsimp [S];linarith
  have hrecip : 1/N ≤ X:=by
    rw [one_div,←Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hN (by norm_num)
  have hDX : X*(D+w) ≤ (D+1)*S:=by
    have hh:=mul_le_mul_of_nonneg_left hXS hD
    nlinarith only [hh,hwS]
  have hfirst : 4/N ≤ 4*S:=by
    calc
      _=4*(1/N):=by ring
      _≤4*S:=mul_le_mul_of_nonneg_left (hrecip.trans hXS) (by norm_num)
  have hthird:=mul_le_mul_of_nonneg_left hDX (mul_nonneg (by norm_num : (0:ℝ) ≤ 66) hB)
  have hquarter:=mul_le_mul_of_nonneg_left hYS (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hA)
  have hbound : e ≤ 4/N+Z+4*A*Y+66*B*X*(D+w):=by
    have hb : 4*e ≤ 4/N+Z+4*A*Y+66*B*X*(D+w):=by
      simpa only [X,Y,Z,w,mul_assoc] using hbudget
    linarith
  have hfinal : e ≤ absoluteComparisonIntegrationConstant A B D*S:=by
    unfold absoluteComparisonIntegrationConstant
    nlinarith only [hbound,hfirst,hZS,hquarter,hthird]
  convert hfinal using 1 <;> dsimp [S,X,Y,Z,w] <;> ring

end QuantitativePaper
