module

public import WallPhysicalIntegratedCost
public import WallClockScaleBounds
public import ConcreteWallRadiusBudget

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal

theorem wall_actual_step_cost_budget {T ε ε0 d rmin s C : ℝ} {n:ℕ}
    (hn:0 < n) (hlogn:1 ≤ Real.log (n:ℝ)) (hs:0 < s) (hC:0 ≤ C) (hd:0 < d)
    (hrmin:0 < rmin) (hr1:rmin ≤ 1) (hr:rmin ≤ 2*C*d)
    (hε:ε∈Ioo 0 T) (hε0:0 < ε0) (hεlower:ε0 ≤ ε) (hdepsilon:d^2 ≤ ε) :
    wallLowStrength T ε/4*(wallPhysicalCostU s (wallMeanScale C d ε) n+
      2*s*(wallLowRadius d rmin ε)^2)+
      (wallLowStrength T ε*wallPhysicalCostV T ε d rmin s (wallMeanScale C d ε) n/4)*
        (-Real.log ((n:ℝ)^(-(10:ℝ))))+
      wallLipschitzConstant T ε d rmin*(n:ℝ)^(-(10:ℝ))  ≤ 
    (3/2:ℝ)*C^2*s*d^6/ε0+
      429000*(10/Real.log 2+2)*C*d/((n:ℝ)*s*rmin)*(Real.log (n:ℝ))^3+
      T*((10/Real.log 2+2)+1)*Real.log (n:ℝ)*(n:ℝ)^(-(10:ℝ)) := by
  have hN : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
  have hlog0 : 0 ≤ Real.log (n:ℝ) := by linarith
  have hlog2 : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  let L := 10/Real.log 2+2
  let A := wallMeanScale C d ε
  let R := wallLowRadius d rmin ε
  let τ := (n:ℝ)^(-(10:ℝ))
  have hL : 0 < L := by dsimp [L]; positivity
  have hτ : 0 < τ := Real.rpow_pos_of_pos hN _
  have hT : 0 < T := hε.1.trans hε.2
  have hcL := wallLowStrength_pos hε
  have hcost := wall_mean_radius_cost_le hε hε0 hεlower hs.le hC hd.le hrmin.le hr
  have hmean : wallLowStrength T ε*s/4*(6*A^2+2*R^2) ≤ (3/2:ℝ)*C^2*s*d^6/ε0 := by
    have hcoef : 0 ≤ wallLowStrength T ε*s/4 := by positivity
    have hfirst := mul_le_mul_of_nonneg_left
      (by nlinarith [sq_nonneg R] : 6*A^2+2*R^2 ≤ 6*(A^2+R^2)) hcoef
    change wallLowStrength T ε*s*(A^2+R^2) ≤ C^2*s*d^6/ε0 at hcost
    calc
      _ ≤ wallLowStrength T ε*s/4*(6*(A^2+R^2)) := hfirst
      _ = (3/2:ℝ)*(wallLowStrength T ε*s*(A^2+R^2)) := by ring
      _ ≤ (3/2:ℝ)*(C^2*s*d^6/ε0) :=
        mul_le_mul_of_nonneg_left hcost (by norm_num)
      _ = _ := by ring
  have hnoise :
      (wallLowStrength T ε*wallPhysicalCostV T ε d rmin s A n/4)*
        (-Real.log ((n:ℝ)^(-(10:ℝ))))=
        429000*L*C*d/((n:ℝ)*s*rmin)*(Real.log (n:ℝ))^3 := by
    unfold wallPhysicalCostV
    rw [Real.log_rpow hN]
    dsimp [A,L,wallMeanScale,wallLowRadius]
    field_simp [hN.ne',hrmin.ne',hd.ne',hs.ne',hε.1.ne',hcL.ne']
    ring
  have hcT : wallLowStrength T ε ≤ T/4 := by
    have hb := wallLowStrength_bounds hε
    linarith [hb.2.1,hb.2.2]
  have hK := wallLipschitzConstant_le_fixed hr1 hrmin.le hε hdepsilon
  have hsmall : wallLowStrength T ε/4*(6*L*Real.log (n:ℝ)+1)+wallLipschitzConstant T ε d rmin ≤ 
      T*(L+1)*Real.log (n:ℝ) := by
    have hcoef := mul_le_mul_of_nonneg_right hcT
      (by positivity : 0 ≤ (6*L*Real.log (n:ℝ)+1)/4)
    have hTL : 0 ≤ T*L*Real.log (n:ℝ) := by positivity
    nlinarith [mul_nonneg hT.le (sub_nonneg.mpr hlogn)]
  have hsmall' := mul_le_mul_of_nonneg_right hsmall hτ.le
  rw [hnoise]
  unfold wallPhysicalCostU
  change wallLowStrength T ε/4*(6*s*A^2+(6*L*Real.log (n:ℝ)+1)*τ+2*s*R^2)+
      429000*L*C*d/((n:ℝ)*s*rmin)*(Real.log (n:ℝ))^3+
      wallLipschitzConstant T ε d rmin*τ ≤ 
    (3/2:ℝ)*C^2*s*d^6/ε0+
      429000*L*C*d/((n:ℝ)*s*rmin)*(Real.log (n:ℝ))^3+
      T*(L+1)*Real.log (n:ℝ)*τ
  linarith

end OAI.SKFluctuations.LaplaceWindowFormalization
