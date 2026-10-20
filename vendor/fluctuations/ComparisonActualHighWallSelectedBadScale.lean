module

public import ComparisonNativeActualBadScaleSelection
public import ComparisonActualHighWallStarProjectionScalars

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 12000000
set_option linter.unusedVariables false
namespace ActualHighWallData
variable {n : ℕ} {m delta cl cu C0 D Bclock : ℝ}

theorem exists_selected_bad_scale_minimum
    (a : ActualHighWallData n delta) (alpha : a.Profile)
    (hmin : ∀beta : a.Profile,a.objective alpha ≤ a.objective beta)
    (hcl : cl ≤ 1) (hcu : 1 ≤ cu) (hsD : a.s ≤ a.d) (hdD : a.d ≤ D)
    (hupper : Real.sqrt (n:ℝ)*a.E ≤ a.d^2)
    (hlower : (n:ℝ)^(-(2:ℝ)/3+m)*a.d ≤ C0*a.E) (hT : a.T ≤ Bclock)
    (hbad : ∃r∈Icc a.d 1,alpha.val.val r < cl*r ∨ cu*r < alpha.val.val r) :
    ∃M : ActualHighWallOverlapMinimum n m delta cl cu 2 C0 1 D Bclock,
      M.data=a ∧ HEq M.alpha alpha ∧ a.d ≤ M.xs ∧ M.xs ≤ 1 ∧
      M.z=min (2*M.xs) 1 ∧
      (M.alpha.val.val M.xs < cl*M.xs ∨ cu*M.xs < M.alpha.val.val M.xs) := by
  obtain ⟨x,hx,hBadX,hOuter⟩ := comparison_exists_bad_scale_with_regular_outer alpha.val.val
    a.hd hcl hcu alpha.property.2.1 (by simpa only [min_eq_left a.hd1] using hbad)
  have hx0 : 0 < x := a.hd.trans_le hx.1
  have hscale : comparisonLowerScale n a.E a.d ≤ x := by
    apply le_trans _ hx.1
    unfold comparisonLowerScale
    exact (div_le_iff₀ a.hd).mpr (by simpa only [pow_two] using hupper)
  have htestD : (n:ℝ)*a.E^2 ≤ a.d^4 := by
    have H:=pow_le_pow_left₀ (mul_nonneg (Real.sqrt_nonneg (n:ℝ)) a.hE.le) hupper 2
    rw [mul_pow,Real.sq_sqrt a.hN.le] at H
    simpa only [←pow_mul] using H
  have hgx : 0 < a.g x := laplaceComparisonStrength_pos a.d (sq_pos_of_pos a.hd) x
  have Hmono := (laplaceComparisonStrength_monotonicities a.hd.ne' (sq_pos_of_pos a.hd)
    (r₀:=0) le_rfl).2 ⟨a.hd.le,a.hd1⟩ ⟨hx0.le,hx.2⟩ hx.1
  change a.g a.d*a.d ≤ a.g x*x at Hmono
  rw [a.strength_at_scale] at Hmono
  have Hfirst := mul_le_mul_of_nonneg_right Hmono a.hd.le
  have Hsecond := mul_le_mul_of_nonneg_left hx.1 (mul_nonneg hgx.le hx0.le)
  have htestX : (n:ℝ)*a.E^2 ≤ a.g x*x^2 := by
    nlinarith only [htestD,Hfirst,Hsecond]
  have hRmin : a.rmin ≤ min (2*x) 1 := by
    apply le_min _ a.hr
    linarith only [a.hrbounds.2.1,a.hd,hx.1]
  let M : ActualHighWallOverlapMinimum n m delta cl cu 2 C0 1 D Bclock := {
    data:=a,alpha:=alpha,minimum:=hmin,xs:=x,z:=min (2*x) 1,
    hxs:=hx0,hscale:=hscale,hsxs:=hsD.trans hx.1,hz:=⟨hRmin,min_le_right _ _⟩,
    hzxs:=min_le_left _ _,hdD:=hdD,hupper:=hupper,hlower:=hlower,
    htest:=by simpa only [one_mul] using htestX,regular:=hOuter,hT:=hT }
  exact ⟨M,rfl,HEq.rfl,hx.1,hx.2,rfl,hBadX⟩

end ActualHighWallData
end OAI.SKFluctuations.LaplaceWindowFormalization
