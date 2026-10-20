module

public import ComparisonNativeCloseThresholdFractions

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 7000000

theorem native_downward_close_fraction {B C dp lp dc lc y r v z rho : ℝ}
    (hB : 0 < B) (hC : 1 ≤ C) (hdp : dp≠0) (hlp : 0 < lp) (hdc : dc≠0) (hlc : 0 < lc)
    (hy : 0 < y) (hy1 : y ≤ 1) (hr : r∈Icc (0:ℝ) 1) (hz : z∈Icc (0:ℝ) 1)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (hvlo : (1-rho/2)*y ≤ v) (hvr : v ≤ r) (hrC : r ≤ C*y) (hzy : z ≤ (1-rho)*y) :
    let t:=(1/C)/100*min 1 (laplaceComparisonStrength dc lc y/laplaceComparisonStrength dp lp y)
    (r-harmonicBarrierRadius B t r v)/(r-z)∈Ico (0:ℝ)
      (laplaceComparisonStrength dc lc z/
        (laplaceComparisonStrength dp lp r+laplaceComparisonStrength dc lc z)) := by
  let ey:=laplaceComparisonStrength dp lp y
  let Dy:=laplaceComparisonStrength dc lc y
  let t:=(1/C)/100*min 1 (Dy/ey)
  have hC0 : 0 < C:=zero_lt_one.trans_le hC
  have hey : 0 < ey:=laplaceComparisonStrength_pos dp hlp y
  have hDy : 0 < Dy:=laplaceComparisonStrength_pos dc hlc y
  have ht0 : 0 ≤ t:=by dsimp [t];positivity
  have ht1 : t ≤ 1 := by
    have hh:=mul_le_mul_of_nonneg_left (min_le_left (1:ℝ) (Dy/ey)) (show 0 ≤ (1/C)/100 by positivity)
    have hi : 1/C ≤ 1 := by simpa only [one_div] using inv_le_one_of_one_le₀ hC
    dsimp [t];nlinarith
  have hvhalf : y/2 ≤ v := by nlinarith
  have hv0 : 0 ≤ v := by linarith
  have hzv : z ≤ v := by nlinarith
  have hzr : z < r := by nlinarith
  have hratio : (r+B)/(v+B) ≤ 2*C := by
    apply (div_le_iff₀ (by linarith : 0 < v+B)).mpr
    have hh:=mul_le_mul_of_nonneg_left hvhalf hC0.le
    have hCB:=mul_le_mul_of_nonneg_right hC hB.le
    nlinarith
  have hs:=harmonic_downward_fraction_bound hB ⟨ht0,ht1⟩ hv0 hvr hzv hzr hratio
  have hyhalf : y/2∈Icc (0:ℝ) 1 := ⟨by positivity,by linarith⟩
  have her : laplaceComparisonStrength dp lp r ≤ 2*ey := by
    have h1:= (laplaceComparisonStrength_monotonicities hdp hlp (r₀:=0) le_rfl).1
      hyhalf hr (hvhalf.trans hvr)
    have h2:= (laplaceComparisonStrength_monotonicities hdp hlp (r₀:=0) le_rfl).2
      hyhalf ⟨hy.le,hy1⟩ (by linarith)
    change laplaceComparisonStrength dp lp (y/2)*(y/2) ≤ ey*y at h2
    nlinarith
  have hDz : Dy ≤ laplaceComparisonStrength dc lc z :=
    (laplaceComparisonStrength_monotonicities hdc hlc (r₀:=0) le_rfl).1
      hz ⟨hy.le,hy1⟩ (by nlinarith)
  refine ⟨hs.1,?_⟩
  apply strict_movement_fraction_of_scale (C:=2*C) (Ce:=2) (Cd:=1) (eta:=(1/C)/100)
    (laplaceComparisonStrength_pos dp hlp r).le hey hDy (by norm_num) (by positivity) (by norm_num)
    (by positivity) her (by simpa using hDz) hs.1
    (by simpa only [t,mul_assoc] using hs.2)
  have he : (2*C)*((1/C)/100)*(2+1:ℝ)=3/50 := by field_simp;norm_num
  rw [he];norm_num

theorem native_downward_close_threshold_gain {B C dp lp dc lc y r v z rho : ℝ}
    (hB : 0 < B) (hC : 1 ≤ C) (hdp : dp≠0) (hlp : 0 < lp) (hlc : 0 < lc)
    (hy : 0 < y) (hy1 : y ≤ 1) (hr : r∈Icc (0:ℝ) 1)
    (hrho : 0 < rho) (_hrho1 : rho ≤ 1) (hv : 0 ≤ v)
    (hvupper : v ≤ (1-rho/4)*y) (hrlower : y ≤ r) (hrC : r ≤ C*y)
    (hzy : z ≤ (1-rho)*y) :
    let t:=(1/C)/100*min 1 (laplaceComparisonStrength dc lc y/laplaceComparisonStrength dp lp y)
    (rho^2/(400*C^2))*min (laplaceComparisonStrength dp lp y) (laplaceComparisonStrength dc lc y)*y^2 ≤
      laplaceComparisonStrength dp lp r*(r-harmonicBarrierRadius B t r v)*(r-z) := by
  let ey:=laplaceComparisonStrength dp lp y
  let Dy:=laplaceComparisonStrength dc lc y
  let t:=(1/C)/100*min 1 (Dy/ey)
  have hC0 : 0 < C:=zero_lt_one.trans_le hC
  have hey : 0 < ey:=laplaceComparisonStrength_pos dp hlp y
  have hDy : 0 < Dy:=laplaceComparisonStrength_pos dc hlc y
  have ht0 : 0 ≤ t:=by dsimp [t];positivity
  have ht1 : t ≤ 1 := by
    have hh:=mul_le_mul_of_nonneg_left (min_le_left (1:ℝ) (Dy/ey)) (show 0 ≤ (1/C)/100 by positivity)
    have hi : 1/C ≤ 1 := by simpa only [one_div] using inv_le_one_of_one_le₀ hC
    dsimp [t];nlinarith
  have her : ey/C ≤ laplaceComparisonStrength dp lp r := by
    have hf : ey*y ≤ laplaceComparisonStrength dp lp r*r :=
      (laplaceComparisonStrength_monotonicities hdp hlp (r₀:=0) le_rfl).2 ⟨hy.le,hy1⟩ hr hrlower
    have hh:=mul_le_mul_of_nonneg_left hrC (laplaceComparisonStrength_pos dp hlp r).le
    apply (div_le_iff₀ hC0).mpr
    nlinarith
  have hvr : v ≤ r := by nlinarith
  have hdisp : t*(r-v) ≤ r-harmonicBarrierRadius B t r v :=
    (harmonicBarrierRadius_displacement_bounds hB ⟨ht0,ht1⟩ hv hvr).1
  have hgap : (rho/4)*y ≤ r-v := by nlinarith
  have hzGap : rho*y ≤ r-z := by nlinarith
  have hdd : t*((rho/4)*y) ≤ r-harmonicBarrierRadius B t r v :=
    (mul_le_mul_of_nonneg_left hgap ht0).trans hdisp
  have hmul:=mul_le_mul hdd hzGap (by positivity)
    ((by positivity : 0 ≤ t*((rho/4)*y)).trans hdd)
  have hg:=mul_le_mul her hmul (by positivity : 0 ≤ t*((rho/4)*y)*(rho*y))
    (laplaceComparisonStrength_pos dp hlp r).le
  have he : t*ey=((1/C)/100)*min ey Dy:=native_barrier_fraction_strength (c:=1/C) hey
  have heq : (ey/C)*(t*((rho/4)*y)*(rho*y))=(rho^2/(400*C^2))*min ey Dy*y^2 := by
    calc
      _ = (t*ey)*rho^2*y^2/(4*C) := by ring
      _ = _ := by rw [he];field_simp;ring
  rw [heq] at hg
  convert hg using 1; ring

end OAI.SKFluctuations.LaplaceWindowFormalization
