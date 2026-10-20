module

public import ComparisonNativeSuccessfulChildBarrier

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 7000000

theorem native_upward_close_fraction {dp lp dc lc y r w z c rho : ℝ}
    (hdp : dp≠0) (hlp : 0 < lp) (hdc : dc≠0) (hlc : 0 < lc)
    (hy : 0 < y) (hy1 : y ≤ 1) (hr : r∈Icc (0:ℝ) 1) (hz : z∈Icc (0:ℝ) 1)
    (hc : 0 < c) (hc1 : c ≤ 1) (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (hroute : c*y ≤ r ∨ laplaceComparisonStrength dp lp 0 ≤ laplaceComparisonStrength dc lc y)
    (hrw : r < w) (hw : w ≤ (1-rho/4)*y) (hyz : y ≤ z) :
    let t:=(c*rho)/100*min 1 (laplaceComparisonStrength dc lc y/laplaceComparisonStrength dp lp y)
    t*(w-r)/(z-r)∈Ico (0:ℝ)
      (laplaceComparisonStrength dc lc z/
        (laplaceComparisonStrength dp lp r+laplaceComparisonStrength dc lc z)) := by
  let ey:=laplaceComparisonStrength dp lp y
  let Dy:=laplaceComparisonStrength dc lc y
  let er:=laplaceComparisonStrength dp lp r
  let Dz:=laplaceComparisonStrength dc lc z
  let q:=min 1 (Dy/ey)
  let t:=(c*rho)/100*q
  have hey : 0 < ey:=laplaceComparisonStrength_pos dp hlp y
  have hDy : 0 < Dy:=laplaceComparisonStrength_pos dc hlc y
  have her : 0 < er:=laplaceComparisonStrength_pos dp hlp r
  have hDz : 0 < Dz:=laplaceComparisonStrength_pos dc hlc z
  have hq0 : 0 ≤ q:=le_min zero_le_one (div_nonneg hDy.le hey.le)
  have hq1 : q ≤ 1:=min_le_left _ _
  have hqey : q*ey ≤ Dy := by
    have hh:=mul_le_mul_of_nonneg_right (min_le_right (1:ℝ) (Dy/ey)) hey.le
    simpa only [q,div_mul_cancel₀ _ hey.ne'] using hh
  have hcer : c*q*er ≤ Dy := by
    rcases hroute with hrlo|hweak
    · have hcy : c*y∈Icc (0:ℝ) 1 := ⟨by positivity,by nlinarith⟩
      have hefield : laplaceComparisonStrength dp lp (c*y)*(c*y) ≤ ey*y :=
        (laplaceComparisonStrength_monotonicities hdp hlp (r₀:=0) le_rfl).2
          hcy ⟨hy.le,hy1⟩ (by nlinarith)
      have heanti : er ≤ laplaceComparisonStrength dp lp (c*y) :=
        (laplaceComparisonStrength_monotonicities hdp hlp (r₀:=0) le_rfl).1 hcy hr hrlo
      have hce : c*er ≤ ey := by
        have hh:=mul_le_mul_of_nonneg_left heanti (mul_nonneg hc.le hy.le)
        nlinarith
      have hh:=mul_le_mul_of_nonneg_left hce hq0
      nlinarith
    · have hle : er ≤ Dy :=
        ((laplaceComparisonStrength_monotonicities hdp hlp (r₀:=0) le_rfl).1
          (by norm_num) hr hr.1).trans hweak
      have hqer:=mul_le_mul_of_nonneg_right hq1 her.le
      have hcer:=mul_le_mul_of_nonneg_left hqer hc.le
      nlinarith [mul_le_mul_of_nonneg_right hc1 her.le]
  have hDanti : Dz ≤ Dy :=
    (laplaceComparisonStrength_monotonicities hdc hlc (r₀:=0) le_rfl).1 ⟨hy.le,hy1⟩ hz hyz
  have hDfield : Dy*y ≤ Dz*z :=
    (laplaceComparisonStrength_monotonicities hdc hlc (r₀:=0) le_rfl).2 ⟨hy.le,hy1⟩ hz hyz
  have hgeom : (rho/4)*z ≤ z-r := by
    have hh:=mul_le_mul_of_nonneg_left hyz (show 0 ≤ 1-rho/4 by linarith)
    nlinarith
  have hgap : 0 < z-r := lt_of_lt_of_le (mul_pos (by positivity) (hy.trans_le hyz)) hgeom
  have hDgap : (rho/4)*Dy*y ≤ Dz*(z-r) := by
    have h1:=mul_le_mul_of_nonneg_left hgeom hDz.le
    have h2:=mul_le_mul_of_nonneg_left hDfield (show 0 ≤ rho/4 by positivity)
    nlinarith
  have ht0 : 0 ≤ t := by dsimp [t];positivity
  have htE : 100*t*er ≤ rho*Dy := by
    have hh:=mul_le_mul_of_nonneg_left hcer hrho.le
    dsimp [t];nlinarith
  have htD : 100*t*Dz ≤ rho*Dy := by
    have h1:=mul_le_mul_of_nonneg_right hq1 hDz.le
    have h2:=mul_le_mul_of_nonneg_left h1 hc.le
    have h3:=mul_le_mul_of_nonneg_right hc1 hDz.le
    have h4:=mul_le_mul_of_nonneg_left (show c*q*Dz ≤ Dy by nlinarith) hrho.le
    dsimp [t];nlinarith
  have hsum : 100*t*(er+Dz) ≤ 2*rho*Dy := by nlinarith
  have hwr : 0 < w-r:=sub_pos.mpr hrw
  have hwrUpper : w-r ≤ y := by nlinarith [hr.1]
  have hcost : 100*(t*(w-r)*(er+Dz)) ≤ 2*rho*Dy*y := by
    have h1:=mul_le_mul_of_nonneg_right hsum hwr.le
    have h2:=mul_le_mul_of_nonneg_left hwrUpper (show 0 ≤ 2*rho*Dy by positivity)
    nlinarith
  have hstrict : t*(w-r)*(er+Dz) < Dz*(z-r) := by
    nlinarith [mul_pos (mul_pos hrho hDy) hy]
  change t*(w-r)/(z-r)∈Ico (0:ℝ) (Dz/(er+Dz))
  exact ⟨div_nonneg (mul_nonneg ht0 hwr.le) hgap.le,
    (div_lt_div_iff₀ hgap (add_pos her hDz)).mpr hstrict⟩

theorem native_upward_close_threshold_gain {dp lp dc lc y r w z c rho : ℝ}
    (hdp : dp≠0) (hlp : 0 < lp) (hlc : 0 < lc)
    (hy : 0 < y) (hy1 : y ≤ 1) (hc : 0 ≤ c) (hrho : 0 < rho) (_hrho1 : rho ≤ 1)
    (hr : 0 ≤ r) (hru : r ≤ (1-rho)*y) (hw : (1-rho/2)*y ≤ w) (hz : y ≤ z) :
    (c*rho^3/200)*min (laplaceComparisonStrength dp lp y) (laplaceComparisonStrength dc lc y)*y^2 ≤
      laplaceComparisonStrength dp lp r*
        ((c*rho)/100*min 1 (laplaceComparisonStrength dc lc y/laplaceComparisonStrength dp lp y))*(w-r)*(z-r) := by
  let ey:=laplaceComparisonStrength dp lp y
  let Dy:=laplaceComparisonStrength dc lc y
  let t:=(c*rho)/100*min 1 (Dy/ey)
  have hey : 0 < ey:=laplaceComparisonStrength_pos dp hlp y
  have hDy : 0 < Dy:=laplaceComparisonStrength_pos dc hlc y
  have hery : ey ≤ laplaceComparisonStrength dp lp r :=
    (laplaceComparisonStrength_monotonicities hdp hlp (r₀:=0) le_rfl).1
      ⟨hr,by nlinarith⟩ ⟨hy.le,hy1⟩ (by nlinarith)
  have ht : 0 ≤ t := by dsimp [t];positivity
  have hwr : (rho/2)*y ≤ w-r := by nlinarith
  have hzr : rho*y ≤ z-r := by nlinarith
  have hp:=mul_le_mul hwr hzr (by positivity) (by nlinarith : 0 ≤ w-r)
  have hh:=mul_le_mul (mul_le_mul_of_nonneg_right hery ht) hp
    (by positivity : 0 ≤ ((rho/2)*y)*(rho*y))
    (mul_nonneg (laplaceComparisonStrength_pos dp hlp r).le ht)
  have he : t*ey=((c*rho)/100)*min ey Dy:=native_barrier_fraction_strength (c:=c*rho) hey
  calc
    _ = (t*ey)*(((rho/2)*y)*(rho*y)) := by rw [he];ring
    _ ≤ _ := by convert hh using 1 <;> ring

end OAI.SKFluctuations.LaplaceWindowFormalization
