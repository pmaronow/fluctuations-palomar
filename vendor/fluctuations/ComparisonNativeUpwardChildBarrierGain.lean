module

public import UpwardRampBarrier
public import DownwardRampSupport
public import ConcreteComparisonStrength
public import ComparisonAveragedChildMovementGain

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 7000000

theorem native_barrier_fraction_strength {ey Dy c:ℝ} (hey:0 < ey) :
    (c/100*min 1 (Dy/ey))*ey=(c/100)*min ey Dy := by
  rw [mul_assoc,min_mul_of_nonneg _ _ hey.le,one_mul,div_mul_cancel₀ _ hey.ne']

theorem native_upward_unbounded_child_fraction
    {dp lp dc lc y r w z c:ℝ}
    (hdp:dp≠0) (hlp:0 < lp) (hdc:dc≠0) (hlc:0 < lc)
    (hy:0 < y) (hy1:y ≤ 1) (hr:r∈Icc (0:ℝ) 1) (hz:z∈Icc (0:ℝ) 1)
    (hc:0 < c) (hc1:c ≤ 1) (hrlower:c*y ≤ r) (hrw:r < w)
    (hw:w ≤ (9/4:ℝ)*y) (hzlarge:4*y ≤ z) :
    let ey:=laplaceComparisonStrength dp lp y
    let Dy:=laplaceComparisonStrength dc lc y
    let t:=c/100*min 1 (Dy/ey)
    t*(w-r)/(z-r)∈Ico (0:ℝ)
      (laplaceComparisonStrength dc lc z/
        (laplaceComparisonStrength dp lp r+laplaceComparisonStrength dc lc z)) := by
  let ey:=laplaceComparisonStrength dp lp y
  let Dy:=laplaceComparisonStrength dc lc y
  let er:=laplaceComparisonStrength dp lp r
  let Dz:=laplaceComparisonStrength dc lc z
  let q:=min 1 (Dy/ey)
  let t:=c/100*q
  have hey:0 < ey:=laplaceComparisonStrength_pos dp hlp y
  have hDy:0 < Dy:=laplaceComparisonStrength_pos dc hlc y
  have her:0 < er:=laplaceComparisonStrength_pos dp hlp r
  have hDz:0 < Dz:=laplaceComparisonStrength_pos dc hlc z
  have hq0:0 ≤ q:=le_min zero_le_one (div_nonneg hDy.le hey.le)
  have hq1:q ≤ 1:=min_le_left _ _
  have hqey:q*ey ≤ Dy:=by
    have hh:=mul_le_mul_of_nonneg_right (min_le_right (1:ℝ) (Dy/ey)) hey.le
    simpa only [q,div_mul_cancel₀ _ hey.ne'] using hh
  have hcy:c*y∈Icc (0:ℝ) 1:=⟨mul_nonneg hc.le hy.le,by nlinarith⟩
  have hcyy:c*y ≤ y:=by nlinarith
  have hefield:laplaceComparisonStrength dp lp (c*y)*(c*y) ≤ ey*y:=
    (laplaceComparisonStrength_monotonicities hdp hlp (r₀:=0) le_rfl).2 hcy ⟨hy.le,hy1⟩ hcyy
  have heanti:er ≤ laplaceComparisonStrength dp lp (c*y):=
    (laplaceComparisonStrength_monotonicities hdp hlp (r₀:=0) le_rfl).1 hcy hr hrlower
  have hec:c*er ≤ ey:=by
    have hh:=mul_le_mul_of_nonneg_left heanti (mul_nonneg hc.le hy.le)
    nlinarith
  have hyz:y ≤ z:=by linarith
  have hDanti:Dz ≤ Dy:=(laplaceComparisonStrength_monotonicities hdc hlc (r₀:=0) le_rfl).1 ⟨hy.le,hy1⟩ hz hyz
  have hDfield:Dy*y ≤ Dz*z:=(laplaceComparisonStrength_monotonicities hdc hlc (r₀:=0) le_rfl).2 ⟨hy.le,hy1⟩ hz hyz
  have hgap:0 < z-r:=by linarith
  have hgeometry:(7/16:ℝ)*z ≤ z-r:=by linarith
  have hDgap:(7/16:ℝ)*Dy*y ≤ Dz*(z-r):=by
    have hh:=mul_le_mul_of_nonneg_left hgeometry hDz.le
    nlinarith
  have ht0:0 ≤ t:=by dsimp [t];positivity
  have htE:100*t*er ≤ Dy:=by
    have hh:=mul_le_mul_of_nonneg_left hec hq0
    dsimp [t]
    nlinarith
  have htD:100*t*Dz ≤ Dy:=by
    have hh:=mul_le_mul_of_nonneg_left hDanti hq0
    have hj:=mul_le_mul_of_nonneg_left hh hc.le
    dsimp [t]
    nlinarith [mul_le_mul_of_nonneg_left hq1 hDy.le]
  have hsum:100*t*(er+Dz) ≤ 2*Dy:=by nlinarith
  have hwr:0 < w-r:=sub_pos.mpr hrw
  have hwrUpper:w-r ≤ (9/4:ℝ)*y:=by linarith [hr.1]
  have hcost:100*(t*(w-r)*(er+Dz)) ≤ (9/2:ℝ)*Dy*y:=by
    have hh:=mul_le_mul_of_nonneg_right hsum hwr.le
    have hj:=mul_le_mul_of_nonneg_left hwrUpper hDy.le
    nlinarith
  have hstrict:t*(w-r)*(er+Dz) < Dz*(z-r):=by nlinarith [mul_pos hDy hy]
  change t*(w-r)/(z-r)∈Ico (0:ℝ) (Dz/(er+Dz))
  exact ⟨div_nonneg (mul_nonneg ht0 hwr.le) hgap.le,
    (div_lt_div_iff₀ hgap (add_pos her hDz)).mpr hstrict⟩

theorem native_upward_threshold_gain {dp lp dc lc y r w z c:ℝ}
    (hdp:dp≠0) (hlp:0 < lp) (hlc:0 < lc) (hy:0 < y) (hy1:y ≤ 1)
    (hr:r∈Icc (0:ℝ) y) (hc:0 ≤ c) (hw:2*y ≤ w) (hz:4*y ≤ z) :
    (3*c/100)*min (laplaceComparisonStrength dp lp y) (laplaceComparisonStrength dc lc y)*y^2 ≤
      laplaceComparisonStrength dp lp r*
        (c/100*min 1 (laplaceComparisonStrength dc lc y/laplaceComparisonStrength dp lp y))*(w-r)*(z-r) := by
  let ey:=laplaceComparisonStrength dp lp y
  let Dy:=laplaceComparisonStrength dc lc y
  let t:=c/100*min 1 (Dy/ey)
  have hey:0 < ey:=laplaceComparisonStrength_pos dp hlp y
  have hDy:0 < Dy:=laplaceComparisonStrength_pos dc hlc y
  have ht:0 ≤ t:=by dsimp [t];positivity
  have her:ey ≤ laplaceComparisonStrength dp lp r:=
    (laplaceComparisonStrength_monotonicities hdp hlp (r₀:=0) le_rfl).1
      ⟨hr.1,hr.2.trans hy1⟩ ⟨hy.le,hy1⟩ hr.2
  have hwr:y ≤ w-r:=by linarith [hr.2]
  have hzr:3*y ≤ z-r:=by linarith [hr.2]
  have hprod:y*(3*y) ≤ (w-r)*(z-r):=
    mul_le_mul hwr hzr (by positivity) (by linarith)
  have hh:=mul_le_mul (mul_le_mul_of_nonneg_right her ht) hprod
    (by positivity : 0 ≤ y*(3*y))
    (mul_nonneg (laplaceComparisonStrength_pos dp hlp r).le ht)
  have he:t*ey=(c/100)*min ey Dy:=native_barrier_fraction_strength hey
  dsimp only [t,ey,Dy] at he hh
  nlinarith

theorem exists_native_upward_child_trial {A B cFloor c y a b finish:ℝ} {M:ℝ → ℝ}
    (hA:0 < A) (hB:0 < B) (hFloor:0 < cFloor)
    (hkc:∀r∈Icc (0:ℝ) 1,cFloor ≤ reciprocalSquareFloor A B r)
    (hMc:Continuous M) (hMm:MonotoneOn M (Icc (0:ℝ) 1))
    (hMp:∀u∈Icc (0:ℝ) 1,0 < M u)
    (α:inverseIntegralConstraints 0 0 (reciprocalSquareFloor A B) M)
    (Z:ℝ → ℝ) (hZm:MonotoneOn Z (Icc (0:ℝ) 1)) (hZb:∀u∈Icc (0:ℝ) 1,Z u∈Icc (0:ℝ) 1)
    {dp lp dc lc:ℝ} (hdp:dp≠0) (hlp:0 < lp) (hdc:dc≠0) (hlc:0 < lc)
    (hc:0 < c) (hc1:c ≤ 1) (hy:0 < y) (ha:0 ≤ a) (hab:a < b) (hbf:b ≤ finish) (hf:finish ≤ 1)
    (hforce:inverseCapPrimitive M 1 ≤ y/4)
    (hspeed:(M 0)⁻¹+2*y/(b-a) ≤ B^2/A)
    (hZlarge:4*y ≤ Z a)
    (hRlower:∀u∈Icc a 1,c*y ≤ comparisonSweepQuantile hFloor (reciprocalSquareFloor_continuousOn hB)
      hkc hMm (hMp 1 (by norm_num)).le α u)
    (hRupper:∀u∈Icc b finish,comparisonSweepQuantile hFloor (reciprocalSquareFloor_continuousOn hB)
      hkc hMm (hMp 1 (by norm_num)).le α u ≤ y) :
    let R:=comparisonSweepQuantile hFloor (reciprocalSquareFloor_continuousOn hB)
      hkc hMm (hMp 1 (by norm_num)).le α
    let t:=c/100*min 1 (laplaceComparisonStrength dc lc y/laplaceComparisonStrength dp lp y)
    let w:=upwardRampBarrier M a b (2*y/(b-a))
    ∃γ:inverseIntegralConstraints 0 0 (reciprocalSquareFloor A B) M,
      (∀u∈Icc (0:ℝ) 1,γ.val.val ((1-t)*R u+t*max (R u) (w u))=u) ∧
      (∀u∈Icc (0:ℝ) 1,R u < w u →
        t*(w u-R u)/(Z u-R u)∈Ico (0:ℝ)
          (laplaceComparisonStrength dc lc (Z u)/
            (laplaceComparisonStrength dp lp (R u)+laplaceComparisonStrength dc lc (Z u)))) ∧
      (∀u∈Icc b finish,(3*c/100)*min (laplaceComparisonStrength dp lp y) (laplaceComparisonStrength dc lc y)*y^2 ≤
        laplaceComparisonStrength dp lp (R u)*t*(max (R u) (w u)-R u)*(Z u-R u)) := by
  let R:=comparisonSweepQuantile hFloor (reciprocalSquareFloor_continuousOn hB)
    hkc hMm (hMp 1 (by norm_num)).le α
  let t:=c/100*min 1 (laplaceComparisonStrength dc lc y/laplaceComparisonStrength dp lp y)
  let speed:=2*y/(b-a)
  let w:=upwardRampBarrier M a b speed
  have haI:a∈Icc (0:ℝ) 1:=⟨ha,hab.le.trans (hbf.trans hf)⟩
  have hy1:y ≤ 1:=by linarith [(hZb a haI).2]
  have hy4:y ≤ 1/4:=by linarith [(hZb a haI).2]
  have hey:0 < laplaceComparisonStrength dp lp y:=laplaceComparisonStrength_pos dp hlp y
  have hDy:0 < laplaceComparisonStrength dc lc y:=laplaceComparisonStrength_pos dc hlc y
  have ht0:0 ≤ t:=by dsimp [t];positivity
  have ht1:t ≤ 1:=by
    have hh:=mul_le_mul_of_nonneg_left
      (min_le_left (1:ℝ) (laplaceComparisonStrength dc lc y/laplaceComparisonStrength dp lp y))
      (by positivity : 0 ≤ c/100)
    dsimp [t]
    nlinarith
  have hspeed0:0 ≤ speed:=by dsimp [speed];positivity
  have hspeedmass:speed*(b-a)=2*y:=by
    dsimp [speed]
    exact div_mul_cancel₀ _ (sub_pos.mpr hab).ne'
  have hrise:inverseCapPrimitive M 1+speed*(b-a) ≤ 1:=by rw [hspeedmass];linarith
  obtain ⟨γ,hγ⟩:=explicit_upward_ramp_trial hA hB hFloor ⟨ht0,ht1⟩ hkc hMc hMm hMp
    ha hab.le hspeed0 hrise hspeed α
  refine ⟨γ,hγ,?_,?_⟩
  · intro u hu hactive
    change R u < w u at hactive
    have hau:a < u:=by
      by_contra hn
      have hw0:truncatedBarrierRamp a b u=0:=truncatedBarrierRamp_before (le_of_not_gt hn)
      have hw:w u=inverseCapPrimitive M u:=by simp only [w,upwardRampBarrier,hw0,mul_zero,add_zero]
      have hcap:inverseCapPrimitive M u ≤ R u:=(comparisonSweepQuantile_cap_envelopes hFloor
        (reciprocalSquareFloor_continuousOn hB) hkc hMc hMm hMp α hu).1
      rw [hw] at hactive
      exact (not_lt_of_ge hcap) hactive
    have hZ:4*y ≤ Z u:=hZlarge.trans (hZm haI hu hau.le)
    have hw:w u ≤ (9/4:ℝ)*y:=by
      have hh: w u ≤ inverseCapPrimitive M 1+speed*(b-a):=
        (upwardRampBarrier_bounds hMc hMm hMp hab.le hspeed0 hu).2
      rw [hspeedmass] at hh
      linarith
    exact native_upward_unbounded_child_fraction hdp hlp hdc hlc hy hy1
      (comparisonSweepQuantile_bounds hFloor (reciprocalSquareFloor_continuousOn hB) hkc hMm
        (hMp 1 (by norm_num)).le α u) (hZb u hu) hc hc1 (hRlower u ⟨hau.le,hu.2⟩) hactive hw hZ
  · intro u hu
    have huI:u∈Icc (0:ℝ) 1:=⟨ha.trans (hab.le.trans hu.1),hu.2.trans hf⟩
    have hR:R u∈Icc (0:ℝ) y:=⟨(comparisonSweepQuantile_bounds hFloor
      (reciprocalSquareFloor_continuousOn hB) hkc hMm (hMp 1 (by norm_num)).le α u).1,hRupper u hu⟩
    have hw:2*y ≤ w u:=by
      have he:truncatedBarrierRamp a b u=b-a:=truncatedBarrierRamp_after hab.le hu.1
      have hp:0 ≤ inverseCapPrimitive M u:=inverseCapPrimitive_nonneg hMc hMm hMp huI
      dsimp only [w,upwardRampBarrier]
      rw [he,hspeedmass]
      linarith
    have hZ:4*y ≤ Z u:=hZlarge.trans (hZm haI huI (hab.le.trans hu.1))
    have hRw:R u ≤ w u:=by linarith [hR.2]
    rw [max_eq_right hRw]
    exact native_upward_threshold_gain hdp hlp hlc hy hy1 hR hc.le hw hZ

end OAI.SKFluctuations.LaplaceWindowFormalization
