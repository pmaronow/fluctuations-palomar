module

public import ComparisonNativeUpwardChildBarrierGain
public import ComparisonActualChildData

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 7000000

theorem actual_child_strength_dominates_weak_parent
    {d lam x y c0 C eta:ℝ} (hd:0 < d) (hlam:0 < lam) (hld:lam ≤ d^2)
    (hx:0 < x) (hy:0 < y) (hc0:0 < c0) (hC:0 < C) (hyC:y ≤ C*x)
    (heta:0 ≤ eta) (heta1:eta ≤ 1)
    (hweak:laplaceComparisonStrength d lam x ≤ eta^3*x^2)
    (hbudget:eta^2 ≤ min (c0^2) (c0^3/C)) :
    laplaceComparisonStrength d lam 0 ≤
      laplaceComparisonStrength (c0*x) ((c0*x)^2) y := by
  have hgap:laplaceComparisonStrength d lam x*x ≤ eta^3*x^3:=by
    have hh:=mul_le_mul_of_nonneg_right hweak hx.le
    nlinarith
  have hparent:=actual_strength_ceiling_of_child_gap hd hlam hld hx hx le_rfl heta heta1 hgap
  have hchild:=laplaceComparisonStrength_lower (mul_pos hc0 hx) (sq_pos_of_pos (mul_pos hc0 hx)) hy
  have htail:(c0^3/C)*x^2 ≤ (c0*x)^3/y:=by
    have hh:=div_le_div_of_nonneg_left (pow_nonneg (mul_nonneg hc0.le hx.le) 3) hy (hyC)
    have he:(c0*x)^3/(C*x)=(c0^3/C)*x^2:=by field_simp
    rw [he] at hh
    exact hh
  have hmin:min (c0^2) (c0^3/C)*x^2 ≤ min ((c0*x)^2) ((c0*x)^3/y):=by
    rw [min_mul_of_nonneg _ _ (sq_nonneg x)]
    apply min_le_min
    · simp only [mul_pow]
      exact le_rfl
    · exact htail
  have hparent0:laplaceComparisonStrength d lam 0 ≤ eta^2*x^2:=
    (laplaceComparisonStrength_le d hlam.le 0).trans hparent
  have hs:=mul_le_mul_of_nonneg_right hbudget (sq_nonneg x)
  exact hparent0.trans (hs.trans (hmin.trans hchild))

theorem native_upward_small_parent_fraction
    {dp lp dc lc y r w z c:ℝ}
    (hdp:dp≠0) (hlp:0 < lp) (hdc:dc≠0) (hlc:0 < lc)
    (hy:0 < y) (hy1:y ≤ 1) (hr:r∈Icc (0:ℝ) 1) (hz:z∈Icc (0:ℝ) 1)
    (hc:0 < c) (hc1:c ≤ 1) (hsmall:laplaceComparisonStrength dp lp 0 ≤ laplaceComparisonStrength dc lc y) (hrw:r < w)
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
  have herDy:er ≤ Dy:=(laplaceComparisonStrength_monotonicities hdp hlp (r₀:=0) le_rfl).1
    (by norm_num) hr hr.1 |>.trans hsmall
  have heyDy:ey ≤ Dy:=(laplaceComparisonStrength_monotonicities hdp hlp (r₀:=0) le_rfl).1
    (by norm_num) ⟨hy.le,hy1⟩ hy.le |>.trans hsmall
  have hqeq:q=1:=min_eq_left ((le_div_iff₀ hey).mpr (by simpa only [one_mul] using heyDy))
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
    have hh:=mul_le_mul_of_nonneg_right hc1 her.le
    dsimp [t]
    rw [hqeq]
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

theorem exists_native_upward_small_parent_trial {A B cFloor c y a b finish:ℝ} {M:ℝ → ℝ}
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
    (hsmall:laplaceComparisonStrength dp lp 0 ≤ laplaceComparisonStrength dc lc y)
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
    exact native_upward_small_parent_fraction hdp hlp hdc hlc hy hy1
      (comparisonSweepQuantile_bounds hFloor (reciprocalSquareFloor_continuousOn hB) hkc hMm
        (hMp 1 (by norm_num)).le α u) (hZb u hu) hc hc1 hsmall hactive hw hZ
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
