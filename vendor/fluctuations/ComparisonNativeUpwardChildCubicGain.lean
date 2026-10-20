module

public import ComparisonNativeUpwardChildBarrierGain

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 7000000

theorem native_upward_interval_gain (R w Z e:ℝ → ℝ)
    (hR:ContinuousOn R (Icc (0:ℝ) 1)) (hw:ContinuousOn w (Icc (0:ℝ) 1))
    (hZ:ContinuousOn Z (Icc (0:ℝ) 1)) (he:Continuous e)
    (he0:∀u∈Icc (0:ℝ) 1,0 ≤ e (R u))
    {t b finish C:ℝ} (hb:0 ≤ b) (hbf:b ≤ finish) (hf:finish ≤ 1)
    (hactive:∀u∈Icc (0:ℝ) 1,R u < w u → 0 ≤ t*(w u-R u)/(Z u-R u))
    (hband:∀u∈Icc b finish,C ≤ e (R u)*t*(max (R u) (w u)-R u)*(Z u-R u)) :
    C*(finish-b) ≤ ∫u in (0:ℝ)..1,e (R u)*t*(max (R u) (w u)-R u)*(Z u-R u) := by
  let G:=fun u=>e (R u)*t*(max (R u) (w u)-R u)*(Z u-R u)
  have hGc:ContinuousOn G (Icc (0:ℝ) 1):=
    (((he.comp_continuousOn hR).mul continuousOn_const).mul ((continuous_max.comp_continuousOn (hR.prodMk hw)).sub hR)).mul (hZ.sub hR)
  have hGi:IntervalIntegrable G volume 0 1:=hGc.intervalIntegrable_of_Icc zero_le_one
  have hG0:∀u∈Icc (0:ℝ) 1,0 ≤ G u:=by
    intro u hu
    by_cases hclip:R u < w u
    · have ho:=hactive u hu hclip
      have heq:t*(w u-R u)*(Z u-R u)=
          (t*(w u-R u)/(Z u-R u))*(Z u-R u)^2:=by
        by_cases hzero:Z u-R u=0
        · simp only [hzero,mul_zero,pow_two,zero_mul,div_zero]
        · field_simp
      have hh:=mul_nonneg (he0 u hu) (mul_nonneg ho (sq_nonneg (Z u-R u)))
      dsimp only [G]
      rw [max_eq_right hclip.le]
      calc
        0 ≤ e (R u)*((t*(w u-R u)/(Z u-R u))*(Z u-R u)^2):=hh
        _ = e (R u)*t*(w u-R u)*(Z u-R u):=by rw [←heq];ring
    · dsimp only [G]
      rw [max_eq_left (le_of_not_gt hclip),sub_self,mul_zero,zero_mul]
  have hsub:Icc b finish⊆Icc (0:ℝ) 1:=Icc_subset_Icc hb hf
  have hGib:IntervalIntegrable G volume b finish:=
    (hGc.mono hsub).intervalIntegrable_of_Icc hbf
  have hlocal:(∫_ in b..finish,C) ≤ ∫u in b..finish,G u:=
    intervalIntegral.integral_mono_on hbf intervalIntegrable_const hGib hband
  have hglobal:(∫u in b..finish,G u) ≤ ∫u in (0:ℝ)..1,G u:=by
    apply intervalIntegral.integral_mono_interval hb hbf hf _ hGi
    change ∀ᵐu∂volume.restrict (Ioc (0:ℝ) 1),0 ≤ G u
    rw [ae_restrict_iff' measurableSet_Ioc]
    exact Eventually.of_forall (fun u hu=>hG0 u ⟨hu.1.le,hu.2⟩)
  have hh:=hlocal.trans hglobal
  change C*(finish-b) ≤ ∫u in (0:ℝ)..1,G u
  simpa only [intervalIntegral.integral_const,smul_eq_mul,mul_comm] using hh

theorem exists_native_upward_child_cubic_gain {A B cFloor c y a b finish q:ℝ} {M:ℝ → ℝ}
    (hA:0 < A) (hB:0 < B) (hFloor:0 < cFloor)
    (hkc:∀r∈Icc (0:ℝ) 1,cFloor ≤ reciprocalSquareFloor A B r)
    (hMc:Continuous M) (hMm:MonotoneOn M (Icc (0:ℝ) 1))
    (hMp:∀u∈Icc (0:ℝ) 1,0 < M u)
    (α:inverseIntegralConstraints 0 0 (reciprocalSquareFloor A B) M)
    (Z:ℝ → ℝ) (hZc:ContinuousOn Z (Icc (0:ℝ) 1)) (hZm:MonotoneOn Z (Icc (0:ℝ) 1)) (hZb:∀u∈Icc (0:ℝ) 1,Z u∈Icc (0:ℝ) 1)
    {dp lp dc lc:ℝ} (hdp:dp≠0) (hlp:0 < lp) (hdc:dc≠0) (hlc:0 < lc)
    (hc:0 < c) (hc1:c ≤ 1) (hy:0 < y) (ha:0 ≤ a) (hab:a < b) (hbf:b ≤ finish) (hf:finish ≤ 1) (hq:0 ≤ q) (hwidth:q*y ≤ finish-b)
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
      (3*c*q/100)*min (laplaceComparisonStrength dp lp y) (laplaceComparisonStrength dc lc y)*y^3 ≤
        ∫u in (0:ℝ)..1,laplaceComparisonStrength dp lp (R u)*t*(max (R u) (w u)-R u)*(Z u-R u) := by
  let R:=comparisonSweepQuantile hFloor (reciprocalSquareFloor_continuousOn hB)
    hkc hMm (hMp 1 (by norm_num)).le α
  let t:=c/100*min 1 (laplaceComparisonStrength dc lc y/laplaceComparisonStrength dp lp y)
  let w:=upwardRampBarrier M a b (2*y/(b-a))
  obtain ⟨γ,hγ,hmove,hpoint⟩:=exists_native_upward_child_trial hA hB hFloor hkc hMc hMm hMp α Z
    hZm hZb hdp hlp hdc hlc hc hc1 hy ha hab hbf hf hforce hspeed hZlarge hRlower hRupper
  refine ⟨γ,hγ,hmove,?_⟩
  have hRc:ContinuousOn R (Icc (0:ℝ) 1):=
    (comparisonSweepQuantile_lipschitzOn hFloor (reciprocalSquareFloor_continuousOn hB) hkc hMm
      (hMp 1 (by norm_num)).le α).continuousOn
  obtain ⟨Cw,hw⟩:=upwardRampBarrier_lipschitz hMc hMm hMp a b (2*y/(b-a))
  have hec:Continuous (laplaceComparisonStrength dp lp):=(laplaceComparisonStrength_contDiff dp lp).continuous
  have hconst:0 ≤ (3*c/100)*min (laplaceComparisonStrength dp lp y) (laplaceComparisonStrength dc lc y)*y^2:=by
    have hey:=laplaceComparisonStrength_pos dp hlp y
    have hDy:=laplaceComparisonStrength_pos dc hlc y
    positivity
  have hbudget:=native_upward_interval_gain R w Z (laplaceComparisonStrength dp lp) hRc hw.continuousOn hZc hec
    (fun u _=>(laplaceComparisonStrength_pos dp hlp (R u)).le) (ha.trans hab.le) hbf hf
    (fun u hu hactive=>(hmove u hu hactive).1) hpoint
  have hwidth':((3*c/100)*min (laplaceComparisonStrength dp lp y) (laplaceComparisonStrength dc lc y)*y^2)*(q*y) ≤
      ((3*c/100)*min (laplaceComparisonStrength dp lp y) (laplaceComparisonStrength dc lc y)*y^2)*(finish-b):=
    mul_le_mul_of_nonneg_left hwidth hconst
  have hh:=hwidth'.trans hbudget
  convert hh using 1 <;> ring

end OAI.SKFluctuations.LaplaceWindowFormalization
