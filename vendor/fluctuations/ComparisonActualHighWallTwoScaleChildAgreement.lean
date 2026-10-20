module

public import ComparisonActualHighWallLocalChildTransfer
public import ComparisonActualShiftedOuterAbsoluteDisagreementMass

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 20000000
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
namespace ActualHighWallOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock : ℝ}

 theorem inverse_radius_outer_band_lower_bound_of_parent_scale_high_wall
    {n : ℕ} (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hcu : 0 < cu) (hAz : 0 ≤ Az) {u x left : ℝ} (hu : u∈Icc (0:ℝ) 1)
    (hxs : M.xs ≤ x) (hleft : left ≤ u) (houter : cu*Az*x ≤ left) :
    left/cu ≤ M.data.wallRadius M.alpha u := by
  have Hmass : M.alpha.val.val M.z ≤ u := by
    have H0 := (M.regular M.z ⟨le_rfl,M.hz.2⟩).2
    have H1 := mul_le_mul_of_nonneg_left M.hzxs hcu.le
    have H2 := mul_le_mul_of_nonneg_left hxs (mul_nonneg hcu.le hAz)
    nlinarith only [H0,H1,H2,houter,hleft]
  have HzR := M.data.wallRadius_monotone M.alpha Hmass
  rw [M.data.wallRadius_inverse M.alpha M.hz] at HzR
  have Hreg := (M.regular _ ⟨HzR,(M.data.wallRadius_bounds M.alpha u).2⟩).2
  have Hs : M.data.s ≤ u := by
    have H := M.alpha.val.property.2 M.hz.1
    rw [M.alpha.property.1] at H
    exact H.trans Hmass
  rw [M.data.wallRadius_spec M.alpha ⟨Hs,hu.2⟩] at Hreg
  exact (div_le_div_of_nonneg_right hleft hcu.le).trans
    ((div_le_iff₀ hcu).mpr (by simpa only [mul_comm] using Hreg))

theorem successful_high_only_child_two_scale_agreement
    (hm : 0 < m) (hdelta : 0 < delta) (hcl : 0 < cl) (hcu : 0 < cu)
    (hAz : 0 ≤ Az) (hC0 : 0 < C0) {c0 : ℝ} (hc0 : 0 < c0)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (a : (n : ℕ)→ActualShiftedParentChildCall (dim n+1) delta)
    (x : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ x n) (hxlim : Tendsto x atTop (𝓝 0))
    (hcontext : ∀n,(a n).context=(M n).data.shiftedParentData)
    (hR : ∀n,(a n).R=(M n).data.wallRadius (M n).alpha)
    (hchild : ∀ᶠn in atTop,(a n).childRadius=c0*x n ∧ (a n).childLam=(c0*x n)^2 ∧
      (a n).err ≤ ((dim n+1:ℕ):ℝ)^(20*delta)*
        actualChildErrorBudget (dim n+1) delta c0 (M n).data.d ((M n).data.d^2) (x n))
    (hweak : Tendsto (fun n=>laplaceComparisonStrength (M n).data.d ((M n).data.d^2) (x n)/(x n)^2)
      atTop (𝓝 0))
    (hs : Tendsto (fun n=>(M n).data.s/x n) atTop (𝓝 0))
    (hr : Tendsto (fun n=>(M n).data.rmin/x n) atTop (𝓝 0)) :
    ∀ratio left right eps theta : ℝ,0 < ratio → 0 < left → left < right →
      0 < eps → 0 < theta → ∀ᶠn in atTop,∀y : ℝ,ratio*x n ≤ y → y*right ≤ 1 →
      volume (physicalPropagationDisagreementMassSet ((M n).data.wallRadius (M n).alpha) (a n).Z
        (y*left) (y*right) (eps*y)) < ENNReal.ofReal (theta*y) := by
  intro ratio left right eps theta hratio hleft hlr heps htheta
  have Hdim : Tendsto (fun n=>dim n+1) atTop atTop := (tendsto_add_atTop_nat 1).comp hdim
  have hright : 0 < right := hleft.trans hlr
  have hx n : 0 < x n := (M n).hxs.trans_le (hxs n)
  let C := (Az+1/cl)*(1/ratio+right)
  let far := cu*Az/left+1
  let stepOuter := eps/3
  let stepNear := eps*ratio/3
  have hC : 0 < C := by dsimp only [C]; positivity
  have hfar : 0 < far := by dsimp only [far]; positivity
  have hstepOuter : 0 < stepOuter := by dsimp only [stepOuter]; positivity
  have hstepNear : 0 < stepNear := by dsimp only [stepNear]; positivity
  obtain ⟨Jo,hJo⟩ := exists_nat_gt (C/stepOuter)
  obtain ⟨Jn,hJn⟩ := exists_nat_gt ((C*far)/stepNear)
  have hJo' : C ≤ (Jo:ℝ)*stepOuter := ((div_lt_iff₀ hstepOuter).mp hJo).le
  have hJn' : C*far ≤ (Jn:ℝ)*stepNear := ((div_lt_iff₀ hstepNear).mp hJn).le
  let Cy := ((Jo:ℝ)+2)*stepOuter
  let cMove := min 1 (left/(cu*Cy))
  let ellOuter := theta/(4*((Jo:ℝ)+1))
  let ellNear := (theta*ratio)/(4*((Jn:ℝ)+1))
  have hCy : 0 < Cy := by dsimp only [Cy]; positivity
  have hcMove : 0 < cMove := lt_min zero_lt_one (by positivity)
  have hcMove1 : cMove ≤ 1 := min_le_left _ _
  have hmove : cMove*Cy ≤ left/cu := by
    have H := (le_div_iff₀ (mul_pos hcu hCy)).mp
      (show cMove ≤ left/(cu*Cy) from min_le_right _ _)
    apply (le_div_iff₀ hcu).mpr
    nlinarith only [H]
  have hellOuter : 0 < ellOuter := by dsimp only [ellOuter]; positivity
  have hellNear : 0 < ellNear := by dsimp only [ellNear]; positivity
  obtain ⟨eta,heta,heta1,Hnear⟩ := eventually_actual_shifted_absolute_disagreement_mass_le
    (Dbound:=D) (eps:=stepNear) (ell:=ellNear) Jn hdelta
      (show 0 < 1/C0 by positivity) hm hc0 hstepNear hellNear
  have Houter := eventually_actual_shifted_outer_absolute_disagreement_mass_le
    (Dbound:=D) (ratio:=ratio) (cMove:=cMove) (eps:=stepOuter) (ell:=ellOuter) Jo hdelta
      (show 0 < 1/C0 by positivity) hm hc0 hratio hcMove hcMove1 hstepOuter hellOuter
  have Hweak := hweak.eventually (gt_mem_nhds (pow_pos heta 3))
  have Hunit := hxlim.eventually (gt_mem_nhds zero_lt_one)
  have Hs := hs.eventually (eventually_le_nhds (mul_pos hratio hleft))
  have HrNear := hr.eventually (eventually_le_nhds
    (show 0 < stepNear/(4*((Jn:ℝ)+2)) by positivity))
  have HrOuter := hr.eventually (eventually_le_nhds
    (show 0 < (stepOuter*ratio)/(4*((Jo:ℝ)+2)) by positivity))
  filter_upwards [Hdim.eventually Hnear,Hdim.eventually Houter,Hweak,Hunit,hchild,Hs,HrNear,HrOuter]
    with n hnnear hnouter hnweak hnunit hnchild hsn hrnear hrouter
  intro y hxy hy1
  have hy : 0 < y := (mul_pos hratio (hx n)).trans_le hxy
  have hband0 : 0 ≤ y*left := mul_nonneg hy.le hleft.le
  have hbandUnit u (hu : u∈Icc (y*left) (y*right)) : u∈Icc (0:ℝ) 1 :=
    ⟨hband0.trans hu.1,hu.2.trans hy1⟩
  have hcap u (hu : u∈Icc (y*left) (y*right)) : (a n).R u ≤ C*y := by
    rw [hR n]
    have Hr := (M n).inverse_radius_le_source_mass hcl hAz (hbandUnit u hu)
    have Hx : x n ≤ y/ratio := (le_div_iff₀ hratio).mpr (by simpa only [mul_comm] using hxy)
    have Hm : (M n).xs+u ≤ (1/ratio+right)*y := by
      have H := add_le_add ((hxs n).trans Hx) hu.2
      convert H using 1; ring
    exact Hr.trans (by
      have H := mul_le_mul_of_nonneg_left Hm (show 0 ≤ Az+1/cl by positivity)
      simpa only [C,mul_assoc] using H)
  have he : (a n).context.E=(M n).data.E := by rw [hcontext n];rfl
  have hd : (a n).context.d=(M n).data.d := by rw [hcontext n];rfl
  have hl : (a n).lam=(M n).data.d^2 := by change (a n).context.lam=_;rw [hcontext n];rfl
  have hRn := hR n
  have hsparent : (a n).context.s ≤ y*left := by
    rw [hcontext n]
    change (M n).data.s ≤ _
    have H := (div_le_iff₀ (hx n)).mp hsn
    nlinarith only [H,mul_le_mul_of_nonneg_right hxy hleft.le]
  have horiginNear : (a n).context.r0 ≤ (stepNear*x n)/(4*((Jn:ℝ)+2)) := by
    rw [hcontext n]
    change (M n).data.rmin ≤ _
    exact ((div_le_iff₀ (hx n)).mp hrnear).trans_eq (by ring)
  have horiginOuter : (a n).context.r0 ≤ (stepOuter*y)/(4*((Jo:ℝ)+2)) := by
    rw [hcontext n]
    change (M n).data.rmin ≤ _
    have H := (div_le_iff₀ (hx n)).mp hrouter
    have HY := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hxy hstepOuter.le)
      (show 0 ≤ 4*((Jo:ℝ)+2) by positivity)
    exact H.trans (by convert HY using 1 <;> ring)
  have hlo : (1/C0)*((dim n+1:ℕ):ℝ)^(-(2:ℝ)/3+m)*(a n).context.d ≤ (a n).context.E := by
    rw [hd,he]
    have H := mul_le_mul_of_nonneg_left (M n).hlower (show 0 ≤ 1/C0 by positivity)
    simpa only [←mul_assoc,one_div_mul_cancel hC0.ne',one_mul] using H
  have hdD : (a n).context.d ≤ D := by simpa only [hd] using (M n).hdD
  have hupp : Real.sqrt ((dim n+1:ℕ):ℝ)*(a n).context.E ≤ (a n).context.d^2 := by
    simpa only [hd,he] using (M n).hupper
  have hax : comparisonLowerScale ((dim n+1:ℕ):ℝ) (a n).context.E (a n).context.d ≤ x n := by
    simpa only [hd,he] using (M n).hscale.trans (hxs n)
  have hld : (a n).lam ≤ (a n).context.d^2 := (a n).hld
  have hwe : (a n).e (x n) ≤ eta^3*(x n)^2 := by
    have H := (div_le_iff₀ (sq_pos_of_pos (hx n))).mp hnweak.le
    simpa only [ActualShiftedParentChildCall.e,hd,hl] using H
  have hwe1 : (a n).e (x n) ≤ (x n)^2 := by
    have He : eta^3 ≤ 1 := by simpa using pow_le_pow_left₀ heta.le heta1 3
    exact hwe.trans (by nlinarith [mul_le_mul_of_nonneg_right He (sq_nonneg (x n))])
  have herr : (a n).err ≤ ((dim n+1:ℕ):ℝ)^(20*delta)*
      actualChildErrorBudget (dim n+1) delta c0 (a n).context.d (a n).lam (x n) := by
    simpa only [hd,hl] using hnchild.2.2
  by_cases hnear : y ≤ far*x n
  · have hupper u (hu : u∈Icc (y*left) (y*right)) :
        (a n).R u ≤ (Jn:ℝ)*(stepNear*x n) := by
      have H1 := mul_le_mul_of_nonneg_left hnear hC.le
      have H2 := mul_le_mul_of_nonneg_right hJn' (hx n).le
      exact (hcap u hu).trans (by nlinarith only [H1,H2])
    have Hmass := hnnear (a n) (x n) (y*left) (y*right) hdD hupp hlo
      ⟨hx n,hnunit.le⟩ hax hld hwe hnchild.1 hnchild.2.1 herr horiginNear hsparent hy1 hupper
    have Hsubset : physicalPropagationDisagreementMassSet ((M n).data.wallRadius (M n).alpha) (a n).Z
        (y*left) (y*right) (eps*y) ⊆
        {u | u∈Icc (y*left) (y*right) ∧ 3*(stepNear*x n) ≤ |(a n).Z u-(a n).R u|} := by
      intro u hu
      refine ⟨hu.1,?_⟩
      rw [hRn]
      have H := mul_le_mul_of_nonneg_left hxy heps.le
      dsimp only [stepNear]
      nlinarith only [H,hu.2.le]
    have Hsmall := native_disagreement_measure_coefficient_lt Jn
      (mul_pos htheta hratio) (hx n)
    have Hlast : ENNReal.ofReal ((theta*ratio)*x n) ≤ ENNReal.ofReal (theta*y) :=
      ENNReal.ofReal_le_ofReal (by nlinarith [mul_le_mul_of_nonneg_left hxy htheta.le])
    exact ((measure_mono Hsubset).trans Hmass).trans_lt (Hsmall.trans_le Hlast)
  · have houter : cu*Az*x n ≤ left*y := by
      have H := mul_le_mul_of_nonneg_left (not_le.mp hnear).le hleft.le
      have heq : left*far=cu*Az+left := by dsimp only [far]; field_simp
      rw [←mul_assoc,heq] at H
      nlinarith only [H,mul_pos hleft (hx n)]
    have hupper u (hu : u∈Icc (y*left) (y*right)) :
        (a n).R u ≤ (Jo:ℝ)*(stepOuter*y) := by
      have H := mul_le_mul_of_nonneg_right hJo' hy.le
      exact (hcap u hu).trans (by nlinarith only [H])
    have hlower u (hu : u∈Icc (y*left) 1) :
        cMove*(((Jo:ℝ)+2)*stepOuter*y) ≤ (a n).R u := by
      rw [hRn]
      have Hu : u∈Icc (0:ℝ) 1 := ⟨hband0.trans hu.1,hu.2⟩
      have Hrad := (M n).inverse_radius_outer_band_lower_bound_of_parent_scale_high_wall hcu hAz Hu
        (hxs n) (by simpa only [mul_comm] using hu.1) houter
      have Hmove := mul_le_mul_of_nonneg_right hmove hy.le
      apply le_trans _ Hrad
      dsimp only [Cy] at Hmove
      convert Hmove using 1 <;> ring
    have Hmass := hnouter (a n) (x n) y (y*left) (y*right) hdD hupp hlo
      ⟨hx n,hnunit.le⟩ hax hxy hwe1 hnchild.1 hnchild.2.1 herr horiginOuter hsparent hy1 hupper hlower
    have Hsubset : physicalPropagationDisagreementMassSet ((M n).data.wallRadius (M n).alpha) (a n).Z
        (y*left) (y*right) (eps*y) ⊆
        {u | u∈Icc (y*left) (y*right) ∧ 3*(stepOuter*y) ≤ |(a n).Z u-(a n).R u|} := by
      intro u hu
      refine ⟨hu.1,?_⟩
      rw [hRn]
      dsimp only [stepOuter]
      nlinarith only [hu.2.le]
    exact ((measure_mono Hsubset).trans Hmass).trans_lt
      (native_disagreement_measure_coefficient_lt Jo htheta hy)

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
