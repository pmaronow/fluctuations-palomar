module

public import ComparisonNativeOuterAbsoluteDisagreementMass
public import ComparisonNativeAbsoluteDisagreementMass
public import ComparisonNativeActualMinimumChild
public import ComparisonNativeActualOuterInverseGeometry

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 22000000
namespace NativeOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem actual_minimum_successful_child_bounded_two_scale_agreement
    (hm : 0 < m) (hdelta : 0 < delta) (hcl : 0 < cl) (hcu : 0 < cu)
    (hAz : 0 ≤ Az) (hC0 : 0 < C0) {c0 : ℝ} (hc0 : 0 < c0)
    (N : ℕ→ℕ) (hN : Tendsto N atTop atTop)
    (M : (n : ℕ)→NativeOverlapMinimum (N n) m delta cl cu Az C0 Ct D Bclock)
    (a : (n : ℕ)→NativeChildBarrierCall (N n) delta)
    (x : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ x n) (hxunit : ∀ᶠn in atTop,x n ≤ 1)
    (hparent : ∀n,(a n).context.E=(M n).context.E ∧
      (a n).context.d=(M n).context.d ∧ (a n).lam=(M n).lam ∧ (a n).R=(M n).R)
    (hchild : ∀ᶠn in atTop,(a n).childRadius=c0*x n ∧ (a n).childLam=(c0*x n)^2 ∧
      (a n).err ≤ (N n:ℝ)^(20*delta)*
        actualChildErrorBudget (N n) delta c0 (M n).context.d (M n).lam (x n))
    (hweak : Tendsto (fun n=>laplaceComparisonStrength (M n).context.d (M n).lam (x n)/(x n)^2)
      atTop (𝓝 0)) :
    ∀ratio left right eps theta : ℝ,0 < ratio → 0 < left → left < right →
      0 < eps → 0 < theta → ∀ᶠn in atTop,∀y : ℝ,ratio*x n ≤ y → y*right ≤ 1 →
      volume (physicalPropagationDisagreementMassSet (M n).R (a n).Z
        (y*left) (y*right) (eps*y)) < ENNReal.ofReal (theta*y) := by
  intro ratio left right eps theta hratio hleft hlr heps htheta
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
  obtain ⟨eta,heta,heta1,Hnear⟩ := eventually_native_absolute_disagreement_mass_le
    (Dbound:=D) (eps:=stepNear) (ell:=ellNear) Jn hdelta
      (show 0 < 1/C0 by positivity) hm hc0 hstepNear hellNear
  have Houter := eventually_native_outer_absolute_disagreement_mass_le
    (Dbound:=D) (ratio:=ratio) (cMove:=cMove) (eps:=stepOuter) (ell:=ellOuter) Jo hdelta
      (show 0 < 1/C0 by positivity) hm hc0 hratio hcMove hcMove1 hstepOuter hellOuter
  have Hweak := hweak.eventually (gt_mem_nhds (pow_pos heta 3))
  filter_upwards [hN.eventually Hnear,hN.eventually Houter,Hweak,hxunit,hchild]
    with n hnnear hnouter hnweak hnunit hnchild
  intro y hxy hy1
  have hy : 0 < y := (mul_pos hratio (hx n)).trans_le hxy
  have hband0 : 0 ≤ y*left := mul_nonneg hy.le hleft.le
  have hbandUnit u (hu : u∈Icc (y*left) (y*right)) : u∈Icc (0:ℝ) 1 :=
    ⟨hband0.trans hu.1,hu.2.trans hy1⟩
  have hcap u (hu : u∈Icc (y*left) (y*right)) : (a n).R u ≤ C*y := by
    rw [(hparent n).2.2.2]
    have Hr := (M n).inverse_radius_le_source_mass hcl hAz (hbandUnit u hu)
    have Hx : x n ≤ y/ratio := (le_div_iff₀ hratio).mpr (by simpa only [mul_comm] using hxy)
    have Hm : (M n).xs+u ≤ (1/ratio+right)*y := by
      have H := add_le_add ((hxs n).trans Hx) hu.2
      convert H using 1; ring
    exact Hr.trans (by
      have H := mul_le_mul_of_nonneg_left Hm (show 0 ≤ Az+1/cl by positivity)
      simpa only [C,mul_assoc] using H)
  rcases hparent n with ⟨he,hd,hl,hR⟩
  have hlo : (1/C0)*(N n:ℝ)^(-(2:ℝ)/3+m)*(a n).context.d ≤ (a n).context.E := by
    rw [hd,he]
    have H := mul_le_mul_of_nonneg_left (M n).hlower (show 0 ≤ 1/C0 by positivity)
    simpa only [←mul_assoc,one_div_mul_cancel hC0.ne',one_mul] using H
  have hdD : (a n).context.d ≤ D := by simpa only [hd] using (M n).hdD
  have hupp : Real.sqrt (N n:ℝ)*(a n).context.E ≤ (a n).context.d^2 := by
    simpa only [hd,he] using (M n).hupper
  have hax : comparisonLowerScale (N n) (a n).context.E (a n).context.d ≤ x n := by
    simpa only [hd,he] using (M n).hscale.trans (hxs n)
  have hld : (a n).lam ≤ (a n).context.d^2 := by simpa only [hd,hl] using (M n).hld
  have hwe : (a n).e (x n) ≤ eta^3*(x n)^2 := by
    have H := (div_le_iff₀ (sq_pos_of_pos (hx n))).mp hnweak.le
    simpa only [NativeChildBarrierCall.e,hd,hl] using H
  have hwe1 : (a n).e (x n) ≤ (x n)^2 := by
    have He : eta^3 ≤ 1 := by simpa using pow_le_pow_left₀ heta.le heta1 3
    exact hwe.trans (by nlinarith [mul_le_mul_of_nonneg_right He (sq_nonneg (x n))])
  have herr : (a n).err ≤ (N n:ℝ)^(20*delta)*
      actualChildErrorBudget (N n) delta c0 (a n).context.d (a n).lam (x n) := by
    simpa only [hd,hl] using hnchild.2.2
  by_cases hnear : y ≤ far*x n
  · have hupper u (hu : u∈Icc (y*left) (y*right)) :
        (a n).R u ≤ (Jn:ℝ)*(stepNear*x n) := by
      have H1 := mul_le_mul_of_nonneg_left hnear hC.le
      have H2 := mul_le_mul_of_nonneg_right hJn' (hx n).le
      exact (hcap u hu).trans (by nlinarith only [H1,H2])
    have Hmass := hnnear (a n) (x n) (y*left) (y*right) hdD hupp hlo
      ⟨hx n,hnunit⟩ hax hld hwe hnchild.1 hnchild.2.1 herr hband0 hy1 hupper
    have Hsubset : physicalPropagationDisagreementMassSet (M n).R (a n).Z
        (y*left) (y*right) (eps*y) ⊆
        {u | u∈Icc (y*left) (y*right) ∧ 3*(stepNear*x n) ≤ |(a n).Z u-(a n).R u|} := by
      intro u hu
      refine ⟨hu.1,?_⟩
      rw [hR]
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
      rw [hR]
      have Hu : u∈Icc (0:ℝ) 1 := ⟨hband0.trans hu.1,hu.2⟩
      have Hrad := (M n).inverse_radius_outer_band_lower_bound_of_parent_scale hcu hAz Hu
        (hxs n) (by simpa only [mul_comm] using hu.1) houter
      have Hmove := mul_le_mul_of_nonneg_right hmove hy.le
      apply le_trans _ Hrad
      dsimp only [Cy] at Hmove
      convert Hmove using 1 <;> ring
    have Hmass := hnouter (a n) (x n) y (y*left) (y*right) hdD hupp hlo
      ⟨hx n,hnunit⟩ hax hxy hwe1 hnchild.1 hnchild.2.1 herr hband0 hy1 hupper hlower
    have Hsubset : physicalPropagationDisagreementMassSet (M n).R (a n).Z
        (y*left) (y*right) (eps*y) ⊆
        {u | u∈Icc (y*left) (y*right) ∧ 3*(stepOuter*y) ≤ |(a n).Z u-(a n).R u|} := by
      intro u hu
      refine ⟨hu.1,?_⟩
      rw [hR]
      dsimp only [stepOuter]
      nlinarith only [hu.2.le]
    exact ((measure_mono Hsubset).trans Hmass).trans_lt
      (native_disagreement_measure_coefficient_lt Jo htheta hy)

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
