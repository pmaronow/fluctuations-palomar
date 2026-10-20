module

public import ComparisonPointSideColumn
public import ComparisonNativeUnitColumns
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 2000000

private theorem limit_invSquare_le {δ t : ℝ} (hδ : 0< δ) (ht : δ ≤ t) :
    (t⁻¹)^2 ≤ (δ⁻¹)^2 :=
  pow_le_pow_left₀ (inv_nonneg.mpr (hδ.le.trans ht))
    ((inv_le_inv₀ (hδ.trans_le ht) hδ).mpr ht) 2

private theorem limit_pointLeftSquare_norm {δ t : ℝ} (hδ : 0< δ) (ht : δ ≤ t) (s : ℝ) :
    ‖pointLeftSquare s t‖ ≤ (δ⁻¹)^2 := by
  by_cases hs : t ∈ Ici s
  · simp only [pointLeftSquare,indicator_of_mem hs,Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg (t⁻¹))]
    exact limit_invSquare_le hδ ht
  · simp only [pointLeftSquare,indicator_of_notMem hs,norm_zero]
    positivity

private theorem limit_integral_supported_abs_le {a b L R C : ℝ} (hab : a ≤ b)
    (hLR : L ≤ R) (hC : 0 ≤ C) (f : ℝ→ℝ)
    (hb : ∀t ∈ Ioc a b,|f t| ≤ (Icc L R).indicator (fun _=>C) t) :
    |∫t in a..b,f t| ≤ C*(R-L) := by
  have hi : Integrable ((Icc L R).indicator (fun _ : ℝ=>C)) :=
    (integrableOn_const (show volume (Icc L R) ≠ ⊤ by simp)).integrable_indicator measurableSet_Icc
  have hh := intervalIntegral.norm_integral_le_of_norm_le (f:=f) hab
    (ae_of_all _ (fun t ht=>by simpa only [Real.norm_eq_abs] using hb t ht))
    ⟨hi.integrableOn,hi.integrableOn⟩
  have hm := integral_mono_measure (μ:=volume.restrict (Ioc a b)) Measure.restrict_le_self
    (ae_of_all _ (fun t=>indicator_nonneg (fun _ _=>hC) t)) hi
  have he : (∫t,(Icc L R).indicator (fun _ : ℝ=>C) t)=C*(R-L) := by
    rw [integral_indicator measurableSet_Icc,setIntegral_const,smul_eq_mul,
      Real.volume_real_Icc,max_eq_left (sub_nonneg.mpr hLR)]
    ring
  simp only [intervalIntegral.integral_of_le hab] at hh
  simpa only [Real.norm_eq_abs,intervalIntegral.integral_of_le hab] using hh.trans (hm.trans_eq he)

private theorem pointLeftColumn_threshold_stability {δ width : ℝ}
    (hδ : 0< δ) (hw : 2*δ ≤ width) (s r : ℝ) :
    |(∫t in δ..width-δ,pointLeftSquare s t)-
      (∫t in δ..width-δ,pointLeftSquare r t)| ≤ (δ⁻¹)^2*|s-r| := by
  have hh := limit_integral_supported_abs_le (by linarith : δ ≤ width-δ)
    (min_le_max : min s r ≤ max s r) (sq_nonneg (δ⁻¹))
    (fun t=>pointLeftSquare s t-pointLeftSquare r t) (by
      intro t ht
      by_cases hm : t ∈ Icc (min s r) (max s r)
      · rw [indicator_of_mem hm]
        have hb q : pointLeftSquare q t ∈ Icc (0:ℝ) ((δ⁻¹)^2) := by
          refine ⟨indicator_nonneg (fun _ _=>sq_nonneg _) _,?_⟩
          exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using (limit_pointLeftSquare_norm hδ ht.1.le q))
        exact abs_le.mpr ⟨by linarith [(hb s).1,(hb s).2,(hb r).1,(hb r).2],
          by linarith [(hb s).1,(hb s).2,(hb r).1,(hb r).2]⟩
      · rw [indicator_of_notMem hm]
        have hcases : t< min s r ∨ max s r< t := by
          simpa only [mem_Icc,not_and_or,not_le] using hm
        rcases hcases with hlo|hhi
        · simp [pointLeftSquare,show ¬s ≤ t by linarith [min_le_left s r],
            show ¬r ≤ t by linarith [min_le_right s r]]
        · simp [pointLeftSquare,show s ≤ t by linarith [le_max_left s r],
            show r ≤ t by linarith [le_max_right s r]])
  rw [intervalIntegral.integral_sub (pointLeftSquare_intervalIntegrable hδ hw s)
    (pointLeftSquare_intervalIntegrable hδ hw r),max_sub_min_eq_abs] at hh
  simpa only [abs_sub_comm] using hh

private theorem pointLeftColumn_width_stability {δ w v : ℝ}
    (hδ : 0< δ) (hw : 2*δ ≤ w) (hv : 2*δ ≤ v) (s : ℝ) :
    |(∫t in δ..w-δ,pointLeftSquare s t)-
      (∫t in δ..v-δ,pointLeftSquare s t)| ≤ (δ⁻¹)^2*|w-v| := by
  rw [intervalIntegral.integral_interval_sub_left
    (pointLeftSquare_intervalIntegrable hδ hw s) (pointLeftSquare_intervalIntegrable hδ hv s),
    ←Real.norm_eq_abs]
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a:=v-δ) (b:=w-δ) (C:=(δ⁻¹)^2) (f:=pointLeftSquare s)
    (fun t ht=>limit_pointLeftSquare_norm hδ (by
      have hmin : δ ≤ min (v-δ) (w-δ) := le_min (by linarith) (by linarith)
      exact hmin.trans ht.1.le) s)
  simpa only [sub_sub_sub_cancel_right] using hh

private theorem pointRightColumn_reflect (δ width s : ℝ) :
    (∫t in δ..width-δ,pointRightSquare width s t)=
      ∫t in δ..width-δ,pointLeftSquare (width-s) t := by
  have he : pointRightSquare width s=(fun t=>pointLeftSquare (width-s) (width-t)) := by
    funext t
    by_cases ht : t ≤ s
    · simp [pointRightSquare,pointLeftSquare,ht,show width-s ≤ width-t by linarith]
    · simp [pointRightSquare,pointLeftSquare,ht,show ¬width-s ≤ width-t by linarith]
  rw [he,intervalIntegral.integral_comp_sub_left]
  congr 1; ring

theorem pointSideColumn_width_stability {δ w v : ℝ}
    (hδ : 0< δ) (hw : 2*δ ≤ w) (hv : 2*δ ≤ v) (s : ℝ) :
    |pointSideColumn δ w s-pointSideColumn δ v s| ≤ 3*(δ⁻¹)^2*|w-v| := by
  have hL := pointLeftColumn_width_stability hδ hw hv s
  have hR1 := pointLeftColumn_width_stability hδ hw hv (w-s)
  have hR2 := pointLeftColumn_threshold_stability hδ hv (w-s) (v-s)
  have hRtri := abs_add_le
    ((∫t in δ..w-δ,pointLeftSquare (w-s) t)-(∫t in δ..v-δ,pointLeftSquare (w-s) t))
    ((∫t in δ..v-δ,pointLeftSquare (w-s) t)-(∫t in δ..v-δ,pointLeftSquare (v-s) t))
  have hR : |(∫t in δ..w-δ,pointLeftSquare (w-s) t)-
      (∫t in δ..v-δ,pointLeftSquare (v-s) t)| ≤ 2*(δ⁻¹)^2*|w-v| := by
    have he : ((∫t in δ..w-δ,pointLeftSquare (w-s) t)-(∫t in δ..v-δ,pointLeftSquare (w-s) t))+
        ((∫t in δ..v-δ,pointLeftSquare (w-s) t)-(∫t in δ..v-δ,pointLeftSquare (v-s) t))=
        ((∫t in δ..w-δ,pointLeftSquare (w-s) t)-(∫t in δ..v-δ,pointLeftSquare (v-s) t)) := by ring
    rw [he] at hRtri
    simp only [sub_sub_sub_cancel_right] at hR2
    nlinarith
  have htri := abs_add_le
    ((∫t in δ..w-δ,pointLeftSquare s t)-(∫t in δ..v-δ,pointLeftSquare s t))
    ((∫t in δ..w-δ,pointLeftSquare (w-s) t)-(∫t in δ..v-δ,pointLeftSquare (v-s) t))
  simp only [sub_sub_sub_cancel_right] at hR2
  dsimp only [pointSideColumn]
  rw [pointRightColumn_reflect,pointRightColumn_reflect]
  have hsum : ((∫t in δ..w-δ,pointLeftSquare s t)+(∫t in δ..w-δ,pointLeftSquare (w-s) t))-
      ((∫t in δ..v-δ,pointLeftSquare s t)+(∫t in δ..v-δ,pointLeftSquare (v-s) t))=
      ((∫t in δ..w-δ,pointLeftSquare s t)-(∫t in δ..v-δ,pointLeftSquare s t))+
      ((∫t in δ..w-δ,pointLeftSquare (w-s) t)-(∫t in δ..v-δ,pointLeftSquare (v-s) t)) := by ring
  rw [hsum]
  nlinarith

theorem pointSideColumn_joint_stability {δ w v : ℝ}
    (hδ : 0< δ) (hw : 2*δ ≤ w) (hv : 2*δ ≤ v) (s r : ℝ) :
    |pointSideColumn δ w s-pointSideColumn δ v r| ≤ 
      (δ⁻¹)^2*(3*|w-v|+2*|s-r|) := by
  have h1 := pointSideColumn_width_stability hδ hw hv s
  have h2 := pointSideColumn_stability hδ hv s r
  have htri := abs_add_le (pointSideColumn δ w s-pointSideColumn δ v s)
    (pointSideColumn δ v s-pointSideColumn δ v r)
  have he : (pointSideColumn δ w s-pointSideColumn δ v s)+
      (pointSideColumn δ v s-pointSideColumn δ v r)=
      pointSideColumn δ w s-pointSideColumn δ v r := by ring
  rw [he] at htri
  nlinarith

theorem pointSideColumn_varying_tendsto {δ width : ℝ}
    (hδ : 0< δ) (hw : 2*δ ≤ width) (widths coords : ℕ→ℝ) (s : ℝ)
    (hwidths : ∀j,2*δ ≤ widths j)
    (hwlim : Tendsto widths atTop (𝓝 width)) (hslim : Tendsto coords atTop (𝓝 s)) :
    Tendsto (fun j=>pointSideColumn δ (widths j) (coords j)) atTop
      (𝓝 (pointSideColumn δ width s)) := by
  have he : Tendsto (fun j=>(δ⁻¹)^2*(3*|widths j-width|+2*|coords j-s|)) atTop (𝓝 0) := by
    convert ((((hwlim.sub_const width).abs.const_mul 3).add
      ((hslim.sub_const s).abs.const_mul 2)).const_mul ((δ⁻¹)^2)) using 1; simp
  have habs := squeeze_zero (fun _=>abs_nonneg _)
    (fun j=>pointSideColumn_joint_stability hδ (hwidths j) hw (coords j) s) he
  have hsub : Tendsto (fun j=>pointSideColumn δ (widths j) (coords j)-pointSideColumn δ width s)
      atTop (𝓝 0) := (tendsto_zero_iff_norm_tendsto_zero).mpr (by
        simpa only [Real.norm_eq_abs] using habs)
  simpa only [sub_add_cancel,zero_add] using hsub.add_const (pointSideColumn δ width s)

theorem radiusCellEnergyDensity_on_original_cell (R : ℝ→ℝ) (hR : Monotone R)
    {u : ℝ} (as : List PositiveMass) (ho : MassOrdered u as) (C : ℕ→ℝ)
    {i : ℕ} (hi : i< as.length) {r : ℝ}
    (hr : r ∈ Ioc (R (partitionPoint u as i)) (R (partitionPoint u as (i+1)))) :
    radiusCellEnergyDensity R u as C r=C i := by
  induction as generalizing u C i with
  | nil=>simp at hi
  | cons a as ih=>
    cases i with
    | zero=>
      have hh : r ∈ Ioc (R u) (R a.val) := by simpa [partitionPoint,partitionValues] using hr
      rw [radiusCellEnergyDensity,indicator_of_mem hh,
        radiusCellEnergyDensity_eq_zero_of_le R hR as ho.2.2 _ hh.2,add_zero]
    | succ i=>
      have hh : r ∈ Ioc (R (partitionPoint a.val as i)) (R (partitionPoint a.val as (i+1))) := by
        simpa only [partitionPoint,partitionValues] using hr
      have hnot : r∉Ioc (R u) (R a.val) := by
        intro h
        have hbase : R a.val ≤ R (partitionPoint a.val as i) :=
          hR (partitionPoint_mem as ho.2.2 i).1
        linarith [hh.1,h.2]
      rw [radiusCellEnergyDensity,indicator_of_notMem hnot,zero_add]
      exact ih ho.2.2 _ (by simpa using hi) hh

section
variable {c : ℝ} {k M : ℝ→ℝ}
variable (hc : 0 < c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r ∈ Icc (0:ℝ) 1,c ≤ k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)

theorem comparisonNativeUnitColumnWeight_point_bound {ι : Type}
    (q : ℝ→ι→ℝ≥0) (α : inverseIntegralConstraints 0 0 k M)
    (as : List PositiveMass) (ho : MassOrdered 0 as) {K : ℕ}
    (J : Finset (Fin ((sampleClockSteps q 0 as).length+1)))
    (unit : Fin ((sampleClockSteps q 0 as).length+1)→Fin K)
    (x : ℕ→ℝ) {δ width r s small : ℝ} (hδ : 0 < δ) (hw : 2*δ ≤ width)
    (hx : ∀u : Fin K,x u.val < x (u.val+1))
    (i : Fin ((sampleClockSteps q 0 as).length+1)) (hi : i ∈ J)
    (hil : i.val < as.length)
    (hr : r ∈ Ioc
      (comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as i.val))
      (comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as (i.val+1))))
    (hs : s ∈ Icc (x (unit i).val) (x ((unit i).val+1)))
    (hsmall : x ((unit i).val+1)-x (unit i).val ≤ small) :
    |comparisonNativeUnitColumnWeight hc hk hkc hm hM q α as J unit
        (fun u=>sideSquareColumn x δ width u.val) r-pointSideColumn δ width s| ≤
      2*(δ⁻¹)^2*small := by
  have he := radiusCellEnergyDensity_on_original_cell
    (comparisonSweepQuantile hc hk hkc hm hM α)
    (comparisonSweepQuantile_monotone hc hk hkc hm hM α) as ho
    (nativeSelectedColumn J unit (fun u=>sideSquareColumn x δ width u.val)) hil hr
  change comparisonNativeUnitColumnWeight hc hk hkc hm hM q α as J unit
    (fun u=>sideSquareColumn x δ width u.val) r=
      nativeSelectedColumn J unit (fun u=>sideSquareColumn x δ width u.val) i.val at he
  rw [he,nativeSelectedColumn_atIndex,ite_eq_left hi]
  exact (sideSquareColumn_point_stability x (unit i).val hδ hw (hx (unit i)) hs).trans
    (mul_le_mul_of_nonneg_left hsmall (by positivity))

theorem comparisonNativeContactColumn_limit_mass {ι : Type}
    (q : ℝ→ι→ℝ≥0) (α : inverseIntegralConstraints 0 0 k M)
    {a z : ℝ} (ha : 0 < a) (hz : z ≤ 1)
    (A : Set ℝ) (hA : MeasurableSet A) (hAband : A ⊆ Ioo a z)
    (as : ℕ→List PositiveMass) (ho : ∀j,MassOrdered 0 (as j))
    (hend : ∀j,partitionEnd 0 (as j)=1) (K : ℕ→ℕ)
    (J : ∀j,Finset (Fin ((sampleClockSteps q 0 (as j)).length+1)))
    (unit : ∀j,Fin ((sampleClockSteps q 0 (as j)).length+1)→Fin (K j))
    (x : ℕ→ℕ→ℝ) (widths : ℕ→ℝ) (small : ℕ→ℝ→ℝ) {δ width : ℝ}
    (hδ : 0 < δ) (hw : 2*δ ≤ width) (hwidths : ∀j,2*δ ≤ widths j)
    (hstart : ∀j,x j 0=0) (hxend : ∀j,x j (K j)=widths j)
    (hx : ∀j,∀u : Fin (K j),x j u.val < x j (u.val+1))
    (hmass : ∀j,∀u : Fin (K j),
      physicalSelectedUnitMass (sampleClockSteps q 0 (as j)) (J j) (unit j) u=
        x j (u.val+1)-x j u.val)
    (hwlim : Tendsto widths atTop (𝓝 width))
    (hsmall : ∀ᵐ r ∂volume.restrict A,Tendsto (fun j=>small j r) atTop (𝓝 0))
    (Fseq : ℕ→ℝ→ℝ) (F : ℝ→ℝ)
    (hFlim : ∀ᵐ r ∂volume.restrict A,Tendsto (fun j=>Fseq j r) atTop (𝓝 (F r)))
    (hcell : ∀ᵐ r ∂volume.restrict A,∀ᶠ j in atTop,
      ∃i : Fin ((sampleClockSteps q 0 (as j)).length+1),i ∈ J j ∧ i.val < (as j).length ∧
        r ∈ Ioc
          (comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 (as j) i.val))
          (comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 (as j) (i.val+1))) ∧
        Fseq j r ∈ Icc (x j (unit j i).val) (x j ((unit j i).val+1)) ∧
        x j ((unit j i).val+1)-x j (unit j i).val ≤ small j r) :
    (∫r in A,deriv α.val.val r*pointSideColumn δ width (F r)) ≤
      2*Real.log (width/δ) := by
  let wj := fun j=>comparisonNativeUnitColumnWeight hc hk hkc hm hM q α
    (as j) (J j) (unit j) (fun u=>sideSquareColumn (x j) δ (widths j) u.val)
  have hwj j r : wj j r ∈ Icc (0:ℝ) (2/δ) :=
    comparisonNativeUnitColumnWeight_side_bound hc hk hkc hm hM q α (as j) (ho j)
      (J j) (unit j) (x j) (hstart j) (hxend j) hδ (hwidths j) (hx j) r
  have hwi j : Integrable (fun r=>deriv α.val.val r*wj j r) := by
    exact (radiusCellEnergyDensity_deriv_integral α.val.val
      (comparisonSweepQuantile hc hk hkc hm hM α)
      (inverseIntegralConstraints_lipschitz hm hM α.property)
      (comparisonSweepQuantile_monotone hc hk hkc hm hM α)
      (fun u _=>comparisonSweepQuantile_bounds hc hk hkc hm hM α u)
      (fun u hu=>comparisonSweepQuantile_mass_spec hc hk hkc hm hM α hu)
      (show (0:ℝ) ∈ Icc (0:ℝ) 1 by simp) (as j) (ho j) _).1
  have hlim : ∀ᵐ r ∂volume.restrict A,
      Tendsto (fun j=>wj j r) atTop (𝓝 (pointSideColumn δ width (F r))) := by
    filter_upwards [hFlim,hcell,hsmall] with r hFr hcr hsr
    have hclose : Tendsto (fun j=>wj j r-pointSideColumn δ (widths j) (Fseq j r))
        atTop (𝓝 0) := by
      have he : Tendsto (fun j=>2*(δ⁻¹)^2*small j r) atTop (𝓝 0) := by
        simpa only [mul_zero] using hsr.const_mul (2*(δ⁻¹)^2)
      have hb : ∀ᶠ j in atTop,
          |wj j r-pointSideColumn δ (widths j) (Fseq j r)| ≤ 2*(δ⁻¹)^2*small j r := by
        filter_upwards [hcr] with j hj
        obtain ⟨i,hi,hil,hr,hs,hsm⟩ := hj
        exact comparisonNativeUnitColumnWeight_point_bound hc hk hkc hm hM q α
          (as j) (ho j) (J j) (unit j) (x j) hδ (hwidths j) (hx j) i hi hil hr hs hsm
      have hh := squeeze_zero' (Eventually.of_forall (fun _=>abs_nonneg _)) hb he
      exact (tendsto_zero_iff_norm_tendsto_zero).mpr (by simpa only [Real.norm_eq_abs] using hh)
    have hp := pointSideColumn_varying_tendsto hδ hw widths (fun j=>Fseq j r) (F r)
      hwidths hwlim hFr
    simpa only [sub_add_cancel,zero_add] using hclose.add hp
  have hAf : volume A ≠ ⊤ := ne_top_of_le_ne_top
    (by simp : volume (Icc (0:ℝ) 1) ≠ ⊤) (measure_mono (fun r hr=>
      ⟨ha.le.trans (hAband hr).1.le,(hAband hr).2.le.trans hz⟩))
  have hbound j : ∀ᵐ r ∂volume.restrict A,
      ‖deriv α.val.val r*wj j r‖ ≤ M 1*(2/δ) := by
    apply (ae_restrict_iff' hA).mpr
    exact ae_of_all _ (fun r hr=>by
      have hr01 : r ∈ Ioo (0:ℝ) 1 := ⟨ha.trans (hAband hr).1,(hAband hr).2.trans_le hz⟩
      have hd := norm_deriv_le_of_lipschitzOn (Icc_mem_nhds hr01.1 hr01.2)
        (inverseIntegralConstraints_lipschitz hm hM α.property)
      have hw0 := hwj j r
      have hwn : ‖wj j r‖ ≤ 2/δ := by
        simpa only [Real.norm_eq_abs,abs_of_nonneg hw0.1] using hw0.2
      rw [norm_mul]
      exact mul_le_mul hd hwn (norm_nonneg _) hM)
  have htrace := tendsto_integral_of_dominated_convergence (μ:=volume.restrict A)
    (fun _=>M 1*(2/δ)) (fun j=>(hwi j).aestronglyMeasurable.restrict)
    (integrableOn_const hAf) hbound (hlim.mono (fun r hr=>hr.const_mul (deriv α.val.val r)))
  have hmassbound j : (∫r in A,deriv α.val.val r*wj j r) ≤ 2*Real.log (widths j/δ) := by
    have hpositive : ∀r,0 ≤ deriv α.val.val r*wj j r :=
      fun r=>mul_nonneg α.val.property.2.deriv_nonneg (hwj j r).1
    exact (setIntegral_le_integral (hwi j) (ae_of_all _ hpositive)).trans
      (comparisonNativeUnitColumnWeight_side_mass_le_log hc hk hkc hm hM q α
        (as j) (ho j) (hend j) (J j) (unit j) (x j) (hstart j) (hxend j) hδ
        (hwidths j) (hx j) (hmass j))
  have hwidth0 : 0 < width := by linarith
  have hloglim : Tendsto (fun j=>2*Real.log (widths j/δ)) atTop
      (𝓝 (2*Real.log (width/δ))) :=
    ((Real.continuousAt_log (div_pos hwidth0 hδ).ne').tendsto.comp
      (hwlim.div_const δ)).const_mul 2
  exact le_of_tendsto_of_tendsto htrace hloglim (Eventually.of_forall hmassbound)

end

end OAI.SKFluctuations.LaplaceWindowFormalization
