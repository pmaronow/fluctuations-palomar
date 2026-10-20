module

public import ComparisonContactSideTrace

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter
open scoped Topology NNReal ENNReal
open WholeUnitSideKernel
set_option maxHeartbeats 1800000

def sideSquareColumnLR (δ width L R : ℝ) : ℝ :=
  ∫t in δ..width-δ,(left 0 L R t)^2+(right width L R t)^2

theorem sideSquareColumn_eq_LR (x : ℕ→ℝ) (i : ℕ) {δ width : ℝ}
    (hδ : 0<δ) (hw : 2*δ≤width) (hx : x i<x (i+1)) :
    sideSquareColumn x δ width i=sideSquareColumnLR δ width (x i) (x (i+1)) := by
  have hIL : IntervalIntegrable (fun t=>(left 0 (x i) (x (i+1)) t)^2)
      volume δ (width-δ) := by
    apply ContinuousOn.intervalIntegrable (μ:=volume)
    simpa [uIcc_of_le (by linarith : δ≤width-δ),Pi.pow_def] using
      (left_continuousOn (a:=0) (b:=width-δ) hδ hx).pow 2
  have hIR : IntervalIntegrable (fun t=>(right width (x i) (x (i+1)) t)^2)
      volume δ (width-δ) := by
    apply ContinuousOn.intervalIntegrable (μ:=volume)
    apply ContinuousOn.mono ((right_continuousOn (a:=δ) hδ hx).pow 2)
    rw [uIcc_of_le (by linarith : δ≤width-δ)]
  exact (intervalIntegral.integral_add hIL hIR).symm

theorem sideSquareColumnLR_tendsto {δ width l r : ℝ}
    (hδ : 0<δ) (hw : 2*δ≤width) (hlr : l<r)
    (widths lefts rights : ℕ→ℝ)
    (hwidths : ∀j,2*δ≤widths j) (hwidthMax : ∀j,widths j≤1)
    (hunits : ∀j,lefts j<rights j)
    (hwlim : Tendsto widths atTop (𝓝 width))
    (hllim : Tendsto lefts atTop (𝓝 l)) (hrlim : Tendsto rights atTop (𝓝 r)) :
    Tendsto (fun j=>sideSquareColumnLR δ (widths j) (lefts j) (rights j))
      atTop (𝓝 (sideSquareColumnLR δ width l r)) := by
  let G := fun (w L R t : ℝ)=>(left 0 L R t)^2+(right w L R t)^2
  let fj := fun j=>(Ioc δ (widths j-δ)).indicator (G (widths j) (lefts j) (rights j))
  let f := (Ioc δ (width-δ)).indicator (G width l r)
  let bound := (Ioc δ 1).indicator (fun _ : ℝ=>2*(δ⁻¹)^2)
  have hmeas j : AEStronglyMeasurable (fj j) volume := by
    apply Measurable.aestronglyMeasurable
    apply Measurable.indicator _ measurableSet_Ioc
    dsimp only [G]
    unfold left right leftFraction rightFraction
    fun_prop
  have hbound j : ∀ᵐ t∂volume,‖fj j t‖≤bound t := by
    apply ae_of_all
    intro t
    by_cases ht:t∈Ioc δ (widths j-δ)
    · have ht1:t∈Ioc δ 1 := ⟨ht.1,ht.2.trans (by linarith [hwidthMax j])⟩
      have hL := left_bounds (hunits j) (hδ.trans ht.1)
      have hR := right_bounds (hunits j) (by linarith [ht.2,hδ] : t<widths j)
      have hLi : t⁻¹≤δ⁻¹ := inv_anti₀ hδ ht.1.le
      have hRi : (widths j-t)⁻¹≤δ⁻¹ := inv_anti₀ hδ (by linarith [ht.2])
      rw [show fj j t=G (widths j) (lefts j) (rights j) t from
          indicator_of_mem ht (G (widths j) (lefts j) (rights j)),
        show bound t=2*(δ⁻¹)^2 from indicator_of_mem ht1 (fun _=>2*(δ⁻¹)^2),Real.norm_eq_abs]
      dsimp only [G]
      rw [abs_of_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _))]
      simp only [sub_zero] at hL
      have hLb := hL.2.trans hLi
      have hRb := hR.2.trans hRi
      nlinarith [hL.1,hR.1,inv_pos.mpr hδ,
        mul_self_le_mul_self hL.1 hLb, mul_self_le_mul_self hR.1 hRb]
    · rw [show fj j t=0 from indicator_of_notMem ht (G (widths j) (lefts j) (rights j))]
      simp only [norm_zero]
      exact indicator_nonneg (fun _ _=>by positivity) t
  have hiBound : Integrable bound volume := by
    apply (integrable_indicator_iff measurableSet_Ioc).mpr
    exact integrableOn_const (by simp)
  have hpoint : ∀ᵐ t∂volume,Tendsto (fun j=>fj j t) atTop (𝓝 (f t)) := by
    filter_upwards [volume.ae_ne δ,volume.ae_ne (width-δ)] with t htδ htw
    by_cases ht0:t≤δ
    · have hj j : fj j t=0 := indicator_of_notMem
        (show t∉Ioc δ (widths j-δ) from fun hh=>not_lt.mpr ht0 hh.1)
        (G (widths j) (lefts j) (rights j))
      have hf : f t=0 := indicator_of_notMem
        (show t∉Ioc δ (width-δ) from fun hh=>not_lt.mpr ht0 hh.1) (G width l r)
      simp_rw [hj,hf]
      exact tendsto_const_nhds
    · have hδt:δ<t := lt_of_not_ge ht0
      by_cases ht:t<width-δ
      · have hinc : ∀ᶠ j in atTop,t<widths j-δ :=
          (hwlim.sub_const δ) (Ioi_mem_nhds ht)
        have hleft : Tendsto (fun j=>left 0 (lefts j) (rights j) t)
            atTop (𝓝 (left 0 l r t)) := by
          exact (((tendsto_const_nhds.min hrlim).sub
            (tendsto_const_nhds.min hllim)).div (hrlim.sub hllim)
              (sub_pos.mpr hlr).ne').div_const (t-0)
        have hright : Tendsto (fun j=>right (widths j) (lefts j) (rights j) t)
            atTop (𝓝 (right width l r t)) := by
          exact (((tendsto_const_nhds.max hrlim).sub
            (tendsto_const_nhds.max hllim)).div (hrlim.sub hllim)
              (sub_pos.mpr hlr).ne').div (hwlim.sub_const t)
                (by linarith : width-t≠0)
        have hG := (hleft.pow 2).add (hright.pow 2)
        have heq : (fun j=>fj j t)=ᶠ[atTop]
            (fun j=>G (widths j) (lefts j) (rights j) t) := by
          filter_upwards [hinc] with j hj
          exact indicator_of_mem (show t∈Ioc δ (widths j-δ) from ⟨hδt,hj.le⟩)
            (G (widths j) (lefts j) (rights j))
        rw [show f t=G width l r t from indicator_of_mem
          (show t∈Ioc δ (width-δ) from ⟨hδt,ht.le⟩) (G width l r)]
        exact (tendsto_congr' heq).mpr hG
      · have hwt:width-δ<t := lt_of_le_of_ne (le_of_not_gt ht) (Ne.symm htw)
        have hout : ∀ᶠ j in atTop,widths j-δ<t :=
          (hwlim.sub_const δ) (Iio_mem_nhds hwt)
        have heq : (fun j=>fj j t)=ᶠ[atTop] (fun _=>0) := by
          filter_upwards [hout] with j hj
          exact indicator_of_notMem
            (show t∉Ioc δ (widths j-δ) from fun hh=>not_le.mpr hj hh.2)
            (G (widths j) (lefts j) (rights j))
        rw [show f t=0 from indicator_of_notMem
          (show t∉Ioc δ (width-δ) from fun hh=>not_le.mpr hwt hh.2) (G width l r)]
        exact (tendsto_congr' heq).mpr tendsto_const_nhds
  have ht := tendsto_integral_of_dominated_convergence bound hmeas hiBound hbound hpoint
  have hj j : (∫t,fj j t)=sideSquareColumnLR δ (widths j) (lefts j) (rights j) := by
    rw [integral_indicator measurableSet_Ioc]
    exact (intervalIntegral.integral_of_le (by linarith [hwidths j])).symm
  have hf : (∫t,f t)=sideSquareColumnLR δ width l r := by
    rw [integral_indicator measurableSet_Ioc]
    exact (intervalIntegral.integral_of_le (by linarith)).symm
  simpa only [hj,hf] using ht

end OAI.SKFluctuations.LaplaceWindowFormalization
