module

public import ComparisonNormalizedClockCoupling

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy ProbabilityTheory
open scoped Topology
set_option maxHeartbeats 2600000

theorem comparison_clock_cdf_limits_eq_below_cut
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : ℕ→Measure Ω) (hfinite : ∀n,IsFiniteMeasure (μ n))
    (q r : ℕ→Ω→ℝ) (U V : ℝ→ℝ) {R t : ℝ} (ht : t<R)
    (hi : ∀n,Integrable (fun w=>|q n w-r n w|) (μ n))
    (hz : Tendsto (fun n=>∫w,|q n w-r n w|∂μ n) atTop (𝓝 0))
    (hU : ∀s≤R,Tendsto (fun n=>comparisonClockCDF (μ n) (q n) s) atTop (𝓝 (U s)))
    (hV : ∀s≤R,Tendsto (fun n=>comparisonClockCDF (μ n) (r n) s) atTop (𝓝 (V s)))
    (hc : ContinuousAt V t) : U t=V t := by
  have hsand {eps : ℝ} (heps : 0<eps) (hsmall : t+eps≤R) : V (t-eps)≤U t ∧ U t≤V (t+eps) := by
    have hup : U t≤V (t+eps) := by
      have hl := (hV (t+eps) hsmall).add (hz.div_const eps)
      simp only [zero_div,add_zero] at hl
      exact le_of_tendsto_of_tendsto (hU t ht.le) hl (Eventually.of_forall fun n=>by
        let _ := hfinite n
        exact comparison_clock_cdf_sandwich (μ n) (q n) (r n) (hi n) heps)
    have hlo : V (t-eps)≤U t := by
      have hl := (hU t ht.le).add (hz.div_const eps)
      simp only [zero_div,add_zero] at hl
      apply le_of_tendsto_of_tendsto (hV (t-eps) (by linarith)) hl
      apply Eventually.of_forall
      intro n
      let _ := hfinite n
      have hrev : Integrable (fun w=>|r n w-q n w|) (μ n) := by simpa only [abs_sub_comm] using hi n
      simpa only [sub_add_cancel,abs_sub_comm] using
        comparison_clock_cdf_sandwich (μ n) (r n) (q n) hrev (t:=t-eps) heps
    exact ⟨hlo,hup⟩
  let eps := fun j : ℕ=>min ((R-t)/2) (1/((j:ℝ)+1))
  have hd : 0<(R-t)/2 := by linarith
  have hep : ∀j,0<eps j := by intro j;exact lt_min hd (by positivity)
  have hes : ∀j,t+eps j≤R := by intro j;have hh:=min_le_left ((R-t)/2) (1/((j:ℝ)+1));dsimp [eps];linarith
  have he0 : Tendsto eps atTop (𝓝 0) := by
    simpa only [min_eq_right hd.le] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ=>(R-t)/2) atTop (𝓝 ((R-t)/2))).min
        tendsto_one_div_add_atTop_nhds_zero_nat)
  have hp : Tendsto (fun j=>V (t+eps j)) atTop (𝓝 (V t)) :=
    hc.tendsto.comp (by simpa using tendsto_const_nhds.add he0)
  have hm : Tendsto (fun j=>V (t-eps j)) atTop (𝓝 (V t)) :=
    hc.tendsto.comp (by simpa using tendsto_const_nhds.sub he0)
  exact le_antisymm
    (ge_of_tendsto hp (Eventually.of_forall fun j=>(hsand (hep j) (hes j)).2))
    (le_of_tendsto hm (Eventually.of_forall fun j=>(hsand (hep j) (hes j)).1))

theorem comparison_normalized_clock_error_integrable (q r : ℝ→ℝ)
    (hq : MonotoneOn q (Icc (0:ℝ) 1)) (hr : MonotoneOn r (Icc (0:ℝ) 1))
    (hqb : ∀u∈Icc (0:ℝ) 1,q u∈Icc (0:ℝ) 1)
    (hrb : ∀u∈Icc (0:ℝ) 1,r u∈Icc (0:ℝ) 1)
    {x v : ℝ} (hx : 0<x) :
    Integrable (fun w : ParisiFinite.OrderPoint=>|q (w:ℝ)/x-r (w:ℝ)/x|)
      (comparisonNormalizedClockMass x v) := by
  have hqm : Monotone (fun w : ParisiFinite.OrderPoint=>q (w:ℝ)) := fun a b hab=>hq a.property b.property hab
  have hrm : Monotone (fun w : ParisiFinite.OrderPoint=>r (w:ℝ)) := fun a b hab=>hr a.property b.property hab
  have hm : AEStronglyMeasurable (fun w : ParisiFinite.OrderPoint=>|q (w:ℝ)/x-r (w:ℝ)/x|)
      (comparisonNormalizedClockMass x v) :=
    ((hqm.measurable.div_const x).sub (hrm.measurable.div_const x)).abs.aestronglyMeasurable
  apply (integrable_const (1/x)).mono' hm
  apply Eventually.of_forall
  intro w
  rw [Real.norm_eq_abs,abs_abs,←sub_div,abs_div,abs_of_pos hx]
  apply div_le_div_of_nonneg_right _ hx.le
  exact abs_le.mpr ⟨by linarith [(hqb w w.property).1,(hrb w w.property).2],
    by linarith [(hqb w w.property).2,(hrb w w.property).1]⟩

theorem comparison_actual_rescaled_clock_laws_identified
    (q r : ℕ→ℝ→ℝ) (x v : ℕ→ℝ) (U V : ℝ→ℝ) {R t : ℝ}
    (hq : ∀n,MonotoneOn (q n) (Icc (0:ℝ) 1))
    (hr : ∀n,MonotoneOn (r n) (Icc (0:ℝ) 1))
    (hqb : ∀n u,u∈Icc (0:ℝ) 1→ q n u∈Icc (0:ℝ) 1)
    (hrb : ∀n u,u∈Icc (0:ℝ) 1→ r n u∈Icc (0:ℝ) 1)
    (hx : ∀n,0<x n) (hv : ∀n,v n∈Icc (0:ℝ) 1)
    (hcut : ∀ᶠ n in atTop,x n*R<q n (v n) ∧ x n*R<r n (v n))
    (hU : ∀s≤R,Tendsto (fun n=>(quantileMassProfile (q n) (hqb n)).val (x n*s)/x n) atTop (𝓝 (U s)))
    (hV : ∀s≤R,Tendsto (fun n=>(quantileMassProfile (r n) (hrb n)).val (x n*s)/x n) atTop (𝓝 (V s)))
    (hz : Tendsto (fun n=>(∫w : ParisiFinite.OrderPoint in {w | (w:ℝ)≤v n},
      |q n (w:ℝ)-r n (w:ℝ)|∂(uniformOrderMass : Measure ParisiFinite.OrderPoint))/(x n)^2)
      atTop (𝓝 0)) (ht : t<R) (hc : ContinuousAt V t) : U t=V t := by
  let μ := fun n=>comparisonNormalizedClockMass (x n) (v n)
  let Q := fun n (w : ParisiFinite.OrderPoint)=>q n (w:ℝ)/x n
  let P := fun n (w : ParisiFinite.OrderPoint)=>r n (w:ℝ)/x n
  have hUi : ∀s≤R,Tendsto (fun n=>comparisonClockCDF (μ n) (Q n) s) atTop (𝓝 (U s)) := by
    intro s hs
    apply (hU s hs).congr'
    filter_upwards [hcut] with n hn
    exact (comparison_normalized_clock_cdf_exact (q n) (hq n) (hqb n) (hx n) (hv n) hs hn.1).symm
  have hVi : ∀s≤R,Tendsto (fun n=>comparisonClockCDF (μ n) (P n) s) atTop (𝓝 (V s)) := by
    intro s hs
    apply (hV s hs).congr'
    filter_upwards [hcut] with n hn
    exact (comparison_normalized_clock_cdf_exact (r n) (hr n) (hrb n) (hx n) (hv n) hs hn.2).symm
  have hzi : Tendsto (fun n=>∫w,|Q n w-P n w|∂μ n) atTop (𝓝 0) := by
    apply hz.congr'
    exact Eventually.of_forall fun n=>(comparison_normalized_clock_error_exact (q n) (r n) (v:=v n) (hx n)).symm
  exact comparison_clock_cdf_limits_eq_below_cut μ (fun n=>inferInstance) Q P U V ht
    (fun n=>comparison_normalized_clock_error_integrable (q n) (r n) (hq n) (hr n) (hqb n) (hrb n) (hx n))
    hzi hUi hVi hc

end OAI.SKFluctuations.LaplaceWindowFormalization
