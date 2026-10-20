module

public import JointScalarVariationalBridge

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

theorem actualComparisonPressure_tendsto_jointScalar (N : ℕ → ℕ)
    (hN : Tendsto N atTop atTop) {T c : ℝ} (hT : 0 < T) (hc : 0 < c)
    (eseq rseq : ℕ → ℝ → ℝ) (e r : ℝ → ℝ)
    (he : AntitoneOn e (Icc (0:ℝ) 1))
    (heb : ∀ u ∈ Icc (0:ℝ) 1, e u ∈ Icc c (T-c))
    (her : MonotoneOn (fun u => e u*r u) (Icc (0:ℝ) 1))
    (hrn : ∀ u ∈ Icc (0:ℝ) 1, 0 ≤ r u)
    (hes : ∀ n, AntitoneOn (eseq n) (Icc (0:ℝ) 1))
    (hesb : ∀ n u, u ∈ Icc (0:ℝ) 1 → eseq n u ∈ Icc (0:ℝ) T)
    (hers : ∀ n, MonotoneOn (fun u => eseq n u*rseq n u) (Icc (0:ℝ) 1))
    (hrsn : ∀ n u, u ∈ Icc (0:ℝ) 1 → 0 ≤ rseq n u)
    (hedist : Tendsto (fun n => ∫u in (0:ℝ)..1,|eseq n u-e u|) atTop (𝓝 0))
    (hfielddist : Tendsto (fun n => ∫u in (0:ℝ)..1,|eseq n u*rseq n u-e u*r u|) atTop (𝓝 0))
    (hpenalty : Tendsto (fun n => ∫u in (0:ℝ)..1,eseq n u*rseq n u^2) atTop
      (𝓝 (∫u in (0:ℝ)..1,e u*r u^2))) :
    Tendsto (fun n => pathCompensatedPressure (N n) (fun _ => T) (fun _ => 0)
      (eseq n) (rseq n) 0) atTop (𝓝 (jointScalarVariationalValue T e r)) := by
  have heb' : ∀ u ∈ Icc (0:ℝ) 1, e u ∈ Icc (0:ℝ) T :=
    fun u hu => ⟨hc.le.trans (heb u hu).1,(heb u hu).2.trans (sub_le_self _ hc.le)⟩
  have hmatrix : MonotoneOn (fun u => T-e u) (Icc (0:ℝ) 1) :=
    fun _ hu _ hv huv => sub_le_sub_left (he hu hv huv) T
  have hb : ∀ u ∈ Icc (0:ℝ) 1, T-e u ∈ Icc (0:ℝ) T :=
    fun u hu => ⟨sub_nonneg.mpr (heb' u hu).2,sub_le_self _ (heb' u hu).1⟩
  have hl : ∀ u ∈ Icc (0:ℝ) 1, c ≤ T-e u := by
    intro u hu; linarith [(heb u hu).2]
  have hmatdist : Tendsto (fun n => ∫u in (0:ℝ)..1,|(T-eseq n u)-(T-e u)|) atTop (𝓝 0) := by
    have heq (n : ℕ) : (∫u in (0:ℝ)..1,|(T-eseq n u)-(T-e u)|)=
        (∫u in (0:ℝ)..1,|eseq n u-e u|) := by
      apply intervalIntegral.integral_congr
      intro u _
      dsimp only
      rw [show (T-eseq n u)-(T-e u)= -(eseq n u-e u) by ring,abs_neg]
    simpa only [heq] using hedist
  have hp := generalMacroPressure_tendsto_of_l1_on N hN (fun n u => T-eseq n u)
    (fun n u => eseq n u*rseq n u) (fun u => T-e u) (fun u => e u*r u)
    hT hc hmatrix her hb hl (fun u hu => mul_nonneg (heb' u hu).1 (hrn u hu))
    (fun n _ hu _ hv huv => sub_le_sub_left (hes n hu hv huv) T) hers
    (fun n => sub_nonneg.mpr (hesb n 0 (by norm_num)).2)
    (fun n => mul_nonneg (hesb n 0 (by norm_num)).1 (hrsn n 0 (by norm_num)))
    hmatdist hfielddist
  have hresult := hp.add (hpenalty.const_mul (1/4:ℝ))
  simpa only [pathCompensatedPressure,jointScalarVariationalValue,zero_add] using hresult

theorem jointScalarVariationalValue_eq_reference_of_comparison {β : ℝ≥0} (hβ : 0 < β)
    {c : ℝ} (hc : 0 < c) (e r : ℝ → ℝ)
    (he : AntitoneOn e (Icc (0:ℝ) 1))
    (heb : ∀ u ∈ Icc (0:ℝ) 1, e u ∈ Icc c ((β:ℝ)^2-c))
    (her : MonotoneOn (fun u => e u*r u) (Icc (0:ℝ) 1))
    (hr : MonotoneOn r (Icc (0:ℝ) 1))
    (hrb : ∀ u ∈ Icc (0:ℝ) 1, r u ∈ Icc (0:ℝ) 1)
    (N : ℕ → ℕ) (eseq rseq : ℕ → ℝ → ℝ) (error : ℕ → ℝ)
    (hvalue : Tendsto (fun n => pathCompensatedPressure (N n) (fun _ => (β:ℝ)^2)
      (fun _ => 0) (eseq n) (rseq n) 0) atTop (𝓝 (jointScalarVariationalValue ((β:ℝ)^2) e r)))
    (herror : Tendsto error atTop (𝓝 0))
    (hcomparison : ∀ᶠ n : ℕ in atTop,
      pathCompensatedPressure (N n) (fun _ => (β:ℝ)^2) (fun _ => 0) (eseq n) (rseq n) 0 ≤
        normalizedScalarParisiReference β+error n) :
    jointScalarVariationalValue ((β:ℝ)^2) e r=normalizedScalarParisiReference β := by
  apply le_antisymm _ (jointScalarVariationalValue_lower hβ hc e r he heb her hr hrb)
  have hu : Tendsto (fun n => normalizedScalarParisiReference β+error n) atTop
      (𝓝 (normalizedScalarParisiReference β)) := by
    simpa only [add_zero] using herror.const_add (normalizedScalarParisiReference β)
  exact le_of_tendsto_of_tendsto hvalue hu hcomparison

end OAI.SKFluctuations.LaplaceWindowFormalization
