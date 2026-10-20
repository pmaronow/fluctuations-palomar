module

public import SKConstants.ParisiCDFBrownianMoments

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
noncomputable section

namespace SKConstants.ParisiFullSupport

open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.SK.Analytic

variable {Ω : Type*} [MeasurableSpace Ω]

def brownianCDFOverlap (W : BrownianSystem Ω) (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0:ℝ) 1) (h1 : α 1 = 1) (q : ℝ) : ℝ :=
  ∫ w, (scalarCDFGradient β α q (Real.toNNReal (1-q))
    (finiteTemperatureCDFProcess W β α ha h1 (Real.toNNReal (β^2*q)) w))^2 ∂W.law

def brownianCDFSusceptibilitySquare (W : BrownianSystem Ω) (β : ℝ)
    (α : StieltjesFunction ℝ) (ha : ∀ z, α z ∈ Icc (0:ℝ) 1)
    (h1 : α 1 = 1) (q : ℝ) : ℝ :=
  ∫ w, (scalarCDFHessian β α q (Real.toNNReal (1-q))
    (finiteTemperatureCDFProcess W β α ha h1 (Real.toNNReal (β^2*q)) w))^2 ∂W.law

lemma brownianCDFOverlap_eq_compact (W : BrownianSystem Ω) (β : ℝ)
    (α : StieltjesFunction ℝ) (ha : ∀ z, α z ∈ Icc (0:ℝ) 1)
    (h1 : α 1 = 1) (hβ : β ≠ 0) {T q : ℝ} (hq : q ∈ Icc (0:ℝ) T) :
    brownianCDFOverlap W β α ha h1 q =
      physicalCDFJetSquareMoment W β α ha h1 T 0 (β^2*q) := by
  unfold brownianCDFOverlap physicalCDFJetSquareMoment
  have he : β^2*q/β^2=q := by field_simp
  simp only [compactCDFJet, iteratedDeriv_zero, compactCDFGradient, he, cdfStripTime_eq hq]

lemma brownianCDFSusceptibilitySquare_eq_compact (W : BrownianSystem Ω) (β : ℝ)
    (α : StieltjesFunction ℝ) (ha : ∀ z, α z ∈ Icc (0:ℝ) 1)
    (h1 : α 1 = 1) (hβ : β ≠ 0) {T q : ℝ} (hT1 : T ≤ 1)
    (hq : q ∈ Icc (0:ℝ) T) :
    brownianCDFSusceptibilitySquare W β α ha h1 q =
      physicalCDFJetSquareMoment W β α ha h1 T 1 (β^2*q) := by
  unfold brownianCDFSusceptibilitySquare physicalCDFJetSquareMoment
  have he : β^2*q/β^2=q := by field_simp
  have hremaining : Real.toNNReal (1-q) ≤ 1 := by
    rw [Real.toNNReal_le_iff_le_coe, NNReal.coe_one]
    linarith [hq.1]
  have hd := scalarCDFGradient_hasDerivAt β ha α.mono q _ hremaining
  simp only [compactCDFJet, iteratedDeriv_one, compactCDFGradient, he, cdfStripTime_eq hq]
  have heG : deriv (scalarCDFGradient β α q (Real.toNNReal (1-q))) =
      scalarCDFHessian β α q (Real.toNNReal (1-q)) := funext (fun x => (hd x).deriv)
  rw [heG]

theorem brownianCDFOverlap_hasDerivAt (W : BrownianSystem Ω) (β : ℝ)
    (α : StieltjesFunction ℝ) (ha : ∀ z, α z ∈ Icc (0:ℝ) 1)
    (h1 : α 1 = 1) (hβ : β ≠ 0) {q : ℝ} (hq : q ∈ Ioo (0:ℝ) 1) :
    HasDerivAt (brownianCDFOverlap W β α ha h1)
      (β^2*brownianCDFSusceptibilitySquare W β α ha h1 q) q := by
  let T := (q+1)/2
  have hqT : q < T := by dsimp [T]; linarith [hq.2]
  have hT1 : T < 1 := by dsimp [T]; linarith [hq.2]
  have hT0 : 0 ≤ T := hq.1.le.trans hqT.le
  have hβ2 := sq_pos_of_ne_zero hβ
  have hphys := physicalCDFJetSquareMoment_gradient_derivative W β α ha h1 hβ hT0 hT1
    (mul_pos hβ2 hq.1) (by
      have he : β^2*q/β^2=q := by field_simp
      rw [he]
      exact hqT)
  have H := hphys.comp q ((hasDerivAt_id q).const_mul (β^2))
  have hs := brownianCDFSusceptibilitySquare_eq_compact W β α ha h1 hβ hT1.le
    ⟨hq.1.le,hqT.le⟩
  rw [← hs] at H
  have H' : HasDerivAt
      (fun r => physicalCDFJetSquareMoment W β α ha h1 T 0 (β^2*r))
      (β^2*brownianCDFSusceptibilitySquare W β α ha h1 q) q := by
    simpa only [Function.comp_def, mul_one, mul_comm] using H
  apply H'.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hq.1 hqT] with r hr
  exact brownianCDFOverlap_eq_compact W β α ha h1 hβ ⟨hr.1.le,hr.2.le⟩

end SKConstants.ParisiFullSupport
