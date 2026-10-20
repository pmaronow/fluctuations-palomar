module

public import SKConstants.ParisiCDFPathRight

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
noncomputable section

namespace SKConstants.ParisiFullSupport

open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.SK.Analytic

variable {Ω : Type*} [MeasurableSpace Ω]

def physicalCDFJetSquareMoment (W : BrownianSystem Ω) (β : ℝ)
    (α : StieltjesFunction ℝ) (ha : ∀ z, α z ∈ Icc (0:ℝ) 1)
    (h1 : α 1 = 1) (T : ℝ) (n : ℕ) (v : ℝ) : ℝ :=
  ∫ w, (compactCDFJet β α T n (v/β^2)
    (finiteTemperatureCDFProcess W β α ha h1 (Real.toNNReal v) w))^2 ∂W.law

lemma physicalCDFJetSquareMoment_eq_expected (W : BrownianSystem Ω) (β : ℝ)
    (α : StieltjesFunction ℝ) (ha : ∀ z, α z ∈ Icc (0:ℝ) 1)
    (h1 : α 1 = 1) (hβ : β ≠ 0) {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1)
    (n : ℕ) :
    physicalCDFJetSquareMoment W β α ha h1 T n =
      ((physicalCDFJetField β α ha h1 hβ hT0 hT1 n).mul
        (physicalCDFJetField β α ha h1 hβ hT0 hT1 n)).expected
        (finiteTemperatureCDFDrift β α ha h1) W := by
  funext v
  unfold physicalCDFJetSquareMoment TimeField.expected TimeField.mul
    physicalCDFJetField rescaleTimeField compactCDFJetField finiteTemperatureCDFProcess
  apply integral_congr_ae
  filter_upwards [] with w
  change (compactCDFJet β α T n (v/β^2)
    ((finiteTemperatureCDFDrift β α ha h1).solution W.driver (Real.toNNReal v) w))^2 = _
  rw [show (1/β^2)*v=v/β^2 by ring]
  exact pow_two _

lemma physicalCDFJetSquareMoment_continuous (W : BrownianSystem Ω) (β : ℝ)
    (α : StieltjesFunction ℝ) (ha : ∀ z, α z ∈ Icc (0:ℝ) 1)
    (h1 : α 1 = 1) (hβ : β ≠ 0) {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1)
    (n : ℕ) : Continuous (physicalCDFJetSquareMoment W β α ha h1 T n) := by
  rw [physicalCDFJetSquareMoment_eq_expected W β α ha h1 hβ hT0 hT1]
  exact TimeField.expected_continuous _ _ _

theorem physicalCDFJetSquareMoment_gradient_right_derivative
    (W : BrownianSystem Ω) (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0:ℝ) 1) (h1 : α 1 = 1) (hβ : β ≠ 0)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) (v : ℝ≥0)
    (hv : (v:ℝ)/β^2 < T) :
    HasDerivWithinAt (physicalCDFJetSquareMoment W β α ha h1 T 0)
      (physicalCDFJetSquareMoment W β α ha h1 T 1 v) (Ioi (v:ℝ)) v := by
  let F := physicalCDFJetField β α ha h1 hβ hT0 hT1 0
  let b := finiteTemperatureCDFDrift β α ha h1
  have hvH : (v:ℝ) < T/(1/β^2) := by
    have hb := sq_pos_of_ne_zero hβ
    simp only [one_div, div_inv_eq_mul]
    exact (div_lt_iff₀ hb).mp hv
  have hbr := (finiteTemperatureCDFDrift_path_right_continuous W β α ha h1).mono
    (fun w hw => hw v)
  have H := (F.mul F).expected_hasDerivWithinAt_right b W v hvH hbr
  have he : (∫ w, (F.mul F).generator b.f v (b.solution W.driver v w) ∂W.law) =
      physicalCDFJetSquareMoment W β α ha h1 T 1 v := by
    apply integral_congr_ae
    filter_upwards [] with w
    have hpt : (v:ℝ)/β^2 ∈ Icc (0:ℝ) T :=
      ⟨div_nonneg v.coe_nonneg (sq_nonneg β),hv.le⟩
    have hbf : b.f v = physicalCDFCompactDrift β α T v := by
      funext x
      exact finiteTemperatureCDFDrift_eq_compact β α ha h1 hβ hT1.le hpt x
    change (F.mul F).generator b.f v (b.solution W.driver v w) = _
    unfold TimeField.generator
    rw [hbf]
    change (F.mul F).generator (physicalCDFCompactDrift β α T) v
      (b.solution W.driver v w) = _
    rw [physicalCDFGradient_square_generator β α ha h1 hβ hT0 hT1]
    simp only [finiteTemperatureCDFProcess, Real.toNNReal_coe]
    rfl
  rw [he, ← physicalCDFJetSquareMoment_eq_expected W β α ha h1 hβ hT0 hT1] at H
  exact H

lemma hasDerivAt_of_continuous_right_derivative {f d : ℝ → ℝ} {H q : ℝ}
    (hf : Continuous f) (hd : Continuous d)
    (hderiv : ∀ r, 0 ≤ r → r < H → HasDerivWithinAt f (d r) (Ioi r) r)
    (hq : q ∈ Ioo (0:ℝ) H) : HasDerivAt f (d q) q := by
  have hD : HasDerivAt (fun r => f 0 + ∫ t in (0:ℝ)..r, d t) (d q) q :=
    (intervalIntegral.integral_hasDerivAt_right (hd.intervalIntegrable _ _)
      hd.stronglyMeasurable.stronglyMeasurableAtFilter hd.continuousAt).const_add (f 0)
  apply hD.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hq.1 hq.2] with r hr
  have hi := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hr.1.le
    hf.continuousOn (fun t ht => hderiv t ht.1.le (ht.2.trans hr.2))
    (hd.intervalIntegrable _ _)
  linarith

theorem physicalCDFJetSquareMoment_gradient_derivative
    (W : BrownianSystem Ω) (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0:ℝ) 1) (h1 : α 1 = 1) (hβ : β ≠ 0)
    {T v : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) (hv0 : 0 < v)
    (hv : v/β^2 < T) :
    HasDerivAt (physicalCDFJetSquareMoment W β α ha h1 T 0)
      (physicalCDFJetSquareMoment W β α ha h1 T 1 v) v := by
  apply hasDerivAt_of_continuous_right_derivative
    (H := T*β^2)
    (physicalCDFJetSquareMoment_continuous W β α ha h1 hβ hT0 hT1 0)
    (physicalCDFJetSquareMoment_continuous W β α ha h1 hβ hT0 hT1 1)
  · intro r hr0 hrH
    have hr : r/β^2 < T := (div_lt_iff₀ (sq_pos_of_ne_zero hβ)).mpr hrH
    simpa only [Real.coe_toNNReal r hr0] using
      physicalCDFJetSquareMoment_gradient_right_derivative W β α ha h1 hβ hT0 hT1
        (Real.toNNReal r) (by simpa only [Real.coe_toNNReal r hr0] using hr)
  · exact ⟨hv0,(div_lt_iff₀ (sq_pos_of_ne_zero hβ)).mp hv⟩

end SKConstants.ParisiFullSupport
