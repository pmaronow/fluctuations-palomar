module

public import ComparisonNativeActualComparableBandHighResponse

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 10000000

 theorem bounded_integral_tendsto_zero_of_positive_cut
    {X : Type*} [MeasurableSpace X]
    (mu : ℕ→Measure X) [∀n,IsFiniteMeasure (mu n)]
    (f : ℕ→X→ℝ) (hf : ∀n,Integrable (f n) (mu n))
    (L : ℝ→ℕ→Set X) (hL : ∀c n,MeasurableSet (L c n))
    (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ᶠn in atTop,∀ᵐw∂mu n,|f n w| ≤ B)
    (hmass : ∀c>0,∀n,(mu n).real (L c n) ≤ c)
    (hpositive : ∀c>0,Tendsto (fun n=>∫w in (L c n)ᶜ,|f n w|∂mu n) atTop (𝓝 0)) :
    Tendsto (fun n=>∫w,|f n w|∂mu n) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall (fun n=>ha.trans_le (integral_nonneg (fun _=>abs_nonneg _)))
  · intro e he
    let c:=e/(2*(B+1))
    have hc : 0 < c:=by dsimp only [c];positivity
    have hBc : B*c < e/2 := by
      have H : B/(B+1) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
      have HH:=mul_lt_mul_of_pos_left H (half_pos he)
      calc
        B*c = (e/2)*(B/(B+1)) := by dsimp only [c];field_simp
        _ < e/2*1 := HH
        _ = e/2 := by ring
    filter_upwards [hbound,(hpositive c hc).eventually (eventually_lt_nhds (half_pos he))]
      with n hn hnpositive
    have Hlow : (∫w in L c n,|f n w|∂mu n) ≤ B*c := by
      have H:=integral_mono_ae (hf n).abs.restrict (integrable_const (μ:=(mu n).restrict (L c n)) B)
        (ae_restrict_of_ae hn)
      rw [integral_const,measureReal_restrict_apply MeasurableSet.univ,univ_inter,smul_eq_mul] at H
      exact H.trans (by nlinarith only [mul_le_mul_of_nonneg_left (hmass c hc n) hB])
    rw [←integral_add_compl (hL c n) (hf n).abs]
    linarith only [Hlow,hBc,hnpositive]

 def positiveOriginalMassBand (x v c : ℝ) : Set ParisiFinite.OrderPoint :=
  {w | c*x ≤ (w:ℝ) ∧ (w:ℝ) ≤ v}

 theorem positiveOriginalMassBand_measurable (x v c : ℝ) :
    MeasurableSet (positiveOriginalMassBand x v c) :=
  (measurableSet_le measurable_const measurable_subtype_coe).inter
    (measurableSet_le measurable_subtype_coe measurable_const)

 theorem normalized_clock_mass_restrict_positive_band (x v c : ℝ) :
    (comparisonNormalizedClockMass x v).restrict {w : ParisiFinite.OrderPoint | (w:ℝ)<c*x}ᶜ=
      ENNReal.ofReal (1/x) • (uniformOrderMass : Measure ParisiFinite.OrderPoint).restrict
        (positiveOriginalMassBand x v c) := by
  unfold comparisonNormalizedClockMass positiveOriginalMassBand
  rw [Measure.restrict_smul,Measure.restrict_restrict]
  · congr 2
    ext w
    simp only [mem_inter_iff,mem_compl_iff,mem_ofPred_eq,not_lt]
  · exact (measurableSet_lt measurable_subtype_coe measurable_const).compl

 theorem normalized_clock_mass_low_prefix_le {x v c : ℝ}
    (hx : 0 < x) (hc : 0 < c) :
    (comparisonNormalizedClockMass x v).real {w : ParisiFinite.OrderPoint | (w:ℝ)<c*x} ≤ c := by
  have Hle : (uniformOrderMass : Measure ParisiFinite.OrderPoint).real
      ({w : ParisiFinite.OrderPoint | (w:ℝ)<c*x} ∩ {w : ParisiFinite.OrderPoint | (w:ℝ)≤v}) ≤ c*x := by
    by_cases hcx : c*x ≤ 1
    · have hcut : min (c*x) 1∈Icc (0:ℝ) 1:=⟨by positivity,min_le_right _ _⟩
      have Hsub : ({w : ParisiFinite.OrderPoint | (w:ℝ)<c*x} ∩ {w : ParisiFinite.OrderPoint | (w:ℝ)≤v}) ⊆
          {w : ParisiFinite.OrderPoint | (w:ℝ)≤ min (c*x) 1}:=
        fun w hw=>le_min hw.1.le w.property.2
      exact (measureReal_mono Hsub).trans ((uniformOrderMass_atMost hcut).le.trans (min_le_left _ _))
    · have H:=measureReal_mono (μ:=(uniformOrderMass : Measure ParisiFinite.OrderPoint))
        (show ({w : ParisiFinite.OrderPoint | (w:ℝ)<c*x} ∩ {w : ParisiFinite.OrderPoint | (w:ℝ)≤v}) ⊆ univ from subset_univ _)
      rw [probReal_univ] at H
      exact H.trans (le_of_not_ge hcx)
  unfold comparisonNormalizedClockMass
  rw [measureReal_ennreal_smul_apply,ENNReal.toReal_ofReal (one_div_nonneg.mpr hx.le),
    measureReal_restrict_apply (measurableSet_lt measurable_subtype_coe measurable_const)]
  exact (mul_le_mul_of_nonneg_left Hle (one_div_nonneg.mpr hx.le)).trans_eq (by field_simp)

end OAI.SKFluctuations.LaplaceWindowFormalization
