module

public import SKConstants.Completion.N13bc.PaddedSeven
public import SKConstants.Completion.N13e.RowEnergy

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal InnerProductSpace Matrix.Norms.L2Operator
namespace SKConstants.Completion.N13bc
open SKConstantsOAI.ZeroTemperatureSK LW Concentration
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]

def actualPaddedWeightedSq
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (V : ℝ≥0) (k r : ℕ) (h : k ≤ 2^r)
    {n : ℕ} (ω : Fin n → (Bool × Ω) × A) : ℝ :=
  LGram.sevenErrorSum r
    (matrixAverage (fun u => liftMatrix h (posteriorGramError W β t k u)) ω)
    (matrixAverage (fun u => liftMatrix h (crossError W Z β hβ t V k u)) ω)
    (liftVector h (posteriorWeight W β t k))
    (rowAverage (fun u => liftVector h
      (scalarHiddenSign u.1.1 • posteriorRow W β t k u - posteriorWeight W β t k)) ω)
    (liftVector h (queryWeight W β t k))
    (rowAverage (fun u => liftVector h
      (scalarHiddenSign u.1.1 • queryRow W Z β hβ t k u - queryWeight W β t k)) ω)

theorem actualPaddedWeightedSq_eq_sum
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (V : ℝ≥0) (k r : ℕ) (h : k ≤ 2^r)
    {n : ℕ} (ω : Fin n → (Bool × Ω) × A) :
    actualPaddedWeightedSq W Z β hβ t V k r h ω =
      ∑ i : SevenIndex r, ‖rowAverage (paddedSevenRow W Z β hβ t V k r h i) ω‖^2 :=
  (sum_sevenFeatures_sq_eq r _ _ _ _ _ _ ω).symm

theorem actual_padded_weightedSq_tail_explicit
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (ht : StrictMono t) (V : ℝ≥0) (k r : ℕ) (h : k ≤ 2^r)
    (hV : t (k+1) ≤ V) {B R : ℝ} (hB : 1 ≤ B) (hR : 1 ≤ R)
    (hProxy : (actualParisiPosteriorRowMGFProxy W β V : ℝ) ≤ R)
    (hWeight : ∀ j : Fin k, |queryWeight W β t k j / posteriorWeight W β t k j| ≤ B)
    {n : ℕ} (hn : 0 < n) {η : ℝ} (hη : 0 < η) :
    (linkedScalarRowsLaw W Z β V n).real
      {ω | 4*η^2*(2+5*(r+1 : ℝ)*((t k : ℝ)-t 0)) <
        actualPaddedWeightedSq W Z β hβ t V k r h ω} ≤
      2*(10*(2 : ℝ)^r-3)*(5 : ℝ)^(2^r)*Real.exp (-(n : ℝ)*
        min (η^2/(4096*B^2*(r+1 : ℝ)^2*Real.log (2+R)))
          (η/(256*B*(r+1 : ℝ)*Real.sqrt R*Real.log (2+R)))) := by
  have hB0 : 0 < B := lt_of_lt_of_le (by norm_num) hB
  have hp := weightedProducer_le_explicit hB0 hR r
  have hRows := actualPaddedSevenRowMGF_of_weight_bound W Z β hβ t ht V k r h hV hB hR hProxy hWeight
  have H := iid_seven_duration_total_tail (linkedScalarLaw W Z β V) hn r
    (paddedSevenRow W Z β hβ t V k r h) (measurable_paddedSevenRow W Z β hβ t V k r h)
    (paddedDuration t h) (paddedDuration_nonneg t ht.monotone h)
    (paddedSevenRow_zero W Z β hβ t ht V k r h)
    (by unfold explicitSevenVariance; positivity [Real.log_pos (by linarith : 1 < 2+R)])
    (by unfold explicitSevenRadius; positivity [Real.log_pos (by linarith : 1 < 2+R)]) hη
    (fun i a ha => localMGF_mono (hRows i a ha) hp.1 hp.2)
  have hsum : (∑ j, paddedDuration t h j) = (t k : ℝ)-t 0 := by
    calc
      _ = ∑ j ∈ restrictSet h Finset.univ, previousDuration t j := paddedDuration_sum t h _
      _ = ∑ j : Fin k, previousDuration t j := by simp [restrictSet]
      _ = _ := sum_previousDuration t k
  simp_rw [← actualPaddedWeightedSq_eq_sum] at H
  rw [hsum] at H
  convert H using 1
  · rfl
  · unfold explicitSevenVariance explicitSevenRadius
    congr 4 <;> field_simp <;> ring

theorem previousDuration_growing (δ : ℝ≥0) (j : ℕ) :
    previousDuration (growingQueryTime δ) j = LQ.meshDuration δ j := by
  exact growingQueryTime_sub δ j

theorem growing_real_weight_bound
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (k : ℕ)
    (hsmall : ∀ j < k, LQ.meshDuration δ j ≤ 1) (j : Fin k) :
    |queryWeight W β (growingQueryTime δ) k j /
      posteriorWeight W β (growingQueryTime δ) k j| ≤ Real.exp (1/8) := by
  have H := queryWeight_div_posteriorWeight_le W β hβ _ (growingQueryTime_strictMono δ hδ) k j
    (κ := (Real.exp (1/8))^2) (by
      rw [previousDuration_growing, previousDuration_growing, LQ.meshDuration_succ,
        mul_div_cancel_left₀ _ (LQ.meshDuration_pos δ hδ _).ne']
      rw [← Real.exp_nat_mul]
      exact Real.exp_le_exp.mpr (by have := hsmall j j.isLt; norm_num; linarith))
  rw [Real.sqrt_sq (Real.exp_pos _).le] at H
  have hs : 0 ≤ posteriorWeight W β (growingQueryTime δ) k j := NNReal.coe_nonneg _
  simpa only [abs_div, abs_of_nonneg hs] using H

end SKConstants.Completion.N13bc
