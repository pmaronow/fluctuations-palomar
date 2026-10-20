module

public import SKConstants.Completion.LM6.Pinning
public import Mathlib.MeasureTheory.Constructions.UnitInterval

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators unitInterval
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace SKConstants.N20
open SKConstantsOAI.ZeroTemperatureSK

variable {Ω : Type*} [MeasurableSpace Ω]
local instance scalarLaw_probability (W : BrownianSystem Ω) : IsProbabilityMeasure W.law := W.isProbability

def thresholdBit (m : ℝ) (u : I) : Bool := decide ((u : ℝ) < (1 + m) / 2)

theorem measurable_thresholdBit : Measurable (fun z : ℝ × I => thresholdBit z.1 z.2) := by
  apply measurable_to_bool
  have hs : MeasurableSet {z : ℝ × I | (z.2 : ℝ) < (1 + z.1) / 2} :=
    measurableSet_lt (measurable_subtype_coe.comp measurable_snd)
      ((measurable_const.add measurable_fst).div_const 2)
  have he : (fun z : ℝ × I => thresholdBit z.1 z.2) ⁻¹' {true} =
      {z : ℝ × I | (z.2 : ℝ) < (1 + z.1) / 2} := by
    ext z
    simp [thresholdBit]
  rwa [he]

def thresholdError (m : ℝ) (u : I) : ℝ := (scalarHiddenSign (thresholdBit m u) - m) ^ 2

theorem measurable_thresholdError : Measurable (fun z : ℝ × I => thresholdError z.1 z.2) :=
  (((measurable_of_finite scalarHiddenSign).comp measurable_thresholdBit).sub
    measurable_fst).pow_const 2

theorem thresholdError_mem_Icc (m : ℝ) (hm : |m| ≤ 1) (u : I) :
    thresholdError m u ∈ Icc (0 : ℝ) 4 := by
  have hs : |scalarHiddenSign (thresholdBit m u)| = 1 := by
    cases thresholdBit m u <;> simp [scalarHiddenSign]
  have hd : |scalarHiddenSign (thresholdBit m u) - m| ≤ 2 :=
    (abs_sub _ _).trans (by rw [hs]; linarith)
  refine ⟨sq_nonneg _, ?_⟩
  dsimp [thresholdError]
  rw [← sq_abs]
  nlinarith [abs_nonneg (scalarHiddenSign (thresholdBit m u) - m)]

theorem integral_thresholdError (m : ℝ) (hm : |m| ≤ 1) :
    (∫ u : I, thresholdError m u) = 1 - m ^ 2 := by
  let p : I := ⟨(1 + m) / 2, by constructor <;> linarith [(abs_le.mp hm).1, (abs_le.mp hm).2]⟩
  have he : (fun u : I => thresholdError m u) =
      (Iio p).piecewise (fun _ => (1 - m) ^ 2) (fun _ => (-1 - m) ^ 2) := by
    funext u
    by_cases hu : u < p
    · simp [thresholdError, thresholdBit, Set.piecewise, hu, p, scalarHiddenSign,
        show (u : ℝ) < (1 + m) / 2 from hu]
    · simp [thresholdError, thresholdBit, Set.piecewise, hu, p, scalarHiddenSign,
        show ¬(u : ℝ) < (1 + m) / 2 from hu]
  rw [he, integral_piecewise measurableSet_Iio (integrable_const _).integrableOn
    (integrable_const _).integrableOn]
  simp only [setIntegral_const, smul_eq_mul, Measure.real, unitInterval.volume_Iio,
    compl_Iio, unitInterval.volume_Ici]
  rw [ENNReal.toReal_ofReal p.property.1, ENNReal.toReal_ofReal (by linarith [p.property.2])]
  dsimp [p]
  ring

def scalarThresholdError (W : BrownianSystem Ω) (β : ℝ) (S : ℝ≥0) (z : Ω × I) : ℝ :=
  thresholdError (actualParisiFullPosteriorMean W β S z.1) z.2

theorem measurable_scalarThresholdError (W : BrownianSystem Ω) (β : ℝ) (S : ℝ≥0) :
    Measurable (scalarThresholdError W β S) :=
  measurable_thresholdError.comp
    (((measurable_actualParisiFullPosteriorMean W β S).comp measurable_fst).prodMk
      measurable_snd)

theorem scalarThresholdError_mem_Icc (W : BrownianSystem Ω) (β : ℝ) (S : ℝ≥0) (z : Ω × I) :
    scalarThresholdError W β S z ∈ Icc (0 : ℝ) 4 :=
  thresholdError_mem_Icc _ (abs_actualParisiFullPosteriorMean_le W β S z.1) _

theorem scalarThresholdError_mean (W : BrownianSystem Ω) (β : ℝ) (S : ℝ≥0) :
    (∫ z, scalarThresholdError W β S z ∂W.law.prod (volume : Measure I)) =
      1 - ∫ w, (actualParisiFullPosteriorMean W β S w) ^ 2 ∂W.law := by
  have hi : Integrable (scalarThresholdError W β S) (W.law.prod (volume : Measure I)) :=
    Integrable.of_bound (measurable_scalarThresholdError W β S).aestronglyMeasurable 4
      (ae_of_all _ (fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (scalarThresholdError_mem_Icc W β S z).1]
        exact (scalarThresholdError_mem_Icc W β S z).2))
  have hiSq : Integrable (fun w => (actualParisiFullPosteriorMean W β S w) ^ 2) W.law :=
    Integrable.of_bound ((measurable_actualParisiFullPosteriorMean W β S).pow_const 2).aestronglyMeasurable
      1 (ae_of_all _ (fun w => by
        rw [Real.norm_eq_abs, abs_pow]
        simpa using pow_le_pow_left₀ (abs_nonneg _)
          (abs_actualParisiFullPosteriorMean_le W β S w) 2))
  rw [integral_prod _ hi]
  simp_rw [scalarThresholdError, integral_thresholdError _
    (abs_actualParisiFullPosteriorMean_le W β S _)]
  rw [integral_sub (integrable_const 1) hiSq]
  simp

theorem bounded_iid_radius_tail {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ] (Y : A → ℝ) (hY : Measurable Y)
    (hRange : ∀ z, Y z ∈ Icc (0 : ℝ) 4) (n : ℕ) (hn : 0 < n)
    (R ε : ℝ) (hR : 0 < R) (hε : 0 < ε) (hMean : (∫ z, Y z ∂μ) ≤ ε)
    (hSmall : 16 * (n : ℝ) * ε ≤ R) :
    (Measure.pi (fun _ : Fin n => μ)).real {z | R / 4 < ∑ i, Y (z i)} ≤
      2 * Real.exp (-R / 64) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let η := R / (8 * (n : ℝ))
  have hη : 0 < η := by dsimp [η]; positivity
  have hSmall' : 2 * ε ≤ η := by
    dsimp [η]
    rw [le_div_iff₀ (by positivity : 0 < 8 * (n : ℝ))]
    nlinarith
  have ht := Concentration.bounded_pinning_iid_tail μ Y hY hRange n hn ε η hε hη hMean hSmall'
  have hsub : {z : Fin n → A | R / 4 < ∑ i, Y (z i)} ⊆
      {z | 2 * η ≤ (∑ i, Y (z i)) / (n : ℝ)} := by
    intro z hz
    change 2 * η ≤ (∑ i, Y (z i)) / (n : ℝ)
    rw [le_div_iff₀ hnR]
    have he : 2 * η * (n : ℝ) = R / 4 := by dsimp [η]; field_simp; ring
    rw [he]
    exact hz.le
  apply (measureReal_mono hsub).trans
  convert ht using 1
  congr 2
  dsimp [η]
  field_simp
  ring

theorem scalarPinning_mean_le_exp (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (v T : ℝ≥0) (hv : 1 ≤ v) (hST : parisiEquilibriumPhysicalEndpoint β + v ≤ T) :
    (∫ z, actualParisiPinningError W β (parisiEquilibriumPhysicalEndpoint β + v) z
      ∂actualParisiFullTerminalSpinLaw β W T) ≤ 4 * Real.exp (-(v : ℝ) / 2) := by
  rw [actualParisiPinningError_mean_postProfile W β hβ v T hST]
  have hv0 : (0 : ℝ) < v := by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℝ≥0) < 1) hv)
  have ht : actualParisiContinuationP W β v ≤ 4 * scalarTailScale v := by
    simpa only [Real.toNNReal_coe] using actualParisiContinuationP_le_tail W β v hv0
  exact ht.trans
    (mul_le_mul_of_nonneg_left (scalarTailScale_le_exp_of_one_le v hv) (by norm_num))

theorem scalarThreshold_mean_le_exp (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (v : ℝ≥0) (hv : 1 ≤ v) :
    (∫ z, scalarThresholdError W β (parisiEquilibriumPhysicalEndpoint β + v) z
      ∂W.law.prod (volume : Measure I)) ≤ 4 * Real.exp (-(v : ℝ) / 2) := by
  rw [scalarThresholdError_mean, ← actualParisiPinningError_mean W β hβ _ _ le_rfl]
  exact scalarPinning_mean_le_exp W β hβ v _ hv le_rfl

end SKConstants.N20
