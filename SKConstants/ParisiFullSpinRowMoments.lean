module
public import SKConstants.ParisiFullRowMGFBudget
public import SKConstants.ParisiSpinPinning

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology BigOperators InnerProductSpace
namespace SKConstants
open SKConstantsOAI.ZeroTemperatureSK
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {Ω : Type*} [MeasurableSpace Ω]
local instance ParisiFullSpinRowMoments_localInstance1 (W : BrownianSystem Ω) : IsProbabilityMeasure W.law := W.isProbability

lemma integrable_actualParisiMagnetizationObservable (W : BrownianSystem Ω) (β : ℝ) (t : ℝ≥0) :
    Integrable (actualParisiMagnetizationObservable W β t) W.law :=
  Integrable.of_bound (measurable_actualParisiMagnetizationObservable W β t).aestronglyMeasurable 1
    (ae_of_all _ (fun w => by rw [Real.norm_eq_abs]; exact actualParisiMagnetizationObservable_abs_le W β t w))

lemma actualParisiMagnetizationObservable_zero_ae (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) :
    actualParisiMagnetizationObservable W β 0=ᵐ[W.law] 0 := by
  have H := actualParisiFullOverlap_pre W β hβ 0 bot_le
  simp only [actualParisiFullOverlap,NNReal.coe_zero,zero_div] at H
  have hi : Integrable (fun w => (actualParisiMagnetizationObservable W β 0 w)^2) W.law := by
    simpa only [pow_two] using integrable_actualParisiMagnetization_pair W β 0 0
  have ha := (integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) hi).mp H
  filter_upwards [ha] with w hw
  simpa only [Pi.zero_apply,sq_eq_zero_iff] using hw

theorem actualParisiMagnetizationObservable_mean_zero (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (T : ℝ≥0) : (∫ w,actualParisiMagnetizationObservable W β T w ∂W.law)=0 := by
  have H := actualParisiFullProcess_martingale_test W β hβ 0 T
    (fun _ => (1:ℝ)) measurable_const 1 (fun _ => by norm_num)
  simp only [zero_add,NNReal.coe_zero,one_mul] at H
  change (∫ w,actualParisiMagnetizationObservable W β T w-actualParisiMagnetizationObservable W β 0 w ∂W.law)=0 at H
  rw [integral_sub (integrable_actualParisiMagnetizationObservable W β T)
    (integrable_actualParisiMagnetizationObservable W β 0),
    integral_congr_ae (actualParisiMagnetizationObservable_zero_ae W β hβ)] at H
  simp only [Pi.zero_apply,integral_zero,sub_zero] at H
  exact H

theorem actualParisiFullTerminalSpinLaw_spin_mean_zero (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (T : ℝ≥0) : (∫ u,scalarHiddenSign u.1 ∂actualParisiFullTerminalSpinLaw β W T)=0 := by
  have H := actualParisiFullTerminalSpinLaw_spin_test W β T (fun _ => (1:ℝ)) measurable_const 1
    (fun _ => by norm_num)
  simp only [mul_one] at H
  exact H.trans (actualParisiMagnetizationObservable_mean_zero W β hβ T)

theorem actualParisiFullTerminalSpinLaw_spin_secondMoment (W : BrownianSystem Ω) (β : ℝ)
    (T : ℝ≥0) : (∫ u,(scalarHiddenSign u.1)^2 ∂actualParisiFullTerminalSpinLaw β W T)=1 := by
  have he : (fun u : Bool × Ω => (scalarHiddenSign u.1)^2)=fun _ => (1:ℝ) := by
    funext u
    cases u.1 <;> norm_num [scalarHiddenSign]
  rw [he,integral_const,probReal_univ,one_smul]

theorem actualParisiFullTerminalSpinLaw_spin_hasSubgaussianMGF (W : BrownianSystem Ω) (β : ℝ)
    (hβ : 1 < β) (T : ℝ≥0) :
    HasSubgaussianMGF (fun u : Bool × Ω => scalarHiddenSign u.1) 1 (actualParisiFullTerminalSpinLaw β W T) := by
  have hm : Measurable (fun u : Bool × Ω => scalarHiddenSign u.1) :=
    (measurable_of_finite scalarHiddenSign).comp measurable_fst
  have hb : ∀ᵐ u ∂actualParisiFullTerminalSpinLaw β W T,scalarHiddenSign u.1∈Icc (-1:ℝ) 1 :=
    ae_of_all _ (fun u => by cases u.1 <;> norm_num [scalarHiddenSign])
  convert hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero hm.aemeasurable hb
    (actualParisiFullTerminalSpinLaw_spin_mean_zero W β hβ T) using 1
  apply NNReal.eq
  simp only [NNReal.coe_one,NNReal.coe_pow,NNReal.coe_div,coe_nnnorm]
  norm_num

theorem actualParisiFullTerminalSpinLaw_increment_spin_moment
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (S T H : ℝ≥0) (hST : S ≤ T) (hTH : T ≤ H) :
    (∫ u,actualParisiMagnetizationIncrement W β S T u.2*scalarHiddenSign u.1
      ∂actualParisiFullTerminalSpinLaw β W H)=
      actualParisiFullOverlap W β T-actualParisiFullOverlap W β S := by
  have HX := actualParisiFullTerminalSpinLaw_spin_test W β H
    (actualParisiMagnetizationIncrement W β S T) (measurable_actualParisiMagnetizationIncrement W β S T) 2
    (actualParisiMagnetizationIncrement_abs_le W β S T)
  simp_rw [mul_comm] at HX
  rw [HX]
  have HT := integrable_actualParisiMagnetization_pair W β T H
  have HS := integrable_actualParisiMagnetization_pair W β S H
  have he (w : Ω) : actualParisiMagnetizationIncrement W β S T w*actualParisiFullPosteriorMean W β H w=
      actualParisiMagnetizationObservable W β T w*actualParisiMagnetizationObservable W β H w-
        actualParisiMagnetizationObservable W β S w*actualParisiMagnetizationObservable W β H w := by
    simp only [actualParisiMagnetizationIncrement,actualParisiFullPosteriorMean,
      actualParisiMagnetizationObservable,mul_sub,sub_mul]
  conv_lhs => arg 2; ext w; rw [mul_comm]
  simp_rw [he]
  rw [integral_sub HT HS,actualParisiMagnetization_crossMoment W β hβ T H hTH,
    actualParisiMagnetization_crossMoment W β hβ S H (hST.trans hTH)]
  rfl

theorem actualParisiFullTerminalSpinLaw_normalized_increment_spin_moment
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (S T H : ℝ≥0) (hST : S < T) (hTH : T ≤ H) :
    (∫ u,(actualParisiMagnetizationIncrement W β S T u.2/
      (actualParisiPosteriorIntervalScale W β S T:ℝ))*scalarHiddenSign u.1
        ∂actualParisiFullTerminalSpinLaw β W H)=(actualParisiPosteriorIntervalScale W β S T:ℝ) := by
  have he (u : Bool × Ω) : (actualParisiMagnetizationIncrement W β S T u.2/
      (actualParisiPosteriorIntervalScale W β S T:ℝ))*scalarHiddenSign u.1=
      (actualParisiMagnetizationIncrement W β S T u.2*scalarHiddenSign u.1)/
        (actualParisiPosteriorIntervalScale W β S T:ℝ) := by ring
  simp_rw [he]
  rw [integral_div,actualParisiFullTerminalSpinLaw_increment_spin_moment W β hβ S T H hST.le hTH,
    ←actualParisiPosteriorIntervalScale_sq W β hβ S T hST]
  have hs := NNReal.coe_pos.mpr (actualParisiPosteriorIntervalScale_pos W β hβ S T hST)
  field_simp

end SKConstants
