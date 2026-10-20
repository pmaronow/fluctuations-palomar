module
public import SKConstants.ParisiFullTerminalSpinLaw
public import SKConstants.ParisiFullMartingale
public import SKConstants.ParisiFullPosteriorProfile

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace SKConstants
open SKConstantsOAI.ZeroTemperatureSK ParisiFullSupport
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {Ω : Type*} [MeasurableSpace Ω]
local instance ParisiSpinPinning_localInstance1 (W : BrownianSystem Ω) : IsProbabilityMeasure W.law := W.isProbability

def actualParisiFullPosteriorMean (W : BrownianSystem Ω) (β : ℝ) (S : ℝ≥0) : Ω → ℝ :=
  fun w => actualParisiFullMagnetization β S (actualParisiFullScalarProcess W β S w)

lemma measurable_actualParisiFullPosteriorMean (W : BrownianSystem Ω) (β : ℝ) (S : ℝ≥0) :
    Measurable (actualParisiFullPosteriorMean W β S) := by
  have hc : Continuous (actualParisiFullMagnetization β (S : ℝ)) :=
    continuous_iff_continuousAt.mpr (fun x =>
      (actualParisiFullMagnetization_hasDerivAt β S x).continuousAt)
  exact hc.measurable.comp ((actualParisiFullScalarDrift β).solution_measurable W S)

lemma abs_actualParisiFullPosteriorMean_le (W : BrownianSystem Ω) (β : ℝ) (S : ℝ≥0) (w : Ω) :
    |actualParisiFullPosteriorMean W β S w| ≤ 1 :=
  (actualParisiFullMagnetization_curvature_bounds β S _).1

lemma integral_scalarHiddenPriorBool_zero (f : Bool → ℝ) :
    (∫ b, f b ∂scalarHiddenPriorBool 0) = (1/2 : ℝ)*f true+(1/2 : ℝ)*f false := by
  rw [scalarHiddenPriorBool, integral_add_measure
    ((integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top)
    ((integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac,
    ENNReal.toReal_ofReal (scalarPlusWeight_pos 0).le,
    ENNReal.toReal_ofReal (scalarMinusWeight_pos 0).le]
  simp [scalarPlusWeight,scalarMinusWeight]

theorem actualParisiFullTerminalSpinLaw_integral_bounded
    (W : BrownianSystem Ω) (β : ℝ) (T : ℝ≥0)
    (f : Bool × Ω → ℝ) (hf : Measurable f) (C : ℝ) (hC : ∀ u, |f u| ≤ C) :
    (∫ u, f u ∂actualParisiFullTerminalSpinLaw β W T) =
      ∫ w, (1/2 : ℝ)*(1+actualParisiFullPosteriorMean W β T w)*f (true,w)+
        (1/2 : ℝ)*(1-actualParisiFullPosteriorMean W β T w)*f (false,w) ∂W.law := by
  let D := actualParisiFullTerminalSpinDensity β W T
  have hD : Measurable D := measurable_actualParisiFullTerminalSpinDensity β W T
  have hDB (u : Bool × Ω) : |D u| ≤ 2 := by
    have hm := abs_actualParisiFullPosteriorMean_le W β T u.2
    change |1+scalarHiddenSign u.1*actualParisiFullPosteriorMean W β T u.2| ≤ 2
    have hs : |scalarHiddenSign u.1|=1 := by cases u.1 <;> simp [scalarHiddenSign]
    calc
      _ ≤ |(1:ℝ)|+|scalarHiddenSign u.1*actualParisiFullPosteriorMean W β T u.2| := abs_add_le _ _
      _ = 1+|actualParisiFullPosteriorMean W β T u.2| := by rw [abs_one,abs_mul,hs,one_mul]
      _ ≤ 2 := by linarith
  have hi : Integrable (fun u => D u*f u) ((scalarHiddenPriorBool 0).prod W.law) := by
    apply Integrable.of_bound (f := fun u => D u*f u) (hD.mul hf).aestronglyMeasurable (2*C)
    apply ae_of_all
    intro u
    rw [Real.norm_eq_abs,abs_mul]
    exact (mul_le_mul_of_nonneg_right (hDB u) (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (hC u) (by norm_num))
  unfold actualParisiFullTerminalSpinLaw
  change (∫ u, f u ∂((scalarHiddenPriorBool 0).prod W.law).withDensity
    (fun u => ENNReal.ofReal (D u))) = _
  rw [integral_withDensity_eq_integral_toReal_smul
    hD.ennreal_ofReal (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  have hpos (u : Bool × Ω) : 0 ≤ D u := (actualParisiFullTerminalSpinDensity_pos β W T u).le
  simp_rw [ENNReal.toReal_ofReal (hpos _),smul_eq_mul]
  rw [integral_prod_symm _ hi]
  apply integral_congr_ae
  apply ae_of_all
  intro w
  change (∫ b, D (b,w)*f (b,w) ∂scalarHiddenPriorBool 0) = _
  rw [integral_scalarHiddenPriorBool_zero]
  simp only [D,actualParisiFullTerminalSpinDensity,actualParisiSpinLinkDensity,
    actualParisiFullTerminalField,actualParisiFullPosteriorMean,actualParisiFullScalarProcess,
    scalarHiddenSign,Bool.false_eq_true,↓reduceIte,one_mul,neg_one_mul]
  ring

theorem actualParisiFullTerminalSpinLaw_spin_test
    (W : BrownianSystem Ω) (β : ℝ) (T : ℝ≥0)
    (f : Ω → ℝ) (hf : Measurable f) (C : ℝ) (hC : ∀ w, |f w| ≤ C) :
    (∫ u, scalarHiddenSign u.1*f u.2 ∂actualParisiFullTerminalSpinLaw β W T) =
      ∫ w, actualParisiFullPosteriorMean W β T w*f w ∂W.law := by
  have hff : Measurable (fun u : Bool × Ω => scalarHiddenSign u.1*f u.2) :=
    ((measurable_of_finite scalarHiddenSign).comp measurable_fst).mul (hf.comp measurable_snd)
  rw [actualParisiFullTerminalSpinLaw_integral_bounded W β T
    (fun u : Bool × Ω => scalarHiddenSign u.1*f u.2) hff C
    (fun u => by cases u.1 <;> simpa [scalarHiddenSign] using hC u.2)]
  apply integral_congr_ae
  exact ae_of_all _ (fun w => by simp only [scalarHiddenSign,Bool.false_eq_true,↓reduceIte]; ring)

theorem actualParisiFullPosteriorMean_covariance
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (S T : ℝ≥0) (hST : S ≤ T) :
    (∫ w, actualParisiFullPosteriorMean W β S w*actualParisiFullPosteriorMean W β T w ∂W.law) =
      ∫ w, (actualParisiFullPosteriorMean W β S w)^2 ∂W.law := by
  exact actualParisiMagnetization_crossMoment W β hβ S T hST

def actualParisiPinningError (W : BrownianSystem Ω) (β : ℝ) (S : ℝ≥0) : Bool × Ω → ℝ :=
  fun u => (scalarHiddenSign u.1-actualParisiFullPosteriorMean W β S u.2)^2

lemma measurable_actualParisiPinningError (W : BrownianSystem Ω) (β : ℝ) (S : ℝ≥0) :
    Measurable (actualParisiPinningError W β S) :=
  (((measurable_of_finite scalarHiddenSign).comp measurable_fst).sub
    ((measurable_actualParisiFullPosteriorMean W β S).comp measurable_snd)).pow_const 2

lemma actualParisiPinningError_mem_Icc (W : BrownianSystem Ω) (β : ℝ) (S : ℝ≥0) (u : Bool × Ω) :
    actualParisiPinningError W β S u ∈ Icc (0:ℝ) 4 := by
  have hm := abs_actualParisiFullPosteriorMean_le W β S u.2
  have hs : |scalarHiddenSign u.1|=1 := by cases u.1 <;> simp [scalarHiddenSign]
  have hd : |scalarHiddenSign u.1-actualParisiFullPosteriorMean W β S u.2|≤2 :=
    (abs_sub _ _).trans (by rw [hs]; linarith)
  refine ⟨sq_nonneg _, ?_⟩
  change (scalarHiddenSign u.1-actualParisiFullPosteriorMean W β S u.2)^2≤4
  rw [← sq_abs]
  exact (pow_le_pow_left₀ (abs_nonneg _) hd 2).trans_eq (by norm_num)

theorem actualParisiPinningError_mean
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (S T : ℝ≥0) (hST : S ≤ T) :
    (∫ u,actualParisiPinningError W β S u ∂actualParisiFullTerminalSpinLaw β W T) =
      1-(∫ w,(actualParisiFullPosteriorMean W β S w)^2 ∂W.law) := by
  rw [actualParisiFullTerminalSpinLaw_integral_bounded W β T _
    (measurable_actualParisiPinningError W β S) 4
    (fun u => by
      rw [abs_of_nonneg (actualParisiPinningError_mem_Icc W β S u).1]
      exact (actualParisiPinningError_mem_Icc W β S u).2)]
  have hp (w : Ω) : (1/2 : ℝ)*(1+actualParisiFullPosteriorMean W β T w)*
      actualParisiPinningError W β S (true,w)+
      (1/2 : ℝ)*(1-actualParisiFullPosteriorMean W β T w)*actualParisiPinningError W β S (false,w) =
      1+(actualParisiFullPosteriorMean W β S w)^2-
        2*(actualParisiFullPosteriorMean W β S w*actualParisiFullPosteriorMean W β T w) := by
    simp only [actualParisiPinningError,scalarHiddenSign,Bool.false_eq_true,↓reduceIte]
    ring
  simp_rw [hp]
  have hiSq : Integrable (fun w => (actualParisiFullPosteriorMean W β S w)^2) W.law := by
    apply Integrable.of_bound (f := fun w => (actualParisiFullPosteriorMean W β S w)^2)
      ((measurable_actualParisiFullPosteriorMean W β S).pow_const 2).aestronglyMeasurable 1
    exact ae_of_all _ (fun w => by
      rw [Real.norm_eq_abs,abs_pow]
      exact (pow_le_pow_left₀ (abs_nonneg _) (abs_actualParisiFullPosteriorMean_le W β S w) 2).trans_eq
        (by norm_num))
  have hiProd : Integrable (fun w => actualParisiFullPosteriorMean W β S w*
      actualParisiFullPosteriorMean W β T w) W.law := by
    apply Integrable.of_bound (f := fun w => actualParisiFullPosteriorMean W β S w*
      actualParisiFullPosteriorMean W β T w) ((measurable_actualParisiFullPosteriorMean W β S).mul
      (measurable_actualParisiFullPosteriorMean W β T)).aestronglyMeasurable 1
    exact ae_of_all _ (fun w => by
      rw [Real.norm_eq_abs,abs_mul]
      simpa using mul_le_mul (abs_actualParisiFullPosteriorMean_le W β S w)
        (abs_actualParisiFullPosteriorMean_le W β T w) (abs_nonneg _) (by norm_num : (0:ℝ)≤1))
  rw [integral_sub (f := fun w => 1+(actualParisiFullPosteriorMean W β S w)^2)
    (g := fun w => 2*(actualParisiFullPosteriorMean W β S w*actualParisiFullPosteriorMean W β T w))
    ((integrable_const 1).add hiSq) (hiProd.const_mul 2),
    integral_add (f := fun _ : Ω => (1:ℝ)) (g := fun w => (actualParisiFullPosteriorMean W β S w)^2)
      (integrable_const 1) hiSq,integral_const_mul,
    actualParisiFullPosteriorMean_covariance W β hβ S T hST]
  simp
  ring

end SKConstants
