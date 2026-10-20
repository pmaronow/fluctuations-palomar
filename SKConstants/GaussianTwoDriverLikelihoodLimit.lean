module
public import SKConstants.ScalarProcessTwoDriverLinked
public import Mathlib.MeasureTheory.Function.UniformIntegrable
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology

namespace SKConstants

def pairedGaussianScaledCoefficient (c : ℝ) (H : PairedGaussianCoefficient) :
    PairedGaussianCoefficient := fun n p => (c * (H n p).1, c * (H n p).2)

lemma measurable_pairedGaussianScaledCoefficient (c : ℝ) (H : PairedGaussianCoefficient)
    (hH : ∀ n, Measurable (H n)) :
    ∀ n, Measurable (pairedGaussianScaledCoefficient c H n) :=
  fun n => ((hH n).fst.const_mul c).prodMk ((hH n).snd.const_mul c)

def pairedGaussianBracket (H : PairedGaussianCoefficient) (h : ℕ → ℝ≥0) :
    (n : ℕ) → PairedGaussianHistory n → ℝ
  | 0, _ => 0
  | n + 1, p => pairedGaussianBracket H h n p.1 +
      ((H n p.1).1 ^ 2 + (H n p.1).2 ^ 2) * (h n : ℝ)

lemma pairedGaussianBracket_nonneg (H : PairedGaussianCoefficient) (h : ℕ → ℝ≥0)
    (n : ℕ) (p : PairedGaussianHistory n) : 0 ≤ pairedGaussianBracket H h n p := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    exact add_nonneg (ih p.1)
      (mul_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (h n).coe_nonneg)

lemma pairedGaussianBracket_bound (H : PairedGaussianCoefficient) (h : ℕ → ℝ≥0)
    (C : ℕ → ℝ) (hC : ∀ n p, (H n p).1 ^ 2 + (H n p).2 ^ 2 ≤ C n)
    (n : ℕ) (p : PairedGaussianHistory n) :
    pairedGaussianBracket H h n p ≤ ∑ j ∈ Finset.range n, C j * (h j : ℝ) := by
  induction n with
  | zero => simp [pairedGaussianBracket]
  | succ n ih =>
    rw [pairedGaussianBracket, Finset.sum_range_succ]
    exact add_le_add (ih p.1) (mul_le_mul_of_nonneg_right (hC n p.1) (h n).coe_nonneg)

lemma pairedGaussianExponential_square (H : PairedGaussianCoefficient) (h : ℕ → ℝ≥0)
    (n : ℕ) (p : PairedGaussianHistory n) :
    pairedGaussianExponential H h n p ^ 2 =
      pairedGaussianExponential (pairedGaussianScaledCoefficient 2 H) h n p *
        Real.exp (pairedGaussianBracket H h n p) := by
  induction n with
  | zero => simp [pairedGaussianExponential, pairedGaussianBracket]
  | succ n ih =>
    change (pairedGaussianExponential H h n p.1 *
      pairedGaussianStepFactor (H n p.1) (h n) p.2) ^ 2 =
      (pairedGaussianExponential (pairedGaussianScaledCoefficient 2 H) h n p.1 *
        pairedGaussianStepFactor (pairedGaussianScaledCoefficient 2 H n p.1) (h n) p.2) *
        Real.exp (pairedGaussianBracket H h n p.1 +
          ((H n p.1).1 ^ 2 + (H n p.1).2 ^ 2) * (h n : ℝ))
    rw [mul_pow, ih p.1, Real.exp_add]
    have hs (a b y w : ℝ) :
        (gaussianExponentialFactor a (h n) y * gaussianExponentialFactor b (h n) w) ^ 2 =
          (gaussianExponentialFactor (2*a) (h n) y * gaussianExponentialFactor (2*b) (h n) w) *
            Real.exp ((a ^ 2+b ^ 2)*(h n : ℝ)) := by
      simp only [gaussianExponentialFactor, pow_two, ← Real.exp_add]
      congr 1
      ring
    rw [show pairedGaussianStepFactor (H n p.1) (h n) p.2 ^ 2 =
        pairedGaussianStepFactor (pairedGaussianScaledCoefficient 2 H n p.1) (h n) p.2 *
          Real.exp (((H n p.1).1 ^ 2 + (H n p.1).2 ^ 2) * (h n : ℝ)) from
        hs (H n p.1).1 (H n p.1).2 p.2.1 p.2.2]
    ring

lemma lintegral_pairedGaussianExponential (H : PairedGaussianCoefficient)
    (hH : ∀ n, Measurable (H n)) (h : ℕ → ℝ≥0) (n : ℕ) :
    ∫⁻ p, ENNReal.ofReal (pairedGaussianExponential H h n p)
      ∂pairedGaussianHistoryLaw h n = 1 := by
  let := pairedGaussianLinkedHistoryLaw_isProbability H hH h n
  have hu : pairedGaussianLinkedHistoryLaw H h n Set.univ = 1 := measure_univ
  rw [pairedGaussianLinkedHistoryLaw_eq_withDensity H hH h n,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at hu
  exact hu

theorem lintegral_pairedGaussianExponential_sq_le (H : PairedGaussianCoefficient)
    (hH : ∀ n, Measurable (H n)) (h : ℕ → ℝ≥0) (n : ℕ) (V : ℝ)
    (hV : ∀ p, pairedGaussianBracket H h n p ≤ V) :
    ∫⁻ p, ENNReal.ofReal (pairedGaussianExponential H h n p ^ 2)
      ∂pairedGaussianHistoryLaw h n ≤ ENNReal.ofReal (Real.exp V) := by
  calc
    _ ≤ ∫⁻ p, ENNReal.ofReal (Real.exp V) * ENNReal.ofReal
        (pairedGaussianExponential (pairedGaussianScaledCoefficient 2 H) h n p)
        ∂pairedGaussianHistoryLaw h n := by
      apply lintegral_mono
      intro p
      change ENNReal.ofReal (pairedGaussianExponential H h n p ^ 2) ≤ _
      rw [pairedGaussianExponential_square, mul_comm,
        ENNReal.ofReal_mul (Real.exp_pos _).le]
      dsimp only
      gcongr
      exact hV p
    _ = _ := by
      rw [lintegral_const_mul _
        (measurable_pairedGaussianExponential _
          (measurable_pairedGaussianScaledCoefficient 2 H hH) h n).ennreal_ofReal,
        lintegral_pairedGaussianExponential _
          (measurable_pairedGaussianScaledCoefficient 2 H hH) h n, mul_one]

theorem integrable_pairedGaussianExponential_sq (H : PairedGaussianCoefficient)
    (hH : ∀ n, Measurable (H n)) (h : ℕ → ℝ≥0) (n : ℕ) (V : ℝ)
    (hV : ∀ p, pairedGaussianBracket H h n p ≤ V) :
    Integrable (fun p => pairedGaussianExponential H h n p ^ 2)
      (pairedGaussianHistoryLaw h n) := by
  refine ⟨((measurable_pairedGaussianExponential H hH h n).pow_const 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  simp_rw [Real.enorm_eq_ofReal (sq_nonneg _)]
  exact (lintegral_pairedGaussianExponential_sq_le H hH h n V hV).trans_lt
    ENNReal.ofReal_lt_top

theorem integral_pairedGaussianExponential_sq_le (H : PairedGaussianCoefficient)
    (hH : ∀ n, Measurable (H n)) (h : ℕ → ℝ≥0) (n : ℕ) (V : ℝ)
    (hV : ∀ p, pairedGaussianBracket H h n p ≤ V) :
    ∫ p, pairedGaussianExponential H h n p ^ 2 ∂pairedGaussianHistoryLaw h n ≤ Real.exp V := by
  have hb := lintegral_pairedGaussianExponential_sq_le H hH h n V hV
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_pairedGaussianExponential_sq H hH h n V hV)
    (ae_of_all _ (fun p => sq_nonneg _))] at hb
  exact (ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le).mp hb

theorem eLpNorm_pairedGaussianExponential_two_le (H : PairedGaussianCoefficient)
    (hH : ∀ n, Measurable (H n)) (h : ℕ → ℝ≥0) (n : ℕ) (V : ℝ)
    (hV : ∀ p, pairedGaussianBracket H h n p ≤ V) :
    eLpNorm (pairedGaussianExponential H h n) 2 (pairedGaussianHistoryLaw h n) ≤
      ENNReal.ofReal (Real.exp V) ^ (1 / (2 : ℝ)) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
    (measurable_pairedGaussianExponential H hH h n).aestronglyMeasurable]
  norm_num only [ENNReal.toReal_ofNat]
  simp_rw [Real.enorm_eq_ofReal (pairedGaussianExponential_pos H h n _).le,
    ENNReal.rpow_two, ← ENNReal.ofReal_pow (pairedGaussianExponential_pos H h n _).le 2]
  exact ENNReal.rpow_le_rpow (lintegral_pairedGaussianExponential_sq_le H hH h n V hV)
    (by norm_num)

theorem uniformIntegrable_of_eLpNorm_two_le {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ι → Ω → ℝ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ) (C : ℝ≥0)
    (hC : ∀ i, eLpNorm (X i) 2 μ ≤ C) : UniformIntegrable X 1 μ := by
  have hs (i : ι) (s : Set Ω) :
      eLpNorm (X i) 1 (μ.restrict s) ≤ (C : ℝ≥0∞) * (μ s) ^ (1 / (2 : ℝ)) := by
    have hc := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
      (μ := μ.restrict s) (p := 1) (q := 2) (by norm_num) ((hX i).restrict (s := s))
    have hm : eLpNorm (X i) 2 (μ.restrict s) ≤ C :=
      (eLpNorm_restrict_le _ _ _ _).trans (hC i)
    norm_num only [ENNReal.toReal_one, ENNReal.toReal_ofNat] at hc
    rw [Measure.restrict_apply_univ] at hc
    convert hc.trans (mul_le_mul' hm le_rfl) using 1
  constructor
  · unfold UnifIntegrable
    have ht : Tendsto (fun ε : ℝ≥0∞ => (C : ℝ≥0∞) * ε ^ (1 / (2 : ℝ)))
        (𝓝 0) (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul
        ((ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto (0 : ℝ≥0∞))
        (a := (C : ℝ≥0∞)) (Or.inr ENNReal.coe_ne_top)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (g := fun _ : ℝ≥0∞ => (0 : ℝ≥0∞)) tendsto_const_nhds ht (fun _ => bot_le)
    intro ε
    refine iSup_le (fun i => iSup_le (fun s => iSup_le (fun hε => ?_)))
    exact (hs i s).trans (mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hε (by norm_num)))
  · refine ⟨C, fun i => ?_⟩
    simpa only [measure_univ, ENNReal.one_rpow, mul_one, Measure.restrict_univ] using hs i Set.univ

theorem probability_density_of_tendstoInMeasure_of_eLpNorm_two_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (Y : Ω → ℝ)
    (hX : ∀ n, AEStronglyMeasurable (X n) μ)
    (hpos : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ X n ω)
    (hone : ∀ n, ∫ ω, X n ω ∂μ = 1)
    (C : ℝ≥0) (hC : ∀ n, eLpNorm (X n) 2 μ ≤ C)
    (hlim : TendstoInMeasure μ X atTop Y) :
    Integrable Y μ ∧ (∀ᵐ ω ∂μ, 0 ≤ Y ω) ∧
      (∫ ω, Y ω ∂μ = 1) ∧
      IsProbabilityMeasure (μ.withDensity (fun ω => ENNReal.ofReal (Y ω))) ∧
      Tendsto (fun n => eLpNorm (X n - Y) 1 μ) atTop (𝓝 0) := by
  have hui := uniformIntegrable_of_eLpNorm_two_le μ X hX C hC
  have hYi := hui.integrable_of_tendstoInMeasure hlim
  have hLp := tendsto_Lp_finite_of_tendstoInMeasure (p := 1) (by norm_num) (by norm_num)
    hX (memLp_one_iff_integrable.mpr hYi) hui.unifIntegrable hlim
  have hXi (n : ℕ) : Integrable (X n) μ :=
    memLp_one_iff_integrable.mp (hui.memLp n)
  have hmean : ∫ ω, Y ω ∂μ = 1 := by
    have hm := tendsto_integral_of_L1' Y (Eventually.of_forall hXi) hLp
    simp_rw [hone] at hm
    exact tendsto_nhds_unique hm tendsto_const_nhds
  have hYpos : ∀ᵐ ω ∂μ, 0 ≤ Y ω := by
    obtain ⟨ns, hns, hae⟩ := hlim.exists_seq_tendsto_ae
    have hp : ∀ᵐ ω ∂μ, ∀ n, 0 ≤ X (ns n) ω := ae_all_iff.mpr (fun n => hpos (ns n))
    filter_upwards [hae, hp] with ω hω hpω
    exact ge_of_tendsto hω (Eventually.of_forall hpω)
  refine ⟨hYi, hYpos, hmean, ?_, hLp⟩
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hYi hYpos, hmean]
  norm_num

lemma integral_pairedGaussianExponential (H : PairedGaussianCoefficient)
    (hH : ∀ n, Measurable (H n)) (h : ℕ → ℝ≥0) (n : ℕ) :
    ∫ p, pairedGaussianExponential H h n p ∂pairedGaussianHistoryLaw h n = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ (fun p => (pairedGaussianExponential_pos H h n p).le))
    (measurable_pairedGaussianExponential H hH h n).aestronglyMeasurable,
    lintegral_pairedGaussianExponential H hH h n, ENNReal.toReal_one]

theorem pairedGaussian_sampled_density_limit
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : ℕ → ℕ) (h : ℕ → ℕ → ℝ≥0) (H : ℕ → PairedGaussianCoefficient)
    (hH : ∀ j n, Measurable (H j n))
    (Z : (j : ℕ) → Ω → PairedGaussianHistory (N j))
    (hZ : ∀ j, HasLaw (Z j) (pairedGaussianHistoryLaw (h j) (N j)) μ)
    (Y : Ω → ℝ) (V : ℝ)
    (hV : ∀ j p, pairedGaussianBracket (H j) (h j) (N j) p ≤ V)
    (hlim : TendstoInMeasure μ
      (fun j ω => pairedGaussianExponential (H j) (h j) (N j) (Z j ω)) atTop Y) :
    Integrable Y μ ∧ (∀ᵐ ω ∂μ, 0 ≤ Y ω) ∧ (∫ ω, Y ω ∂μ = 1) ∧
      IsProbabilityMeasure (μ.withDensity (fun ω => ENNReal.ofReal (Y ω))) ∧
      Tendsto (fun j => eLpNorm
        ((fun ω => pairedGaussianExponential (H j) (h j) (N j) (Z j ω)) - Y) 1 μ)
        atTop (𝓝 0) := by
  let C : ℝ≥0 := ⟨(Real.exp V) ^ (1 / (2 : ℝ)), Real.rpow_nonneg (Real.exp_pos V).le _⟩
  apply probability_density_of_tendstoInMeasure_of_eLpNorm_two_le μ _ Y
    (fun j => ((measurable_pairedGaussianExponential (H j) (hH j) (h j) (N j)).comp_aemeasurable
      (hZ j).aemeasurable).aestronglyMeasurable)
    (fun j => ae_of_all _ (fun ω => (pairedGaussianExponential_pos _ _ _ _).le))
    (fun j => ?_) C (fun j => ?_) hlim
  · rw [(hZ j).integral_comp
      (measurable_pairedGaussianExponential (H j) (hH j) (h j) (N j)).aestronglyMeasurable]
    exact integral_pairedGaussianExponential _ (hH j) _ _
  · have hm : AEStronglyMeasurable (pairedGaussianExponential (H j) (h j) (N j))
        (μ.map (Z j)) := by
      rw [(hZ j).map_eq]
      exact (measurable_pairedGaussianExponential (H j) (hH j) (h j) (N j)).aestronglyMeasurable
    change eLpNorm (pairedGaussianExponential (H j) (h j) (N j) ∘ Z j) 2 μ ≤ C
    rw [← eLpNorm_map_measure hm (hZ j).aemeasurable, (hZ j).map_eq]
    have hb := eLpNorm_pairedGaussianExponential_two_le (H j) (hH j) (h j) (N j) V (hV j)
    rw [← ENNReal.ofReal_coe_nnreal]
    change eLpNorm (pairedGaussianExponential (H j) (h j) (N j)) 2
      (pairedGaussianHistoryLaw (h j) (N j)) ≤ ENNReal.ofReal ((Real.exp V) ^ (1 / (2 : ℝ)))
    simpa only [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos V).le
      (by norm_num : 0 ≤ 1 / (2 : ℝ))] using hb

theorem density_limit_preserves_marginal
    {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    (μ : Measure Ω) (ν : Measure A) (F : Ω → A) (hF : Measurable F)
    (X : ℕ → Ω → ℝ) (Y : Ω → ℝ)
    (hXi : ∀ n, Integrable (X n) μ) (hYi : Integrable Y μ)
    (hXpos : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ X n ω) (hYpos : ∀ᵐ ω ∂μ, 0 ≤ Y ω)
    (hmap : ∀ n, (μ.withDensity (fun ω => ENNReal.ofReal (X n ω))).map F = ν)
    (hlim : Tendsto (fun n => eLpNorm (X n - Y) 1 μ) atTop (𝓝 0)) :
    (μ.withDensity (fun ω => ENNReal.ofReal (Y ω))).map F = ν := by
  ext s hs
  let t := F ⁻¹' s
  have ht : MeasurableSet t := hF hs
  have he (n : ℕ) : ENNReal.ofReal (∫ ω in t, X n ω ∂μ) = ν s := by
    have hm := congrArg (fun κ : Measure A => κ s) (hmap n)
    rw [Measure.map_apply hF hs, withDensity_apply _ ht,
      ← ofReal_integral_eq_lintegral_ofReal (hXi n).restrict
        ((hXpos n).filter_mono ae_restrict_le)] at hm
    exact hm
  have hl := tendsto_setIntegral_of_L1' Y (Eventually.of_forall hXi) hlim t
  have hl' := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hl
  simp only [Function.comp_def, he] at hl'
  rw [Measure.map_apply hF hs, withDensity_apply _ ht,
    ← ofReal_integral_eq_lintegral_ofReal hYi.restrict (hYpos.filter_mono ae_restrict_le)]
  exact tendsto_nhds_unique hl' tendsto_const_nhds

end SKConstants
