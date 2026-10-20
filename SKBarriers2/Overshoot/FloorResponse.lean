module

public import SKBarriers2.Overshoot.Prefix
public import OAI.Probability.SKBarriers.Scalar.GeneralCDFStability
public import OAI.Probability.SKBarriers.Scalar.ScalarSplit
public import OAI.Probability.SKBarriers.Scalar.DslopeLipschitz
public import OAI.Probability.SKBarriers.Gaussian.GaussianTiltedCramer

@[expose] public section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
open OAI.SK.Analytic

namespace SKBarriers2.FloorResponse

theorem gaussian_tilted_noise_sq_le {V dV : ℝ → ℝ}
    (hdV : ∀ y, HasDerivAt V (dV y) y) (hdVc : Continuous dV)
    (he : HasExpGrowth (fun y => Real.exp (V y)))
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ y, |dV y| ≤ B) :
    (∫ y, y ^ 2 ∂(gaussianReal 0 1).tilted V) ≤ 2 + B ^ 2 := by
  have hVc : Continuous V := continuous_iff_continuousAt.mpr (fun y => (hdV y).continuousAt)
  let μ := (gaussianReal 0 1).tilted V
  let : IsProbabilityMeasure μ := isProbabilityMeasure_tilted
    (he.integrable_gaussianMeasure (Real.continuous_exp.comp hVc))
  have hx : HasExpGrowth (fun y : ℝ => y) := HasExpGrowth.linear (ContinuousLinearMap.id ℝ ℝ)
  have hdg : HasExpGrowth dV := HasExpGrowth.of_bounded hB
    (fun y => by simpa only [Real.norm_eq_abs] using hb y)
  have hi2 : Integrable (fun y : ℝ => y ^ 2) μ :=
    (hx.pow 2).integrable_gaussianTilt he hVc (continuous_id.pow 2)
  have hip : Integrable (fun y : ℝ => y * dV y) μ :=
    (hx.mul hdg).integrable_gaussianTilt he hVc (continuous_id.mul hdVc)
  have hstein := gaussian_tilted_stein_growth hdV (fun y : ℝ => hasDerivAt_id y)
    he hdg hx (HasExpGrowth.const 1) hdVc continuous_const
  change (∫ y : ℝ, y * y ∂μ) = (∫ _y, (1 : ℝ) ∂μ) + ∫ y, y * dV y ∂μ at hstein
  norm_num only [integral_const, probReal_univ, smul_eq_mul] at hstein
  have H := integral_mono (hip.const_mul 2) (hi2.add (integrable_const (B ^ 2)))
    (fun y => by
      change 2 * (y * dV y) ≤ y ^ 2 + B ^ 2
      have hs : (dV y) ^ 2 ≤ B ^ 2 := by
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (dV y)) hB).mpr (hb y)
      nlinarith [sq_nonneg (y - dV y)])
  simp only [Pi.add_apply] at H
  rw [integral_const_mul, integral_add hi2 (integrable_const (B ^ 2)), integral_const] at H
  simp only [probReal_univ, smul_eq_mul, one_mul] at H
  change (∫ y : ℝ, y ^ 2 ∂μ) ≤ 2 + B ^ 2
  simp only [← pow_two] at hstein
  linarith

theorem variance_bounded_tilt_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {δ X : Ω → ℝ}
    (hδ : AEMeasurable δ μ) {ε : ℝ} (hb : ∀ z, |δ z| ≤ ε)
    (hX : MemLp X 2 μ) :
    variance X (μ.tilted δ) ≤ Real.exp (2 * ε) * variance X μ := by
  have hiE : Integrable (fun z => Real.exp (δ z)) μ := Integrable.of_bound
    hδ.exp.aestronglyMeasurable (Real.exp ε) (ae_of_all _ (fun z => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (abs_le.mp (hb z)).2))
  let Z : ℝ := ∫ z, Real.exp (δ z) ∂μ
  have hZ : 0 < Z := integral_exp_pos hiE
  have hlo : Real.exp (-ε) ≤ Z := by
    have H := integral_mono (integrable_const (Real.exp (-ε))) hiE
      (fun z => Real.exp_le_exp.mpr (abs_le.mp (hb z)).1)
    simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using H
  have hd (z : Ω) : Real.exp (δ z) / Z ≤ Real.exp (2 * ε) := by
    calc
      _ ≤ Real.exp ε / Real.exp (-ε) := div_le_div₀ (Real.exp_nonneg ε)
        (Real.exp_le_exp.mpr (abs_le.mp (hb z)).2) (Real.exp_pos _) hlo
      _ = _ := by rw [← Real.exp_sub]; congr 1; ring
  let : IsProbabilityMeasure (μ.tilted δ) := isProbabilityMeasure_tilted hiE
  have hXm : AEStronglyMeasurable X (μ.tilted δ) :=
    hX.aestronglyMeasurable.mono_ac (tilted_absolutelyContinuous μ δ)
  have hi : Integrable (fun z => (X z - ∫ y, X y ∂μ) ^ 2) μ :=
    (hX.sub (memLp_const _)).integrable_sq
  rw [← variance_sub_const hXm (∫ y, X y ∂μ)]
  calc
    _ ≤ ∫ z, (X z - ∫ y, X y ∂μ) ^ 2 ∂μ.tilted δ :=
      variance_le_expectation_sq (hXm.sub aestronglyMeasurable_const)
    _ = ∫ z, (Real.exp (δ z) / Z) * (X z - ∫ y, X y ∂μ) ^ 2 ∂μ := by
      rw [integral_tilted]
      rfl
    _ ≤ ∫ z, Real.exp (2 * ε) * (X z - ∫ y, X y ∂μ) ^ 2 ∂μ :=
      integral_mono_of_nonneg (ae_of_all _ (fun z => mul_nonneg
        (div_nonneg (Real.exp_nonneg _) hZ.le) (sq_nonneg _)))
        (hi.const_mul _) (ae_of_all _ (fun z => mul_le_mul_of_nonneg_right (hd z) (sq_nonneg _)))
    _ = _ := by rw [integral_const_mul, variance_eq_integral hX.aemeasurable]

theorem scalarHierarchy_gradient_terminal_stability (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i, m i ∈ Icc (0 : ℝ) 1)
    {F G dF dG : ℝ → ℝ} (hF : BoundedDerivs F) (hG : BoundedDerivs G)
    (hdF : ∀ z, HasDerivAt F (dF z) z) (hdG : ∀ z, HasDerivAt G (dG z) z)
    {K H L ε : ℝ≥0} (hdFH : LipschitzWith H dF)
    (hdFK : ∀ z, |dF z| ≤ K) (hdGK : ∀ z, |dG z| ≤ K)
    (hGF : ∀ z, |G z - F z| ≤ ε) (hdGF : ∀ z, |dG z - dF z| ≤ L) (x : ℝ) :
    |deriv (scalarHierarchy n m v G) x - deriv (scalarHierarchy n m v F) x| ≤
      (L : ℝ) + (K : ℝ) * ε := by
  have hdGc : Continuous dG := by
    have he : dG = deriv G := funext (fun z => (hdG z).deriv.symm)
    rw [he]
    exact hG.1.continuous_deriv (by norm_num)
  have hobs := scalarHierarchyAverage_observable_distance hG
    (g := dG) (a := dF) ⟨hdGc, K, K.coe_nonneg, hdGK⟩
    ⟨hdFH.continuous, K, K.coe_nonneg, hdFK⟩ L.coe_nonneg hdGF n m v x
  have htilt := Prefix.scalarHierarchyAverage_terminal_stability n m v hm
    hG hF hdFH ε.coe_nonneg hGF hdFK x
  rw [scalarHierarchy_gradient_average n m v hG hdG,
    scalarHierarchy_gradient_average n m v hF hdF]
  exact (abs_sub_le _ (scalarHierarchyAverage n m v G dF x) _).trans
    (add_le_add hobs htilt)

theorem scalarHierarchy_gradient_sq_terminal_stability (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i, m i ∈ Icc (0 : ℝ) 1)
    {F G dF dG : ℝ → ℝ} (hF : BoundedDerivs F) (hG : BoundedDerivs G)
    (hdF : ∀ z, HasDerivAt F (dF z) z) (hdG : ∀ z, HasDerivAt G (dG z) z)
    {K H L ε : ℝ≥0} (hdFH : LipschitzWith H dF)
    (hdFK : ∀ z, |dF z| ≤ K) (hdGK : ∀ z, |dG z| ≤ K)
    (hGF : ∀ z, |G z - F z| ≤ ε) (hdGF : ∀ z, |dG z - dF z| ≤ L) (x : ℝ) :
    |deriv (scalarHierarchy n m v G) x ^ 2 - deriv (scalarHierarchy n m v F) x ^ 2| ≤
      2 * (K : ℝ) * ((L : ℝ) + (K : ℝ) * ε) := by
  have hdiff := scalarHierarchy_gradient_terminal_stability n m v hm hF hG
    hdF hdG hdFH hdFK hdGK hGF hdGF x
  have hbF : |deriv (scalarHierarchy n m v F) x| ≤ K := by
    rw [scalarHierarchy_gradient_average n m v hF hdF]
    exact scalarHierarchyAverage_abs_le hF hdFK n m v x
  have hbG : |deriv (scalarHierarchy n m v G) x| ≤ K := by
    rw [scalarHierarchy_gradient_average n m v hG hdG]
    exact scalarHierarchyAverage_abs_le hG hdGK n m v x
  calc
    _ = |deriv (scalarHierarchy n m v G) x - deriv (scalarHierarchy n m v F) x| *
        |deriv (scalarHierarchy n m v G) x + deriv (scalarHierarchy n m v F) x| := by
      rw [← abs_mul]
      congr 1
      ring
    _ ≤ ((L : ℝ) + (K : ℝ) * ε) * (2 * (K : ℝ)) :=
      mul_le_mul hdiff ((abs_add_le _ _).trans (by linarith)) (abs_nonneg _) (by positivity)
    _ = _ := by ring

theorem scalarHierarchy_outer_response_le (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i, m i ∈ Icc (0 : ℝ) 1)
    {F G W : ℝ → ℝ} (hF : BoundedDerivs F) (hG : BoundedDerivs G)
    (hW : BoundedDerivs W) {A B : ℝ≥0} (hWA : LipschitzWith A W)
    {ε : ℝ} (hε : 0 ≤ ε) (hGF : ∀ z, |G z - F z| ≤ ε)
    (hWB : ∀ z, |W z| ≤ B) (x : ℝ) :
    |(scalarHierarchy n m v (fun z => G z + W z) x - scalarHierarchy n m v G x) -
      (scalarHierarchy n m v (fun z => F z + W z) x - scalarHierarchy n m v F x)| ≤
      (B : ℝ) * ε + (B : ℝ) ^ 2 := by
  have hRG := Prefix.scalarHierarchy_remainder n m v hm hG (hG.add hW)
    B.coe_nonneg (fun z => by simpa only [add_sub_cancel_left] using hWB z) x
  have hRF := Prefix.scalarHierarchy_remainder n m v hm hF (hF.add hW)
    B.coe_nonneg (fun z => by simpa only [add_sub_cancel_left] using hWB z) x
  simp only [add_sub_cancel_left] at hRG hRF
  have hE := Prefix.scalarHierarchyAverage_terminal_stability n m v hm
    hG hF hWA hε hGF hWB x
  calc
    _ = |((scalarHierarchy n m v (fun z => G z + W z) x - scalarHierarchy n m v G x -
          scalarHierarchyAverage n m v G W x) -
        (scalarHierarchy n m v (fun z => F z + W z) x - scalarHierarchy n m v F x -
          scalarHierarchyAverage n m v F W x)) +
        (scalarHierarchyAverage n m v G W x - scalarHierarchyAverage n m v F W x)| := by
      congr 1
      ring
    _ ≤ (|scalarHierarchy n m v (fun z => G z + W z) x - scalarHierarchy n m v G x -
          scalarHierarchyAverage n m v G W x| +
        |scalarHierarchy n m v (fun z => F z + W z) x - scalarHierarchy n m v F x -
          scalarHierarchyAverage n m v F W x|) +
        |scalarHierarchyAverage n m v G W x - scalarHierarchyAverage n m v F W x| :=
      (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ _ := by linarith

private theorem dslope_sub_at_zero {f g : ℝ → ℝ}
    (hf : DifferentiableAt ℝ f 0) (hg : DifferentiableAt ℝ g 0) (a : ℝ) :
    dslope (f - g) 0 a = dslope f 0 a - dslope g 0 a := by
  by_cases ha : a = 0
  · subst a
    simpa only [dslope_same] using (hf.hasDerivAt.sub hg.hasDerivAt).deriv
  · rw [dslope_of_ne _ ha, dslope_of_ne _ ha, dslope_of_ne _ ha]
    simp only [slope_def_field, sub_zero, Pi.sub_apply]
    ring

theorem scalarStep_response_of_variance_bound
    {F G : ℝ → ℝ} (hF : BoundedDerivs F) (hG : BoundedDerivs G)
    (v x : ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hvar : ∀ a ∈ Icc (0 : ℝ) 1,
      |variance (fun y => G (x + v * y))
          (gaussianStepLaw a (fun z : ℝ × ℝ => G (z.1 + v * z.2)) x) -
        variance (fun y => F (x + v * y))
          (gaussianStepLaw a (fun z : ℝ × ℝ => F (z.1 + v * z.2)) x)| ≤ C)
    {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) :
    |(scalarStep b v G x - scalarStep b v F x) -
      (scalarStep a v G x - scalarStep a v F x)| ≤ C * |b - a| := by
  let T : (ℝ × ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.fst ℝ ℝ ℝ + v • ContinuousLinearMap.snd ℝ ℝ ℝ
  have hFT : BoundedDerivs (fun z : ℝ × ℝ => F (z.1 + v * z.2)) := hF.compCLM T
  have hGT : BoundedDerivs (fun z : ℝ × ℝ => G (z.1 + v * z.2)) := hG.compCLM T
  let f : ℝ → ℝ := cgf (fun y => F (x + v * y)) (gaussianReal 0 1)
  let g : ℝ → ℝ := cgf (fun y => G (x + v * y)) (gaussianReal 0 1)
  have hf (a : ℝ) : AnalyticAt ℝ f a :=
    analyticAt_cgf (hFT.mem_interior_integrableExpSet_section x a)
  have hg (a : ℝ) : AnalyticAt ℝ g a :=
    analyticAt_cgf (hGT.mem_interior_integrableExpSet_section x a)
  have hsecond (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) :
      |iteratedDeriv 2 (g - f) a| ≤ C := by
    rw [iteratedDeriv_sub (hg a).contDiffAt (hf a).contDiffAt]
    rw [← variance_tilted_mul (hGT.mem_interior_integrableExpSet_section x a),
      ← variance_tilted_mul (hFT.mem_interior_integrableExpSet_section x a)]
    exact hvar a ha
  have H := dslope_mass_lipschitz (fun a => (hg a).sub (hf a)) hC hsecond ha hb
  rw [dslope_sub_at_zero (hg 0).differentiableAt (hf 0).differentiableAt,
    dslope_sub_at_zero (hg 0).differentiableAt (hf 0).differentiableAt] at H
  have heF := congrFun (gaussianStep_mass_eq_dslope hFT x)
  have heG := congrFun (gaussianStep_mass_eq_dslope hGT x)
  change |(dslope g 0 b - dslope f 0 b) - (dslope g 0 a - dslope f 0 a)| ≤ _ at H
  rw [← heG b, ← heF b, ← heG a, ← heF a] at H
  exact H

theorem dyadic_response_le (β : ℝ) {α γ : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0 : ℝ) 1) (hγ : ∀ z, γ z ∈ Icc (0 : ℝ) 1)
    {F G : ℝ → ℝ} (hF : BoundedDerivs F) (hG : BoundedDerivs G)
    {K L : ℝ≥0} (hFK : LipschitzWith K F) (hGL : LipschitzWith L G)
    (n : ℕ) (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) (x : ℝ) :
    |(dyadicScalar β γ n s t G x - dyadicScalar β γ n s t F x) -
      (dyadicScalar β α n s t G x - dyadicScalar β α n s t F x)| ≤
      (scalarTimeMassConstantK β L + scalarTimeMassConstantK β K) *
        dyadicCDFDistance γ α n s t := by
  have hGmass := dyadicScalar_cdf_mass_bound_general hG hGL β hγ hα n s t ht x
  have hFmass := dyadicScalar_cdf_mass_bound_general hF hFK β hγ hα n s t ht x
  calc
    _ = |(dyadicScalar β γ n s t G x - dyadicScalar β α n s t G x) -
        (dyadicScalar β γ n s t F x - dyadicScalar β α n s t F x)| := by
      congr 1
      ring
    _ ≤ |dyadicScalar β γ n s t G x - dyadicScalar β α n s t G x| +
        |dyadicScalar β γ n s t F x - dyadicScalar β α n s t F x| := abs_sub _ _
    _ ≤ _ := (add_le_add hGmass hFmass).trans_eq (by ring)

theorem scalarCDFOperator_response_le (β : ℝ) {α γ : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0 : ℝ) 1) (hαm : Monotone α)
    (hγ : ∀ z, γ z ∈ Icc (0 : ℝ) 1) (hγm : Monotone γ)
    {F G : ℝ → ℝ} (hF : BoundedDerivs F) (hG : BoundedDerivs G)
    {K L : ℝ≥0} (hFK : LipschitzWith K F) (hGL : LipschitzWith L G)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) (x : ℝ) :
    |(scalarCDFOperator β γ s t G x - scalarCDFOperator β γ s t F x) -
      (scalarCDFOperator β α s t G x - scalarCDFOperator β α s t F x)| ≤
      (scalarTimeMassConstantK β L + scalarTimeMassConstantK β K) *
        (∫ z in s..s+t, |γ z - α z|) := by
  let C : ℝ := scalarTimeMassConstantK β L + scalarTimeMassConstantK β K
  have hC : 0 ≤ C := add_nonneg (scalarTimeMassConstantK_nonneg β L)
    (scalarTimeMassConstantK_nonneg β K)
  have hfinite (n : ℕ) := (dyadic_response_le β hα hγ hF hG hFK hGL n s t ht x).trans
    (mul_le_mul_of_nonneg_left (dyadicCDFDistance_integral_bound hγm hαm n s t) hC)
  have hGγ := (dyadicScalar_general_uniform hG hGL β hγ hγm s t ht).tendsto_at x
  have hFγ := (dyadicScalar_general_uniform hF hFK β hγ hγm s t ht).tendsto_at x
  have hGα := (dyadicScalar_general_uniform hG hGL β hα hαm s t ht).tendsto_at x
  have hFα := (dyadicScalar_general_uniform hF hFK β hα hαm s t ht).tendsto_at x
  have hzero : Tendsto (fun n : ℕ => (t : ℝ) / (2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  have hr := (((hzero.mul_const ((γ (s+t) - γ s) + (α (s+t) - α s))).const_add
    (∫ z in s..s+t, |γ z - α z|)).const_mul C)
  have H := le_of_tendsto_of_tendsto ((hGγ.sub hFγ).sub (hGα.sub hFα)).abs hr
    (Eventually.of_forall hfinite)
  simpa only [zero_mul, add_zero] using H

theorem scalarCDFOperator_add_response_le (β : ℝ) {α γ : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0 : ℝ) 1) (hαm : Monotone α)
    (hγ : ∀ z, γ z ∈ Icc (0 : ℝ) 1) (hγm : Monotone γ)
    {F V : ℝ → ℝ} (hF : BoundedDerivs F) (hV : BoundedDerivs V)
    {K L : ℝ≥0} (hFK : LipschitzWith K F) (hVL : LipschitzWith L V)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) (x : ℝ) :
    |(scalarCDFOperator β γ s t (fun z => F z + V z) x - scalarCDFOperator β γ s t F x) -
      (scalarCDFOperator β α s t (fun z => F z + V z) x - scalarCDFOperator β α s t F x)| ≤
      (scalarTimeMassConstantK β (K + L) + scalarTimeMassConstantK β K) *
        (∫ z in s..s+t, |γ z - α z|) := by
  exact scalarCDFOperator_response_le β hα hαm hγ hγm hF (hF.add hV)
    hFK (hFK.add hVL) s t ht x

theorem linear_lower_extend {α : ℝ → ℝ} (hαm : Monotone α)
    {c T : ℝ} (hc : 0 ≤ c) (hT : T ∈ Ioc (0 : ℝ) 1)
    (hlin : ∀ z ∈ Icc (0 : ℝ) T, c * z ≤ α z) :
    ∀ z ∈ Icc (0 : ℝ) 1, (c * T) * z ≤ α z := by
  intro z hz
  rcases le_total z T with hzT | hTz
  · have H := mul_le_mul_of_nonneg_left hT.2 (mul_nonneg hc hz.1)
    have H' : (c * T) * z ≤ c * z := by nlinarith
    exact H'.trans (hlin z ⟨hz.1, hzT⟩)
  · have H : (c * T) * z ≤ c * T :=
      mul_le_of_le_one_right (mul_nonneg hc hT.1.le) hz.2
    exact H.trans ((hlin T ⟨hT.1.le, le_rfl⟩).trans (hαm hTz))

theorem floor_distance_le {α : ℝ → ℝ} (hαm : Monotone α)
    {c ℓ : ℝ} (hc : 0 < c) (hℓ : 0 ≤ ℓ) (a : ℝ≥0)
    (hlin : ∀ z ∈ Icc (0 : ℝ) a, c * z ≤ α z) :
    (∫ z in (0 : ℝ)..a, |max (α z) ℓ - α z|) ≤ ℓ ^ 2 / c := by
  let d : ℝ → ℝ := fun z => |max (α z) ℓ - α z|
  let R : ℝ := ℓ / c
  have hR : 0 ≤ R := div_nonneg hℓ hc.le
  have hdint (u v : ℝ) : IntervalIntegrable d volume u v :=
    (((hαm.max monotone_const).intervalIntegrable).sub hαm.intervalIntegrable).abs
  have hbound (z : ℝ) (hz : z ∈ Icc (0 : ℝ) a) : d z ≤ ℓ := by
    have hαz : 0 ≤ α z := (mul_nonneg hc.le hz.1).trans (hlin z hz)
    dsimp only [d]
    rw [abs_of_nonneg (sub_nonneg.mpr (le_max_left _ _))]
    exact sub_le_iff_le_add.mpr (max_le (by linarith) (by linarith))
  have hsmall (b : ℝ) (hb : 0 ≤ b) (hba : b ≤ a) :
      (∫ z in (0 : ℝ)..b, d z) ≤ ℓ * b := by
    have H := intervalIntegral.integral_mono_on hb (hdint 0 b) intervalIntegrable_const
      (fun z hz => hbound z ⟨hz.1, hz.2.trans hba⟩)
    simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm] using H
  rcases le_total (a : ℝ) R with haR | hRa
  · exact (hsmall a a.coe_nonneg le_rfl).trans
      ((mul_le_mul_of_nonneg_left haR hℓ).trans_eq (by dsimp only [R]; ring))
  · have hzero (z : ℝ) (hz : z ∈ Icc R a) : d z = 0 := by
      have hcz : ℓ ≤ c * z := by
        have H := mul_le_mul_of_nonneg_left hz.1 hc.le
        have he : c * R = ℓ := by dsimp only [R]; field_simp
        rw [he] at H
        exact H
      have hℓα : ℓ ≤ α z := hcz.trans (hlin z ⟨hR.trans hz.1, hz.2⟩)
      simp only [d, max_eq_left hℓα, sub_self, abs_zero]
    have htail : (∫ z in R..(a : ℝ), d z) = 0 := by
      calc
        _ = ∫ _z in R..(a : ℝ), (0 : ℝ) := intervalIntegral.integral_congr
          (fun z hz => hzero z (by simpa only [uIcc_of_le hRa] using hz))
        _ = 0 := intervalIntegral.integral_zero
    have hsplit := intervalIntegral.integral_add_adjacent_intervals (hdint 0 R) (hdint R a)
    rw [htail, add_zero] at hsplit
    change (∫ z in (0 : ℝ)..a, d z) ≤ _
    rw [← hsplit]
    exact (hsmall R hR hRa).trans_eq (by dsimp only [R]; ring)

theorem scalarCDFOperator_floor_response_quadratic (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0 : ℝ) 1) (hαm : Monotone α)
    {c σ : ℝ} (hc : 0 < c) (hσ : 0 ≤ σ) (hσ1 : 3 * σ ≤ 1)
    {F G : ℝ → ℝ} (hF : BoundedDerivs F) (hG : BoundedDerivs G)
    {K L : ℝ≥0} (hFK : LipschitzWith K F) (hGL : LipschitzWith L G)
    (t : ℝ≥0) (ht : t ≤ 1) (hlin : ∀ z ∈ Icc (0 : ℝ) t, c * z ≤ α z) (x : ℝ) :
    |(scalarCDFOperator β (fun z => max (α z) (3 * σ)) 0 t G x -
        scalarCDFOperator β (fun z => max (α z) (3 * σ)) 0 t F x) -
      (scalarCDFOperator β α 0 t G x - scalarCDFOperator β α 0 t F x)| ≤
      (scalarTimeMassConstantK β L + scalarTimeMassConstantK β K) * (9 * σ ^ 2 / c) := by
  have hγ : ∀ z, max (α z) (3 * σ) ∈ Icc (0 : ℝ) 1 := by
    intro z
    exact ⟨(hα z).1.trans (le_max_left _ _), max_le (hα z).2 hσ1⟩
  have H := scalarCDFOperator_response_le β hα hαm hγ (hαm.max monotone_const)
    hF hG hFK hGL 0 t ht x
  have hD := floor_distance_le hαm hc (show 0 ≤ 3 * σ by positivity) t hlin
  simp only [zero_add] at H
  have hD' : (∫ z in (0 : ℝ)..t, |max (α z) (3 * σ) - α z|) ≤ 9 * σ ^ 2 / c := by
    exact hD.trans_eq (by ring)
  exact H.trans (mul_le_mul_of_nonneg_left hD'
    (add_nonneg (scalarTimeMassConstantK_nonneg β L) (scalarTimeMassConstantK_nonneg β K)))

theorem common_prefix_floor_response_quadratic (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0 : ℝ) 1) (hαm : Monotone α)
    {c σ : ℝ} (hc : 0 < c) (hσ : 0 ≤ σ) (hσ1 : 3 * σ ≤ 1)
    {F G : ℝ → ℝ} (hF : BoundedDerivs F) (hG : BoundedDerivs G)
    {K L : ℝ≥0} (hFK : LipschitzWith K F) (hGL : LipschitzWith L G)
    (t : ℝ≥0) (ht : t ≤ 1) (hlin : ∀ z ∈ Icc (0 : ℝ) t, c * z ≤ α z) (x : ℝ) :
    |(scalarCDFOperator β (fun z => max (α z) (3 * σ) / 3) 0 t G x -
        scalarCDFOperator β (fun z => max (α z) (3 * σ) / 3) 0 t F x) -
      (scalarCDFOperator β (fun z => α z / 3) 0 t G x -
        scalarCDFOperator β (fun z => α z / 3) 0 t F x)| ≤
      (scalarTimeMassConstantK β L + scalarTimeMassConstantK β K) * (3 * σ ^ 2 / c) := by
  have hγ : ∀ z, max (α z) (3 * σ) ∈ Icc (0 : ℝ) 1 := by
    intro z
    exact ⟨(hα z).1.trans (le_max_left _ _), max_le (hα z).2 hσ1⟩
  have hdiv (f : ℝ → ℝ) (hf : ∀ z, f z ∈ Icc (0 : ℝ) 1) :
      ∀ z, f z / 3 ∈ Icc (0 : ℝ) 1 := by
    intro z
    constructor
    · exact div_nonneg (hf z).1 (by norm_num)
    · linarith [(hf z).2]
  have hdivm (f : ℝ → ℝ) (hf : Monotone f) : Monotone (fun z => f z / 3) := by
    intro z w hzw
    exact div_le_div_of_nonneg_right (hf hzw) (by norm_num)
  have H := scalarCDFOperator_response_le β (hdiv α hα) (hdivm α hαm)
    (hdiv _ hγ) (hdivm _ (hαm.max monotone_const)) hF hG hFK hGL 0 t ht x
  have hD := floor_distance_le hαm hc (show 0 ≤ 3 * σ by positivity) t hlin
  have he : (∫ z in (0 : ℝ)..t, |max (α z) (3 * σ) / 3 - α z / 3|) =
      (∫ z in (0 : ℝ)..t, |max (α z) (3 * σ) - α z|) / 3 := by
    simp_rw [← sub_div, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    exact intervalIntegral.integral_div _ _
  simp only [zero_add] at H
  rw [he] at H
  apply H.trans
  apply mul_le_mul_of_nonneg_left _
    (add_nonneg (scalarTimeMassConstantK_nonneg β L) (scalarTimeMassConstantK_nonneg β K))
  exact (div_le_div_of_nonneg_right hD (by norm_num : (0 : ℝ) ≤ 3)).trans_eq (by ring)

private theorem variance_diff_of_noise_bounds (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {X Y : ℝ → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    (hi : MemLp (fun y : ℝ => y) 2 μ) {A D M : ℝ}
    (hA : 0 ≤ A) (hD : 0 ≤ D) (hM : 0 ≤ M)
    (habs : (∫ y : ℝ, |y| ∂μ) ≤ M) (hsq : (∫ y : ℝ, y ^ 2 ∂μ) ≤ M)
    (hbX : ∀ y, |X y| ≤ A * |y|) (hbY : ∀ y, |Y y| ≤ A * |y|)
    (hbD : ∀ y, |Y y - X y| ≤ D * |y|) :
    |variance Y μ - variance X μ| ≤ 2 * A * D * (M + M ^ 2) := by
  have mean_bound (Z : ℝ → ℝ) (hZ : Integrable Z μ) (B : ℝ) (hB : 0 ≤ B)
      (hbZ : ∀ y, |Z y| ≤ B * |y|) : |∫ y, Z y ∂μ| ≤ B * M := by
    calc
      _ ≤ ∫ y, |Z y| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ y : ℝ, B * |y| ∂μ := integral_mono hZ.abs
        ((hi.integrable one_le_two).abs.const_mul B) hbZ
      _ = B * (∫ y : ℝ, |y| ∂μ) := integral_const_mul _ _
      _ ≤ B * M := mul_le_mul_of_nonneg_left habs hB
  have hmX := mean_bound X (hX.integrable one_le_two) A hA hbX
  have hmY := mean_bound Y (hY.integrable one_le_two) A hA hbY
  have hmD : |(∫ y, Y y ∂μ) - ∫ y, X y ∂μ| ≤ D * M := by
    rw [← integral_sub (hY.integrable one_le_two) (hX.integrable one_le_two)]
    exact mean_bound _ ((hY.sub hX).integrable one_le_two) D hD hbD
  have hp (y : ℝ) : |Y y ^ 2 - X y ^ 2| ≤ (2 * A * D) * y ^ 2 := by
    calc
      _ = |Y y - X y| * |Y y + X y| := by rw [← abs_mul]; congr 1; ring
      _ ≤ (D * |y|) * (2 * A * |y|) := mul_le_mul (hbD y)
        ((abs_add_le _ _).trans (by linarith [hbY y, hbX y])) (abs_nonneg _) (by positivity)
      _ = _ := by rw [show D * |y| * (2 * A * |y|) = 2 * A * D * |y| ^ 2 by ring, sq_abs]
  have hs : |(∫ y, Y y ^ 2 ∂μ) - ∫ y, X y ^ 2 ∂μ| ≤ (2 * A * D) * M := by
    rw [← integral_sub hY.integrable_sq hX.integrable_sq]
    calc
      _ ≤ ∫ y, |Y y ^ 2 - X y ^ 2| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ y : ℝ, (2 * A * D) * y ^ 2 ∂μ :=
        integral_mono (hY.integrable_sq.sub hX.integrable_sq).abs
          (hi.integrable_sq.const_mul _) hp
      _ = (2 * A * D) * (∫ y : ℝ, y ^ 2 ∂μ) := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hsq (by positivity)
  have hmeans : |(∫ y, Y y ∂μ) ^ 2 - (∫ y, X y ∂μ) ^ 2| ≤ 2 * A * D * M ^ 2 := by
    calc
      _ = |(∫ y, Y y ∂μ) - ∫ y, X y ∂μ| * |(∫ y, Y y ∂μ) + ∫ y, X y ∂μ| := by
        rw [← abs_mul]; congr 1; ring
      _ ≤ (D * M) * (2 * A * M) := mul_le_mul hmD
        ((abs_add_le _ _).trans (by linarith)) (abs_nonneg _) (by positivity)
      _ = _ := by ring
  rw [variance_eq_sub hY, variance_eq_sub hX]
  calc
    _ = |((∫ y, Y y ^ 2 ∂μ) - ∫ y, X y ^ 2 ∂μ) -
        ((∫ y, Y y ∂μ) ^ 2 - (∫ y, X y ∂μ) ^ 2)| := by
      simp only [Pi.pow_apply]
      congr 1
      ring
    _ ≤ |(∫ y, Y y ^ 2 ∂μ) - ∫ y, X y ^ 2 ∂μ| +
        |(∫ y, Y y ∂μ) ^ 2 - (∫ y, X y ∂μ) ^ 2| := abs_sub _ _
    _ ≤ _ := (add_le_add hs hmeans).trans_eq (by ring)

private theorem exp_two_sub_one_le {ε : ℝ} (hε : ε ∈ Icc (0 : ℝ) 1) :
    Real.exp (2 * ε) - 1 ≤ (Real.exp 2 - 1) * ε := by
  have H := convexOn_exp.2 (mem_univ (0 : ℝ)) (mem_univ (2 : ℝ))
    (sub_nonneg.mpr hε.2) hε.1 (by ring : 1 - ε + ε = 1)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at H
  rw [mul_comm ε 2] at H
  linarith

private theorem scalar_noise_memLp {F Z : ℝ → ℝ}
    (hF : BoundedDerivs F) (hZ : BoundedDerivs Z) (m v x : ℝ) :
    MemLp (fun y => Z (x + v * y)) 2
      (gaussianStepLaw m (fun z : ℝ × ℝ => F (z.1 + v * z.2)) x) := by
  have hf : BoundedDerivs (fun y : ℝ => F (x + v * y)) :=
    (hF.translate x).compCLM (v • ContinuousLinearMap.id ℝ ℝ)
  have hz : BoundedDerivs (fun y : ℝ => Z (x + v * y)) :=
    (hZ.translate x).compCLM (v • ContinuousLinearMap.id ℝ ℝ)
  exact hz.hasExpGrowth.memLp_two_gaussianTilt (hf.exp_growths m).1
    (continuous_const.mul hf.1.continuous) hz.1.continuous

private theorem scalar_noise_moments {F : ℝ → ℝ} (hF : BoundedDerivs F)
    {K B : ℝ≥0} (hFK : LipschitzWith K F) {m v : ℝ} (hm : m ∈ Icc (0 : ℝ) 1)
    (hv : |v| ≤ B) (x : ℝ) :
    let μ := gaussianStepLaw m (fun z : ℝ × ℝ => F (z.1 + v * z.2)) x
    MemLp (fun y : ℝ => y) 2 μ ∧
      (∫ y : ℝ, |y| ∂μ) ≤ 3 + ((K : ℝ) * B) ^ 2 ∧
      (∫ y : ℝ, y ^ 2 ∂μ) ≤ 3 + ((K : ℝ) * B) ^ 2 := by
  let f : ℝ → ℝ := fun y => F (x + v * y)
  let V : ℝ → ℝ := fun y => m * f y
  let dV : ℝ → ℝ := fun y => m * (deriv F (x + v * y) * v)
  let μ := gaussianStepLaw m (fun z : ℝ × ℝ => F (z.1 + v * z.2)) x
  have hf : BoundedDerivs f := (hF.translate x).compCLM (v • ContinuousLinearMap.id ℝ ℝ)
  have he : HasExpGrowth (fun y => Real.exp (V y)) := (hf.exp_growths m).1
  have hd (y : ℝ) : HasDerivAt V (dV y) y := by
    simpa only [V, dV, f, Function.comp_def, id_eq, mul_one] using
      (((hF.1.differentiable (by norm_num) _).hasDerivAt).comp y
      (((hasDerivAt_id y).const_mul v).const_add x)).const_mul m
  have hdc : Continuous dV := by
    exact continuous_const.mul (((hF.1.continuous_deriv (by norm_num)).comp
      (continuous_const.add (continuous_const.mul continuous_id))).mul continuous_const)
  have hb (y : ℝ) : |dV y| ≤ (K : ℝ) * B := by
    have hder : |deriv F (x + v * y)| ≤ K := norm_deriv_le_of_lipschitz hFK
    dsimp only [dV]
    rw [abs_mul, abs_mul, abs_of_nonneg hm.1]
    calc
      _ ≤ 1 * ((K : ℝ) * B) := mul_le_mul hm.2
        (mul_le_mul hder hv (abs_nonneg _) K.coe_nonneg) (by positivity) (by norm_num)
      _ = _ := one_mul _
  have hi : MemLp (fun y : ℝ => y) 2 μ :=
    (HasExpGrowth.linear (ContinuousLinearMap.id ℝ ℝ)).memLp_two_gaussianTilt he
      (continuous_const.mul hf.1.continuous) continuous_id
  let : IsProbabilityMeasure μ := isProbabilityMeasure_tilted
    (he.integrable_gaussianMeasure (Real.continuous_exp.comp (continuous_const.mul hf.1.continuous)))
  have hs : (∫ y : ℝ, y ^ 2 ∂μ) ≤ 2 + ((K : ℝ) * B) ^ 2 :=
    gaussian_tilted_noise_sq_le hd hdc he (by positivity) hb
  have ha : (∫ y : ℝ, |y| ∂μ) ≤ 3 + ((K : ℝ) * B) ^ 2 := by
    have H := integral_mono (hi.integrable one_le_two).abs
      ((integrable_const (1 : ℝ)).add hi.integrable_sq)
      (fun y : ℝ => by change |y| ≤ 1 + y ^ 2; nlinarith [sq_nonneg (|y| - 1), sq_abs y])
    simp only [Pi.add_apply] at H
    rw [integral_add (integrable_const _) hi.integrable_sq, integral_const] at H
    simp only [probReal_univ, smul_eq_mul, one_mul] at H
    linarith
  exact ⟨hi, ha, hs.trans (by linarith)⟩

private theorem variance_of_noise_anchor (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {Z : ℝ → ℝ} (hZ : MemLp Z 2 μ) (hi : MemLp (fun y : ℝ => y) 2 μ)
    {A M : ℝ} (hA : 0 ≤ A) (hm : (∫ y : ℝ, y ^ 2 ∂μ) ≤ M)
    (hb : ∀ y, |Z y - Z 0| ≤ A * |y|) : variance Z μ ≤ A ^ 2 * M := by
  rw [← variance_sub_const hZ.aestronglyMeasurable (Z 0)]
  calc
    _ ≤ ∫ y, (Z y - Z 0) ^ 2 ∂μ :=
      variance_le_expectation_sq (hZ.aestronglyMeasurable.sub aestronglyMeasurable_const)
    _ ≤ ∫ y : ℝ, A ^ 2 * y ^ 2 ∂μ := by
      apply integral_mono_of_nonneg (ae_of_all _ (fun _ => sq_nonneg _))
        (hi.integrable_sq.const_mul _)
      exact ae_of_all _ (fun y => by
        have H := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hA (abs_nonneg y))).mpr (hb y)
        simpa only [sq_abs, mul_pow] using H)
    _ = A ^ 2 * (∫ y : ℝ, y ^ 2 ∂μ) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hm (sq_nonneg A)

def mixedVarianceConstant (K B : ℝ≥0) : ℝ :=
  let M : ℝ := 3 + ((K : ℝ) * B) ^ 2
  2 * (K : ℝ) * (M + M ^ 2) + (Real.exp 2 - 1) * (K : ℝ) ^ 2 * M

theorem mixedVarianceConstant_nonneg (K B : ℝ≥0) : 0 ≤ mixedVarianceConstant K B := by
  have he : 0 ≤ Real.exp 2 - 1 := sub_nonneg.mpr (Real.one_le_exp (by norm_num))
  dsimp only [mixedVarianceConstant]
  positivity

theorem scalarStep_mixed_variance_le
    {F G : ℝ → ℝ} (hF : BoundedDerivs F) (hG : BoundedDerivs G)
    {K B J ε : ℝ≥0} (hFK : LipschitzWith K F) (hGK : LipschitzWith K G)
    (hJ : LipschitzWith J (fun z => G z - F z))
    (hGF : ∀ z, |G z - F z| ≤ ε) (hε : ε ≤ 1)
    {m v : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (hv : |v| ≤ B) (x : ℝ) :
    |variance (fun y => G (x + v * y))
        (gaussianStepLaw m (fun z : ℝ × ℝ => G (z.1 + v * z.2)) x) -
      variance (fun y => F (x + v * y))
        (gaussianStepLaw m (fun z : ℝ × ℝ => F (z.1 + v * z.2)) x)| ≤
      v ^ 2 * mixedVarianceConstant K B * ((J : ℝ) + ε) := by
  let μF := gaussianStepLaw m (fun z : ℝ × ℝ => F (z.1 + v * z.2)) x
  let μG := gaussianStepLaw m (fun z : ℝ × ℝ => G (z.1 + v * z.2)) x
  let X : ℝ → ℝ := fun y => F (x + v * y)
  let Y : ℝ → ℝ := fun y => G (x + v * y)
  let M : ℝ := 3 + ((K : ℝ) * B) ^ 2
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  let T : (ℝ × ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.fst ℝ ℝ ℝ + v • ContinuousLinearMap.snd ℝ ℝ ℝ
  have hfT : BoundedDerivs (fun z : ℝ × ℝ => F (z.1 + v * z.2)) := hF.compCLM T
  have hgT : BoundedDerivs (fun z : ℝ × ℝ => G (z.1 + v * z.2)) := hG.compCLM T
  let : IsProbabilityMeasure μF := gaussianStepLaw_probability hfT m x
  let : IsProbabilityMeasure μG := gaussianStepLaw_probability hgT m x
  obtain ⟨hiF, _, hsF⟩ := scalar_noise_moments hF hFK hm hv x
  obtain ⟨hiG, haG, hsG⟩ := scalar_noise_moments hG hGK hm hv x
  have hXF : MemLp X 2 μF := scalar_noise_memLp hF hF m v x
  have hXG : MemLp X 2 μG := scalar_noise_memLp hG hF m v x
  have hYG : MemLp Y 2 μG := scalar_noise_memLp hG hG m v x
  have hbX (y : ℝ) : |X y - F x| ≤ ((K : ℝ) * |v|) * |y| := by
    simpa only [X, Real.norm_eq_abs, add_sub_cancel_left, abs_mul, mul_assoc] using
      hFK.norm_sub_le (x + v * y) x
  have hbY (y : ℝ) : |Y y - G x| ≤ ((K : ℝ) * |v|) * |y| := by
    simpa only [Y, Real.norm_eq_abs, add_sub_cancel_left, abs_mul, mul_assoc] using
      hGK.norm_sub_le (x + v * y) x
  have hbD (y : ℝ) : |(Y y - G x) - (X y - F x)| ≤ ((J : ℝ) * |v|) * |y| := by
    calc
      _ = |(G (x + v * y) - F (x + v * y)) - (G x - F x)| := by
        dsimp only [X, Y]
        congr 1
        ring
      _ ≤ _ := by simpa only [Real.norm_eq_abs, add_sub_cancel_left, abs_mul, mul_assoc] using
          hJ.norm_sub_le (x + v * y) x
  have hsame := variance_diff_of_noise_bounds μG
    (X := fun y => X y - F x) (Y := fun y => Y y - G x) (hXG.sub (memLp_const (F x)))
    (hYG.sub (memLp_const (G x))) hiG (by positivity : 0 ≤ (K : ℝ) * |v|)
    (by positivity : 0 ≤ (J : ℝ) * |v|) hM haG hsG hbX hbY hbD
  simp only [variance_sub_const hYG.aestronglyMeasurable,
    variance_sub_const hXG.aestronglyMeasurable] at hsame
  have hXFbound : variance X μF ≤ ((K : ℝ) * |v|) ^ 2 * M := by
    apply variance_of_noise_anchor μF hXF hiF (by positivity) hsF
    intro y
    simpa only [X, mul_zero, add_zero] using hbX y
  have hXGbound : variance X μG ≤ ((K : ℝ) * |v|) ^ 2 * M := by
    apply variance_of_noise_anchor μG hXG hiG (by positivity) hsG
    intro y
    simpa only [X, mul_zero, add_zero] using hbX y
  let δ : ℝ → ℝ := fun y => m * (Y y - X y)
  have hδc : Continuous δ := continuous_const.mul
    ((hG.1.continuous.comp (continuous_const.add (continuous_const.mul continuous_id))).sub
      (hF.1.continuous.comp (continuous_const.add (continuous_const.mul continuous_id))))
  have hδ (y : ℝ) : |δ y| ≤ (ε : ℝ) := by
    dsimp only [δ, X, Y]
    rw [abs_mul, abs_of_nonneg hm.1]
    exact (mul_le_mul_of_nonneg_left (hGF _) hm.1).trans
      (mul_le_of_le_one_left ε.coe_nonneg hm.2)
  have heG : μF.tilted δ = μG := by
    dsimp only [μF, μG, gaussianStepLaw]
    rw [tilted_tilted (hfT.exp_integrable m x)]
    apply tilted_congr
    exact ae_of_all _ (fun y => by dsimp only [δ, X, Y, Pi.add_apply]; ring)
  have heF : μG.tilted (fun y => -δ y) = μF := by
    dsimp only [μF, μG, gaussianStepLaw]
    rw [tilted_tilted (hgT.exp_integrable m x)]
    apply tilted_congr
    exact ae_of_all _ (fun y => by dsimp only [δ, X, Y, Pi.add_apply]; ring)
  have hforward := variance_bounded_tilt_le μF hδc.measurable.aemeasurable hδ hXF
  have hback := variance_bounded_tilt_le μG (δ := fun y => -δ y) (ε := (ε : ℝ))
    hδc.neg.measurable.aemeasurable (fun y => by simpa only [abs_neg] using hδ y) hXG
  rw [heG] at hforward
  rw [heF] at hback
  have hq : 0 ≤ Real.exp (2 * (ε : ℝ)) - 1 :=
    sub_nonneg.mpr (Real.one_le_exp (by positivity))
  have hlaw : |variance X μG - variance X μF| ≤
      (Real.exp 2 - 1) * (ε : ℝ) * (((K : ℝ) * |v|) ^ 2 * M) := by
    have H : |variance X μG - variance X μF| ≤
        (Real.exp (2 * (ε : ℝ)) - 1) * (((K : ℝ) * |v|) ^ 2 * M) := by
      apply abs_le.mpr
      constructor
      · nlinarith [mul_le_mul_of_nonneg_left hXGbound hq]
      · nlinarith [mul_le_mul_of_nonneg_left hXFbound hq]
    exact H.trans (mul_le_mul_of_nonneg_right
      (exp_two_sub_one_le ⟨ε.coe_nonneg, by exact_mod_cast hε⟩) (by positivity))
  have hA : 0 ≤ 2 * (K : ℝ) * (M + M ^ 2) := by positivity
  have he : 0 ≤ Real.exp 2 - 1 := sub_nonneg.mpr (Real.one_le_exp (by norm_num))
  have hB : 0 ≤ (Real.exp 2 - 1) * (K : ℝ) ^ 2 * M := by positivity
  change |variance Y μG - variance X μF| ≤ _
  calc
    _ ≤ |variance Y μG - variance X μG| + |variance X μG - variance X μF| := abs_sub_le _ _ _
    _ ≤ 2 * ((K : ℝ) * |v|) * ((J : ℝ) * |v|) * (M + M ^ 2) +
        (Real.exp 2 - 1) * (ε : ℝ) * (((K : ℝ) * |v|) ^ 2 * M) := add_le_add hsame hlaw
    _ = v ^ 2 * ((2 * (K : ℝ) * (M + M ^ 2)) * J +
        ((Real.exp 2 - 1) * (K : ℝ) ^ 2 * M) * ε) := by
      rw [← sq_abs v]
      ring
    _ ≤ _ := by
      rw [mul_assoc (v ^ 2) (mixedVarianceConstant K B) ((J : ℝ) + ε)]
      dsimp only [mixedVarianceConstant]
      change v ^ 2 * _ ≤ v ^ 2 * ((2 * (K : ℝ) * (M + M ^ 2) +
        (Real.exp 2 - 1) * (K : ℝ) ^ 2 * M) * ((J : ℝ) + ε))
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg v)
      nlinarith [mul_nonneg hA ε.coe_nonneg, mul_nonneg hB J.coe_nonneg]

theorem scalarStep_mixed_response_le
    {F G : ℝ → ℝ} (hF : BoundedDerivs F) (hG : BoundedDerivs G)
    {K B J ε : ℝ≥0} (hFK : LipschitzWith K F) (hGK : LipschitzWith K G)
    (hJ : LipschitzWith J (fun z => G z - F z))
    (hGF : ∀ z, |G z - F z| ≤ ε) (hε : ε ≤ 1)
    {v : ℝ} (hv : |v| ≤ B) {a b : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) (x : ℝ) :
    |(scalarStep b v G x - scalarStep b v F x) -
      (scalarStep a v G x - scalarStep a v F x)| ≤
      v ^ 2 * mixedVarianceConstant K B * ((J : ℝ) + ε) * |b - a| := by
  exact scalarStep_response_of_variance_bound hF hG v x
    (mul_nonneg (mul_nonneg (sq_nonneg v) (mixedVarianceConstant_nonneg K B))
      (add_nonneg J.coe_nonneg ε.coe_nonneg))
    (fun m hm => scalarStep_mixed_variance_le hF hG hFK hGK hJ hGF hε hm hv x) ha hb

def mixedTimeConstant (β : ℝ) (K : ℝ≥0) : ℝ :=
  β ^ 2 * mixedVarianceConstant K ‖β‖₊

theorem mixedTimeConstant_nonneg (β : ℝ) (K : ℝ≥0) : 0 ≤ mixedTimeConstant β K :=
  mul_nonneg (sq_nonneg β) (mixedVarianceConstant_nonneg K ‖β‖₊)

theorem scalarTimeStep_mixed_response_le (β : ℝ)
    {F G : ℝ → ℝ} (hF : BoundedDerivs F) (hG : BoundedDerivs G)
    {K J ε : ℝ≥0} (hFK : LipschitzWith K F) (hGK : LipschitzWith K G)
    (hJ : LipschitzWith J (fun z => G z - F z))
    (hGF : ∀ z, |G z - F z| ≤ ε) (hε : ε ≤ 1)
    {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1)
    (t : ℝ≥0) (ht : t ≤ 1) (x : ℝ) :
    |(scalarTimeStep β b t G x - scalarTimeStep β b t F x) -
      (scalarTimeStep β a t G x - scalarTimeStep β a t F x)| ≤
      mixedTimeConstant β K * ((J : ℝ) + ε) * (t : ℝ) * |b - a| := by
  have hv : |β * Real.sqrt (t : ℝ)| ≤ (‖β‖₊ : ℝ) := by
    rw [coe_nnnorm, Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_of_le_one_right (abs_nonneg β) (Real.sqrt_le_one.mpr ht)
  have H := scalarStep_mixed_response_le hF hG hFK hGK hJ hGF hε hv ha hb x
  change |(scalarTimeStep β b t G x - scalarTimeStep β b t F x) -
      (scalarTimeStep β a t G x - scalarTimeStep β a t F x)| ≤ _ at H
  apply H.trans_eq
  rw [mul_pow, Real.sq_sqrt t.coe_nonneg]
  dsimp only [mixedTimeConstant]
  ring

private theorem timeChain_difference_lipschitz (β : ℝ) (l : List (ℝ × ℝ≥0))
    (hm : ∀ p ∈ l, p.1 ∈ Icc (0 : ℝ) 1)
    {F G : ℝ → ℝ} (hF : BoundedDerivs F) (hG : BoundedDerivs G)
    {K H L ε : ℝ≥0} (hFK : LipschitzWith K F) (hGK : LipschitzWith K G)
    (hdF : LipschitzWith H (deriv F))
    (hL : LipschitzWith L (fun z => G z - F z)) (hGF : ∀ z, |G z - F z| ≤ ε) :
    LipschitzWith (L + K * ε) (fun z => scalarTimeChain β l G z - scalarTimeChain β l F z) := by
  have hf := scalarTimeChain_regular hF β l
  have hg := scalarTimeChain_regular hG β l
  have hd (z : ℝ) : HasDerivAt (fun z => scalarTimeChain β l G z - scalarTimeChain β l F z)
      (deriv (scalarTimeChain β l G) z - deriv (scalarTimeChain β l F) z) z :=
    (hg.1.differentiable (by norm_num) z).hasDerivAt.sub
      (hf.1.differentiable (by norm_num) z).hasDerivAt
  have hb (z : ℝ) : |deriv (scalarTimeChain β l G) z - deriv (scalarTimeChain β l F) z| ≤
      (L : ℝ) + (K : ℝ) * ε := by
    simp only [scalarTimeChain_eq_hierarchy]
    apply scalarHierarchy_gradient_terminal_stability _ _ _
      (fun i => hm (l.get i) (List.get_mem l i)) hF hG
      (fun y => (hF.1.differentiable (by norm_num) y).hasDerivAt)
      (fun y => (hG.1.differentiable (by norm_num) y).hasDerivAt) hdF
      (fun _ => norm_deriv_le_of_lipschitz hFK) (fun _ => norm_deriv_le_of_lipschitz hGK) hGF
    intro y
    have he := ((hG.1.differentiable (by norm_num) y).hasDerivAt.sub
      (hF.1.differentiable (by norm_num) y).hasDerivAt).deriv
    rw [← he]
    exact norm_deriv_le_of_lipschitz hL
  apply lipschitzWith_of_nnnorm_deriv_le (fun z => (hd z).differentiableAt)
  intro z
  rw [(hd z).deriv]
  exact_mod_cast hb z

def floorResponseConstant (β : ℝ) (K : ℝ≥0) : ℝ :=
  mixedTimeConstant β K * ((K : ℝ) + 1) + scalarTimeMassConstantK β K

theorem floorResponseConstant_nonneg (β : ℝ) (K : ℝ≥0) : 0 ≤ floorResponseConstant β K :=
  add_nonneg (mul_nonneg (mixedTimeConstant_nonneg β K) (by positivity))
    (scalarTimeMassConstantK_nonneg β K)

private theorem timeChain_single_mass_response (β : ℝ) (p l : List (ℝ × ℝ≥0))
    (hp : ∀ q ∈ p, q.1 ∈ Icc (0 : ℝ) 1) (hl : ∀ q ∈ l, q.1 ∈ Icc (0 : ℝ) 1)
    {F G : ℝ → ℝ} (hF : BoundedDerivs F) (hG : BoundedDerivs G)
    {K H L ε : ℝ≥0} (hFK : LipschitzWith K F) (hGK : LipschitzWith K G)
    (hdF : LipschitzWith H (deriv F))
    (hL : LipschitzWith L (fun z => G z - F z)) (hGF : ∀ z, |G z - F z| ≤ ε) (hε : ε ≤ 1)
    {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1)
    (t : ℝ≥0) (ht : t ≤ 1) (x : ℝ) :
    |(scalarTimeChain β (p ++ (b,t)::l) G x - scalarTimeChain β (p ++ (b,t)::l) F x) -
      (scalarTimeChain β (p ++ (a,t)::l) G x - scalarTimeChain β (p ++ (a,t)::l) F x)| ≤
      floorResponseConstant β K * ((ε : ℝ) + L) * ((t : ℝ) * |b - a|) +
        (scalarTimeMassConstantK β K * ((t : ℝ) * |b - a|)) ^ 2 := by
  let f := scalarTimeChain β l F
  let g := scalarTimeChain β l G
  have hf : BoundedDerivs f := scalarTimeChain_regular hF β l
  have hg : BoundedDerivs g := scalarTimeChain_regular hG β l
  have hfk : LipschitzWith K f := scalarTimeChain_lipschitz hF hFK β l (fun q hq => (hl q hq).1)
  have hgk : LipschitzWith K g := scalarTimeChain_lipschitz hG hGK β l (fun q hq => (hl q hq).1)
  have hgf : ∀ z, |g z - f z| ≤ ε := scalarTimeChain_uniform_nonexpansive hG hF β l
    (fun q hq => (hl q hq).1) hGF
  have hdiff := timeChain_difference_lipschitz β l hl hF hG hFK hGK hdF hL hGF
  let fa := scalarTimeStep β a t f
  let fb := scalarTimeStep β b t f
  let ga := scalarTimeStep β a t g
  let gb := scalarTimeStep β b t g
  have hfa : BoundedDerivs fa := scalarTimeStep_regular hf β a t
  have hfb : BoundedDerivs fb := scalarTimeStep_regular hf β b t
  have hga : BoundedDerivs ga := scalarTimeStep_regular hg β a t
  have hgb : BoundedDerivs gb := scalarTimeStep_regular hg β b t
  let W : ℝ → ℝ := fun z => fb z - fa z
  have hW : BoundedDerivs W := by
    simpa only [neg_one_mul, ← sub_eq_add_neg] using hfb.add (hfa.const_mul (-1))
  have hWlip : LipschitzWith (K + K) W :=
    (scalarTimeStep_lipschitz hf hfk hb.1 β t).sub (scalarTimeStep_lipschitz hf hfk ha.1 β t)
  let D : ℝ := (t : ℝ) * |b - a|
  have hD : 0 ≤ D := mul_nonneg t.coe_nonneg (abs_nonneg _)
  let C := scalarTimeMassConstantK β K
  have hC : 0 ≤ C := scalarTimeMassConstantK_nonneg β K
  let B₀ : ℝ≥0 := NNReal.mk (C * D) (mul_nonneg hC hD)
  have hWB : ∀ z, |W z| ≤ B₀ := by
    intro z
    simpa only [B₀, NNReal.coe_mk, C, D, mul_assoc] using
      scalarTimeStep_mass_lipschitz_general hf hfk β ht ha hb z
  have hbase : ∀ z, |ga z - fa z| ≤ ε :=
    scalarStep_uniform_nonexpansive hg hf ha.1 hgf (β * Real.sqrt (t : ℝ))
  have hout : |(scalarTimeChain β p (fun z => ga z + W z) x - scalarTimeChain β p ga x) -
      (scalarTimeChain β p (fun z => fa z + W z) x - scalarTimeChain β p fa x)| ≤
      (B₀ : ℝ) * ε + (B₀ : ℝ) ^ 2 := by
    simp only [scalarTimeChain_eq_hierarchy]
    exact scalarHierarchy_outer_response_le _ _ _ (fun i => hp _ (List.get_mem p i))
      hfa hga hW hWlip ε.coe_nonneg hbase hWB x
  have hfaW : (fun z => fa z + W z) = fb := by
    funext z
    dsimp only [W]
    ring
  rw [hfaW] at hout
  let P : ℝ := mixedTimeConstant β K * ((L : ℝ) + (K : ℝ) * ε + ε) * D
  have hreplace : ∀ z, |gb z - (ga z + W z)| ≤ P := by
    intro z
    calc
      _ = |(scalarTimeStep β b t g z - scalarTimeStep β b t f z) -
          (scalarTimeStep β a t g z - scalarTimeStep β a t f z)| := by
        dsimp only [gb, ga, W, fb, fa]
        congr 1
        ring
      _ ≤ mixedTimeConstant β K * ((L : ℝ) + (K : ℝ) * ε + ε) * (t : ℝ) * |b - a| := by
        simpa only [NNReal.coe_add, NNReal.coe_mul] using
          scalarTimeStep_mixed_response_le β hf hg hfk hgk hdiff hgf hε ha hb t ht z
      _ = P := by dsimp only [P, D]; ring
  have hrep := scalarTimeChain_uniform_nonexpansive hgb (hga.add hW) β p
    (fun q hq => (hp q hq).1) hreplace x
  have hcoef : P + (B₀ : ℝ) * ε ≤ floorResponseConstant β K * ((ε : ℝ) + L) * D := by
    have hJ : (L : ℝ) + (K : ℝ) * ε + ε ≤ ((K : ℝ) + 1) * ((ε : ℝ) + L) := by
      nlinarith [mul_nonneg K.coe_nonneg L.coe_nonneg]
    have h₁ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hJ (mixedTimeConstant_nonneg β K)) hD
    have h₂ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right L.coe_nonneg : (ε : ℝ) ≤ (ε : ℝ) + L)
      (mul_nonneg hC hD)
    dsimp only [P, B₀, NNReal.coe_mk, floorResponseConstant, C] at *
    nlinarith
  simp only [scalarTimeChain_append, scalarTimeChain]
  change |(scalarTimeChain β p gb x - scalarTimeChain β p fb x) -
    (scalarTimeChain β p ga x - scalarTimeChain β p fa x)| ≤ _
  calc
    _ = |(scalarTimeChain β p gb x - scalarTimeChain β p (fun z => ga z + W z) x) +
        ((scalarTimeChain β p (fun z => ga z + W z) x - scalarTimeChain β p ga x) -
          (scalarTimeChain β p fb x - scalarTimeChain β p fa x))| := by congr 1; ring
    _ ≤ P + ((B₀ : ℝ) * ε + (B₀ : ℝ) ^ 2) := (abs_add_le _ _).trans (add_le_add hrep hout)
    _ ≤ _ := by dsimp only [B₀, NNReal.coe_mk, C, D] at *; linarith

private def pairDistance (l : List (ℝ × ℝ × ℝ≥0)) : ℝ :=
  (l.map (fun q => (q.2.2 : ℝ) * |q.2.1 - q.1|)).sum

private def pairSquareDistance (l : List (ℝ × ℝ × ℝ≥0)) : ℝ :=
  (l.map (fun q => ((q.2.2 : ℝ) * |q.2.1 - q.1|) ^ 2)).sum

private theorem paired_timeChain_response (β : ℝ) (l : List (ℝ × ℝ × ℝ≥0))
    (hm : ∀ q ∈ l, q.1 ∈ Icc (0 : ℝ) 1 ∧ q.2.1 ∈ Icc (0 : ℝ) 1 ∧ q.2.2 ≤ 1)
    (p : List (ℝ × ℝ≥0)) (hp : ∀ q ∈ p, q.1 ∈ Icc (0 : ℝ) 1)
    {F G : ℝ → ℝ} (hF : BoundedDerivs F) (hG : BoundedDerivs G)
    {K H L ε : ℝ≥0} (hFK : LipschitzWith K F) (hGK : LipschitzWith K G)
    (hdF : LipschitzWith H (deriv F))
    (hL : LipschitzWith L (fun z => G z - F z)) (hGF : ∀ z, |G z - F z| ≤ ε) (hε : ε ≤ 1)
    (x : ℝ) :
    |(scalarTimeChain β (p ++ l.map (fun q => (q.2.1,q.2.2))) G x -
        scalarTimeChain β (p ++ l.map (fun q => (q.2.1,q.2.2))) F x) -
      (scalarTimeChain β (p ++ l.map (fun q => (q.1,q.2.2))) G x -
        scalarTimeChain β (p ++ l.map (fun q => (q.1,q.2.2))) F x)| ≤
      floorResponseConstant β K * ((ε : ℝ) + L) * pairDistance l +
        (scalarTimeMassConstantK β K) ^ 2 * pairSquareDistance l := by
  induction l generalizing p with
  | nil => simp only [List.map_nil, List.append_nil, sub_self, abs_zero,
      pairDistance, pairSquareDistance, List.sum_nil, mul_zero, add_zero, le_refl]
  | cons q l ih =>
    have hq := hm q (List.mem_cons_self)
    have htail r (hr : r ∈ l) := hm r (List.mem_cons_of_mem q hr)
    have hγtail : ∀ r ∈ l.map (fun q => (q.2.1,q.2.2)), r.1 ∈ Icc (0 : ℝ) 1 := by
      intro r hr
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
      exact (htail w hw).2.1
    have h₁ := timeChain_single_mass_response β p (l.map (fun q => (q.2.1,q.2.2)))
      hp hγtail hF hG hFK hGK hdF hL hGF hε hq.1 hq.2.1 q.2.2 hq.2.2 x
    have hpa : ∀ r ∈ p ++ [(q.1,q.2.2)], r.1 ∈ Icc (0 : ℝ) 1 := by
      intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · exact hp r hr
      · have he : r = (q.1,q.2.2) := List.mem_singleton.mp hr
        simpa only [he] using hq.1
    have h₂ := ih htail (p ++ [(q.1,q.2.2)]) hpa
    simp only [List.append_assoc, List.singleton_append] at h₂
    simp only [List.map_cons]
    calc
      _ ≤ |(scalarTimeChain β (p ++ (q.2.1,q.2.2)::l.map (fun q => (q.2.1,q.2.2))) G x -
            scalarTimeChain β (p ++ (q.2.1,q.2.2)::l.map (fun q => (q.2.1,q.2.2))) F x) -
          (scalarTimeChain β (p ++ (q.1,q.2.2)::l.map (fun q => (q.2.1,q.2.2))) G x -
            scalarTimeChain β (p ++ (q.1,q.2.2)::l.map (fun q => (q.2.1,q.2.2))) F x)| +
        |(scalarTimeChain β (p ++ (q.1,q.2.2)::l.map (fun q => (q.2.1,q.2.2))) G x -
            scalarTimeChain β (p ++ (q.1,q.2.2)::l.map (fun q => (q.2.1,q.2.2))) F x) -
          (scalarTimeChain β (p ++ (q.1,q.2.2)::l.map (fun q => (q.1,q.2.2))) G x -
            scalarTimeChain β (p ++ (q.1,q.2.2)::l.map (fun q => (q.1,q.2.2))) F x)| := abs_sub_le _ _ _
      _ ≤ (floorResponseConstant β K * ((ε : ℝ) + L) * ((q.2.2 : ℝ) * |q.2.1 - q.1|) +
          (scalarTimeMassConstantK β K * ((q.2.2 : ℝ) * |q.2.1 - q.1|)) ^ 2) +
        (floorResponseConstant β K * ((ε : ℝ) + L) * pairDistance l +
          (scalarTimeMassConstantK β K) ^ 2 * pairSquareDistance l) := add_le_add h₁ h₂
      _ = _ := by simp only [pairDistance, pairSquareDistance, List.map_cons, List.sum_cons]; ring

private def pairedDyadic (α γ : ℝ → ℝ) : ℕ → ℝ → ℝ≥0 → List (ℝ × ℝ × ℝ≥0)
  | 0, s, t => [(α s,γ s,t)]
  | n+1, s, t => pairedDyadic α γ n s (t/2) ++ pairedDyadic α γ n (s+(t:ℝ)/2) (t/2)

private theorem pairedDyadic_left (α γ : ℝ → ℝ) (n : ℕ) (s : ℝ) (t : ℝ≥0) :
    (pairedDyadic α γ n s t).map (fun q => (q.1,q.2.2)) = dyadicIntervals α n s t := by
  induction n generalizing s t with
  | zero => rfl
  | succ n ih => simp only [pairedDyadic, List.map_append, ih, dyadicIntervals]

private theorem pairedDyadic_right (α γ : ℝ → ℝ) (n : ℕ) (s : ℝ) (t : ℝ≥0) :
    (pairedDyadic α γ n s t).map (fun q => (q.2.1,q.2.2)) = dyadicIntervals γ n s t := by
  induction n generalizing s t with
  | zero => rfl
  | succ n ih => simp only [pairedDyadic, List.map_append, ih, dyadicIntervals]

private theorem pairedDyadic_bounds {α γ : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0 : ℝ) 1) (hγ : ∀ z, γ z ∈ Icc (0 : ℝ) 1)
    (n : ℕ) (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) :
    ∀ q ∈ pairedDyadic α γ n s t,
      q.1 ∈ Icc (0 : ℝ) 1 ∧ q.2.1 ∈ Icc (0 : ℝ) 1 ∧ q.2.2 ≤ 1 := by
  induction n generalizing s t with
  | zero =>
    intro q hq
    have he : q = (α s,γ s,t) := List.mem_singleton.mp hq
    simpa only [he] using And.intro (hα s) (And.intro (hγ s) ht)
  | succ n ih =>
    have hhalf : t / 2 ≤ 1 := (div_le_self (show (0 : ℝ≥0) ≤ t from bot_le) (by norm_num)).trans ht
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact ih s (t/2) hhalf q hq
    · exact ih (s+(t:ℝ)/2) (t/2) hhalf q hq

private theorem pairedDyadic_distance (α γ : ℝ → ℝ) (n : ℕ) (s : ℝ) (t : ℝ≥0) :
    pairDistance (pairedDyadic α γ n s t) = dyadicCDFDistance γ α n s t := by
  induction n generalizing s t with
  | zero => simp only [pairedDyadic, pairDistance, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero, dyadicCDFDistance]
  | succ n ih =>
    simpa only [pairedDyadic, pairDistance, List.map_append, List.sum_append, dyadicCDFDistance] using
      congrArg₂ (· + ·) (ih s (t/2)) (ih (s+(t:ℝ)/2) (t/2))

private theorem pairedDyadic_square_le {α γ : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0 : ℝ) 1) (hγ : ∀ z, γ z ∈ Icc (0 : ℝ) 1)
    (n : ℕ) (s : ℝ) (t : ℝ≥0) :
    pairSquareDistance (pairedDyadic α γ n s t) ≤ (t : ℝ) ^ 2 / (2 : ℝ) ^ n := by
  induction n generalizing s t with
  | zero =>
    have hd : |γ s - α s| ≤ 1 := abs_le.mpr ⟨by linarith [(hγ s).1, (hα s).2],
      by linarith [(hγ s).2, (hα s).1]⟩
    have hs := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hd 2) (sq_nonneg (t : ℝ))
    simpa only [pairedDyadic, pairSquareDistance, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero, pow_zero, div_one, mul_pow, one_pow, mul_one] using hs
  | succ n ih =>
    have H := add_le_add (ih s (t/2)) (ih (s+(t:ℝ)/2) (t/2))
    simp only [pairedDyadic, pairSquareDistance, List.map_append, List.sum_append]
    apply H.trans_eq
    rw [show ((t/2 : ℝ≥0) : ℝ) = (t : ℝ) / 2 by norm_num, pow_succ]
    ring

theorem dyadic_homogeneous_response_le (β : ℝ) {α γ : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0 : ℝ) 1) (hγ : ∀ z, γ z ∈ Icc (0 : ℝ) 1)
    {F G : ℝ → ℝ} (hF : BoundedDerivs F) (hG : BoundedDerivs G)
    {K H L ε : ℝ≥0} (hFK : LipschitzWith K F) (hGK : LipschitzWith K G)
    (hdF : LipschitzWith H (deriv F))
    (hL : LipschitzWith L (fun z => G z - F z)) (hGF : ∀ z, |G z - F z| ≤ ε) (hε : ε ≤ 1)
    (n : ℕ) (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) (x : ℝ) :
    |(dyadicScalar β γ n s t G x - dyadicScalar β γ n s t F x) -
      (dyadicScalar β α n s t G x - dyadicScalar β α n s t F x)| ≤
      floorResponseConstant β K * ((ε : ℝ) + L) * dyadicCDFDistance γ α n s t +
        (scalarTimeMassConstantK β K) ^ 2 * ((t : ℝ) ^ 2 / (2 : ℝ) ^ n) := by
  have H := paired_timeChain_response β (pairedDyadic α γ n s t)
    (pairedDyadic_bounds hα hγ n s t ht) [] (fun _ h => (List.not_mem_nil h).elim)
    hF hG hFK hGK hdF hL hGF hε x
  simp only [List.nil_append, pairedDyadic_left, pairedDyadic_right, pairedDyadic_distance] at H
  exact H.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left (pairedDyadic_square_le hα hγ n s t)
      (sq_nonneg (scalarTimeMassConstantK β K))))

theorem scalarCDFOperator_homogeneous_response_le (β : ℝ) {α γ : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0 : ℝ) 1) (hαm : Monotone α)
    (hγ : ∀ z, γ z ∈ Icc (0 : ℝ) 1) (hγm : Monotone γ)
    {F G : ℝ → ℝ} (hF : BoundedDerivs F) (hG : BoundedDerivs G)
    {K H L ε : ℝ≥0} (hFK : LipschitzWith K F) (hGK : LipschitzWith K G)
    (hdF : LipschitzWith H (deriv F))
    (hL : LipschitzWith L (fun z => G z - F z)) (hGF : ∀ z, |G z - F z| ≤ ε) (hε : ε ≤ 1)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) (x : ℝ) :
    |(scalarCDFOperator β γ s t G x - scalarCDFOperator β γ s t F x) -
      (scalarCDFOperator β α s t G x - scalarCDFOperator β α s t F x)| ≤
      floorResponseConstant β K * ((ε : ℝ) + L) * (∫ z in s..s+t, |γ z - α z|) := by
  let A : ℝ := floorResponseConstant β K * ((ε : ℝ) + L)
  have hA : 0 ≤ A := mul_nonneg (floorResponseConstant_nonneg β K) (by positivity)
  have hfinite (n : ℕ) := (dyadic_homogeneous_response_le β hα hγ hF hG hFK hGK
    hdF hL hGF hε n s t ht x).trans (add_le_add
      (mul_le_mul_of_nonneg_left (dyadicCDFDistance_integral_bound hγm hαm n s t) hA) le_rfl)
  have hGγ := (dyadicScalar_general_uniform hG hGK β hγ hγm s t ht).tendsto_at x
  have hFγ := (dyadicScalar_general_uniform hF hFK β hγ hγm s t ht).tendsto_at x
  have hGα := (dyadicScalar_general_uniform hG hGK β hα hαm s t ht).tendsto_at x
  have hFα := (dyadicScalar_general_uniform hF hFK β hα hαm s t ht).tendsto_at x
  have hz : Tendsto (fun n : ℕ => (t : ℝ) / (2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  have hz₂ : Tendsto (fun n : ℕ => (t : ℝ) ^ 2 / (2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  have hr := ((((hz.mul_const ((γ (s+t) - γ s) + (α (s+t) - α s))).const_add
    (∫ z in s..s+t, |γ z - α z|)).const_mul A).add
      (hz₂.const_mul ((scalarTimeMassConstantK β K) ^ 2)))
  have H := le_of_tendsto_of_tendsto ((hGγ.sub hFγ).sub (hGα.sub hFα)).abs hr
    (Eventually.of_forall hfinite)
  simpa only [zero_mul, mul_zero, add_zero] using H

private theorem lipschitz_mono {f : ℝ → ℝ} {A B : ℝ≥0}
    (hf : LipschitzWith A f) (hAB : A ≤ B) : LipschitzWith B f := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  exact (hf.dist_le_mul x y).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hAB) (dist_nonneg : 0 ≤ dist x y))

theorem scalarCDFOperator_add_homogeneous_response_le (β : ℝ) {α γ : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0 : ℝ) 1) (hαm : Monotone α)
    (hγ : ∀ z, γ z ∈ Icc (0 : ℝ) 1) (hγm : Monotone γ)
    {F V : ℝ → ℝ} (hF : BoundedDerivs F) (hV : BoundedDerivs V)
    {K H L ε : ℝ≥0} (hFK : LipschitzWith K F) (hdF : LipschitzWith H (deriv F))
    (hVL : LipschitzWith L V) (hVB : ∀ z, |V z| ≤ ε) (hε : ε ≤ 1) (hL : L ≤ 1)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) (x : ℝ) :
    |(scalarCDFOperator β γ s t (fun z => F z + V z) x - scalarCDFOperator β γ s t F x) -
      (scalarCDFOperator β α s t (fun z => F z + V z) x - scalarCDFOperator β α s t F x)| ≤
      floorResponseConstant β (K + 1) * ((ε : ℝ) + L) * (∫ z in s..s+t, |γ z - α z|) := by
  apply scalarCDFOperator_homogeneous_response_le β hα hαm hγ hγm hF (hF.add hV)
    (lipschitz_mono hFK (le_add_of_nonneg_right (by positivity)))
    (lipschitz_mono (hFK.add hVL) (add_le_add le_rfl hL)) hdF
  · simpa only [add_sub_cancel_left] using hVL
  · intro z
    simpa only [add_sub_cancel_left] using hVB z
  · exact hε
  · exact ht

theorem scalarCDFOperator_add_homogeneous_response_of_deriv_le (β : ℝ) {α γ : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0 : ℝ) 1) (hαm : Monotone α)
    (hγ : ∀ z, γ z ∈ Icc (0 : ℝ) 1) (hγm : Monotone γ)
    {F V : ℝ → ℝ} (hF : BoundedDerivs F) (hV : BoundedDerivs V)
    {K H L ε : ℝ≥0} (hFK : LipschitzWith K F) (hdF : LipschitzWith H (deriv F))
    (hVL : ∀ z, |deriv V z| ≤ L) (hVB : ∀ z, |V z| ≤ ε) (hε : ε ≤ 1) (hL : L ≤ 1)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) (x : ℝ) :
    |(scalarCDFOperator β γ s t (fun z => F z + V z) x - scalarCDFOperator β γ s t F x) -
      (scalarCDFOperator β α s t (fun z => F z + V z) x - scalarCDFOperator β α s t F x)| ≤
      floorResponseConstant β (K + 1) * ((ε : ℝ) + L) * (∫ z in s..s+t, |γ z - α z|) := by
  have hLip : LipschitzWith L V := lipschitzWith_of_nnnorm_deriv_le
    (hV.1.differentiable (by norm_num)) (fun z => by exact_mod_cast hVL z)
  exact scalarCDFOperator_add_homogeneous_response_le β hα hαm hγ hγm hF hV
    hFK hdF hLip hVB hε hL s t ht x

theorem scalarCDFOperator_floor_homogeneous_response_le (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0 : ℝ) 1) (hαm : Monotone α)
    {c σ : ℝ} (hc : 0 < c) (hσ : 0 ≤ σ) (hσ1 : 3 * σ ≤ 1)
    {F V : ℝ → ℝ} (hF : BoundedDerivs F) (hV : BoundedDerivs V)
    {K H L ε : ℝ≥0} (hFK : LipschitzWith K F) (hdF : LipschitzWith H (deriv F))
    (hVL : ∀ z, |deriv V z| ≤ L) (hVB : ∀ z, |V z| ≤ ε) (hε : ε ≤ 1) (hL : L ≤ 1)
    (t : ℝ≥0) (ht : t ≤ 1) (hlin : ∀ z ∈ Icc (0 : ℝ) t, c * z ≤ α z) (x : ℝ) :
    |(scalarCDFOperator β (fun z => max (α z) (3 * σ)) 0 t (fun z => F z + V z) x -
        scalarCDFOperator β (fun z => max (α z) (3 * σ)) 0 t F x) -
      (scalarCDFOperator β α 0 t (fun z => F z + V z) x - scalarCDFOperator β α 0 t F x)| ≤
      floorResponseConstant β (K + 1) * ((ε : ℝ) + L) * (9 * σ ^ 2 / c) := by
  have hγ : ∀ z, max (α z) (3 * σ) ∈ Icc (0 : ℝ) 1 := by
    intro z
    exact ⟨(hα z).1.trans (le_max_left _ _), max_le (hα z).2 hσ1⟩
  have H := scalarCDFOperator_add_homogeneous_response_of_deriv_le β hα hαm hγ
    (hαm.max monotone_const) hF hV hFK hdF hVL hVB hε hL 0 t ht x
  have hD := floor_distance_le hαm hc (show 0 ≤ 3 * σ by positivity) t hlin
  simp only [zero_add] at H
  have hD' : (∫ z in (0 : ℝ)..t, |max (α z) (3 * σ) - α z|) ≤ 9 * σ ^ 2 / c := by
    exact hD.trans_eq (by ring)
  exact H.trans (mul_le_mul_of_nonneg_left hD'
    (mul_nonneg (floorResponseConstant_nonneg β (K + 1)) (by positivity)))

theorem common_prefix_floor_homogeneous_response_le (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0 : ℝ) 1) (hαm : Monotone α)
    {c σ : ℝ} (hc : 0 < c) (hσ : 0 ≤ σ) (hσ1 : 3 * σ ≤ 1)
    {F V : ℝ → ℝ} (hF : BoundedDerivs F) (hV : BoundedDerivs V)
    {K H L ε : ℝ≥0} (hFK : LipschitzWith K F) (hdF : LipschitzWith H (deriv F))
    (hVL : ∀ z, |deriv V z| ≤ L) (hVB : ∀ z, |V z| ≤ ε) (hε : ε ≤ 1) (hL : L ≤ 1)
    (t : ℝ≥0) (ht : t ≤ 1) (hlin : ∀ z ∈ Icc (0 : ℝ) t, c * z ≤ α z) (x : ℝ) :
    |(scalarCDFOperator β (fun z => max (α z) (3 * σ) / 3) 0 t (fun z => F z + V z) x -
        scalarCDFOperator β (fun z => max (α z) (3 * σ) / 3) 0 t F x) -
      (scalarCDFOperator β (fun z => α z / 3) 0 t (fun z => F z + V z) x -
        scalarCDFOperator β (fun z => α z / 3) 0 t F x)| ≤
      floorResponseConstant β (K + 1) * ((ε : ℝ) + L) * (3 * σ ^ 2 / c) := by
  have hγ : ∀ z, max (α z) (3 * σ) ∈ Icc (0 : ℝ) 1 := by
    intro z
    exact ⟨(hα z).1.trans (le_max_left _ _), max_le (hα z).2 hσ1⟩
  have hdiv (f : ℝ → ℝ) (hf : ∀ z, f z ∈ Icc (0 : ℝ) 1) :
      ∀ z, f z / 3 ∈ Icc (0 : ℝ) 1 := by
    intro z
    constructor
    · exact div_nonneg (hf z).1 (by norm_num)
    · linarith [(hf z).2]
  have hdivm (f : ℝ → ℝ) (hf : Monotone f) : Monotone (fun z => f z / 3) := by
    intro z w hzw
    exact div_le_div_of_nonneg_right (hf hzw) (by norm_num)
  have H := scalarCDFOperator_add_homogeneous_response_of_deriv_le β (hdiv α hα) (hdivm α hαm)
    (hdiv _ hγ) (hdivm _ (hαm.max monotone_const)) hF hV hFK hdF hVL hVB hε hL 0 t ht x
  have hD := floor_distance_le hαm hc (show 0 ≤ 3 * σ by positivity) t hlin
  have he : (∫ z in (0 : ℝ)..t, |max (α z) (3 * σ) / 3 - α z / 3|) =
      (∫ z in (0 : ℝ)..t, |max (α z) (3 * σ) - α z|) / 3 := by
    simp_rw [← sub_div, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    exact intervalIntegral.integral_div _ _
  simp only [zero_add] at H
  rw [he] at H
  apply H.trans
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg (floorResponseConstant_nonneg β (K + 1)) (by positivity))
  exact (div_le_div_of_nonneg_right hD (by norm_num : (0 : ℝ) ≤ 3)).trans_eq (by ring)

end SKBarriers2.FloorResponse
