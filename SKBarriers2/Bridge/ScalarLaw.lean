module

public import SKBarriers2.Bridge.ScalarLawBasic
public import FRSB.ForwardStateLawLimit
public import FRSB.SupportQuotient

@[expose] public section

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open OAI.SK.Analytic Paper

namespace SKBarriers2.Bridge

private def prefixGrid (n : ℕ) (t : ℝ) (i : Fin (n + 2)) : ℝ :=
  min ((i : ℝ) / (n + 1 : ℕ)) t

private theorem prefixGrid_monotone (n : ℕ) (t : ℝ) : Monotone (prefixGrid n t) := by
  intro i j hij
  apply min_le_min_right
  apply div_le_div_of_nonneg_right _ (by positivity : (0 : ℝ) ≤ (n + 1 : ℕ))
  exact_mod_cast hij

private theorem prefixGrid_zero (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    prefixGrid n t 0 = 0 := by
  simp only [prefixGrid, Fin.val_zero, Nat.cast_zero, zero_div, min_eq_left ht]

private theorem prefixGrid_last (n : ℕ) (t : ℝ) (ht : t ≤ 1) :
    prefixGrid n t (Fin.last (n + 1)) = t := by
  simp only [prefixGrid, Fin.val_last]
  rw [div_self (by positivity : ((n + 1 : ℕ) : ℝ) ≠ 0), min_eq_right ht]

private theorem prefixGrid_models (μ : ParisiMeasure) (n : ℕ) (t : ℝ)
    (i : Fin (n + 1)) (z : ℝ)
    (hz : z ∈ Ico (prefixGrid n t i.castSucc) (prefixGrid n t i.succ)) :
    parisiCDF (parisiGridMeasure μ n) z =
      parisiCDF (parisiGridMeasure μ n) ((i : ℝ) / (n + 1 : ℕ)) := by
  apply parisiCDF_grid_eq_node μ n i.val
  have hzt : z < t := hz.2.trans_le (min_le_right _ _)
  have hlo : (i : ℝ) / (n + 1 : ℕ) ≤ z :=
    (min_le_iff.mp hz.1).resolve_right (not_le.mpr hzt)
  exact ⟨hlo, hz.2.trans_le (min_le_left _ _)⟩

theorem scalarLaw_grid (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (n : ℕ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
    {g : ℝ → ℝ} {L B : ℝ≥0} (hg : LipschitzWith L g) (hB : ∀ x, |g x| ≤ B) :
    scalarLaw β (cdf (realMeasure (parisiGridMeasure μ n) : Measure ℝ)) t g =
      ∫ ω, g (FRSB.optimalStateReal β (parisiGridMeasure μ n) ω t)
        ∂canonicalBrownianMeasure := by
  let ν := parisiGridMeasure μ n
  let q := prefixGrid n t
  let hq : Monotone q := prefixGrid_monotone n t
  let m : Fin (n + 1) → ℝ := fun i => parisiCDF ν ((i : ℝ) / (n + 1 : ℕ))
  let l := partitionTimeChain (n + 1) q hq m
  have hq0 : q 0 = 0 := prefixGrid_zero n t ht.1
  have hq1 : q (Fin.last (n + 1)) = t := prefixGrid_last n t ht.2
  have hd : (chainDuration l : ℝ) = t := by
    rw [partitionTimeChain_duration, hq0, hq1, sub_zero]
  have hdur : chainDuration l = t.toNNReal := by
    apply NNReal.coe_injective
    rw [hd, Real.coe_toNNReal _ ht.1]
  have hmodel : TimeChainModels (parisiCDF ν) 0 l := by
    rw [← hq0]
    exact partitionTimeChain_models (n + 1) q hq m (prefixGrid_models μ n t)
  have hm : ∀ p ∈ l, p.1 ∈ Icc (0 : ℝ) 1 := by
    intro p hp
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
    exact ⟨parisiCDF_nonneg ν _, parisiCDF_le_one ν _⟩
  have htNN : (t.toNNReal : ℝ) ≤ 1 := by rw [Real.coe_toNNReal _ ht.1]; exact ht.2
  have hchain := scalarCDFAverage_eq_chainAverage_lipschitz (Phi_regular β ν t ht)
    (Phi_lipschitz β ν t ht) hg hB β
    (fun z => ⟨parisiCDF_nonneg ν z, parisiCDF_le_one ν z⟩)
    (parisiCDF_monotone ν) l hm 0 t.toNNReal htNN hdur hmodel 0
  have hi := integral_scalarTimeChainAverage_eq β hβ ν l 0 t.toNNReal htNN
    (by simpa only [zero_add] using hdur) hmodel
    (show BoundedScalar g from ⟨hg.continuous, B, B.coe_nonneg, hB⟩)
  have hz (ω : BrownianSample) : selectedParisiItoState β 0 hβ ν 0 ω = 0 := by
    rw [← FRSB.optimalState_eq_selected β hβ ν,
      FRSB.optimalState_eq_real β ν (by norm_num), NNReal.coe_zero,
      FRSB.optimalState_initial]
  have he (ω : BrownianSample) : selectedParisiItoState β 0 hβ ν t.toNNReal ω =
      FRSB.optimalStateReal β ν ω t := by
    rw [← FRSB.optimalState_eq_selected β hβ ν,
      FRSB.optimalState_eq_real β ν htNN, Real.coe_toNNReal _ ht.1]
  simp_rw [Real.coe_toNNReal _ ht.1, hz, he] at hi
  simp only [integral_const, probReal_univ, one_smul] at hi
  simpa only [scalarLaw, cdf_realMeasure_eq] using hchain.trans hi

private theorem cdfDistance_eq_paper (μ ν : ParisiMeasure) :
    cdfDistance (cdf (realMeasure μ : Measure ℝ)) (cdf (realMeasure ν : Measure ℝ)) =
      parisiCDFDistance μ ν := by
  rw [cdf_realMeasure_eq, cdf_realMeasure_eq, cdfDistance, parisiCDFDistance,
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_Icc_eq_integral_Ioc]

theorem scalarLaw_grid_tendsto (β : ℝ) (μ : ParisiMeasure)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
    {g : ℝ → ℝ} {L B : ℝ≥0} (hg : LipschitzWith L g) (hB : ∀ x, |g x| ≤ B) :
    Tendsto (fun n => scalarLaw β
      (cdf (realMeasure (parisiGridMeasure μ n) : Measure ℝ)) t g) atTop
      (𝓝 (scalarLaw β (cdf (realMeasure μ : Measure ℝ)) t g)) := by
  let α := cdf (realMeasure μ : Measure ℝ)
  let αn := fun n => cdf (realMeasure (parisiGridMeasure μ n) : Measure ℝ)
  have hα : ∀ z, α z ∈ Icc (0 : ℝ) 1 := fun z => ⟨cdf_nonneg _ z, cdf_le_one _ z⟩
  have hn : ∀ n z, αn n z ∈ Icc (0 : ℝ) 1 := fun n z => ⟨cdf_nonneg _ z, cdf_le_one _ z⟩
  have hmono : Monotone α := (cdf _).mono
  have hnmono : ∀ n, Monotone (αn n) := fun n => (cdf _).mono
  have hD : Tendsto (fun n => cdfDistance (αn n) α) atTop (𝓝 0) := by
    simp only [αn, α, cdfDistance_eq_paper]
    exact FRSB.tendsto_parisiCDFDistance_of_tendsto (FRSB.tendsto_parisiGridMeasure μ)
  have ht1 : (1 - t).toNNReal ≤ 1 := Real.toNNReal_le_one.mpr (sub_le_self 1 ht.1)
  have hend : t + ((1 - t).toNNReal : ℝ) ≤ 1 := by
    rw [Real.coe_toNNReal _ (sub_nonneg.mpr ht.2)]; linarith
  have hfU : TendstoUniformly (fun n => Phi β (αn n) t) (Phi β α t) atTop :=
    scalarCDFValue_tendstoUniformly_interval β hα hmono hn hnmono hD
      t _ ht1 ht.1 hend
  have hgU : TendstoUniformly (fun _ : ℕ => g) g atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    exact .of_forall fun _ _ => by simpa only [dist_self] using hε
  have hav := scalarCDFAverage_tendstoUniformly_varying β hα hmono hn hnmono hD
    (Phi_regular β μ t ht) (fun n => Phi_regular β (parisiGridMeasure μ n) t ht)
    (Phi_lipschitz β μ t ht) (fun n => Phi_lipschitz β (parisiGridMeasure μ n) t ht)
    hg (fun _ => hg) hB (fun _ => hB) hfU hgU
    0 t.toNNReal (Real.toNNReal_le_one.mpr ht.2) (by norm_num)
    (by rw [zero_add, Real.coe_toNNReal _ ht.1]; exact ht.2)
  exact hav.tendsto_at 0

private theorem scalarHierarchyAverage_zero_coefficients (n : ℕ)
    (m : Fin n → ℝ) (f g : ℝ → ℝ) :
    scalarHierarchyAverage n m (fun _ => 0) f g = g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    simp only [scalarHierarchyAverage, scalarStep_zero, scalarStepAverage_zero_coefficient]
    exact ih _ _ _

theorem scalarLaw_beta_zero (α : ℝ → ℝ) (t : ℝ) (g : ℝ → ℝ) :
    scalarLaw 0 α t g = g 0 := by
  have he (n : ℕ) : dyadicScalarAverage 0 α n 0 t.toNNReal (Phi 0 α t) g 0 = g 0 := by
    simp only [dyadicScalarAverage, zero_mul, scalarHierarchyAverage_zero_coefficients]
  unfold scalarLaw scalarCDFAverage
  simp only [he]
  exact tendsto_const_nhds.limUnder_eq

theorem scalarLaw_eq_optimalState (β : ℝ) (μ : ParisiMeasure)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
    {g : ℝ → ℝ} {L B : ℝ≥0} (hg : LipschitzWith L g) (hB : ∀ x, |g x| ≤ B) :
    scalarLaw β (cdf (realMeasure μ : Measure ℝ)) t g =
      ∫ ω, g (FRSB.optimalStateReal β μ ω t) ∂canonicalBrownianMeasure := by
  by_cases hβ : β = 0
  · subst β
    have hz (ω : BrownianSample) : FRSB.optimalStateReal 0 μ ω t = 0 := by
      rw [FRSB.optimalState_integral_equation 0 μ ω ht]
      simp only [zero_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, intervalIntegral.integral_zero, add_zero]
    rw [scalarLaw_beta_zero]
    simp only [hz, integral_const, probReal_univ, one_smul]
  · have hU := scalarLaw_grid_tendsto β μ t ht hg hB
    have hP := FRSB.tendsto_integral_optimalStateReal_of_weak β hβ
      (parisiGridMeasure μ) μ (FRSB.tendsto_parisiGridMeasure μ) ht g hg.continuous
      B (fun x => hB x)
    exact tendsto_nhds_unique hU (hP.congr' (.of_forall fun n =>
      (scalarLaw_grid β hβ μ n t ht hg hB).symm))

theorem scalarLaw_eq_optimalState_overlapMeasure (β : ℝ) (μ : ProbabilityMeasure ℝ)
    (hμ : (μ : Measure ℝ) (Icc 0 1) = 1)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
    {g : ℝ → ℝ} {L B : ℝ≥0} (hg : LipschitzWith L g) (hB : ∀ x, |g x| ≤ B) :
    scalarLaw β (cdf (μ : Measure ℝ)) t g =
      ∫ ω, g (FRSB.optimalStateReal β (overlapMeasure μ hμ) ω t)
        ∂canonicalBrownianMeasure := by
  have he := scalarLaw_eq_optimalState β (overlapMeasure μ hμ) t ht hg hB
  rw [realMeasure_overlapMeasure] at he
  exact he

theorem parisiSpatialJet_power_test (β : ℝ) (μ : ParisiMeasure) (j n : ℕ) (t : ℝ) :
    ∃ L B : ℝ≥0, LipschitzWith L (fun x => FRSB.parisiSpatialJet β μ (j + 1) t x ^ n) ∧
      ∀ x, |FRSB.parisiSpatialJet β μ (j + 1) t x ^ n| ≤ B := by
  let K : ℝ≥0 := ‖bcfSpatialDerivative (parisiGradientBCF β μ) j‖₊
  let K' : ℝ≥0 := ‖bcfSpatialDerivative (parisiGradientBCF β μ) (j + 1)‖₊
  have hb (x : ℝ) : ‖FRSB.parisiSpatialJet β μ (j + 1) t x‖ ≤ K :=
    FRSB.norm_parisiSpatialJet_succ_le β μ j t x
  have hb' (x : ℝ) : ‖FRSB.parisiSpatialJet β μ (j + 2) t x‖ ≤ K' :=
    FRSB.norm_parisiSpatialJet_succ_le β μ (j + 1) t x
  have hd (x : ℝ) : HasDerivAt (fun y => FRSB.parisiSpatialJet β μ (j + 1) t y ^ n)
      ((n : ℝ) * FRSB.parisiSpatialJet β μ (j + 1) t x ^ (n - 1) *
        FRSB.parisiSpatialJet β μ (j + 2) t x) x :=
    (FRSB.hasDerivAt_parisiSpatialJet_succ β μ j t x).pow n
  refine ⟨n * K ^ (n - 1) * K', K ^ n, ?_, ?_⟩
  · apply lipschitzWith_of_nnnorm_deriv_le (fun x => (hd x).differentiableAt)
    intro x
    rw [(hd x).deriv]
    apply NNReal.coe_le_coe.mp
    simp only [NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_natCast, coe_nnnorm,
      norm_mul, norm_pow, Real.norm_natCast]
    gcongr
    · exact hb x
    · exact hb' x
  · intro x
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hb x) n

theorem scalarLaw_jet_power_eq (β : ℝ) (μ : ParisiMeasure) (j n : ℕ)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    scalarLaw β (cdf (realMeasure μ : Measure ℝ)) t
      (fun x => jet β (cdf (realMeasure μ : Measure ℝ)) (j + 1) t x ^ n) =
      ∫ ω, FRSB.jetProcess β μ (j + 1) t ω ^ n ∂canonicalBrownianMeasure := by
  simp_rw [jet_succ_eq_parisiSpatialJet β μ j t ht]
  obtain ⟨L, B, hL, hB⟩ := parisiSpatialJet_power_test β μ j n t
  exact scalarLaw_eq_optimalState β μ t ht hL hB

theorem scalarLaw_contact₁ (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (hmin : FRSB.IsParisiMinimizer β 0 μ) (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1)
    (hsupp : FRSB.parisiSupport μ = Icc (0 : ℝ) q)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) q) :
    β ^ 2 * scalarLaw β (cdf (realMeasure μ : Measure ℝ)) t
      (fun x => jet β (cdf (realMeasure μ : Measure ℝ)) 2 t x ^ 2) = 1 := by
  rw [scalarLaw_jet_power_eq β μ 1 2 t ⟨ht.1, ht.2.trans hq1⟩]
  exact FRSB.GammaPrime_eq_one_on_support_interval β hβ μ hmin q hq hq1 hsupp t ht

theorem scalarLaw_contact₂ (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (hmin : FRSB.IsParisiMinimizer β 0 μ) (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1)
    (hsupp : FRSB.parisiSupport μ = Icc (0 : ℝ) q)
    (t : ℝ) (ht : t ∈ Ico (0 : ℝ) q) :
    scalarLaw β (cdf (realMeasure μ : Measure ℝ)) t
      (fun x => jet β (cdf (realMeasure μ : Measure ℝ)) 3 t x ^ 2) =
      2 * cdf (realMeasure μ : Measure ℝ) t *
        scalarLaw β (cdf (realMeasure μ : Measure ℝ)) t
          (fun x => jet β (cdf (realMeasure μ : Measure ℝ)) 2 t x ^ 3) := by
  have ht1 : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.le.trans hq1⟩
  have he := FRSB.parisiCDF_eq_momentQuotient_on_support_interval β hβ μ hmin
    q hq hq1 hsupp t ht
  have hpos := FRSB.quotientDenominator_pos β hβ μ t ht1
  unfold FRSB.momentQuotient at he
  have hm : FRSB.quotientNumerator β μ t =
      2 * parisiCDF μ t * FRSB.quotientDenominator β μ t := by
    have hh := (eq_div_iff (ne_of_gt (mul_pos (by norm_num) hpos))).mp he
    linarith
  rw [scalarLaw_jet_power_eq β μ 2 2 t ht1, scalarLaw_jet_power_eq β μ 1 3 t ht1,
    cdf_realMeasure_eq]
  simpa only [FRSB.quotientNumerator, FRSB.quotientDenominator,
    FRSB.quotientNumeratorPolynomial, FRSB.quotientDenominatorPolynomial,
    FRSB.moment_X_pow] using hm

theorem scalarLaw_contacts_of_minimizer (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (hmin : scalarCDFParisi β (cdf (realMeasure μ : Measure ℝ)) = finiteParisiInf β)
    (q : ℝ) (hq : q ∈ Ioo (0 : ℝ) 1)
    (hsupp : FRSB.parisiSupport μ = Icc (0 : ℝ) q) :
    (∀ t ∈ Ioo (0 : ℝ) q,
      β ^ 2 * scalarLaw β (cdf (realMeasure μ : Measure ℝ)) t
        (fun x => jet β (cdf (realMeasure μ : Measure ℝ)) 2 t x ^ 2) = 1) ∧
    (∀ t ∈ Ioo (0 : ℝ) q,
      scalarLaw β (cdf (realMeasure μ : Measure ℝ)) t
        (fun x => jet β (cdf (realMeasure μ : Measure ℝ)) 3 t x ^ 2) =
      2 * cdf (realMeasure μ : Measure ℝ) t *
        scalarLaw β (cdf (realMeasure μ : Measure ℝ)) t
          (fun x => jet β (cdf (realMeasure μ : Measure ℝ)) 2 t x ^ 3)) := by
  have hP : FRSB.IsParisiMinimizer β 0 μ := (scalarCDFParisi_minimizer_iff β μ).mp hmin
  exact ⟨fun t ht => scalarLaw_contact₁ β hβ μ hP q hq.1 hq.2.le hsupp t
    ⟨ht.1.le, ht.2.le⟩,
    fun t ht => scalarLaw_contact₂ β hβ μ hP q hq.1 hq.2.le hsupp t ⟨ht.1.le, ht.2⟩⟩

end SKBarriers2.Bridge
