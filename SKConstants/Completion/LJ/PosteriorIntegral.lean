module

public import SKConstants.Completion.LJ.OriginalPredictable
public import SKConstants.ParisiFullVarianceIntegral
public import SKConstants.ParisiFullSpinRowMoments
public import SKConstants.BrownianContinuousLikelihood
public import SKConstants.BrownianDyadicGrid

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology BigOperators

namespace SKConstants.Completion.LJ
open SKConstantsOAI.ZeroTemperatureSK LC1
variable {Ω : Type*} [MeasurableSpace Ω]

def actualCurvature (W : BrownianSystem Ω) (β : ℝ) (s : ℝ≥0) (w : Ω) : ℝ :=
  actualParisiFullCurvature β s (actualParisiFullScalarProcess W β s w)

theorem measurable_actualCurvature (W : BrownianSystem Ω) (β : ℝ) (s : ℝ≥0) :
    Measurable (actualCurvature W β s) := by
  have ha := ((continuous_actualParisiFullCurvature β).comp
    ((continuous_const : Continuous (fun _ : ℝ => (s : ℝ))).prodMk continuous_id)).measurable
  change Measurable (actualParisiFullCurvature β s) at ha
  exact ha.comp ((actualParisiFullScalarDrift β).solution_measurable W s)

theorem actualCurvature_abs_le (W : BrownianSystem Ω) (β : ℝ) (s : ℝ≥0) (w : Ω) :
    |actualCurvature W β s w| ≤ 1 := actualParisiFullCurvature_abs_le_one β s _

theorem actualCurvature_continuous_ae (W : BrownianSystem Ω) (β : ℝ) :
    ∀ᵐ w ∂W.law, Continuous (fun s => actualCurvature W β s w) := by
  filter_upwards [(actualParisiFullScalarDrift β).solution_continuous_ae W] with w hw
  have hc := (continuous_actualParisiFullCurvature β).comp (NNReal.continuous_coe.prodMk hw)
  exact hc

def curvatureFieldCoefficient (β : ℝ) (t : ℕ → ℝ≥0) : OriginalFieldCoefficient t :=
  fun k p => actualParisiFullCurvature β (t k) (p ⟨t k, (t k).coe_nonneg, le_rfl⟩)

theorem measurable_curvatureFieldCoefficient (β : ℝ) (t : ℕ → ℝ≥0) (k : ℕ) :
    Measurable (curvatureFieldCoefficient β t k) := by
  have ha := ((continuous_actualParisiFullCurvature β).comp
    ((continuous_const : Continuous (fun _ : ℝ => (t k : ℝ))).prodMk continuous_id)).measurable
  change Measurable (actualParisiFullCurvature β (t k)) at ha
  exact ha.comp (ContinuousMap.measurable_eval _)

theorem curvatureFieldCoefficient_actual (W : BrownianSystem Ω) (β : ℝ)
    (t : ℕ → ℝ≥0) (k : ℕ) :
    originalFieldCoefficient W (actualParisiFullScalarDrift β) t (curvatureFieldCoefficient β t) k
      =ᵐ[W.law] actualCurvature W β (t k) := by
  filter_upwards [boundedDriftPastPath_version W (actualParisiFullScalarDrift β) (t k)] with w hw
  change actualParisiFullCurvature β (t k)
    (boundedDriftPastPath W (actualParisiFullScalarDrift β) (t k) w _) = _
  rw [hw]
  rfl

def posteriorBrownianSum (W : BrownianSystem Ω) (β : ℝ) (t : ℕ → ℝ≥0)
    (n : ℕ) (w : Ω) : ℝ :=
  ∑ k ∈ Finset.range n, actualCurvature W β (t k) w * (W.B (t (k + 1)) w - W.B (t k) w)

theorem measurable_posteriorBrownianSum (W : BrownianSystem Ω) (β : ℝ)
    (t : ℕ → ℝ≥0) (n : ℕ) : Measurable (posteriorBrownianSum W β t n) := by
  apply Finset.measurable_sum
  intro k _
  exact (measurable_actualCurvature W β _).mul ((W.measurable _).sub (W.measurable _))

theorem posteriorBrownianSum_originalField (W : BrownianSystem Ω) (β : ℝ)
    (t : ℕ → ℝ≥0) (n : ℕ) :
    originalFieldSum W (actualParisiFullScalarDrift β) t (curvatureFieldCoefficient β t) n
      =ᵐ[W.law] posteriorBrownianSum W β t n := by
  have hc : ∀ᵐ w ∂W.law, ∀ k : ℕ,
      originalFieldCoefficient W (actualParisiFullScalarDrift β) t (curvatureFieldCoefficient β t) k w =
        actualCurvature W β (t k) w := ae_all_iff.mpr (curvatureFieldCoefficient_actual W β t)
  filter_upwards [hc] with w hw
  rw [originalFieldSum, predictableGaussianSum_eq_range_sum]
  simp only [hw, brownianMeshIncrement, posteriorBrownianSum]

theorem posteriorBrownianSum_isometry (W : BrownianSystem Ω) (β : ℝ)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (n : ℕ) :
    MemLp (posteriorBrownianSum W β t n) 2 W.law ∧
      (∫ w, posteriorBrownianSum W β t n w ^ 2 ∂W.law) =
        ∑ k ∈ Finset.range n, ((t (k + 1) : ℝ) - t k) *
          actualParisiFullSusceptibilitySquareExpected W β (t k) := by
  let := W.isProbability
  have hsq (k : ℕ) : Integrable (fun w =>
      originalFieldCoefficient W (actualParisiFullScalarDrift β) t (curvatureFieldCoefficient β t) k w ^ 2)
      W.law := by
    apply Integrable.of_bound
      ((measurable_originalFieldCoefficient W _ t _ (measurable_curvatureFieldCoefficient β t) k).pow_const 2).aestronglyMeasurable 1
    apply ae_of_all
    intro w
    rw [Real.norm_eq_abs, abs_pow]
    exact (pow_le_pow_left₀ (abs_nonneg _) (actualParisiFullCurvature_abs_le_one β _ _) 2).trans_eq (by norm_num)
  have hi := originalFieldSum_isometry W (actualParisiFullScalarDrift β) t ht
    (curvatureFieldCoefficient β t) (measurable_curvatureFieldCoefficient β t) hsq n
  have he := posteriorBrownianSum_originalField W β t n
  have hi' : Integrable (fun w => posteriorBrownianSum W β t n w ^ 2) W.law :=
    hi.1.congr (he.mono (fun w hw => congrArg (fun x : ℝ => x ^ 2) hw))
  refine ⟨(memLp_two_iff_integrable_sq (measurable_posteriorBrownianSum W β t n).aestronglyMeasurable).mpr hi', ?_⟩
  rw [← integral_congr_ae (he.mono (fun w hw => congrArg (fun x : ℝ => x ^ 2) hw)), hi.2.2]
  rw [Fin.sum_univ_eq_sum_range (fun k => (brownianMeshVariance t k : ℝ) *
    ∫ w, originalFieldCoefficient W (actualParisiFullScalarDrift β) t (curvatureFieldCoefficient β t) k w ^ 2 ∂W.law)]
  apply Finset.sum_congr rfl
  intro k _
  rw [brownianMeshVariance, NNReal.coe_sub (ht (Nat.le_succ k))]
  congr 1
  refine (integral_congr_ae ((curvatureFieldCoefficient_actual W β t k).mono
    (fun w hw => congrArg (fun x : ℝ => x ^ 2) hw))).trans ?_
  simp only [actualParisiFullSusceptibilitySquareExpected, actualCurvature, Real.toNNReal_coe]

theorem actualCurvature_pair_integrable (W : BrownianSystem Ω) (β : ℝ) (s u : ℝ≥0) :
    Integrable (fun w => actualCurvature W β s w * actualCurvature W β u w) W.law := by
  let := W.isProbability
  apply Integrable.of_bound ((measurable_actualCurvature W β s).mul
    (measurable_actualCurvature W β u)).aestronglyMeasurable 1
  apply ae_of_all
  intro w
  change ‖actualCurvature W β s w * actualCurvature W β u w‖ ≤ 1
  rw [Real.norm_eq_abs, abs_mul]
  exact (mul_le_mul (actualCurvature_abs_le W β s w) (actualCurvature_abs_le W β u w)
    (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)

theorem posteriorBrownianSum_terminal_cross (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (n : ℕ) :
    (∫ w, actualParisiMagnetizationObservable W β (t n) w *
      posteriorBrownianSum W β t n w ∂W.law) =
      ∑ k ∈ Finset.range n, ∫ u in (t k : ℝ)..(t (k + 1) : ℝ),
        ∫ w, actualCurvature W β (t k) w * actualCurvature W β u.toNNReal w ∂W.law := by
  let := W.isProbability
  have hm := measurable_actualParisiMagnetizationObservable W β (t n)
  have hi (k : ℕ) : Integrable (fun w => actualParisiMagnetizationObservable W β (t n) w *
      (actualCurvature W β (t k) w * (W.B (t (k + 1)) w - W.B (t k) w))) W.law := by
    have hb : ∀ᵐ w ∂W.law, ‖actualParisiMagnetizationObservable W β (t n) w *
        actualCurvature W β (t k) w‖ ≤ (1 : ℝ≥0) := ae_of_all _ (fun w => by
      rw [Real.norm_eq_abs, abs_mul]
      exact (mul_le_mul (actualParisiMagnetizationObservable_abs_le W β _ w)
        (actualCurvature_abs_le W β _ w) (abs_nonneg _) zero_le_one).trans_eq (one_mul 1))
    have hi := ((W.brownian.integrable_eval (t (k + 1))).sub
      (W.brownian.integrable_eval (t k))).bdd_mul
      (hm.mul (measurable_actualCurvature W β (t k))).aestronglyMeasurable hb
    simpa only [Pi.mul_apply, Pi.sub_apply, mul_assoc] using hi
  unfold posteriorBrownianSum
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun k _ => hi k)]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn := Finset.mem_range.mp hk
  let F := curvatureFieldCoefficient β t k
  have hF : Measurable F := measurable_curvatureFieldCoefficient β t k
  have hFb (p : ScalarContinuousPath (t k)) : |F p| ≤ (1 : ℝ≥0) :=
    actualParisiFullCurvature_abs_le_one β _ _
  have hc := actualFullProcess_terminal_brownian_cross_moment_test W β hβ
    (t k) (t (k + 1)) (t n) (ht (Nat.le_succ k)) (ht (by omega)) F hF 1 hFb
  have he := curvatureFieldCoefficient_actual W β t k
  refine (integral_congr_ae (he.symm.mono (fun w hw => ?_))).trans (hc.trans ?_)
  · change actualCurvature W β (t k) w = F (boundedDriftPastPath W (actualParisiFullScalarDrift β) (t k) w) at hw
    rw [hw]
    ring
  · apply intervalIntegral.integral_congr
    intro u _
    apply integral_congr_ae (he.mono (fun w hw => ?_))
    change F (boundedDriftPastPath W (actualParisiFullScalarDrift β) (t k) w) = actualCurvature W β (t k) w at hw
    rw [hw]
    dsimp only [actualCurvature]

theorem continuous_actualCurvature_pair (W : BrownianSystem Ω) (β : ℝ) (s : ℝ≥0) :
    Continuous (fun u : ℝ => ∫ w, actualCurvature W β s w *
      actualCurvature W β u.toNNReal w ∂W.law) := by
  let := W.isProbability
  apply continuous_of_dominated (bound := fun _ => (1 : ℝ))
  · intro u
    exact ((measurable_actualCurvature W β s).mul
      (measurable_actualCurvature W β u.toNNReal)).aestronglyMeasurable
  · intro u
    exact ae_of_all _ (fun w => by
      rw [Real.norm_eq_abs, abs_mul]
      exact (mul_le_mul (actualCurvature_abs_le W β s w) (actualCurvature_abs_le W β _ w)
        (abs_nonneg _) zero_le_one).trans_eq (one_mul 1))
  · exact integrable_const _
  · filter_upwards [actualCurvature_continuous_ae W β] with w hw
    exact continuous_const.mul (hw.comp continuous_real_toNNReal)

theorem actualCurvature_difference_sq (W : BrownianSystem Ω) (β : ℝ) (s u : ℝ≥0) :
    (∫ w, (actualCurvature W β s w - actualCurvature W β u w) ^ 2 ∂W.law) =
      actualParisiFullSusceptibilitySquareExpected W β s +
        actualParisiFullSusceptibilitySquareExpected W β u -
          2 * (∫ w, actualCurvature W β s w * actualCurvature W β u w ∂W.law) := by
  have he (w : Ω) : (actualCurvature W β s w - actualCurvature W β u w) ^ 2 =
      actualCurvature W β s w * actualCurvature W β s w +
        actualCurvature W β u w * actualCurvature W β u w -
          2 * (actualCurvature W β s w * actualCurvature W β u w) := by ring
  simp_rw [he]
  have hsub := integral_sub ((actualCurvature_pair_integrable W β s s).add
      (actualCurvature_pair_integrable W β u u)) ((actualCurvature_pair_integrable W β s u).const_mul 2)
  simp only [Pi.add_apply] at hsub
  rw [hsub,
    integral_add (actualCurvature_pair_integrable W β s s) (actualCurvature_pair_integrable W β u u),
    integral_const_mul]
  simp only [actualParisiFullSusceptibilitySquareExpected, actualCurvature, Real.toNNReal_coe,
    pow_two]

theorem posteriorBrownianSum_error (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (ht0 : t 0 = 0) (n : ℕ) :
    (∫ w, (actualParisiMagnetizationObservable W β (t n) w -
      posteriorBrownianSum W β t n w) ^ 2 ∂W.law) =
      ∑ k ∈ Finset.range n, ∫ u in (t k : ℝ)..(t (k + 1) : ℝ),
        ∫ w, (actualCurvature W β (t k) w - actualCurvature W β u.toNNReal w) ^ 2 ∂W.law := by
  let := W.isProbability
  let M := actualParisiMagnetizationObservable W β (t n)
  let S := posteriorBrownianSum W β t n
  let r := actualParisiFullSusceptibilitySquareExpected W β
  have hm : MemLp M 2 W.law :=
    (memLp_two_iff_integrable_sq (measurable_actualParisiMagnetizationObservable W β _).aestronglyMeasurable).mpr
      (by simpa only [pow_two] using integrable_actualParisiMagnetization_pair W β (t n) (t n))
  have hs := (posteriorBrownianSum_isometry W β t ht n).1
  have hms := hm.integrable_mul hs
  have he (w : Ω) : (M w - S w) ^ 2 = M w ^ 2 + S w ^ 2 - 2 * (M w * S w) := by ring
  change (∫ w, (M w - S w) ^ 2 ∂W.law) = _
  simp_rw [he]
  have hsub := integral_sub (hm.integrable_sq.add hs.integrable_sq) (hms.const_mul 2)
  have hadd := integral_add hm.integrable_sq hs.integrable_sq
  simp only [Pi.add_apply, Pi.mul_apply] at hsub hadd
  rw [hsub, hadd, integral_const_mul]
  have hm2 : (∫ w, M w ^ 2 ∂W.law) = ∫ u in (0 : ℝ)..(t n : ℝ), r u := by
    have h := actualParisiFullSusceptibilitySquareExpected_interval W β hβ 0 (t n) bot_le
    have h0 := actualParisiFullOverlap_pre W β hβ 0 bot_le
    rw [h0] at h
    simpa only [actualParisiFullOverlap, NNReal.coe_zero, zero_div, sub_zero, M, r] using h.symm
  have hsum : (∫ u in (0 : ℝ)..(t n : ℝ), r u) =
      ∑ k ∈ Finset.range n, ∫ u in (t k : ℝ)..(t (k + 1) : ℝ), r u := by
    have h := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (f := r) (a := fun k => (t k : ℝ))
      (n := n) (fun k _ => (continuous_actualParisiFullSusceptibilitySquareExpected W β).intervalIntegrable _ _)
    simpa only [ht0, NNReal.coe_zero] using h.symm
  change (∫ w, M w ^ 2 ∂W.law) + (∫ w, S w ^ 2 ∂W.law) -
    2 * (∫ w, M w * S w ∂W.law) = _
  rw [hm2, hsum, posteriorBrownianSum_isometry W β t ht n |>.2,
    posteriorBrownianSum_terminal_cross W β hβ t ht n,
    Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  have hr : IntervalIntegrable r volume (t k : ℝ) (t (k + 1) : ℝ) :=
    (continuous_actualParisiFullSusceptibilitySquareExpected W β).intervalIntegrable _ _
  have hc : IntervalIntegrable (fun u : ℝ => ∫ w, actualCurvature W β (t k) w *
      actualCurvature W β u.toNNReal w ∂W.law) volume (t k : ℝ) (t (k + 1) : ℝ) :=
    (continuous_actualCurvature_pair W β (t k)).intervalIntegrable _ _
  have hconst : ((t (k + 1) : ℝ) - t k) * r (t k) =
      ∫ _ in (t k : ℝ)..(t (k + 1) : ℝ), r (t k) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
  rw [hconst]
  rw [← intervalIntegral.integral_add hr (intervalIntegrable_const),
    ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_sub (hr.add intervalIntegrable_const) (hc.const_mul 2)]
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le (NNReal.coe_le_coe.mpr (ht (Nat.le_succ k)))] at hu
  have hu0 : 0 ≤ u := (t k).coe_nonneg.trans hu.1
  dsimp only
  rw [actualCurvature_difference_sq, Real.coe_toNNReal u hu0]
  dsimp only [r]
  ring

theorem continuous_actualCurvature_difference_sq (W : BrownianSystem Ω) (β : ℝ) :
    Continuous (fun p : ℝ≥0 × ℝ≥0 =>
      ∫ w, (actualCurvature W β p.1 w - actualCurvature W β p.2 w) ^ 2 ∂W.law) := by
  let := W.isProbability
  exact continuous_expected_sq_difference_of_bounded W.law (actualCurvature W β)
    (fun s => (measurable_actualCurvature W β s).aestronglyMeasurable)
    (actualCurvature_continuous_ae W β) 1
    (fun s w => by rw [Real.norm_eq_abs]; exact actualCurvature_abs_le W β s w)

theorem integrable_posteriorBrownianSum_error (W : BrownianSystem Ω) (β : ℝ)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (n : ℕ) :
    Integrable (fun w => (actualParisiMagnetizationObservable W β (t n) w -
      posteriorBrownianSum W β t n w) ^ 2) W.law := by
  have hm : MemLp (actualParisiMagnetizationObservable W β (t n)) 2 W.law :=
    (memLp_two_iff_integrable_sq (measurable_actualParisiMagnetizationObservable W β _).aestronglyMeasurable).mpr
      (by simpa only [pow_two] using integrable_actualParisiMagnetization_pair W β (t n) (t n))
  exact (hm.sub (posteriorBrownianSum_isometry W β t ht n).1).integrable_sq

attribute [local irreducible] actualCurvature posteriorBrownianSum
  actualParisiMagnetizationObservable actualParisiFullCurvature

theorem posteriorBrownianSum_tendsto_L2 (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℕ → ℝ≥0) (n : ℕ → ℕ) (T : ℝ≥0)
    (ht : ∀ l, Monotone (t l)) (ht0 : ∀ l, t l 0 = 0) (htT : ∀ l, t l (n l) = T)
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (hmesh : ∀ l k, k < n l → ((t l (k + 1) : ℝ) - t l k) ≤ δ l) :
    Tendsto (fun l => ∫ w, (posteriorBrownianSum W β (t l) (n l) w -
      actualParisiMagnetizationObservable W β T w) ^ 2 ∂W.law) atTop (𝓝 0) := by
  let := W.isProbability
  have hC (s : ℝ≥0) (w : Ω) : ‖actualCurvature W β s w‖ ≤ 1 := by
    rw [Real.norm_eq_abs]
    exact actualCurvature_abs_le W β s w
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hT : 0 < (T : ℝ) + 1 := by positivity
  obtain ⟨η, hη, hsmall⟩ := expected_sq_difference_uniform_small_of_bounded W.law
    (actualCurvature W β) (fun s => (measurable_actualCurvature W β s).aestronglyMeasurable)
    (actualCurvature_continuous_ae W β) 1 hC T (ε / ((T : ℝ) + 1)) (div_pos hε hT)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hδ.eventually (eventually_lt_nhds hη))
  refine ⟨N, fun l hl => ?_⟩
  have he : (∫ w, (posteriorBrownianSum W β (t l) (n l) w -
      actualParisiMagnetizationObservable W β T w) ^ 2 ∂W.law) =
      ∑ k ∈ Finset.range (n l), ∫ u in (t l k : ℝ)..(t l (k + 1) : ℝ),
        ∫ w, (actualCurvature W β (t l k) w - actualCurvature W β u.toNNReal w) ^ 2 ∂W.law := by
    rw [← htT l]
    simp_rw [sub_sq_comm (posteriorBrownianSum W β (t l) (n l) _) _]
    exact posteriorBrownianSum_error W β hβ (t l) (ht l) (ht0 l) (n l)
  have hb : (∑ k ∈ Finset.range (n l), ∫ u in (t l k : ℝ)..(t l (k + 1) : ℝ),
        ∫ w, (actualCurvature W β (t l k) w - actualCurvature W β u.toNNReal w) ^ 2 ∂W.law) ≤
      (T : ℝ) * (ε / ((T : ℝ) + 1)) := by
    calc
      _ ≤ ∑ k ∈ Finset.range (n l),
          ((t l (k + 1) : ℝ) - t l k) * (ε / ((T : ℝ) + 1)) := by
        apply Finset.sum_le_sum
        intro k hk
        have hkn := Finset.mem_range.mp hk
        have hst : (t l k : ℝ) ≤ t l (k + 1) := NNReal.coe_le_coe.mpr (ht l (Nat.le_succ k))
        have hpair : Continuous (fun u : ℝ => (t l k, u.toNNReal)) :=
          continuous_const.prodMk continuous_real_toNNReal
        have hc : Continuous (fun u : ℝ => ∫ w,
            (actualCurvature W β (t l k) w - actualCurvature W β u.toNNReal w) ^ 2 ∂W.law) :=
          (continuous_actualCurvature_difference_sq W β).comp hpair
        have hi := intervalIntegral.integral_mono_on hst (hc.intervalIntegrable _ _)
          (intervalIntegrable_const (c := ε / ((T : ℝ) + 1)) (μ := volume)) (fun u hu => ?_)
        · simpa only [intervalIntegral.integral_const, smul_eq_mul] using hi
        · have hu0 : 0 ≤ u := (t l k).coe_nonneg.trans hu.1
          have hsT : t l k ≤ T := by rw [← htT l]; exact ht l hkn.le
          have huT : u.toNNReal ≤ T := by
            apply NNReal.coe_le_coe.mp
            rw [Real.coe_toNNReal u hu0]
            exact hu.2.trans (NNReal.coe_le_coe.mpr (by rw [← htT l]; exact ht l (by omega)))
          apply (hsmall (t l k) hsT u.toNNReal huT ?_).le
          rw [Real.coe_toNNReal u hu0, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hu.1)]
          exact ((sub_le_sub_right hu.2 _).trans (hmesh l k hkn)).trans_lt (hN l hl)
      _ = (T : ℝ) * (ε / ((T : ℝ) + 1)) := by
        rw [← Finset.sum_mul, Finset.sum_range_sub (fun k => (t l k : ℝ)), htT l, ht0 l,
          NNReal.coe_zero, sub_zero]
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg (fun _ => sq_nonneg _)), he]
  apply hb.trans_lt
  rw [← mul_div_assoc]
  apply (div_lt_iff₀ hT).mpr
  nlinarith

theorem posteriorBrownianDyadic_tendsto_L2 (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (T : ℝ≥0) :
    Tendsto (fun l => ∫ w, (posteriorBrownianSum W β ((brownianDyadicGrid T).time l) (2 ^ l) w -
      actualParisiMagnetizationObservable W β T w) ^ 2 ∂W.law) atTop (𝓝 0) := by
  apply posteriorBrownianSum_tendsto_L2 W β hβ ((brownianDyadicGrid T).time) (fun l => 2 ^ l) T
    (brownianDyadicGrid T).monotone (brownianDyadicGrid T).zero
    (fun l => by simp [brownianDyadicGrid]) (brownianDyadicWidth T) (brownianDyadicWidth_tendsto T)
  exact fun l k _ => brownianDyadicGrid_width_le T l k

end SKConstants.Completion.LJ
