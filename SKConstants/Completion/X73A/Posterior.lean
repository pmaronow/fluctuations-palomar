module

public import SKConstants.Completion.S73.Node

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace SKConstants.Completion.X73A
open SKConstantsOAI.ZeroTemperatureSK
variable {Ω : Type} [MeasurableSpace Ω]

theorem memLp_of_abs_le (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → ℝ)
    (hf : Measurable f) (C : ℝ) (hC : ∀ w, |f w| ≤ C) (p : ℝ≥0∞) :
    MemLp f p μ :=
  (memLp_const C).mono' hf.aestronglyMeasurable
    (ae_of_all _ (fun w => by simpa only [Real.norm_eq_abs] using hC w))

theorem posteriorBrownianSum_initial_cross (W : BrownianSystem Ω) (β : ℝ)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (n : ℕ) :
    (∫ w, actualParisiMagnetizationObservable W β (t 0) w *
      LJ.posteriorBrownianSum W β t n w ∂W.law) = 0 := by
  let := W.isProbability
  have hM := memLp_of_abs_le W.law (actualParisiMagnetizationObservable W β (t 0))
    (measurable_actualParisiMagnetizationObservable W β _) 1
    (actualParisiMagnetizationObservable_abs_le W β _) 2
  have hi (k : ℕ) : Integrable (fun w => actualParisiMagnetizationObservable W β (t 0) w *
      (LJ.actualCurvature W β (t k) w * (W.B (t (k + 1)) w - W.B (t k) w))) W.law := by
    have hY := (LJ.posteriorBrownianSum_isometry W β
      (fun i => if i = 0 then t k else t (k + 1)) (by
        apply monotone_nat_of_le_succ
        intro i
        by_cases h : i = 0
        · simpa [h] using ht (Nat.le_succ k)
        · simp [h]) 1).1
    have hh := hM.integrable_mul hY
    change Integrable (fun w => actualParisiMagnetizationObservable W β (t 0) w *
      LJ.posteriorBrownianSum W β (fun i => if i = 0 then t k else t (k + 1)) 1 w) W.law at hh
    simpa only [LJ.posteriorBrownianSum, Finset.sum_range_one, ite_eq_left rfl,
      ite_eq_right Nat.one_ne_zero, ↓reduceIte, zero_add, Pi.mul_apply] using hh
  simp only [LJ.posteriorBrownianSum, Finset.mul_sum]
  rw [integral_finsetSum _ (fun k _ => hi k)]
  apply Finset.sum_eq_zero
  intro k _
  let F : ScalarContinuousPath (t k) → ℝ := fun p =>
    actualParisiPastMagnetization β (t 0)
      (scalarContinuousPathRestrict (t 0) (t k) (ht (Nat.zero_le k)) p) *
        LJ.curvatureFieldCoefficient β t k p
  have hF : Measurable F :=
    ((measurable_actualParisiPastMagnetization β _).comp
      (measurable_scalarContinuousPathRestrict _ _ _)).mul
        (LJ.measurable_curvatureFieldCoefficient β t k)
  have he : (fun w => F (boundedDriftPastPath W (actualParisiFullScalarDrift β) (t k) w))
      =ᵐ[W.law] (fun w => actualParisiMagnetizationObservable W β (t 0) w *
        LJ.actualCurvature W β (t k) w) := by
    filter_upwards [boundedDriftPastPath_restrict W (actualParisiFullScalarDrift β)
      (t 0) (t k) (ht (Nat.zero_le k)), actualParisiPastMagnetization_version W β (t 0),
      LJ.curvatureFieldCoefficient_actual W β t k] with w hr hm ha
    dsimp only [F]
    change LJ.curvatureFieldCoefficient β t k
      (boundedDriftPastPath W (actualParisiFullScalarDrift β) (t k) w) = _ at ha
    rw [hr, hm, ha]
  have hFi : Integrable (fun w => F
      (boundedDriftPastPath W (actualParisiFullScalarDrift β) (t k) w)) W.law := by
    apply Integrable.of_bound
      (hF.comp (measurable_boundedDriftPastPath W _ _)).aestronglyMeasurable 1
    filter_upwards [he] with w hw
    change ‖F (boundedDriftPastPath W (actualParisiFullScalarDrift β) (t k) w)‖ ≤ 1
    rw [hw, Real.norm_eq_abs, abs_mul]
    exact (mul_le_mul (actualParisiMagnetizationObservable_abs_le W β _ w)
      (LJ.actualCurvature_abs_le W β _ w) (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hz := S73.originalIncrement_integral_past_test W (actualParisiFullScalarDrift β)
    (t k) (t (k + 1)) (ht (Nat.le_succ k)) F hF hFi
  refine (integral_congr_ae ?_).trans hz
  filter_upwards [he] with w hw
  rw [hw]
  ring

theorem posteriorBrownianSum_error (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (n : ℕ) :
    (∫ w, (actualParisiMagnetizationIncrement W β (t 0) (t n) w -
      LJ.posteriorBrownianSum W β t n w) ^ 2 ∂W.law) =
      ∑ k ∈ Finset.range n, ∫ u in (t k : ℝ)..(t (k + 1) : ℝ), ∫ w,
        (LJ.actualCurvature W β (t k) w - LJ.actualCurvature W β u.toNNReal w) ^ 2 ∂W.law := by
  let := W.isProbability
  let X := actualParisiMagnetizationIncrement W β (t 0) (t n)
  let Y := LJ.posteriorBrownianSum W β t n
  have hX : MemLp X 2 W.law :=
    (S73.posteriorIncrement_hasSubgaussianMGF W β hβ _ _ (ht (Nat.zero_le n))).memLp 2
  have hY : MemLp Y 2 W.law := (LJ.posteriorBrownianSum_isometry W β t ht n).1
  have hMt := memLp_of_abs_le W.law (actualParisiMagnetizationObservable W β (t n))
    (measurable_actualParisiMagnetizationObservable W β _) 1
    (actualParisiMagnetizationObservable_abs_le W β _) 2
  have hMs := memLp_of_abs_le W.law (actualParisiMagnetizationObservable W β (t 0))
    (measurable_actualParisiMagnetizationObservable W β _) 1
    (actualParisiMagnetizationObservable_abs_le W β _) 2
  have hcross : (∫ w, X w * Y w ∂W.law) =
      ∑ k ∈ Finset.range n, ∫ u in (t k : ℝ)..(t (k + 1) : ℝ), ∫ w,
        LJ.actualCurvature W β (t k) w * LJ.actualCurvature W β u.toNNReal w ∂W.law := by
    change (∫ w, (actualParisiMagnetizationObservable W β (t n) w -
      actualParisiMagnetizationObservable W β (t 0) w) * Y w ∂W.law) = _
    simp_rw [sub_mul]
    have hi := integral_sub (hMt.integrable_mul hY) (hMs.integrable_mul hY)
    simp only [Pi.mul_apply] at hi
    rw [hi,
      posteriorBrownianSum_initial_cross W β t ht n, sub_zero]
    exact LJ.posteriorBrownianSum_terminal_cross W β hβ t ht n
  have hX2 : (∫ w, X w ^ 2 ∂W.law) =
      ∑ k ∈ Finset.range n, ∫ u in (t k : ℝ)..(t (k + 1) : ℝ),
        actualParisiFullSusceptibilitySquareExpected W β u := by
    rw [(actualParisiIncrement_secondMoment W β hβ _ _ (ht (Nat.zero_le n))).trans
      (actualParisiFullSusceptibilitySquareExpected_interval W β hβ _ _
        (ht (Nat.zero_le n))).symm]
    exact (intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
      (f := actualParisiFullSusceptibilitySquareExpected W β) (a := fun k => (t k : ℝ))
      (n := n) (fun k _ =>
        (continuous_actualParisiFullSusceptibilitySquareExpected W β).intervalIntegrable _ _)).symm
  have he (w : Ω) : (X w - Y w) ^ 2 = X w ^ 2 + Y w ^ 2 - 2 * (X w * Y w) := by ring
  change (∫ w, (X w - Y w) ^ 2 ∂W.law) = _
  simp_rw [he]
  have hsub := integral_sub (hX.integrable_sq.add hY.integrable_sq)
    ((hX.integrable_mul hY).const_mul 2)
  have hadd := integral_add hX.integrable_sq hY.integrable_sq
  simp only [Pi.add_apply, Pi.mul_apply] at hsub hadd
  rw [hsub, hadd, integral_const_mul, hcross, hX2,
    (LJ.posteriorBrownianSum_isometry W β t ht n).2,
    Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  have hr := (continuous_actualParisiFullSusceptibilitySquareExpected W β).intervalIntegrable (μ := volume)
    (t k : ℝ) (t (k + 1) : ℝ)
  have hc := (LJ.continuous_actualCurvature_pair W β (t k)).intervalIntegrable (μ := volume)
    (t k : ℝ) (t (k + 1) : ℝ)
  rw [show ((t (k + 1) : ℝ) - t k) *
      actualParisiFullSusceptibilitySquareExpected W β (t k) =
      ∫ _ in (t k : ℝ)..(t (k + 1) : ℝ),
        actualParisiFullSusceptibilitySquareExpected W β (t k) by
          rw [intervalIntegral.integral_const, smul_eq_mul]]
  rw [← intervalIntegral.integral_add hr intervalIntegrable_const,
    ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_sub (hr.add intervalIntegrable_const) (hc.const_mul 2)]
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le (NNReal.coe_le_coe.mpr (ht (Nat.le_succ k)))] at hu
  dsimp only
  rw [LJ.actualCurvature_difference_sq, Real.coe_toNNReal u ((t k).coe_nonneg.trans hu.1)]
  ring

attribute [local irreducible] LJ.actualCurvature LJ.posteriorBrownianSum
  actualParisiMagnetizationObservable actualParisiFullCurvature

theorem posteriorBrownianSum_tendsto_L2 (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℕ → ℝ≥0) (n : ℕ → ℕ) (s T : ℝ≥0)
    (ht : ∀ l, Monotone (t l)) (ht0 : ∀ l, t l 0 = s) (htT : ∀ l, t l (n l) = T)
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (hmesh : ∀ l k, k < n l → ((t l (k + 1) : ℝ) - t l k) ≤ δ l) :
    Tendsto (fun l => ∫ w, (LJ.posteriorBrownianSum W β (t l) (n l) w -
      actualParisiMagnetizationIncrement W β s T w) ^ 2 ∂W.law) atTop (𝓝 0) := by
  let := W.isProbability
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hT : 0 < (T : ℝ) + 1 := by positivity
  obtain ⟨η, hη, hsmall⟩ := expected_sq_difference_uniform_small_of_bounded W.law
    (LJ.actualCurvature W β) (fun s => (LJ.measurable_actualCurvature W β s).aestronglyMeasurable)
    (LJ.actualCurvature_continuous_ae W β) 1
    (fun s w => by rw [Real.norm_eq_abs]; exact LJ.actualCurvature_abs_le W β s w)
    T (ε / ((T : ℝ) + 1)) (div_pos hε hT)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hδ.eventually (eventually_lt_nhds hη))
  refine ⟨N, fun l hl => ?_⟩
  have he : (∫ w, (LJ.posteriorBrownianSum W β (t l) (n l) w -
      actualParisiMagnetizationIncrement W β s T w) ^ 2 ∂W.law) =
      ∑ k ∈ Finset.range (n l), ∫ u in (t l k : ℝ)..(t l (k + 1) : ℝ), ∫ w,
        (LJ.actualCurvature W β (t l k) w - LJ.actualCurvature W β u.toNNReal w) ^ 2 ∂W.law := by
    rw [← ht0 l, ← htT l]
    simp_rw [sub_sq_comm (LJ.posteriorBrownianSum W β (t l) (n l) _) _]
    exact posteriorBrownianSum_error W β hβ (t l) (ht l) (n l)
  have hb : (∑ k ∈ Finset.range (n l), ∫ u in (t l k : ℝ)..(t l (k + 1) : ℝ), ∫ w,
      (LJ.actualCurvature W β (t l k) w - LJ.actualCurvature W β u.toNNReal w) ^ 2 ∂W.law) ≤
      (T : ℝ) * (ε / ((T : ℝ) + 1)) := by
    calc
      _ ≤ ∑ k ∈ Finset.range (n l),
          ((t l (k + 1) : ℝ) - t l k) * (ε / ((T : ℝ) + 1)) := by
        apply Finset.sum_le_sum
        intro k hk
        have hkn := Finset.mem_range.mp hk
        have hst : (t l k : ℝ) ≤ t l (k + 1) := NNReal.coe_le_coe.mpr (ht l (Nat.le_succ k))
        have hc : Continuous (fun u : ℝ => ∫ w,
            (LJ.actualCurvature W β (t l k) w - LJ.actualCurvature W β u.toNNReal w) ^ 2 ∂W.law) :=
          (LJ.continuous_actualCurvature_difference_sq W β).comp
            (continuous_const.prodMk continuous_real_toNNReal)
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
      _ ≤ (T : ℝ) * (ε / ((T : ℝ) + 1)) := by
        rw [← Finset.sum_mul, Finset.sum_range_sub (fun k => (t l k : ℝ)), htT l, ht0 l]
        exact mul_le_mul_of_nonneg_right (sub_le_self _ s.coe_nonneg) (by positivity)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg (fun _ => sq_nonneg _)), he]
  apply hb.trans_lt
  rw [← mul_div_assoc]
  apply (div_lt_iff₀ hT).mpr
  nlinarith

theorem posteriorBrownianRefined_tendsto_L2 (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (j : ℕ) :
    Tendsto (fun l => ∫ w, (LJ.posteriorBrownianSum W β
      (Blueprint5a.refinedGrid δ l j) (2 ^ l) w -
        actualParisiMagnetizationIncrement W β (Blueprint5a.mesh δ j)
          (Blueprint5a.mesh δ (j + 1)) w) ^ 2 ∂W.law) atTop (𝓝 0) := by
  apply posteriorBrownianSum_tendsto_L2 W β hβ (fun l => Blueprint5a.refinedGrid δ l j)
    (fun l => 2 ^ l) _ _ (fun l => LJ3.growingLagDyadicTime_monotone δ l j)
    (fun l => LJ3.growingLagDyadicTime_zero δ l j)
    (fun l => LJ3.growingLagDyadicTime_end δ l j)
    (brownianDyadicWidth (growingQueryDuration δ j)) (brownianDyadicWidth_tendsto _)
  intro l k _
  simpa only [Blueprint5a.refinedGrid, LJ3.growingLagDyadicTime, scalarBrownianDyadicTime,
    brownianDyadicGrid, NNReal.coe_add, add_sub_add_left_eq_sub] using brownianDyadicGrid_width_le
      (growingQueryDuration δ j) l k

theorem memLp_bounded_mul {μ : Measure Ω} {p : ℝ≥0∞} {g : Ω → ℝ}
    (hg : MemLp g p μ) (f : Ω → ℝ) (hf : Measurable f) (C : ℝ)
    (hC : ∀ w, |f w| ≤ C) : MemLp (fun w => f w * g w) p μ := by
  apply hg.of_le_mul (c := C) (hf.aestronglyMeasurable.mul hg.aestronglyMeasurable)
  exact ae_of_all _ (fun w => by
    change ‖f w * g w‖ ≤ C * ‖g w‖
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hC w) (norm_nonneg _))

theorem posteriorBrownianSum_tested_isometry (W : BrownianSystem Ω) (β : ℝ)
    (t : ℕ → ℝ≥0) (ht : Monotone t)
    (s : ℝ≥0) (hst : s ≤ t 0)
    (F : ScalarContinuousPath s → ℝ) (hF : Measurable F)
    (C : ℝ≥0) (hC : ∀ p, |F p| ≤ C) (n : ℕ) :
    (∫ w, (F (boundedDriftPastPath W (actualParisiFullScalarDrift β) s w) *
      LJ.posteriorBrownianSum W β t n w) ^ 2 ∂W.law) =
      ∑ k ∈ Finset.range n, ((t (k + 1) : ℝ) - t k) * ∫ w,
        F (boundedDriftPastPath W (actualParisiFullScalarDrift β) s w) ^ 2 *
          LJ.actualCurvature W β (t k) w ^ 2 ∂W.law := by
  let := W.isProbability
  let b := actualParisiFullScalarDrift β
  let H : LJ.OriginalFieldCoefficient t := fun k p =>
    F (scalarContinuousPathRestrict s (t k) (hst.trans (ht (Nat.zero_le k))) p) *
      LJ.curvatureFieldCoefficient β t k p
  have hH (k : ℕ) : Measurable (H k) :=
    (hF.comp (measurable_scalarContinuousPathRestrict _ _ _)).mul
      (LJ.measurable_curvatureFieldCoefficient β t k)
  have hb (k : ℕ) (p : ScalarContinuousPath (t k)) : |H k p| ≤ C := by
    dsimp only [H]
    rw [abs_mul]
    exact (mul_le_mul (hC _) (actualParisiFullCurvature_abs_le_one β _ _)
      (abs_nonneg _) C.coe_nonneg).trans_eq (mul_one _)
  have hHsq (k : ℕ) : Integrable (fun w =>
      LJ.originalFieldCoefficient W b t H k w ^ 2) W.law := by
    apply Integrable.of_bound
      (((LJ.measurable_originalFieldCoefficient W b t H hH k).pow_const 2).aestronglyMeasurable)
      ((C : ℝ) ^ 2)
    apply ae_of_all
    intro w
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hb k _) 2
  have he (k : ℕ) : LJ.originalFieldCoefficient W b t H k =ᵐ[W.law]
      (fun w => F (boundedDriftPastPath W b s w) * LJ.actualCurvature W β (t k) w) := by
    filter_upwards [boundedDriftPastPath_restrict W b s (t k) (hst.trans (ht (Nat.zero_le k))),
      LJ.curvatureFieldCoefficient_actual W β t k] with w hr ha
    change LJ.curvatureFieldCoefficient β t k (boundedDriftPastPath W b (t k) w) = _ at ha
    change F (scalarContinuousPathRestrict _ _ _ (boundedDriftPastPath W b (t k) w)) *
      LJ.curvatureFieldCoefficient β t k (boundedDriftPastPath W b (t k) w) = _
    rw [hr, ha]
  have hsum : LJ.originalFieldSum W b t H n =ᵐ[W.law]
      (fun w => F (boundedDriftPastPath W b s w) * LJ.posteriorBrownianSum W β t n w) := by
    filter_upwards [ae_all_iff.mpr he] with w hw
    rw [LJ.originalFieldSum, predictableGaussianSum_eq_range_sum]
    simp only [hw, brownianMeshIncrement, LJ.posteriorBrownianSum, Finset.mul_sum, mul_assoc]
  have hi := (LJ.originalFieldSum_isometry W b t ht H hH hHsq n).2.2
  rw [integral_congr_ae (hsum.mono (fun w hw => congrArg (fun x : ℝ => x ^ 2) hw))] at hi
  rw [Fin.sum_univ_eq_sum_range (fun k => (brownianMeshVariance t k : ℝ) *
    ∫ w, LJ.originalFieldCoefficient W b t H k w ^ 2 ∂W.law)] at hi
  refine hi.trans ?_
  apply Finset.sum_congr rfl
  intro k _
  rw [brownianMeshVariance, NNReal.coe_sub (ht (Nat.le_succ k))]
  congr 1
  apply integral_congr_ae
  filter_upwards [he k] with w hw
  rw [hw, mul_pow]

theorem meanSquare_bounded_mul {μ : Measure Ω} {X : ℕ → Ω → ℝ} {Y : Ω → ℝ}
    (hX : ∀ l, MemLp (X l) 2 μ) (hY : MemLp Y 2 μ)
    (hlim : Tendsto (fun l => ∫ w, (X l w - Y w) ^ 2 ∂μ) atTop (𝓝 0))
    (f : Ω → ℝ) (hf : Measurable f) (C : ℝ≥0) (hC : ∀ w, |f w| ≤ C) :
    Tendsto (fun l => ∫ w, (f w * X l w - f w * Y w) ^ 2 ∂μ) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => integral_nonneg (fun _ => sq_nonneg _))
    (fun l => ?_) (by simpa using hlim.const_mul ((C : ℝ) ^ 2))
  have hprod := memLp_bounded_mul ((hX l).sub hY) f hf C hC
  have hi := integral_mono hprod.integrable_sq (((hX l).sub hY).integrable_sq.const_mul
    ((C : ℝ) ^ 2)) (fun w => ?_)
  · simpa only [mul_sub, Pi.sub_apply, integral_const_mul] using hi
  · change (f w * (X l w - Y w)) ^ 2 ≤ (C : ℝ) ^ 2 * (X l w - Y w) ^ 2
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right
      (by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (f w)) (hC w) 2)
      (sq_nonneg _)

theorem shifted_left_riemann_tendsto (f : ℝ → ℝ) (hf : Continuous f) (s v : ℝ≥0) :
    Tendsto (fun l => ∑ k ∈ Finset.range (2 ^ l),
      f (s + (brownianDyadicGrid v).time l k) *
        (((s + (brownianDyadicGrid v).time l (k + 1) : ℝ≥0) : ℝ) -
          (s + (brownianDyadicGrid v).time l k : ℝ≥0))) atTop
      (𝓝 (∫ r in (s : ℝ)..((s + v : ℝ≥0) : ℝ), f r)) := by
  have h := SJ7.frozen_integral_dyadic_tendsto
    (fun r => f ((s : ℝ) + r)) (fun _ => (1 : ℝ))
    (hf.comp (continuous_const.add continuous_id)) continuous_const v
    (fun _ _ => by norm_num)
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one,
    intervalIntegral.integral_comp_add_left, add_zero] at h
  simpa only [NNReal.coe_add, add_sub_add_left_eq_sub] using h

theorem continuous_tested_curvature_sq (W : BrownianSystem Ω) (β : ℝ)
    (f : Ω → ℝ) (hf : Measurable f) (C : ℝ≥0) (hC : ∀ w, |f w| ≤ C) :
    Continuous (fun r : ℝ => ∫ w, f w ^ 2 * LJ.actualCurvature W β r.toNNReal w ^ 2 ∂W.law) := by
  let := W.isProbability
  apply continuous_of_dominated (bound := fun _ => (C : ℝ) ^ 2)
  · intro r
    exact ((hf.pow_const 2).mul ((LJ.measurable_actualCurvature W β _).pow_const 2)).aestronglyMeasurable
  · intro r
    exact ae_of_all _ (fun w => by
      rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_pow]
      exact (mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (hC w) 2)
        (pow_le_pow_left₀ (abs_nonneg _) (LJ.actualCurvature_abs_le W β _ w) 2)
        (by positivity) (by positivity)).trans_eq (by ring))
  · exact integrable_const _
  · filter_upwards [LJ.actualCurvature_continuous_ae W β] with w hw
    exact continuous_const.mul ((hw.comp continuous_real_toNNReal).pow 2)

theorem posteriorIncrement_tested_square (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (s v : ℝ≥0) (F : ScalarContinuousPath s → ℝ) (hF : Measurable F)
    (C : ℝ≥0) (hC : ∀ p, |F p| ≤ C) :
    (∫ w, (F (boundedDriftPastPath W (actualParisiFullScalarDrift β) s w) *
      actualParisiMagnetizationIncrement W β s (s + v) w) ^ 2 ∂W.law) =
      ∫ r in (s : ℝ)..((s + v : ℝ≥0) : ℝ), ∫ w,
        F (boundedDriftPastPath W (actualParisiFullScalarDrift β) s w) ^ 2 *
          LJ.actualCurvature W β r.toNNReal w ^ 2 ∂W.law := by
  let := W.isProbability
  let t : ℕ → ℕ → ℝ≥0 := fun l k => s + (brownianDyadicGrid v).time l k
  have ht (l : ℕ) : Monotone (t l) := monotone_const.add ((brownianDyadicGrid v).monotone l)
  have ht0 (l : ℕ) : t l 0 = s := by simp [t, brownianDyadicGrid]
  have htT (l : ℕ) : t l (2 ^ l) = s + v := by simp [t, brownianDyadicGrid]
  let f : Ω → ℝ := fun w => F (boundedDriftPastPath W (actualParisiFullScalarDrift β) s w)
  have hf : Measurable f := hF.comp (measurable_boundedDriftPastPath W _ s)
  have hfC (w : Ω) : |f w| ≤ C := hC _
  let X := fun l => LJ.posteriorBrownianSum W β (t l) (2 ^ l)
  let Y := actualParisiMagnetizationIncrement W β s (s + v)
  have hX (l : ℕ) : MemLp (X l) 2 W.law := (LJ.posteriorBrownianSum_isometry W β _ (ht l) _).1
  have hY : MemLp Y 2 W.law := memLp_of_abs_le W.law Y
    (measurable_actualParisiMagnetizationIncrement W β _ _) 2
    (actualParisiMagnetizationIncrement_abs_le W β _ _) 2
  have hlim : Tendsto (fun l => ∫ w, (X l w - Y w) ^ 2 ∂W.law) atTop (𝓝 0) := by
    apply posteriorBrownianSum_tendsto_L2 W β hβ t (fun l => 2 ^ l) s (s + v) ht ht0 htT
      (brownianDyadicWidth v) (brownianDyadicWidth_tendsto v)
    intro l k _
    simpa only [t, NNReal.coe_add, add_sub_add_left_eq_sub] using brownianDyadicGrid_width_le v l k
  have hs := integral_sq_tendsto_of_meanSquare
    (fun l => memLp_bounded_mul (hX l) f hf C hfC)
    (memLp_bounded_mul hY f hf C hfC) (meanSquare_bounded_mul hX hY hlim f hf C hfC)
  have he (l : ℕ) : (∫ w, (f w * X l w) ^ 2 ∂W.law) =
      ∑ k ∈ Finset.range (2 ^ l), ((t l (k + 1) : ℝ) - t l k) * ∫ w,
        f w ^ 2 * LJ.actualCurvature W β (t l k) w ^ 2 ∂W.law :=
    posteriorBrownianSum_tested_isometry W β (t l) (ht l) s (by rw [ht0]) F hF C hC _
  simp_rw [he] at hs
  have hr := shifted_left_riemann_tendsto
    (fun r => ∫ w, f w ^ 2 * LJ.actualCurvature W β r.toNNReal w ^ 2 ∂W.law)
    (continuous_tested_curvature_sq W β f hf C hfC) s v
  apply tendsto_nhds_unique hs
  simpa only [t, ← NNReal.coe_add, Real.toNNReal_coe, mul_comm] using hr

theorem posteriorIncrement_secondMoment_past_test (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (s v : ℝ≥0) (F : ScalarContinuousPath s → ℝ) (hF : Measurable F)
    (C : ℝ≥0) (hC : ∀ p, |F p| ≤ C) :
    (∫ w, F (boundedDriftPastPath W (actualParisiFullScalarDrift β) s w) *
      actualParisiMagnetizationIncrement W β s (s + v) w ^ 2 ∂W.law) =
      ∫ r in (s : ℝ)..((s + v : ℝ≥0) : ℝ), ∫ w,
        F (boundedDriftPastPath W (actualParisiFullScalarDrift β) s w) *
          LJ.actualCurvature W β r.toNNReal w ^ 2 ∂W.law := by
  let := W.isProbability
  let f := fun w => F (boundedDriftPastPath W (actualParisiFullScalarDrift β) s w)
  let Y := actualParisiMagnetizationIncrement W β s (s + v)
  have hf : Measurable f := hF.comp (measurable_boundedDriftPastPath W _ _)
  have hfC (w : Ω) : |f w| ≤ C := hC _
  have hplus (p) : |F p + 1| ≤ (C + 1 : ℝ≥0) := by
    have hh := abs_add_le (F p) (1 : ℝ)
    simp only [abs_one, NNReal.coe_add, NNReal.coe_one] at *
    linarith [hC p]
  have hminus (p) : |F p - 1| ≤ (C + 1 : ℝ≥0) := by
    have hh := abs_sub (F p) (1 : ℝ)
    simp only [abs_one, NNReal.coe_add, NNReal.coe_one] at *
    linarith [hC p]
  have hp := posteriorIncrement_tested_square W β hβ s v (fun p => F p + 1)
    (hF.add_const 1) (C + 1) hplus
  have hm := posteriorIncrement_tested_square W β hβ s v (fun p => F p - 1)
    (hF.sub_const 1) (C + 1) hminus
  have hY : MemLp Y 2 W.law := memLp_of_abs_le W.law Y
    (measurable_actualParisiMagnetizationIncrement W β _ _) 2
    (actualParisiMagnetizationIncrement_abs_le W β _ _) 2
  have hPi := (memLp_bounded_mul hY (fun w => f w + 1) (hf.add_const 1)
    (C + 1 : ℝ≥0) (fun w => hplus _)).integrable_sq
  have hMi := (memLp_bounded_mul hY (fun w => f w - 1) (hf.sub_const 1)
    (C + 1 : ℝ≥0) (fun w => hminus _)).integrable_sq
  have hleft : 4 * (∫ w, f w * Y w ^ 2 ∂W.law) =
      (∫ w, ((f w + 1) * Y w) ^ 2 ∂W.law) -
        ∫ w, ((f w - 1) * Y w) ^ 2 ∂W.law := by
    rw [← integral_sub hPi hMi, ← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ (fun w => by ring)
  have hright (r : ℝ) :
      (∫ w, (f w + 1) ^ 2 * LJ.actualCurvature W β r.toNNReal w ^ 2 ∂W.law) -
        (∫ w, (f w - 1) ^ 2 * LJ.actualCurvature W β r.toNNReal w ^ 2 ∂W.law) =
          4 * ∫ w, f w * LJ.actualCurvature W β r.toNNReal w ^ 2 ∂W.law := by
    have ha : MemLp (LJ.actualCurvature W β r.toNNReal) 2 W.law :=
      memLp_of_abs_le W.law _ (LJ.measurable_actualCurvature W β _) 1
        (LJ.actualCurvature_abs_le W β _) 2
    have hpp := (memLp_bounded_mul ha (fun w => f w + 1) (hf.add_const 1)
      (C + 1 : ℝ≥0) (fun w => hplus _)).integrable_sq
    have hmm := (memLp_bounded_mul ha (fun w => f w - 1) (hf.sub_const 1)
      (C + 1 : ℝ≥0) (fun w => hminus _)).integrable_sq
    simp only [mul_pow] at hpp hmm
    rw [← integral_sub hpp hmm, ← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ (fun w => by ring)
  have hpc := continuous_tested_curvature_sq W β (fun w => f w + 1)
    (hf.add_const 1) (C + 1) (fun _ => hplus _)
  have hmc := continuous_tested_curvature_sq W β (fun w => f w - 1)
    (hf.sub_const 1) (C + 1) (fun _ => hminus _)
  have heq : 4 * (∫ w, f w * Y w ^ 2 ∂W.law) =
      4 * ∫ r in (s : ℝ)..((s + v : ℝ≥0) : ℝ), ∫ w,
        f w * LJ.actualCurvature W β r.toNNReal w ^ 2 ∂W.law := by
    rw [hleft]
    change (∫ w, ((F (boundedDriftPastPath W (actualParisiFullScalarDrift β) s w) + 1) *
      actualParisiMagnetizationIncrement W β s (s + v) w) ^ 2 ∂W.law) -
      (∫ w, ((F (boundedDriftPastPath W (actualParisiFullScalarDrift β) s w) - 1) *
      actualParisiMagnetizationIncrement W β s (s + v) w) ^ 2 ∂W.law) = _
    rw [hp, hm, ← intervalIntegral.integral_sub
      (hpc.intervalIntegrable _ _) (hmc.intervalIntegrable _ _)]
    simp_rw [hright]
    rw [intervalIntegral.integral_const_mul]
  change (∫ w, f w * Y w ^ 2 ∂W.law) = _
  linarith

end SKConstants.Completion.X73A
