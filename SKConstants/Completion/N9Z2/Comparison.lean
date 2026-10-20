module

public import SKConstants.Completion.N9c.RowStatistics
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology

namespace SKConstants.Completion.N9Z2
open SKConstantsOAI.ZeroTemperatureSK M1 LFine N9 N9c

theorem correctionIter_mono_of_driver {Ξ : Type*} [mΞ : MeasurableSpace Ξ]
    (b : BoundedLipschitzDrift) (hb : ∀ t : ℝ, Monotone (b.f t))
    (ℱ : Filtration ℝ≥0 mΞ) (B : ℝ≥0 → Ξ → ℝ) (hB : IsProgressive ℱ B)
    (x y : Ξ) (hxy : ∀ t, B t x ≤ B t y) (k : ℕ) (t : ℝ≥0) :
    b.correctionIter B k t x ≤ b.correctionIter B k t y := by
  induction k generalizing t with
  | zero => exact le_rfl
  | succ k ih =>
    exact intervalIntegral.integral_mono t.coe_nonneg
      (progressive_bounded_integrable ℱ
        (b.action_progressive ℱ hB (b.correctionIter_progressive ℱ hB k))
        (b.action_bound _ _) x 0 t)
      (progressive_bounded_integrable ℱ
        (b.action_progressive ℱ hB (b.correctionIter_progressive ℱ hB k))
        (b.action_bound _ _) y 0 t)
      (fun s => hb _ (add_le_add (hxy _) (ih _)))

theorem solution_mono_of_driver {Ξ : Type*} [mΞ : MeasurableSpace Ξ]
    (b : BoundedLipschitzDrift) (hb : ∀ t : ℝ, Monotone (b.f t))
    (ℱ : Filtration ℝ≥0 mΞ) (B : ℝ≥0 → Ξ → ℝ) (hB : IsProgressive ℱ B)
    (x y : Ξ) (hxy : ∀ t, B t x ≤ B t y) (t : ℝ≥0) :
    b.solution B t x ≤ b.solution B t y := by
  apply add_le_add (hxy t)
  exact le_of_tendsto_of_tendsto (b.correctionIter_tendsto ℱ hB t x)
    (b.correctionIter_tendsto ℱ hB t y)
    (Eventually.of_forall fun k => correctionIter_mono_of_driver b hb ℱ B hB x y hxy k t)

theorem scalarForwardPicardPath_mono (b : BoundedLipschitzDrift)
    (hb : ∀ t : ℝ, Monotone (b.f t)) (T : ℝ≥0)
    (p q : ℝ × ScalarContinuousPath T) (hz : p.1 ≤ q.1)
    (hpq : ∀ t, p.2 t ≤ q.2 t) (t : Icc (0 : ℝ) (T : ℝ)) :
    scalarForwardPicardPath b T p t ≤ scalarForwardPicardPath b T q t :=
  solution_mono_of_driver b hb (scalarPathFiltration T) (scalarContinuousSeedDriver T)
    (scalarContinuousSeedDriver_progressive T) p q
    (fun _ => add_le_add hz (hpq _)) ⟨t,t.property.1⟩

theorem scalarStieltjesWeightedPath_antitone_of_nonpos
    (f : StieltjesFunction ℝ) (hf : Continuous f) (hf0 : ∀ t, f t ≤ 0)
    (T : ℝ≥0) (B C : ScalarContinuousPath T) (hBC : ∀ t, B t ≤ C t)
    (t : Icc (0 : ℝ) (T : ℝ)) :
    scalarStieltjesWeightedPath f hf T C t ≤ scalarStieltjesWeightedPath f hf T B t := by
  have hi (p : ScalarContinuousPath T) :
      IntervalIntegrable (IccExtend T.coe_nonneg p) f.measure 0 t :=
    (p.continuous.Icc_extend'.continuousOn.integrableOn_compact isCompact_uIcc).intervalIntegrable
  have hint := intervalIntegral.integral_mono t.property.1 (hi B) (hi C)
    (fun s => hBC (projIcc 0 (T : ℝ) T.coe_nonneg s))
  have hmul := mul_le_mul_of_nonpos_left (hBC t) (hf0 t)
  change f t*C t - _ ≤ f t*B t - _
  linarith

theorem scalarTwoDriverPicardPath_mono_first (b : BoundedLipschitzDrift)
    (hb : ∀ t : ℝ, Monotone (b.f t)) (f g : StieltjesFunction ℝ)
    (hf : Continuous f) (hg : Continuous g) (hf0 : ∀ t, f t ≤ 0)
    (T : ℝ≥0) (z : ℝ) (B C D : ScalarContinuousPath T)
    (hBC : ∀ t, B t ≤ C t) (t : Icc (0 : ℝ) (T : ℝ)) :
    scalarTwoDriverPicardPath b f g hf hg T (z,(B,D)) t ≤
      scalarTwoDriverPicardPath b f g hf hg T (z,(C,D)) t := by
  unfold scalarTwoDriverPicardPath
  apply scalarForwardPicardPath_mono b hb T
    (z,scalarTwoDriverWeightedPath f g hf hg T (B,D))
    (z,scalarTwoDriverWeightedPath f g hf hg T (C,D)) le_rfl _ t
  intro s
  change -scalarStieltjesWeightedPath f hf T B s + _ ≤
    -scalarStieltjesWeightedPath f hf T C s + _
  linarith [scalarStieltjesWeightedPath_antitone_of_nonpos f hf hf0 T B C hBC s]

theorem actualParisiFullMagnetization_monotone (β t : ℝ) :
    Monotone (actualParisiFullMagnetization β t) :=
  monotone_of_hasDerivAt_nonneg (actualParisiFullMagnetization_hasDerivAt β t)
    (fun x => (actualParisiFullMagnetization_curvature_bounds β t x).2.1)

theorem actualParisiFullScalarDrift_monotone (β t : ℝ) :
    Monotone ((actualParisiFullScalarDrift β).f t) := by
  intro x y hxy
  exact mul_le_mul_of_nonneg_left (actualParisiFullMagnetization_monotone β t hxy)
    (cdf_nonneg _ _)

theorem scalarConcatPath_zero (a h : ℝ≥0)
    (p : ScalarContinuousPath a × ScalarContinuousPath h) :
    scalarConcatPath a h p ⟨0,le_rfl,(a+h).coe_nonneg⟩ =
      p.1 ⟨0,le_rfl,a.coe_nonneg⟩ := by
  simp only [scalarConcatPath, ContinuousMap.coe_mk, projIcc_left,
    zero_sub, projIcc_of_le_left h.coe_nonneg (neg_nonpos.mpr a.coe_nonneg)]
  ring

theorem scalarConcatPath_mono_left (a h : ℝ≥0)
    (B C : ScalarContinuousPath a) (D : ScalarContinuousPath h)
    (hBC : ∀ t, B t ≤ C t) (t : Icc (0 : ℝ) ((a+h : ℝ≥0) : ℝ)) :
    scalarConcatPath a h (B,D) t ≤ scalarConcatPath a h (C,D) t := by
  change B _ + D _ - D _ ≤ C _ + D _ - D _
  linarith [hBC (projIcc 0 (a : ℝ) a.coe_nonneg t)]

theorem scalarConcatPath_mono_right (a h : ℝ≥0)
    (B : ScalarContinuousPath a) (C D : ScalarContinuousPath h)
    (hCD : ∀ t, C t ≤ D t)
    (h0 : C ⟨0,le_rfl,h.coe_nonneg⟩ = D ⟨0,le_rfl,h.coe_nonneg⟩)
    (t : Icc (0 : ℝ) ((a+h : ℝ≥0) : ℝ)) :
    scalarConcatPath a h (B,C) t ≤ scalarConcatPath a h (B,D) t := by
  change B _ + C _ - C _ ≤ B _ + D _ - D _
  rw [h0]
  linarith [hCD (projIcc 0 (h : ℝ) h.coe_nonneg ((t : ℝ)-a))]

theorem scalarQueryBridgeComplete_endpoint_mono (h : ℝ≥0)
    (c : ScalarContinuousPath h) (x y : ℝ) (hxy : x ≤ y)
    (t : Icc (0 : ℝ) (h : ℝ)) :
    scalarQueryBridgeComplete h (x,c) t ≤ scalarQueryBridgeComplete h (y,c) t := by
  change scalarPinnedBridge h c t + (t : ℝ)/(h : ℝ)*(Real.sqrt h*x) ≤
    scalarPinnedBridge h c t + (t : ℝ)/(h : ℝ)*(Real.sqrt h*y)
  have hm := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hxy (Real.sqrt_nonneg (h : ℝ)))
      (div_nonneg t.property.1 h.coe_nonneg)
  linarith

theorem freshRowDrivers_endpoint_mono (a h f : ℝ≥0)
    (B D : ScalarContinuousPath a) (s : FreshRowSeed h f)
    (x y : ℝ) (hxy : x ≤ y)
    (t : Icc (0 : ℝ) ((a+(h+f) : ℝ≥0) : ℝ)) :
    (freshRowDrivers a h f B D (x,s)).1 t ≤
      (freshRowDrivers a h f B D (y,s)).1 t := by
  apply scalarConcatPath_mono_right
  · exact scalarConcatPath_mono_left h f _ _ s.2.1
      (scalarQueryBridgeComplete_endpoint_mono h s.1 x y hxy)
  · rw [scalarConcatPath_zero, scalarConcatPath_zero,
      scalarQueryBridgeComplete_zero, scalarQueryBridgeComplete_zero]

theorem freshRowTerminalField_endpoint_monotone {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (a h f : ℝ≥0)
    (B D : ScalarContinuousPath a) (s : FreshRowSeed h f) :
    Monotone (fun x : ℝ => freshRowTerminalField W β hβ a h f B D (x,s)) := by
  intro x y hxy
  exact scalarTwoDriverPicardPath_mono_first (actualParisiFullScalarDrift β)
    (actualParisiFullScalarDrift_monotone β)
    (actualParisiNegativeRhoStieltjes W β hβ) (actualParisiSigmaStieltjes W β hβ)
    (continuous_actualParisiNegativeRhoStieltjes W β hβ)
    (continuous_actualParisiSigmaStieltjes W β hβ)
    (fun t => neg_nonpos.mpr (actualParisiQueryRho_bounds W β hβ t).1)
    (a+(h+f)) 0 _ _ _ (freshRowDrivers_endpoint_mono a h f B D s x y hxy) _

theorem freshRowSign_endpoint_monotone {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (a h f : ℝ≥0)
    (B D : ScalarContinuousPath a) (s : FreshRowSeed h f) :
    Monotone (fun x : ℝ =>
      if freshRowSign W β hβ a h f B D (x,s) then (1 : ℝ) else -1) := by
  intro x y hxy
  have hm := actualParisiFullMagnetization_monotone β (a+(h+f))
    (freshRowTerminalField_endpoint_monotone W β hβ a h f B D s hxy)
  dsimp only at hm
  simp only [freshRowSign]
  split_ifs <;> norm_num at *
  linarith

end SKConstants.Completion.N9Z2
