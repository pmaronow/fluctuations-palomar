module

public import SKConstants.Completion.X33C.OriginalPartitions
public import SKConstants.Completion.S33aA.Node
public import SKConstants.BrownianQuadraticVariation

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace SKConstants.Completion.X33C
open SKConstantsOAI.ZeroTemperatureSK
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
local instance likelihood_W_probability (W : BrownianSystem Ω) : IsProbabilityMeasure W.law := W.isProbability
local instance likelihood_Z_probability (Z : BrownianSystem A) : IsProbabilityMeasure Z.law := Z.isProbability
attribute [local irreducible] actualParisiFullScalarDrift actualParisiFullMagnetization

theorem inMeasure_of_eventual_meanSquare {U : Type*} [MeasurableSpace U]
    {μ : Measure U} [IsFiniteMeasure μ] {F : ℕ → U → ℝ} {X : U → ℝ}
    (hi : ∀ᶠ l in atTop, Integrable (fun u => (F l u - X u) ^ 2) μ)
    (hl : Tendsto (fun l => ∫ u, (F l u - X u) ^ 2 ∂μ) atTop (𝓝 0)) :
    TendstoInMeasure μ F atTop X := by
  obtain ⟨L, hL⟩ := eventually_atTop.mp hi
  have hh := tendstoInMeasure_of_tendsto_integral_sq
    (fun l => hL (l + L) (by omega)) (hl.comp (tendsto_add_atTop_nat L))
  intro ε hε
  exact (tendsto_add_atTop_iff_nat L).mp (hh ε hε)

theorem inMeasure_const_mul {U : Type*} [MeasurableSpace U] {μ : Measure U} [IsFiniteMeasure μ]
    {F : ℕ → U → ℝ} {X : U → ℝ} (hF : TendstoInMeasure μ F atTop X) (c : ℝ) :
    TendstoInMeasure μ (fun l u => c * F l u) atTop (fun u => c * X u) := by
  rw [tendstoInMeasure_iff_measureReal_norm] at hF ⊢
  intro ε hε
  by_cases hc : c = 0
  · simp only [hc, zero_mul, sub_self, norm_zero, not_le.mpr hε, ofPred_false, measureReal_empty]
    exact tendsto_const_nhds
  have hc0 : 0 < |c| := abs_pos.mpr hc
  convert hF (ε / |c|) (div_pos hε hc0) using 1
  funext l
  congr 1
  ext u
  change ε ≤ ‖c * F l u - c * X u‖ ↔ ε / |c| ≤ ‖F l u - X u‖
  rw [← mul_sub, norm_mul, Real.norm_eq_abs, mul_comm |c|, ← div_le_iff₀ hc0]

theorem inMeasure_constant {U : Type*} [MeasurableSpace U] {μ : Measure U}
    (X : U → ℝ) : TendstoInMeasure μ (fun _ : ℕ => X) atTop X := by
  intro ε hε
  simp only [edist_self, not_le.mpr hε, ofPred_false, measure_empty]
  exact tendsto_const_nhds

theorem dyadicVariance_coe (T : ℝ≥0) (l k : ℕ) :
    (brownianMeshVariance ((brownianDyadicGrid T).time l) k : ℝ) = brownianDyadicWidth T l := by
  rw [brownianMeshVariance, NNReal.coe_sub ((brownianDyadicGrid T).monotone l (Nat.le_succ k))]
  simp only [brownianDyadicGrid_time_coe, brownianDyadicWidth, Nat.cast_succ]
  ring

theorem dyadicLogCoshBudget_eq (T : ℝ≥0) (l : ℕ) :
    12 * (∑ k ∈ Finset.range (2 ^ l),
        (brownianMeshVariance ((brownianDyadicGrid T).time l) k : ℝ) ^ 2) +
      18 * (∑ k ∈ Finset.range (2 ^ l),
        (brownianMeshVariance ((brownianDyadicGrid T).time l) k : ℝ) *
          Real.sqrt (brownianMeshVariance ((brownianDyadicGrid T).time l) k : ℝ)) ^ 2 =
    (12 * (T : ℝ) + 18 * (T : ℝ) ^ 2) * brownianDyadicWidth T l := by
  simp_rw [dyadicVariance_coe]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
  have hw : (2 : ℝ) ^ l * brownianDyadicWidth T l = T := by
    unfold brownianDyadicWidth
    field_simp
  have hs := Real.sq_sqrt (show 0 ≤ brownianDyadicWidth T l by unfold brownianDyadicWidth; positivity)
  calc
    _ = 12 * ((2 : ℝ) ^ l * brownianDyadicWidth T l) * brownianDyadicWidth T l +
        18 * (((2 : ℝ) ^ l * brownianDyadicWidth T l) ^ 2 *
          Real.sqrt (brownianDyadicWidth T l) ^ 2) := by ring
    _ = _ := by rw [hw, hs]; ring

theorem postDyadicLogCoshError_tendstoInMeasure
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β) (T : ℝ≥0) :
    TendstoInMeasure (LM4.actualRowBaseLaw W Z)
      (fun l u => S33aA.postLogCoshError W β ((brownianDyadicGrid T).time l) (2 ^ l) u.1.2)
      atTop (fun _ => 0) := by
  have hwidth : ∀ᶠ l in atTop, ∀ k,
      brownianMeshVariance ((brownianDyadicGrid T).time l) k ≤ 1 := by
    filter_upwards [(brownianDyadicWidth_tendsto T).eventually
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))] with l hl
    intro k
    apply NNReal.coe_le_coe.mp
    simpa only [dyadicVariance_coe, NNReal.coe_one] using hl.le
  have hb : ∀ᶠ l in atTop,
      Integrable (fun u : (Bool × Ω) × A =>
        S33aA.postLogCoshError W β ((brownianDyadicGrid T).time l) (2 ^ l) u.1.2 ^ 2)
          (LM4.actualRowBaseLaw W Z) ∧
      (∫ u : (Bool × Ω) × A,
        S33aA.postLogCoshError W β ((brownianDyadicGrid T).time l) (2 ^ l) u.1.2 ^ 2
          ∂LM4.actualRowBaseLaw W Z) ≤
        (12 * (T : ℝ) + 18 * (T : ℝ) ^ 2) * brownianDyadicWidth T l := by
    filter_upwards [hwidth] with l hl
    obtain ⟨hi, hb⟩ := S33aA.postLogCoshError_bound W β hβ T
      ((brownianDyadicGrid T).time l) ((brownianDyadicGrid T).monotone l)
      ((brownianDyadicGrid T).zero l) (2 ^ l) (by simp [brownianDyadicGrid]) hl
    rw [dyadicLogCoshBudget_eq] at hb
    refine ⟨(hi.comp_snd (scalarHiddenPriorBool 0)).comp_fst Z.law, ?_⟩
    have he := (S33aB.row_projection_measurePreserving W Z).hasLaw.integral_comp hi.aestronglyMeasurable
    exact he.trans_le hb
  apply inMeasure_of_eventual_meanSquare (by simpa only [sub_zero] using hb.mono (fun _ h => h.1))
  simp only [sub_zero]
  apply squeeze_zero' (Eventually.of_forall (fun l => integral_nonneg (fun _ => sq_nonneg _)))
    (hb.mono (fun _ h => h.2))
  simpa using (brownianDyadicWidth_tendsto T).const_mul (12 * (T : ℝ) + 18 * (T : ℝ) ^ 2)

def postDefectBracketSum (W : BrownianSystem Ω) (β : ℝ) (T : ℝ≥0) (l : ℕ)
    (u : (Bool × Ω) × A) : ℝ :=
  ∑ k ∈ Finset.range (2 ^ l),
    actualParisiPinningError W β
      (parisiEquilibriumPhysicalEndpoint β + (brownianDyadicGrid T).time l k) u.1 *
      (brownianMeshVariance ((brownianDyadicGrid T).time l) k : ℝ)

def postDefectBracket (W : BrownianSystem Ω) (β : ℝ) (T : ℝ≥0)
    (u : (Bool × Ω) × A) : ℝ :=
  ∫ t in (parisiEquilibriumPhysicalEndpoint β : ℝ)..
      (parisiEquilibriumPhysicalEndpoint β + T : ℝ≥0),
    actualParisiPinningError W β t.toNNReal u.1

theorem measurable_postDefectBracketSum (W : BrownianSystem Ω) (β : ℝ) (T : ℝ≥0) (l : ℕ) :
    Measurable (postDefectBracketSum (A := A) W β T l) := by
  apply Finset.measurable_fun_sum
  intro k _
  exact ((measurable_actualParisiPinningError W β _).comp measurable_fst).mul_const _

theorem postDefectBracketSum_tendsto_ae
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (T : ℝ≥0) :
    ∀ᵐ u ∂LM4.actualRowBaseLaw W Z,
      Tendsto (fun l => postDefectBracketSum W β T l u) atTop (𝓝 (postDefectBracket W β T u)) := by
  filter_upwards [(S33aB.row_projection_measurePreserving W Z).quasiMeasurePreserving.ae
    (S33aB.posterior_continuous_ae W β)] with u hu
  let S := parisiEquilibriumPhysicalEndpoint β
  let f : ℝ → ℝ := fun t => actualParisiPinningError W β (S + t.toNNReal) u.1
  have hc : Continuous f :=
    (continuous_const.sub (hu.comp (continuous_const.add continuous_real_toNNReal))).pow 2
  have h := continuous_left_quadrature_tendsto f hc T (brownianDyadicGrid T) 1
    (by simp) (brownianDyadicWidth T) (brownianDyadicWidth_tendsto T)
    (fun l i _ => brownianDyadicGrid_width_le T l i)
  have he : (∫ t in (0 : ℝ)..(T : ℝ), f t) = postDefectBracket W β T u := by
    have hh := intervalIntegral.integral_comp_add_left
      (fun t : ℝ => actualParisiPinningError W β t.toNNReal u.1) (a := 0) (b := T) (S : ℝ)
    rw [add_zero] at hh
    change (∫ t in (0 : ℝ)..(T : ℝ), f t) =
      ∫ t in (S : ℝ)..((S : ℝ) + T), actualParisiPinningError W β t.toNNReal u.1
    rw [← hh]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le T.coe_nonneg] at ht
    simp only [f, Real.toNNReal_add (by positivity : (0 : ℝ) ≤ S) ht.1,
      Real.toNNReal_coe]
  simpa only [Nat.one_mul, f, Real.toNNReal_coe, he, postDefectBracketSum, S] using h

theorem postDefectBracketSum_tendstoInMeasure
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (T : ℝ≥0) :
    TendstoInMeasure (LM4.actualRowBaseLaw W Z) (postDefectBracketSum W β T) atTop
      (postDefectBracket W β T) :=
  tendstoInMeasure_of_tendsto_ae
    (fun l => (measurable_postDefectBracketSum W β T l).aestronglyMeasurable)
    (postDefectBracketSum_tendsto_ae W Z β T)

def postOriginalSum (W : BrownianSystem Ω) (β : ℝ) (T : ℝ≥0) (l : ℕ)
    (u : (Bool × Ω) × A) : ℝ :=
  originalPartitionSum W β (fun k =>
    parisiEquilibriumPhysicalEndpoint β + (brownianDyadicGrid T).time l k) (2 ^ l) u

def postLogLikelihood (W : BrownianSystem Ω) (β : ℝ) (T : ℝ≥0)
    (u : (Bool × Ω) × A) : ℝ :=
  Real.log (actualParisiFullTerminalSpinDensity β W
    (parisiEquilibriumPhysicalEndpoint β + T) u.1) -
      Real.log (actualParisiFullTerminalSpinDensity β W (parisiEquilibriumPhysicalEndpoint β) u.1)

omit [MeasurableSpace A] in
theorem postOriginalSum_logLikelihood_error (W : BrownianSystem Ω) (β : ℝ)
    (hβ : 1 < β) (T : ℝ≥0) (l : ℕ) (u : (Bool × Ω) × A) :
    postOriginalSum W β T l u -
        (postLogLikelihood W β T u + postDefectBracketSum W β T l u / 2) =
      S33aA.postLogCoshError W β ((brownianDyadicGrid T).time l) (2 ^ l) u.1.2 -
        S33aB.driftDyadicSum W β (parisiEquilibriumPhysicalEndpoint β) T l u := by
  let S := parisiEquilibriumPhysicalEndpoint β
  let t := (brownianDyadicGrid T).time l
  have he := S33aA.postSignedEulerSum_log_error_eq W β hβ t (2 ^ l) u.1.1 u.1.2
  have htend : t (2 ^ l) = T := by simp [t, brownianDyadicGrid]
  have ht0 : t 0 = 0 := by simp [t, brownianDyadicGrid]
  rw [htend, ht0, add_zero] at he
  have heuler : postOriginalSum W β T l u + S33aB.driftDyadicSum W β S T l u -
      postDefectBracketSum W β T l u / 2 =
        S33aA.postSignedEulerSum W β t (2 ^ l) u.1.1 u.1.2 := by
    unfold postOriginalSum originalPartitionSum S71.Mesh.partitionSum S33aB.driftDyadicSum
      postDefectBracketSum S33aA.postSignedEulerSum
    rw [← Finset.sum_add_distrib, Finset.sum_div, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    have hpost (j : ℕ) : S ≤ S + t j := le_add_of_nonneg_right (by positivity)
    have hv : (brownianMeshVariance t k : ℝ) =
        ((S + t (k + 1) : ℝ≥0) : ℝ) - (S + t k : ℝ≥0) := by
      rw [brownianMeshVariance, NNReal.coe_sub ((brownianDyadicGrid T).monotone l (Nat.le_succ k))]
      simp only [NNReal.coe_add]
      ring
    change _ = (scalarHiddenSign u.1.1 - Real.tanh (actualParisiFullScalarProcess W β (S + t k) u.1.2)) *
      scalarInnovation (actualParisiFullScalarProcess W β (S + t k) u.1.2)
        (brownianMeshVariance t k) (actualParisiFullScalarProcess W β (S + t (k + 1)) u.1.2) -
      (brownianMeshVariance t k : ℝ) / 2 *
        (scalarHiddenSign u.1.1 - Real.tanh (actualParisiFullScalarProcess W β (S + t k) u.1.2)) ^ 2
    dsimp only [S33aB.driftError, actualParisiPinningError, scalarInnovation]
    rw [S33aB.posterior_eq_tanh W β hβ (S + t k) (hpost k)]
    rw [← hv]
    ring
  change S33aA.postSignedEulerSum W β t (2 ^ l) u.1.1 u.1.2 - postLogLikelihood W β T u = _ at he
  rw [← heuler] at he
  change _ = S33aA.postLogCoshError W β t (2 ^ l) u.1.2 - _
  linarith only [he]

attribute [local irreducible] postOriginalSum postLogLikelihood postDefectBracket postDefectBracketSum

theorem postOriginalSum_likelihood_tendstoInMeasure
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β) (T : ℝ≥0) :
    TendstoInMeasure (LM4.actualRowBaseLaw W Z) (postOriginalSum W β T) atTop
      (fun u => postLogLikelihood W β T u + postDefectBracket W β T u / 2) := by
  have he := postDyadicLogCoshError_tendstoInMeasure W Z β hβ T
  obtain ⟨hi, hl⟩ := S33aB.driftDyadicSum_tendsto_L2_base W Z β hβ
    (parisiEquilibriumPhysicalEndpoint β) T le_rfl
  have hd : TendstoInMeasure (LM4.actualRowBaseLaw W Z)
      (S33aB.driftDyadicSum W β (parisiEquilibriumPhysicalEndpoint β) T) atTop (fun _ => 0) :=
    tendstoInMeasure_of_tendsto_integral_sq
    (by simpa only [sub_zero] using hi) (by simpa only [sub_zero] using hl)
  have hb := inMeasure_const_mul (postDefectBracketSum_tendstoInMeasure W Z β T) (1 / 2 : ℝ)
  have h := inMeasure_add
    (inMeasure_add (inMeasure_sub he hd) hb) (inMeasure_constant (postLogLikelihood (A := A) W β T))
  apply h.congr (fun l => ae_of_all _ (fun u => ?_)) (ae_of_all _ (fun u => ?_))
  · have hh := postOriginalSum_logLikelihood_error W β hβ T l u
    linarith only [hh]
  · ring

end SKConstants.Completion.X33C
