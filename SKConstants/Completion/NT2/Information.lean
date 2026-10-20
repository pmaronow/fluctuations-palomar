module

public import SKConstants.Completion.NT2.Energy

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology

namespace SKConstants.Completion.NT2
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal Blueprint Blueprint4 N13A LGram LC4a LM3 N13t

variable {Ω : Type} [MeasurableSpace Ω]

theorem isL2Limit_sum_comp {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {N : ℕ} (R : Fin N → X → Y)
    (hR : ∀ i, HasLaw (R i) ν μ) (hRm : ∀ i, Measurable (R i))
    {S : ℕ → Y → ℝ} {J : Y → ℝ} (hJ : IsL2Limit ν S J)
    (hSm : ∀ l, Measurable (S l)) :
    IsL2Limit μ (fun l x => ∑ i, S l (R i x)) (fun x => ∑ i, J (R i x)) := by
  have hE (l : ℕ) : MemLp (fun y => S l y - J y) 2 ν :=
    (memLp_two_iff_integrable_sq
      (((hSm l).sub hJ.1).aemeasurable.aestronglyMeasurable)).mpr (hJ.2.2.1 l)
  have hPull (i : Fin N) (l : ℕ) := (hR i).memLp_fun_comp (hE l)
  have hMean (i : Fin N) (l : ℕ) :
      (∫ x, (S l (R i x) - J (R i x)) ^ 2 ∂μ) = ∫ y, (S l y - J y) ^ 2 ∂ν :=
    (hR i).integral_comp (hJ.2.2.1 l).aestronglyMeasurable
  have hlim (i : Fin N) :
      Tendsto (fun l => ∫ x, (S l (R i x) - J (R i x)) ^ 2 ∂μ) atTop (𝓝 0) := by
    simp_rw [hMean]
    exact hJ.2.2.2
  refine ⟨Finset.measurable_fun_sum _ (fun i _ => hJ.1.comp (hRm i)),
    memLp_finsetSum Finset.univ (fun i _ => (hR i).memLp_fun_comp hJ.2.1), ?_, ?_⟩
  · intro l
    simp_rw [← Finset.sum_sub_distrib]
    exact integrable_sq_finset_sum Finset.univ
      (fun i _ => (hPull i l).aemeasurable) (fun i _ => (hPull i l).integrable_sq)
  · simp_rw [← Finset.sum_sub_distrib]
    exact tendsto_integral_sq_finset_sum Finset.univ
      (fun i _ l => (hPull i l).aemeasurable) (fun i _ l => (hPull i l).integrable_sq)
      (fun i _ => hlim i)

theorem sharpDLeftSum_eq_history_sum (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n l : ℕ) (y : SharpInput p n) :
    sharpDLeftSum W β hβ p n l y =
      ∑ i, fullHistoryDLeftSum W β (coarseTime p n) l (sharpHistories W β hβ p n y i) := by
  unfold sharpDLeftSum
  apply Finset.sum_congr rfl
  intro i _
  simp only [fullHistoryDLeftSum, Function.comp_apply, historyDLeftSum,
    predictableGaussianSum_eq_fin_sum, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k _
  rfl

def sharpHistoryIntegral (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (J : ObservationDHistory (coarseTime p n) → ℝ)
    (y : SharpInput p n) : ℝ :=
  ∑ i, J (observationDProjection (coarseTime p n) (sharpHistories W β hβ p n y i))

theorem isSharpDIntegral_historySum (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (hn : 0 < n)
    (J : ObservationDHistory (coarseTime p n) → ℝ) (hJm : Measurable J)
    (hJ : IsHistoryDIntegral W β hβ (coarseTime p n) J) :
    IsSharpDIntegral W β hβ p n (sharpHistoryIntegral W β hβ p n J) := by
  let V := coarseTime p n
  have hproj : HasLaw (observationDProjection V)
      (unlinkedObservationDHistoryLaw W β hβ V) (fullHistoryBaseLaw W W β hβ V) := by
    refine ⟨(measurable_observationDProjection V).aemeasurable, ?_⟩
    rw [fullHistoryBaseLaw, Measure.map_map (measurable_observationDProjection V)
      (measurable_modelFullHistory W W β hβ V), modelFullHistory_observationD]
    rfl
  have hfull : IsL2Limit (fullHistoryBaseLaw W W β hβ V) (fullHistoryDLeftSum W β V)
      (J ∘ observationDProjection V) :=
    (show IsL2Limit (unlinkedObservationDHistoryLaw W β hβ V) (historyDLeftSum W β V) J
      from ⟨hJm, hJ⟩).comp_hasLaw hproj (measurable_observationDProjection V)
  have hrows := sharpHistories_unlinked_hasLaw W β hβ p n hn
  have hlim := isL2Limit_sum_comp
    (fun i y => sharpHistories W β hβ p n y i)
    (fun i => (measurePreserving_eval (fun _ : Fin n => fullHistoryBaseLaw W W β hβ V) i).hasLaw.comp hrows)
    (fun i => (measurable_pi_apply i).comp (measurable_sharpHistories W β hβ p n))
    hfull (measurable_fullHistoryDLeftSum W β V)
  exact hlim.congr_sums (fun l => Eventually.of_forall fun y =>
    (sharpDLeftSum_eq_history_sum W β hβ p n l y).symm)

theorem sharpField_eq_history (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (t : ℝ≥0) (y : SharpInput p n) (i : Fin n) :
    sharpField W β hβ p n t y i =
      historyPathAt (coarseTime p n) (sharpHistories W β hβ p n y i).2.1 t := rfl

theorem sharpHistories_spin (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (y : SharpInput p n) (i : Fin n) :
    (sharpHistories W β hβ p n y i).1 = y.1 i := by
  simp only [sharpHistories, M1.ReplayHistories, T0.sharpToReplay,
    Fin.cast_cast, Fin.cast_refl, id_eq]

theorem sharpLink_eq_history_product (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (y : SharpInput p n) :
    sharpLink W β hβ p n y =
      ∏ i, historyLinkDensity β (coarseTime p n)
        (observationDProjection (coarseTime p n) (sharpHistories W β hβ p n y i)) := by
  apply Finset.prod_congr rfl
  intro i _
  change actualParisiSpinLinkDensity β (y.1 i) (coarseTime p n)
      (sharpField W β hβ p n (coarseTime p n) y i) =
    actualParisiSpinLinkDensity β (sharpHistories W β hβ p n y i).1 (coarseTime p n)
      ((sharpHistories W β hβ p n y i).2.1 ⟨coarseTime p n, (coarseTime p n).coe_nonneg, le_rfl⟩)
  rw [sharpHistories_spin, sharpField_eq_history, historyPathAt, projIcc_right]

theorem sharpDBracket_eq_history_sum (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (y : SharpInput p n) :
    sharpDBracket W β hβ p n y =
      ∑ i, fullHistoryDBracket W β (coarseTime p n) (sharpHistories W β hβ p n y i) := by
  unfold sharpDBracket
  apply Finset.sum_congr rfl
  intro i _
  change (∫ t in (0 : ℝ)..(coarseTime p n : ℝ), sharpDCoefficient W β hβ p n t.toNNReal y i ^ 2) =
    ∫ t in (0 : ℝ)..(coarseTime p n : ℝ),
      historyDCoefficient W β (coarseTime p n) t
        (observationDProjection (coarseTime p n) (sharpHistories W β hβ p n y i)) ^ 2
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le (coarseTime p n).coe_nonneg] at ht
  dsimp only [sharpDCoefficient, historyDCoefficient, observationDProjection]
  rw [sharpField_eq_history, sharpHistories_spin, Real.coe_toNNReal t ht.1]

theorem sharpInformation_historySum (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (J : ObservationDHistory (coarseTime p n) → ℝ)
    (y : SharpInput p n) :
    sharpInformation W β hβ p n (sharpHistoryIntegral W β hβ p n J) y =
      ∑ i, fullHistoryInformation W β (coarseTime p n)
        (J ∘ observationDProjection (coarseTime p n)) (sharpHistories W β hβ p n y i) := by
  have hp (i : Fin n) : historyLinkDensity β (coarseTime p n)
      (observationDProjection (coarseTime p n) (sharpHistories W β hβ p n y i)) ≠ 0 :=
    (actualParisiSpinLinkDensity_pos β _ _ _).ne'
  rw [sharpInformation, sharpLink_eq_history_product, Real.log_prod (fun i _ => hp i),
    sharpDBracket_eq_history_sum]
  simp only [sharpHistoryIntegral, fullHistoryInformation, Function.comp_apply,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_div]

theorem sharpInformation_eq_history_sum_ae
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (p : Parameters)
    (n : ℕ) (hn : 0 < n) (I : SharpInput p n → ℝ)
    (hI : IsSharpDIntegral W β hβ p n I)
    (J : ObservationDHistory (coarseTime p n) → ℝ) (hJm : Measurable J)
    (hJ : IsHistoryDIntegral W β hβ (coarseTime p n) J) :
    sharpInformation W β hβ p n I =ᵐ[sharpLinkedLaw W β hβ p n]
      fun y => ∑ i, fullHistoryInformation W β (coarseTime p n)
        (J ∘ observationDProjection (coarseTime p n)) (sharpHistories W β hβ p n y i) := by
  have hac : sharpLinkedLaw W β hβ p n ≪ sharpUnlinkedLaw W p n :=
    withDensity_absolutelyContinuous _ _
  have he := hac.ae_le (T0.isSharpDIntegral_unique W β hβ p n I _ hI
    (isSharpDIntegral_historySum W β hβ p n hn J hJm hJ))
  filter_upwards [he] with y hy
  change Real.log (sharpLink W β hβ p n y) - I y + sharpDBracket W β hβ p n y / 2 = _
  rw [hy]
  exact sharpInformation_historySum W β hβ p n J y

theorem sharpInformation_sub_linearEnergy_identDistrib
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (p : Parameters)
    (n : ℕ) (hn : 0 < n) (I : SharpInput p n → ℝ)
    (hI : IsSharpDIntegral W β hβ p n I)
    (J : ObservationDHistory (coarseTime p n) → ℝ) (hJm : Measurable J)
    (hJ : IsHistoryDIntegral W β hβ (coarseTime p n) J) :
    IdentDistrib
      (fun y => sharpInformation W β hβ p n I y / n -
        β * linearEnergy W β hβ (sharpRows W β hβ p n y))
      (fun ω : Fin n → (Bool × Ω) × Ω =>
        (∑ i, (rowInformationV W β (coarseTime p n)
            (J ∘ modelObservationDHistory W β hβ (coarseTime p n)) (ω i) -
          β * LJ.actualFiniteRow W W β hβ (growingQueryTime (coarseMesh p n))
            (coarseCount p n) (ω i))) / n)
      (sharpLinkedLaw W β hβ p n)
      (Measure.pi fun _ : Fin n => actualParisiFullQuerySpinLaw W W β (coarseTime p n)) := by
  let V := coarseTime p n
  let Jf := J ∘ observationDProjection V
  let S : (Fin n → M1.ScalarDriverHistory V) → ℝ := fun a =>
    (∑ i, (fullHistoryInformation W β V Jf (a i) -
      β * finiteHistoryRow W β V (growingQueryTime (coarseMesh p n)) (coarseCount p n) (a i))) / n
  let T : (Fin n → (Bool × Ω) × Ω) → Fin n → M1.ScalarDriverHistory V :=
    fun ω i => modelFullHistory W W β hβ V (ω i)
  have hSm : Measurable S :=
    (Finset.measurable_fun_sum _ fun i _ =>
      ((measurable_fullHistoryInformation W β V Jf
        (hJm.comp (measurable_observationDProjection V))).sub
        ((measurable_finiteHistoryRow W β V (growingQueryTime (coarseMesh p n))
          (coarseCount p n)).const_mul β)).comp (measurable_pi_apply i)).div_const _
  have hTm : Measurable T := Measurable.of_eval fun i =>
    (measurable_modelFullHistory W W β hβ V).comp (measurable_pi_apply i)
  have hrep : (S ∘ sharpHistories W β hβ p n) =ᵐ[sharpLinkedLaw W β hβ p n]
      fun y => sharpInformation W β hβ p n I y / n -
        β * linearEnergy W β hβ (sharpRows W β hβ p n y) := by
    filter_upwards [sharpInformation_eq_history_sum_ae W β hβ p n hn I hI J hJm hJ,
      linearEnergy_eq_finiteRowAverage_ae W β hβ p n hn] with y hi he
    dsimp only [Function.comp_apply, S]
    rw [hi, he, Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  have hrow : ∀ᵐ ω ∂Measure.pi (fun _ : Fin n => actualParisiFullQuerySpinLaw W W β V),
      ∀ i, fullHistoryInformation W β V Jf (T ω i) =
        rowInformationV W β V (J ∘ modelObservationDHistory W β hβ V) (ω i) ∧
      finiteHistoryRow W β V (growingQueryTime (coarseMesh p n)) (coarseCount p n) (T ω i) =
        LJ.actualFiniteRow W W β hβ (growingQueryTime (coarseMesh p n)) (coarseCount p n) (ω i) := by
    rw [ae_all_iff]
    intro i
    exact (Measure.quasiMeasurePreserving_eval
      (fun _ : Fin n => actualParisiFullQuerySpinLaw W W β V) i).ae
      ((fullHistoryInformation_model_ae W W β hβ V Jf).and
        ((actualRowLinked_absolutelyContinuous W W β V).ae_le
          (finiteHistoryRow_model_ae W W β hβ V (growingQueryTime (coarseMesh p n))
            (growingQueryTime_strictMono _ (paperGrowingQueryMeshSize_pos p.a n hn)).monotone
            (coarseCount p n) le_rfl)))
  have hmodel : (S ∘ T) =ᵐ[Measure.pi (fun _ : Fin n => actualParisiFullQuerySpinLaw W W β V)]
      fun ω => (∑ i, (rowInformationV W β V
          (J ∘ modelObservationDHistory W β hβ V) (ω i) -
        β * LJ.actualFiniteRow W W β hβ (growingQueryTime (coarseMesh p n))
          (coarseCount p n) (ω i))) / n := by
    filter_upwards [hrow] with ω hω
    apply congrArg (fun x : ℝ => x / n)
    exact Finset.sum_congr rfl fun i _ => by rw [(hω i).1, (hω i).2]
  exact (IdentDistrib.of_ae_eq
    (hSm.comp (measurable_sharpHistories W β hβ p n)).aemeasurable hrep).symm.trans
      ((((sharpHistories_linked_hasLaw W β hβ p n hn).identDistrib
        (modelFullHistories_linked_hasLaw W W β hβ V n)).comp hSm).trans
          (IdentDistrib.of_ae_eq (hSm.comp hTm).aemeasurable hmodel))

end SKConstants.Completion.NT2
