module

public import SKConstants.Completion.Blueprint4.NodesSharp
public import SKConstants.BrownianMartingaleIdentification
public import SKConstants.Completion.LM3.RowScalarReduction

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace SKConstants.Completion.SJ3
open SKConstantsOAI.ZeroTemperatureSK Blueprint4
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]

theorem meanSquare_limit_unique {U : Type*} [MeasurableSpace U] {μ : Measure U}
    {S : ℕ → U → ℝ} {X Y : U → ℝ} (hm : ∀ l, Measurable (S l))
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    (hXi : ∀ l, Integrable (fun u => (S l u - X u) ^ 2) μ)
    (hXlim : Tendsto (fun l => ∫ u, (S l u - X u) ^ 2 ∂μ) atTop (𝓝 0))
    (hYlim : Tendsto (fun l => ∫ u, (S l u - Y u) ^ 2 ∂μ) atTop (𝓝 0)) :
    X =ᵐ[μ] Y := by
  have hS (l : ℕ) : MemLp (S l) 2 μ := by
    have he : MemLp (fun u => S l u - X u) 2 μ :=
      (memLp_two_iff_integrable_sq
        (((hm l).aemeasurable.sub hX.aemeasurable).aestronglyMeasurable)).mpr (hXi l)
    convert he.add hX using 1
    funext u
    simp only [Pi.add_apply, sub_add_cancel]
  exact (hX.toLp_eq_toLp_iff hY).mp
    (tendsto_nhds_unique (tendsto_toLp_of_meanSquare hS hX hXlim)
      (tendsto_toLp_of_meanSquare hS hY hYlim))

theorem measurable_jointRowLeftSum (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) (l : ℕ) :
    Measurable (jointRowLeftSum W Z β hβ V l) := by
  apply Finset.measurable_fun_sum
  intro k _
  apply Measurable.add
  · exact ((LJ.measurable_actualRowPotential W β _).comp measurable_fst |>.sub
      ((LJ.measurable_actualRowPotential W β _).comp measurable_fst)).const_mul _
  · exact (((measurable_of_finite scalarHiddenSign).comp (measurable_fst.comp measurable_fst)).sub
      ((measurable_actualParisiMagnetizationObservable W β _).comp
        (measurable_snd.comp measurable_fst)) |>.const_mul _).mul
      (((((actualParisiQueryBrownianSystem W Z β hβ).measurable _).sub
        ((actualParisiQueryBrownianSystem W Z β hβ).measurable _))).comp
          ((measurable_snd.comp measurable_fst).prodMk measurable_snd))

theorem rowLinked_absolutelyContinuous (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (V : ℝ≥0) :
    actualParisiFullQuerySpinLaw W Z β V ≪ LM4.actualRowBaseLaw W Z := by
  rw [← LM4.actual_linkedRowLaw_eq]
  exact LM4.linkedRowLaw_absolutelyContinuous _

theorem rowLinked_le_two (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (V : ℝ≥0) :
    actualParisiFullQuerySpinLaw W Z β V ≤ (2 : ℝ≥0∞) • LM4.actualRowBaseLaw W Z := by
  rw [← LM4.actual_linkedRowLaw_eq]
  exact LM4.linkedRowLaw_le_two (ae_of_all _ (fun u => (LM4.actualRowLink_bounds β W V u).2))

theorem memLp_rowLinked {p : ℝ≥0∞} (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (V : ℝ≥0) {f : (Bool × Ω) × A → ℝ}
    (hf : MemLp f p (LM4.actualRowBaseLaw W Z)) :
    MemLp f p (actualParisiFullQuerySpinLaw W Z β V) :=
  (hf.smul_measure (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).mono_measure (rowLinked_le_two W Z β V)

theorem jointRowIntegral_unique (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) {X Y : (Bool × Ω) × A → ℝ}
    (hX : IsJointRowIntegral W Z β hβ V X) (hY : IsJointRowIntegral W Z β hβ V Y) :
    X =ᵐ[LM4.actualRowBaseLaw W Z] Y :=
  meanSquare_limit_unique (measurable_jointRowLeftSum W Z β hβ V)
    hX.2.1 hY.2.1 hX.2.2.1 hX.2.2.2 hY.2.2.2

theorem jointRowIntegral_unique_linked (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) {X Y : (Bool × Ω) × A → ℝ}
    (hX : IsJointRowIntegral W Z β hβ V X) (hY : IsJointRowIntegral W Z β hβ V Y) :
    X =ᵐ[actualParisiFullQuerySpinLaw W Z β V] Y :=
  (rowLinked_absolutelyContinuous W Z β V).ae_eq (jointRowIntegral_unique W Z β hβ V hX hY)

theorem rowDIntegral_unique (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) {J K : (Bool × Ω) × A → ℝ}
    (hJ : LM4b.IsActualRowDIntegral W Z β hβ V J)
    (hK : LM4b.IsActualRowDIntegral W Z β hβ V K) :
    J =ᵐ[LM4.actualRowBaseLaw W Z] K :=
  meanSquare_limit_unique (LM4b.measurable_actualRowDLeftSum W Z β hβ V)
    hJ.1 hK.1 hJ.2.1 hJ.2.2 hK.2.2

theorem rowDIntegral_unique_linked (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) {J K : (Bool × Ω) × A → ℝ}
    (hJ : LM4b.IsActualRowDIntegral W Z β hβ V J)
    (hK : LM4b.IsActualRowDIntegral W Z β hβ V K) :
    J =ᵐ[actualParisiFullQuerySpinLaw W Z β V] K :=
  (rowLinked_absolutelyContinuous W Z β V).ae_eq (rowDIntegral_unique W Z β hβ V hJ hK)

theorem rowDLeftSum_eq_zero_pre (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) (hV : V ≤ parisiEquilibriumPhysicalEndpoint β)
    (l : ℕ) (u : (Bool × Ω) × A) : LM4b.actualRowDLeftSum W Z β hβ V l u = 0 := by
  apply Finset.sum_eq_zero
  intro k hk
  have ht : ((brownianDyadicGrid V).time l k : ℝ) ≤ parisiEquilibriumPhysicalEndpoint β := by
    exact_mod_cast (LM3.dyadic_time_le_horizon V l k (Finset.mem_range.mp hk).le).trans hV
  simp only [LM4b.actualRowDCoefficient, actualParisiQuerySigma_eq_zero_pre W β hβ _ ht,
    zero_mul]

omit [MeasurableSpace A] in
theorem rowDBracket_eq_zero_pre (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (V : ℝ≥0) (hV : V ≤ parisiEquilibriumPhysicalEndpoint β) (u : (Bool × Ω) × A) :
    LM4b.actualRowDBracket W β V u = 0 := by
  change (∫ t in (0 : ℝ)..(V : ℝ), (LM4b.actualRowDCoefficient W β t.toNNReal u) ^ 2) = 0
  rw [intervalIntegral.integral_of_le V.coe_nonneg]
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have hts : (t.toNNReal : ℝ) ≤ parisiEquilibriumPhysicalEndpoint β := by
    rw [Real.coe_toNNReal t ht.1.le]
    exact ht.2.trans (NNReal.coe_le_coe.mpr hV)
  simp only [LM4b.actualRowDCoefficient, actualParisiQuerySigma_eq_zero_pre W β hβ _ hts,
    zero_mul, zero_pow (by decide : 2 ≠ 0), Pi.zero_apply]

theorem rowDIntegral_zero_pre (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) (hV : V ≤ parisiEquilibriumPhysicalEndpoint β) :
    LM4b.IsActualRowDIntegral W Z β hβ V (fun _ => 0) := by
  refine ⟨MemLp.zero, ?_, ?_⟩
  · intro l
    simp only [rowDLeftSum_eq_zero_pre W Z β hβ V hV, sub_self, zero_pow (by decide : 2 ≠ 0)]
    simp
  · simp only [rowDLeftSum_eq_zero_pre W Z β hβ V hV, sub_self,
      zero_pow (by decide : 2 ≠ 0), integral_zero]
    exact tendsto_const_nhds

theorem rowInformationV_eq_log_pre (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) (hV : V ≤ parisiEquilibriumPhysicalEndpoint β)
    {J : (Bool × Ω) × A → ℝ} (hJ : LM4b.IsActualRowDIntegral W Z β hβ V J) :
    rowInformationV W β V J =ᵐ[actualParisiFullQuerySpinLaw W Z β V]
      (fun u => Real.log (actualParisiFullTerminalSpinDensity β W V u.1)) := by
  filter_upwards [rowDIntegral_unique_linked W Z β hβ V hJ (rowDIntegral_zero_pre W Z β hβ V hV)] with u hu
  simp only [rowInformationV, LM4.actualRowInformation, LM4.rowInformation, LM4.actualRowLink,
    rowDBracket_eq_zero_pre W β hβ V hV, hu, sub_zero, zero_div, add_zero]

end SKConstants.Completion.SJ3
