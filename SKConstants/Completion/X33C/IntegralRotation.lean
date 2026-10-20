module

public import SKConstants.Completion.S33aA.ActualRotation
public import SKConstants.Completion.S33aB.Node
public import SKConstants.ScalarProcessRowMGFLimit

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace SKConstants.Completion.X33C
open SKConstantsOAI.ZeroTemperatureSK
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
local instance rotation_W_probability (W : BrownianSystem Ω) : IsProbabilityMeasure W.law := W.isProbability
local instance rotation_Z_probability (Z : BrownianSystem A) : IsProbabilityMeasure Z.law := Z.isProbability

theorem inMeasure_add {U : Type*} [MeasurableSpace U] {μ : Measure U} [IsFiniteMeasure μ]
    {F G : ℕ → U → ℝ} {X Y : U → ℝ}
    (hF : TendstoInMeasure μ F atTop X) (hG : TendstoInMeasure μ G atTop Y) :
    TendstoInMeasure μ (fun l u => F l u + G l u) atTop (fun u => X u + Y u) := by
  rw [tendstoInMeasure_iff_measureReal_norm] at hF hG ⊢
  intro ε hε
  apply squeeze_zero (fun _ => measureReal_nonneg) (fun l => ?_)
    (by simpa using (hF (ε / 2) (half_pos hε)).add (hG (ε / 2) (half_pos hε)))
  apply (measureReal_mono (show {u | ε ≤ ‖F l u + G l u - (X u + Y u)‖} ⊆
      {u | ε / 2 ≤ ‖F l u - X u‖} ∪ {u | ε / 2 ≤ ‖G l u - Y u‖} from ?_)).trans
    (measureReal_union_le _ _)
  intro u hu
  by_contra hh
  simp only [mem_union, mem_ofPred_eq, not_or, not_le] at hh
  have ht := norm_add_le (F l u - X u) (G l u - Y u)
  have he : F l u + G l u - (X u + Y u) = (F l u - X u) + (G l u - Y u) := by ring
  change ε ≤ ‖F l u + G l u - (X u + Y u)‖ at hu
  rw [he] at hu
  linarith

theorem inMeasure_neg {U : Type*} [MeasurableSpace U] {μ : Measure U}
    {F : ℕ → U → ℝ} {X : U → ℝ} (hF : TendstoInMeasure μ F atTop X) :
    TendstoInMeasure μ (fun l u => -F l u) atTop (fun u => -X u) := by
  rw [tendstoInMeasure_iff_norm] at hF ⊢
  simpa only [neg_sub_neg, norm_sub_rev] using hF

theorem inMeasure_sub {U : Type*} [MeasurableSpace U] {μ : Measure U} [IsFiniteMeasure μ]
    {F G : ℕ → U → ℝ} {X Y : U → ℝ}
    (hF : TendstoInMeasure μ F atTop X) (hG : TendstoInMeasure μ G atTop Y) :
    TendstoInMeasure μ (fun l u => F l u - G l u) atTop (fun u => X u - Y u) := by
  simpa only [sub_eq_add_neg] using inMeasure_add hF (inMeasure_neg hG)

theorem measurable_originalRowLeftSum (W : BrownianSystem Ω) (β : ℝ) (V : ℝ≥0) (l : ℕ) :
    Measurable (S33aA.originalRowLeftSum (A := A) W β V l) := by
  apply Finset.measurable_fun_sum
  intro k _
  exact (((measurable_of_finite scalarHiddenSign).comp (measurable_fst.comp measurable_fst)).sub
    ((measurable_actualParisiFullPosteriorMean W β _).comp (measurable_snd.comp measurable_fst))).mul
    (((W.measurable _).sub (W.measurable _)).comp (measurable_snd.comp measurable_fst))

theorem actualRotationLeftSumError_tendstoInMeasure
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) :
    TendstoInMeasure (LM4.actualRowBaseLaw W Z)
      (S33aA.actualRotationLeftSumError W Z β hβ V) atTop (fun _ => 0) := by
  apply tendstoInMeasure_of_tendsto_ae
  · intro l
    exact ((((SJ3.measurable_queryRowLeftSum W Z β hβ V l).const_mul β).add
      (LM4b.measurable_actualRowDLeftSum W Z β hβ V l)).sub
      (measurable_originalRowLeftSum W β V l)).aestronglyMeasurable
  · exact S33aA.actualRotationLeftSumError_tendsto_ae W Z β hβ V

theorem originalRowLeftSum_tendstoInMeasure
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β) (V : ℝ≥0)
    {Q J : (Bool × Ω) × A → ℝ}
    (hQ : SJ3.IsQueryRowIntegral W Z β hβ V Q)
    (hJ : LM4b.IsActualRowDIntegral W Z β hβ V J) :
    TendstoInMeasure (LM4.actualRowBaseLaw W Z) (S33aA.originalRowLeftSum W β V) atTop
      (fun u => β * Q u + J u) := by
  have hQs (l : ℕ) : MemLp (SJ3.queryRowLeftSum W Z β hβ V l) 2
      (LM4.actualRowBaseLaw W Z) := by
    have he := (memLp_two_iff_integrable_sq
      (((SJ3.measurable_queryRowLeftSum W Z β hβ V l).aestronglyMeasurable).sub
        hQ.2.1.aestronglyMeasurable)).mpr (hQ.2.2.1 l)
    simpa only [Pi.add_apply, sub_add_cancel] using he.add hQ.2.1
  have hJs (l : ℕ) : MemLp (LM4b.actualRowDLeftSum W Z β hβ V l) 2
      (LM4.actualRowBaseLaw W Z) := by
    have he := (memLp_two_iff_integrable_sq
      (((LM4b.measurable_actualRowDLeftSum W Z β hβ V l).aestronglyMeasurable).sub
        hJ.1.aestronglyMeasurable)).mpr (hJ.2.1 l)
    simpa only [Pi.add_apply, sub_add_cancel] using he.add hJ.1
  have hcomb := SJ3.meanSquare_linearCombination hQs hJs hQ.2.1 hJ.1 hQ.2.2.2 hJ.2.2 β 1
  have hi (l : ℕ) : Integrable (fun u =>
      (β * SJ3.queryRowLeftSum W Z β hβ V l u + LM4b.actualRowDLeftSum W Z β hβ V l u -
        (β * Q u + J u)) ^ 2) (LM4.actualRowBaseLaw W Z) :=
    ((((hQs l).const_mul β).add (hJs l)).sub ((hQ.2.1.const_mul β).add hJ.1)).integrable_sq
  have hc := tendstoInMeasure_of_tendsto_integral_sq hi (by simpa only [one_mul] using hcomb)
  have hr := inMeasure_sub hc (actualRotationLeftSumError_tendstoInMeasure W Z β hβ V)
  simpa only [S33aA.actualRotationLeftSumError, sub_sub_cancel, sub_zero] using hr

theorem originalRowLeftSum_post_increment_tendstoInMeasure
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β) (V : ℝ≥0)
    {Q Qs J : (Bool × Ω) × A → ℝ}
    (hQ : SJ3.IsQueryRowIntegral W Z β hβ V Q)
    (hQs : SJ3.IsQueryRowIntegral W Z β hβ (parisiEquilibriumPhysicalEndpoint β) Qs)
    (hJ : LM4b.IsActualRowDIntegral W Z β hβ V J) :
    TendstoInMeasure (LM4.actualRowBaseLaw W Z)
      (fun l u => S33aA.originalRowLeftSum W β V l u -
        S33aA.originalRowLeftSum W β (parisiEquilibriumPhysicalEndpoint β) l u) atTop
      (fun u => β * (Q u - Qs u) + J u) := by
  have h := inMeasure_sub (originalRowLeftSum_tendstoInMeasure W Z β hβ V hQ hJ)
    (originalRowLeftSum_tendstoInMeasure W Z β hβ _ hQs
      (SJ3.rowDIntegral_zero_pre W Z β hβ _ le_rfl))
  convert h using 1
  funext u
  ring

end SKConstants.Completion.X33C
