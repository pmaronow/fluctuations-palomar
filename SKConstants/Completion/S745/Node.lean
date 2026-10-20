module

public import SKConstants.Completion.S745.Budgets
public import SKConstants.Completion.S745.Transforms

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology BigOperators

namespace SKConstants.Completion.S745
open SKConstantsOAI.ZeroTemperatureSK Blueprint5a Blueprint4
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]

def queryBudgetConstant (β : ℝ) : ℝ≥0 :=
  ⟨1 + 8 * (33 / 8 : ℝ) ^ 2 *
    Real.exp (((parisiEquilibriumPhysicalEndpoint β : ℝ) + 1) / 2), by positivity⟩

theorem queryBudgetConstant_pos (β : ℝ) : 0 < queryBudgetConstant β := by
  change (0 : ℝ) < 1 + 8 * (33 / 8 : ℝ) ^ 2 * Real.exp _
  positivity

def refinedTransform (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (K l : ℕ) (predictable : Bool) (u : (Bool × Ω) × A) : ℝ :=
  posteriorTransform W β (flatTime δ l)
    (fun k => coarseCoefficient W β δ K l (k / 2 ^ l) (k % 2 ^ l)) predictable
    (2 ^ l * (K + 1)) u.1.2 +
  queryTransform W Z β hβ (flatTime δ l) (fun k => Blueprint5a.mesh δ (k / 2 ^ l))
    (fun k => queryCoefficient W β δ l (k / 2 ^ l) (k % 2 ^ l)) predictable
    (2 ^ l * (K + 1)) (u.1.2, u.2)

theorem measurable_refinedTransform (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (K l : ℕ) (predictable : Bool) :
    Measurable (refinedTransform W Z β hβ δ K l predictable) :=
  ((measurable_posteriorTransform W β _ _ predictable _).comp measurable_fst.snd).add
    ((measurable_queryTransform W Z β hβ _ _ _ predictable _).comp
      (measurable_fst.snd.prodMk measurable_snd))

theorem sqrt_add_sq_le (v w : ℝ≥0) : (v.sqrt + w.sqrt) ^ 2 ≤ 2 * (v + w) := by
  apply NNReal.coe_le_coe.mp
  push_cast
  nlinarith [Real.sq_sqrt v.coe_nonneg, Real.sq_sqrt w.coe_nonneg,
    sq_nonneg (Real.sqrt (v : ℝ) - Real.sqrt (w : ℝ))]

theorem refinedTransform_subgaussian (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (K l : ℕ) (hm : LagMesh β δ K)
    (C : ℝ≥0) (hC : squareBudget δ K l (coarseCoefficient W β δ K l) ≤ C * δ)
    (predictable : Bool) :
    HasSubgaussianMGF (refinedTransform W Z β hβ δ K l predictable)
      ((2 * (C + queryBudgetConstant β)) * δ) (meshLaw W Z β δ K) := by
  have hp0 := posteriorTransform_subgaussian W β hβ (flatTime δ l) (flatTime_monotone δ l)
    (fun k => coarseCoefficient W β δ K l (k / 2 ^ l) (k % 2 ^ l)) predictable
    (2 ^ l * (K + 1)) (C * δ) (by rw [squareBudget_flat]; exact hC)
  have hbase (k : ℕ) : Blueprint5a.mesh δ (k / 2 ^ l) ≤ flatTime δ l k :=
    (refinedGrid_mem δ l (k / 2 ^ l) (k % 2 ^ l)
      (Nat.mod_lt k (pow_pos (by norm_num) l)).le).1
  have hq0 := queryTransform_subgaussian W Z β hβ (flatTime δ l)
    (fun k => Blueprint5a.mesh δ (k / 2 ^ l)) (flatTime_monotone δ l) hbase
    (fun k => queryCoefficient W β δ l (k / 2 ^ l) (k % 2 ^ l)) predictable
    (2 ^ l * (K + 1)) (queryBudgetConstant β * δ) (by
      rw [squareBudget_flat]
      exact query_squareBudget_le W β hβ δ K l hm)
  have hp : HasSubgaussianMGF (fun u : (Bool × Ω) × A =>
      posteriorTransform W β (flatTime δ l)
        (fun k => coarseCoefficient W β δ K l (k / 2 ^ l) (k % 2 ^ l)) predictable
        (2 ^ l * (K + 1)) u.1.2) (C * δ) (meshLaw W Z β δ K) := by
    apply HasSubgaussianMGF.of_map
      (X := posteriorTransform W β (flatTime δ l)
        (fun k => coarseCoefficient W β δ K l (k / 2 ^ l) (k % 2 ^ l)) predictable
        (2 ^ l * (K + 1)))
      (actualParisiFullQuerySpinLaw_path_hasLaw W Z β (growingQueryTime δ (K + 1))).aemeasurable
    rw [(actualParisiFullQuerySpinLaw_path_hasLaw W Z β (growingQueryTime δ (K + 1))).map_eq]
    exact hp0
  have hq : HasSubgaussianMGF (fun u : (Bool × Ω) × A =>
      queryTransform W Z β hβ (flatTime δ l) (fun k => Blueprint5a.mesh δ (k / 2 ^ l))
        (fun k => queryCoefficient W β δ l (k / 2 ^ l) (k % 2 ^ l)) predictable
        (2 ^ l * (K + 1)) (u.1.2, u.2)) (queryBudgetConstant β * δ) (meshLaw W Z β δ K) := by
    apply HasSubgaussianMGF.of_map
      (X := queryTransform W Z β hβ (flatTime δ l) (fun k => Blueprint5a.mesh δ (k / 2 ^ l))
        (fun k => queryCoefficient W β δ l (k / 2 ^ l) (k % 2 ^ l)) predictable
        (2 ^ l * (K + 1)))
      (actualParisiFullQuerySpinLaw_drivers_hasLaw W Z β (growingQueryTime δ (K + 1))).aemeasurable
    rw [(actualParisiFullQuerySpinLaw_drivers_hasLaw W Z β (growingQueryTime δ (K + 1))).map_eq]
    exact hq0
  have H := Concentration.hasSubgaussianMGF_of_proxy_le (hp.add hq) (sqrt_add_sq_le _ _)
  unfold refinedTransform
  convert H using 1; ring

theorem linearGroup_eq_transform (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (K l : ℕ) :
    linearGroup W Z β hβ δ K l = refinedTransform W Z β hβ δ K l false := by
  funext u
  unfold linearGroup LJ.refinedResidualLinear refinedTransform posteriorTransform queryTransform
  rw [predictableGaussianSum_eq_range_sum, sum_range_blocks, sum_range_blocks]
  simp only [queryTransformCoefficient, Bool.false_eq_true, ↓reduceIte, mul_one]
  simp only [brownianMeshIncrement]
  simp_rw [Finset.sum_add_distrib]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro j _ <;> apply Finset.sum_congr rfl <;> intro i hi
  all_goals
    have hi' := Finset.mem_range.mp hi
    simp only [flatTime_next, flatTime_block δ l j i hi']
    simp only [Nat.mul_add_div (pow_pos (by norm_num : 0 < (2 : ℕ)) l),
      Nat.div_eq_of_lt hi', Nat.add_zero, Nat.mul_add_mod, Nat.mod_eq_of_lt hi']
    rfl

theorem predictableGroup_eq_transform (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (K l : ℕ) :
    predictableGroup W Z β hβ δ K l = fun u => -refinedTransform W Z β hβ δ K l true u := by
  funext u
  unfold predictableGroup LJ.refinedResidualPredictable refinedTransform posteriorTransform queryTransform
  rw [predictableGaussianSum_eq_range_sum, sum_range_blocks, sum_range_blocks]
  simp only [queryTransformCoefficient, ↓reduceIte]
  simp only [brownianMeshIncrement]
  rw [neg_add]
  simp_rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := Finset.mem_range.mp hi
  simp only [flatTime_next, flatTime_block δ l j i hi']
  simp only [Nat.mul_add_div (pow_pos (by norm_num : 0 < (2 : ℕ)) l),
    Nat.div_eq_of_lt hi', Nat.add_zero, Nat.mul_add_mod, Nat.mod_eq_of_lt hi']
  unfold coarseCoefficient queryCoefficient
  ring

theorem linearGroupSubgaussian_holds (h2 : CoarseCoefficientBudgetStatement) :
    LinearGroupSubgaussianStatement := by
  intro Ω A _ _ W Z β hβ
  obtain ⟨C, hC, hbudget⟩ := coarse_squareBudget_le h2 W β hβ
  let Cn : ℝ≥0 := ⟨C, hC.le⟩
  have hCn : 0 < Cn := hC
  refine ⟨2 * (Cn + queryBudgetConstant β), by positivity, ?_⟩
  intro δ K hm l
  rw [linearGroup_eq_transform]
  exact ⟨measurable_refinedTransform W Z β hβ δ K l false,
    refinedTransform_subgaussian W Z β hβ δ K l hm Cn (hbudget δ K hm l) false⟩

theorem predictableGroup_subgaussian (h2 : CoarseCoefficientBudgetStatement)
    {Ω A : Type} [MeasurableSpace Ω] [MeasurableSpace A]
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ (δ : ℝ≥0) (K : ℕ), LagMesh β δ K → ∀ l,
      Measurable (predictableGroup W Z β hβ δ K l) ∧
      HasSubgaussianMGF (predictableGroup W Z β hβ δ K l) (C * δ) (meshLaw W Z β δ K) := by
  obtain ⟨C, hC, hbudget⟩ := coarse_squareBudget_le h2 W β hβ
  let Cn : ℝ≥0 := ⟨C, hC.le⟩
  have hCn : 0 < Cn := hC
  refine ⟨2 * (Cn + queryBudgetConstant β), by positivity, ?_⟩
  intro δ K hm l
  rw [predictableGroup_eq_transform]
  exact ⟨(measurable_refinedTransform W Z β hβ δ K l true).neg,
    (refinedTransform_subgaussian W Z β hβ δ K l hm Cn (hbudget δ K hm l) true).neg⟩

theorem predictableGroupMGF_holds (h2 : CoarseCoefficientBudgetStatement) :
    PredictableGroupMGFStatement := by
  intro Ω A _ _ W Z β hβ
  obtain ⟨C, hC, hbudget⟩ := predictableGroup_subgaussian h2 W Z β hβ
  refine ⟨C, 1, by exact_mod_cast hC, by norm_num, ?_⟩
  intro δ K hm l
  obtain ⟨hM, hG⟩ := hbudget δ K hm l
  have hpos : 0 < C * δ := mul_pos hC hm.1
  have hmean := integral_eq_zero_of_subgaussian_mgf (meshLaw W Z β δ K)
    (predictableGroup W Z β hβ δ K l) (C * δ) hpos hG
  refine ⟨hM, hG.integrable, ?_⟩
  simp only [hmean, sub_zero]
  constructor
  · intro θ _
    exact hG.integrable_exp_mul θ
  · intro θ _
    exact (hG.mgf_le θ).trans (Real.exp_le_exp.mpr (by
      have H : 0 ≤ (C : ℝ) * δ * θ ^ 2 := by positivity
      push_cast
      linarith))

end SKConstants.Completion.S745
