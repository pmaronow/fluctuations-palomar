module

public import SKConstants.Completion.LJ3.Iteration
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology BigOperators
namespace SKConstants.Completion.LJ3
open SKConstantsOAI.ZeroTemperatureSK LJ
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

theorem originalLagSum_cells_mgf (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℕ → ℝ≥0) (ht : ∀ j, Monotone (t j)) (q : ℕ → ℕ → ℝ) (N : ℕ → ℕ)
    (Q h : ℕ → ℝ) (hQ : ∀ j, 0 < Q j) (hh : ∀ j, 0 < h j)
    (hq : ∀ j k, |q j k| ≤ Q j) (hduration : ∀ j, (t j (N j) : ℝ) - t j 0 ≤ h j)
    (horder : ∀ i j, i < j → t i (N i) ≤ t j 0)
    (L : ℝ) (hscale : ∀ j, h j * Q j ≤ L)
    (θ : ℝ) (hθ : |θ| ≤ 1 / (4 * L)) (K : ℕ) :
    Integrable (fun w => Real.exp (θ * ∑ j ∈ Finset.range K, originalLagSum W β (t j) (q j) (N j) w)) W.law ∧
      mgf (fun w => ∑ j ∈ Finset.range K, originalLagSum W β (t j) (q j) (N j) w) W.law θ ≤
        Real.exp (32 * θ ^ 2 * ∑ j ∈ Finset.range K, (h j) ^ 2 * (Q j) ^ 2) := by
  let := W.isProbability
  let X := fun j => originalLagSum W β (t j) (q j) (N j)
  let m := fun j => MeasurableSpace.comap
    (boundedDriftPastPath W (actualParisiFullScalarDrift β) (t j 0)) inferInstance
  have hm (j : ℕ) : m j ≤ mΩ :=
    (measurable_boundedDriftPastPath W (actualParisiFullScalarDrift β) (t j 0)).comap_le
  have hXm (j : ℕ) : Measurable (X j) := measurable_originalLagSum W β (t j) (q j) (N j)
  have hi (j : ℕ) (a : ℝ) : Integrable (fun w => Real.exp (a * X j w)) W.law :=
    (originalLagSum_subgaussian W β (t j) (ht j) (q j) (N j) (Q j) (h j)
      (hQ j).le (hh j).le (hq j) (hduration j)).integrable_exp_mul a
  have hpast (j : ℕ) : AEStronglyMeasurable[m j] (fun w => ∑ i ∈ Finset.range j, X i w) W.law := by
    have hsum (s : Finset ℕ) (hs : ∀ i ∈ s, i < j) :
        AEStronglyMeasurable[m j] (fun w => ∑ i ∈ s, X i w) W.law := by
      induction s using Finset.induction_on with
      | empty => simpa using (aestronglyMeasurable_const :
          AEStronglyMeasurable[m j] (fun _ : Ω => (0 : ℝ)) W.law)
      | @insert i s his ih =>
        have hi := originalLagSum_measurable_past W β (t i) (ht i) (q i) (N i) (t j 0)
          (horder i j (hs i (Finset.mem_insert_self _ _)))
        have hh := ih (fun k hk => hs k (Finset.mem_insert_of_mem hk))
        have hi' : AEStronglyMeasurable[m j] (X i) W.law := hi
        convert hi'.add hh using 1
        ext w
        exact Finset.sum_insert his
    exact hsum _ (fun _ hi => Finset.mem_range.mp hi)
  have hθlocal (j : ℕ) : |θ| ≤ 1 / (4 * h j * Q j) := by
    apply hθ.trans
    apply one_div_le_one_div_of_le (mul_pos (mul_pos (by norm_num) (hh j)) (hQ j))
    nlinarith [hscale j]
  have hc (j : ℕ) : W.law[fun w => Real.exp (θ * X j w) | m j] ≤ᵐ[W.law]
      (fun _ => Real.exp (32 * (h j) ^ 2 * (Q j) ^ 2 * θ ^ 2)) :=
    originalLagSum_condExp_mgf W β hβ (t j) (ht j) (q j) (N j) (Q j) (h j)
      (hQ j) (hh j) (hq j) (hduration j) θ (hθlocal j)
  refine ⟨integrable_exp_sum W.law X hXm hi K θ, ?_⟩
  have hb := mgf_sum_of_condExp_bounds W.law m hm X hXm hi hpast θ
    (fun j => 32 * (h j) ^ 2 * (Q j) ^ 2 * θ ^ 2) hc K
  apply hb.trans_eq
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

def actualGrowingOriginalLag (W : BrownianSystem Ω) (β : ℝ)
    (t : ℕ → ℕ → ℝ≥0) (weight : ℝ≥0 → ℝ) (N : ℕ → ℕ) (K : ℕ) (w : Ω) : ℝ :=
  ∑ j ∈ Finset.range (K + 1), actualOriginalLagSum W β (t j) weight (N j) w

theorem actualGrowingOriginalLag_mgf (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (t : ℕ → ℕ → ℝ≥0) (ht : ∀ j, Monotone (t j))
    (ht0 : ∀ j, t j 0 = growingQueryTime δ j) (N : ℕ → ℕ)
    (htend : ∀ j, t j (N j) ≤ growingQueryTime δ (j + 1))
    (weight : ℝ≥0 → ℝ) (hweight : ∀ s, |weight s| ≤ 1) (K : ℕ)
    (hsmall : ∀ j < K + 1, growingQueryDuration δ j ≤ 1) :
    Concentration.LocalQuadraticMGF (actualGrowingOriginalLag W β t weight N K) W.law
      (256 * Real.exp ((parisiEquilibriumPhysicalEndpoint β : ℝ) / 2) * (δ : ℝ))
      (1 / (4 * Real.sqrt (Real.exp ((parisiEquilibriumPhysicalEndpoint β : ℝ) / 2)) * (δ : ℝ))) := by
  let r := actualParisiFullSusceptibilitySquareExpected W β
  let Q := fun j => Real.sqrt (r (t j 0))
  let h := fun j => (growingQueryDuration δ j : ℝ)
  let A := Real.exp ((parisiEquilibriumPhysicalEndpoint β : ℝ) / 2)
  let L := Real.sqrt A * (δ : ℝ)
  have hQ (j : ℕ) : 0 < Q j := by
    apply Real.sqrt_pos.mpr
    rw [show r (t j 0) = actualParisiContinuationR W β
      ((t j 0 : ℝ) - (parisiEquilibriumPhysicalEndpoint β : ℝ)) from
        LQ.actual_square_profile_eq W β hβ (t j 0) (t j 0).coe_nonneg]
    exact actualParisiContinuationR_pos W β _
  have hh (j : ℕ) : 0 < h j := NNReal.coe_pos.mpr (growingQueryDuration_pos δ hδ j)
  have hq (j k : ℕ) : |Real.sqrt (r (t j k)) * weight (t j k)| ≤ Q j := by
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    apply (mul_le_mul_of_nonneg_left (hweight _) (Real.sqrt_nonneg _)).trans
    rw [mul_one]
    exact Real.sqrt_le_sqrt (LQ.actual_square_profile_antitone W β hβ
      (t j 0).coe_nonneg (t j k).coe_nonneg (NNReal.coe_le_coe.mpr (ht j (Nat.zero_le k))))
  have hd (j : ℕ) : (t j (N j) : ℝ) - t j 0 ≤ h j := by
    have he := NNReal.coe_le_coe.mpr (htend j)
    rw [growingQueryTime_succ, NNReal.coe_add, ← ht0 j] at he
    dsimp only [h]
    linarith
  have horder (i j : ℕ) (hij : i < j) : t i (N i) ≤ t j 0 := by
    rw [ht0 j]
    exact (htend i).trans ((growingQueryTime_strictMono δ hδ).monotone (by omega))
  have hscale (j : ℕ) : h j * Q j ≤ L := by
    dsimp only [h, Q, L, A, r]
    rw [ht0 j]
    exact growingLagCellScale_le W β hβ δ j
  have hbudget : (∑ j ∈ Finset.range (K + 1), (h j) ^ 2 * (Q j) ^ 2) ≤
      8 * A * (δ : ℝ) := by
    have he (j : ℕ) : (h j) ^ 2 * (Q j) ^ 2 = (growingLagCellScale W β δ j) ^ 2 := by
      dsimp only [h, Q, r]
      rw [ht0 j, growingLagCellScale, mul_pow]
    simp_rw [he]
    exact growingLagCellScale_square_sum_le W β hβ δ hδ K hsmall
  have hresult (θ : ℝ) (hθ : |θ| ≤ 1 / (4 * Real.sqrt A * (δ : ℝ))) :
      Integrable (fun w => Real.exp (θ * actualGrowingOriginalLag W β t weight N K w)) W.law ∧
        mgf (actualGrowingOriginalLag W β t weight N K) W.law θ ≤
          Real.exp ((256 * A * (δ : ℝ)) * θ ^ 2) := by
    have hm := originalLagSum_cells_mgf W β hβ t ht
      (fun j k => Real.sqrt (r (t j k)) * weight (t j k)) N Q h hQ hh hq hd horder L
      hscale θ (by simpa only [L, mul_assoc] using hθ) (K + 1)
    refine ⟨hm.1, hm.2.trans (Real.exp_le_exp.mpr ?_)⟩
    have hb := mul_le_mul_of_nonneg_left hbudget (by positivity : 0 ≤ 32 * θ ^ 2)
    nlinarith
  exact ⟨fun θ hθ => (hresult θ hθ).1, fun θ hθ => (hresult θ hθ).2⟩

theorem actualGrowingOriginalLag_mean_zero (W : BrownianSystem Ω) (β : ℝ)
    (t : ℕ → ℕ → ℝ≥0) (ht : ∀ j, Monotone (t j))
    (weight : ℝ≥0 → ℝ) (hweight : ∀ s, |weight s| ≤ 1) (N : ℕ → ℕ) (K : ℕ) :
    (∫ w, actualGrowingOriginalLag W β t weight N K w ∂W.law) = 0 := by
  let := W.isProbability
  let q := fun j k => Real.sqrt (actualParisiFullSusceptibilitySquareExpected W β (t j k)) * weight (t j k)
  let h := fun j => (t j (N j) : ℝ) - t j 0 + 1
  have hh (j : ℕ) : 0 < h j := by
    have hs := NNReal.coe_le_coe.mpr (ht j (Nat.zero_le (N j)))
    dsimp only [h]
    linarith
  have hd (j : ℕ) : (t j (N j) : ℝ) - t j 0 ≤ h j := by dsimp only [h]; linarith
  have hq (j k : ℕ) : |q j k| ≤ 1 := by
    dsimp only [q]
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    apply (mul_le_mul_of_nonneg_left (hweight _) (Real.sqrt_nonneg _)).trans
    rw [mul_one]
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt
      (actualParisiFullSusceptibilitySquareExpected_bounds W β (t j k)).2
  have hi (j : ℕ) : Integrable (actualOriginalLagSum W β (t j) weight (N j)) W.law :=
    (originalLagSum_subgaussian W β (t j) (ht j) (q j) (N j) 1 (h j)
      zero_le_one (hh j).le (hq j) (hd j)).integrable
  unfold actualGrowingOriginalLag
  rw [integral_finsetSum _ (fun j _ => hi j)]
  have hz (j : ℕ) : (∫ w, actualOriginalLagSum W β (t j) weight (N j) w ∂W.law) = 0 :=
    originalLagSum_mean_zero W β (t j) (ht j) (q j) (N j) 1 (h j)
      zero_lt_one (hh j) (hq j) (hd j)
  simp only [hz, Finset.sum_const_zero]

theorem actualGrowingOriginalLag_centered_log_mgf (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (t : ℕ → ℕ → ℝ≥0) (ht : ∀ j, Monotone (t j))
    (ht0 : ∀ j, t j 0 = growingQueryTime δ j) (N : ℕ → ℕ)
    (htend : ∀ j, t j (N j) ≤ growingQueryTime δ (j + 1))
    (weight : ℝ≥0 → ℝ) (hweight : ∀ s, |weight s| ≤ 1) (K : ℕ)
    (hsmall : ∀ j < K + 1, growingQueryDuration δ j ≤ 1) (θ : ℝ)
    (hθ : |θ| ≤ 1 / (4 * Real.sqrt (Real.exp ((parisiEquilibriumPhysicalEndpoint β : ℝ) / 2)) * (δ : ℝ))) :
    Real.log (∫ w, Real.exp (θ * (actualGrowingOriginalLag W β t weight N K w -
      ∫ z, actualGrowingOriginalLag W β t weight N K z ∂W.law)) ∂W.law) ≤
        256 * Real.exp ((parisiEquilibriumPhysicalEndpoint β : ℝ) / 2) * (δ : ℝ) * θ ^ 2 := by
  let := W.isProbability
  have hm := actualGrowingOriginalLag_mgf W β hβ δ hδ t ht ht0 N htend weight hweight K hsmall
  rw [actualGrowingOriginalLag_mean_zero W β t ht weight hweight N K]
  simp only [sub_zero]
  exact (Real.log_le_iff_le_exp (mgf_pos (hm.integrable_exp_mul θ hθ))).mpr (hm.mgf_le θ hθ)

theorem actualQuerySpinLaw_growingOriginalLag_mgf {A : Type*} [MeasurableSpace A]
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (t : ℕ → ℕ → ℝ≥0) (ht : ∀ j, Monotone (t j))
    (ht0 : ∀ j, t j 0 = growingQueryTime δ j) (N : ℕ → ℕ)
    (htend : ∀ j, t j (N j) ≤ growingQueryTime δ (j + 1))
    (weight : ℝ≥0 → ℝ) (hweight : ∀ s, |weight s| ≤ 1) (K : ℕ)
    (hsmall : ∀ j < K + 1, growingQueryDuration δ j ≤ 1) (V : ℝ≥0) :
    Concentration.LocalQuadraticMGF
      (fun u : (Bool × Ω) × A => actualGrowingOriginalLag W β t weight N K u.1.2)
      (actualParisiFullQuerySpinLaw W Z β V)
      (256 * Real.exp ((parisiEquilibriumPhysicalEndpoint β : ℝ) / 2) * (δ : ℝ))
      (1 / (4 * Real.sqrt (Real.exp ((parisiEquilibriumPhysicalEndpoint β : ℝ) / 2)) * (δ : ℝ))) := by
  exact (actualGrowingOriginalLag_mgf W β hβ δ hδ t ht ht0 N htend weight hweight K hsmall).comp_hasLaw
    (actualParisiFullQuerySpinLaw_path_hasLaw W Z β V)

end SKConstants.Completion.LJ3
