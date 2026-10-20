module

public import SKConstants.Completion.S76.LocalMGF

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology BigOperators

namespace SKConstants.Completion.S76
open SKConstantsOAI.ZeroTemperatureSK LJ LJ3
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]

theorem queryLagSum_cells_mgf (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℕ → ℝ≥0) (ht : ∀ j, Monotone (t j)) (q : ℕ → ℕ → ℝ) (N : ℕ → ℕ)
    (Q h : ℕ → ℝ) (hQ : ∀ j, 0 < Q j) (hh : ∀ j, 0 < h j)
    (hq : ∀ j k, |q j k| ≤ Q j) (hduration : ∀ j, (t j (N j) : ℝ) - t j 0 ≤ h j)
    (horder : ∀ i j, i < j → t i (N i) ≤ t j 0)
    (L : ℝ) (hscale : ∀ j, h j * Q j ≤ L)
    (θ : ℝ) (hθ : |θ| ≤ 1 / (4 * L)) (K : ℕ) :
    Integrable (fun w => Real.exp (θ * ∑ j ∈ Finset.range K, queryLagSum W Z β hβ (t j) (q j) (N j) w))
      (W.law.prod Z.law) ∧
      mgf (fun w => ∑ j ∈ Finset.range K, queryLagSum W Z β hβ (t j) (q j) (N j) w)
        (W.law.prod Z.law) θ ≤ Real.exp (32 * θ ^ 2 * ∑ j ∈ Finset.range K, (h j) ^ 2 * (Q j) ^ 2) := by
  let := W.isProbability
  let := Z.isProbability
  let X := fun j => queryLagSum W Z β hβ (t j) (q j) (N j)
  let m := fun j => MeasurableSpace.comap (pairPast W Z (t j 0)) inferInstance
  have hm (j : ℕ) : m j ≤ (inferInstance : MeasurableSpace (Ω × A)) :=
    (measurable_pairPast W Z (t j 0)).comap_le
  have hXm (j : ℕ) : Measurable (X j) := measurable_queryLagSum W Z β hβ (t j) (q j) (N j)
  have hi (j : ℕ) (a : ℝ) : Integrable (fun w => Real.exp (a * X j w)) (W.law.prod Z.law) :=
    (queryLagSum_subgaussian W Z β hβ (t j) (ht j) (q j) (N j) (Q j) (h j)
      (hQ j).le (hh j).le (hq j) (hduration j)).integrable_exp_mul a
  have hpast (j : ℕ) : AEStronglyMeasurable[m j] (fun w => ∑ i ∈ Finset.range j, X i w)
      (W.law.prod Z.law) := by
    have hsum (s : Finset ℕ) (hs : ∀ i ∈ s, i < j) :
        AEStronglyMeasurable[m j] (fun w => ∑ i ∈ s, X i w) (W.law.prod Z.law) := by
      induction s using Finset.induction_on with
      | empty => simpa using (aestronglyMeasurable_const :
          AEStronglyMeasurable[m j] (fun _ : Ω × A => (0 : ℝ)) (W.law.prod Z.law))
      | @insert i s his ih =>
        have hi := queryLagSum_measurable_past W Z β hβ (t i) (ht i) (q i) (N i) (t j 0)
          (horder i j (hs i (Finset.mem_insert_self _ _)))
        have hh := ih (fun k hk => hs k (Finset.mem_insert_of_mem hk))
        have hi' : AEStronglyMeasurable[m j] (X i) (W.law.prod Z.law) := hi
        convert hi'.add hh using 1
        ext w
        exact Finset.sum_insert his
    exact hsum _ (fun _ hi => Finset.mem_range.mp hi)
  have hθlocal (j : ℕ) : |θ| ≤ 1 / (4 * h j * Q j) := by
    apply hθ.trans
    apply one_div_le_one_div_of_le (mul_pos (mul_pos (by norm_num) (hh j)) (hQ j))
    nlinarith [hscale j]
  have hc (j : ℕ) : (W.law.prod Z.law)[fun w => Real.exp (θ * X j w) | m j] ≤ᵐ[W.law.prod Z.law]
      (fun _ => Real.exp (32 * (h j) ^ 2 * (Q j) ^ 2 * θ ^ 2)) :=
    queryLagSum_condExp_mgf W Z β hβ (t j) (ht j) (q j) (N j) (Q j) (h j)
      (hQ j) (hh j) (hq j) (hduration j) θ (hθlocal j)
  refine ⟨integrable_exp_sum (W.law.prod Z.law) X hXm hi K θ, ?_⟩
  have hb := mgf_sum_of_condExp_bounds (W.law.prod Z.law) m hm X hXm hi hpast θ
    (fun j => 32 * (h j) ^ 2 * (Q j) ^ 2 * θ ^ 2) hc K
  apply hb.trans_eq
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

def growingQueryLag (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (K l : ℕ) (u : Ω × A) : ℝ :=
  ∑ j ∈ Finset.range (K + 1), queryLagSum W Z β hβ (growingLagDyadicTime δ l j)
    (fun k => Real.sqrt (actualParisiFullSusceptibilitySquareExpected W β (growingLagDyadicTime δ l j k)))
    (2 ^ l) u

theorem measurable_growingQueryLag (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (K l : ℕ) :
    Measurable (growingQueryLag W Z β hβ δ K l) :=
  Finset.measurable_sum _ (fun _ _ => measurable_queryLagSum W Z β hβ _ _ _)

theorem growingQueryLag_mgf (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (K l : ℕ)
    (hsmall : ∀ j < K + 1, growingQueryDuration δ j ≤ 1) :
    Concentration.LocalQuadraticMGF (growingQueryLag W Z β hβ δ K l) (W.law.prod Z.law)
      (256 * Real.exp ((parisiEquilibriumPhysicalEndpoint β : ℝ) / 2) * (δ : ℝ))
      (1 / (4 * Real.sqrt (Real.exp ((parisiEquilibriumPhysicalEndpoint β : ℝ) / 2)) * (δ : ℝ))) := by
  let t := growingLagDyadicTime δ l
  let r := actualParisiFullSusceptibilitySquareExpected W β
  let Q := fun j => Real.sqrt (r (t j 0))
  let h := fun j => (growingQueryDuration δ j : ℝ)
  let Aβ := Real.exp ((parisiEquilibriumPhysicalEndpoint β : ℝ) / 2)
  let L := Real.sqrt Aβ * (δ : ℝ)
  have ht (j : ℕ) : Monotone (t j) := growingLagDyadicTime_monotone δ l j
  have ht0 (j : ℕ) : t j 0 = growingQueryTime δ j := growingLagDyadicTime_zero δ l j
  have htend (j : ℕ) : t j (2 ^ l) = growingQueryTime δ (j + 1) := growingLagDyadicTime_end δ l j
  have hQ (j : ℕ) : 0 < Q j := by
    apply Real.sqrt_pos.mpr
    rw [show r (t j 0) = actualParisiContinuationR W β
      ((t j 0 : ℝ) - (parisiEquilibriumPhysicalEndpoint β : ℝ)) from
        LQ.actual_square_profile_eq W β hβ (t j 0) (t j 0).coe_nonneg]
    exact actualParisiContinuationR_pos W β _
  have hh (j : ℕ) : 0 < h j := NNReal.coe_pos.mpr (growingQueryDuration_pos δ hδ j)
  have hq (j k : ℕ) : |Real.sqrt (r (t j k))| ≤ Q j := by
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt (LQ.actual_square_profile_antitone W β hβ
      (t j 0).coe_nonneg (t j k).coe_nonneg (NNReal.coe_le_coe.mpr (ht j (Nat.zero_le k))))
  have hd (j : ℕ) : (t j (2 ^ l) : ℝ) - t j 0 ≤ h j := by
    rw [htend j, ht0 j, growingQueryTime_succ, NNReal.coe_add]
    dsimp only [h]
    linarith
  have horder (i j : ℕ) (hij : i < j) : t i (2 ^ l) ≤ t j 0 := by
    rw [htend i, ht0 j]
    exact (growingQueryTime_strictMono δ hδ).monotone (by omega)
  have hscale (j : ℕ) : h j * Q j ≤ L := by
    dsimp only [h, Q, L, Aβ, r]
    rw [ht0 j]
    exact growingLagCellScale_le W β hβ δ j
  have hbudget : (∑ j ∈ Finset.range (K + 1), (h j) ^ 2 * (Q j) ^ 2) ≤ 8 * Aβ * (δ : ℝ) := by
    have he (j : ℕ) : (h j) ^ 2 * (Q j) ^ 2 = (growingLagCellScale W β δ j) ^ 2 := by
      dsimp only [h, Q, r]
      rw [ht0 j, growingLagCellScale, mul_pow]
    simp_rw [he]
    exact growingLagCellScale_square_sum_le W β hβ δ hδ K hsmall
  have hresult (θ : ℝ) (hθ : |θ| ≤ 1 / (4 * Real.sqrt Aβ * (δ : ℝ))) :
      Integrable (fun w => Real.exp (θ * growingQueryLag W Z β hβ δ K l w)) (W.law.prod Z.law) ∧
        mgf (growingQueryLag W Z β hβ δ K l) (W.law.prod Z.law) θ ≤
          Real.exp ((256 * Aβ * (δ : ℝ)) * θ ^ 2) := by
    have hm := queryLagSum_cells_mgf W Z β hβ t ht (fun j k => Real.sqrt (r (t j k)))
      (fun _ => 2 ^ l) Q h hQ hh hq hd horder L hscale θ
      (by simpa only [L, mul_assoc] using hθ) (K + 1)
    refine ⟨hm.1, hm.2.trans (Real.exp_le_exp.mpr ?_)⟩
    have hb := mul_le_mul_of_nonneg_left hbudget (by positivity : 0 ≤ 32 * θ ^ 2)
    nlinarith
  exact ⟨fun θ hθ => (hresult θ hθ).1, fun θ hθ => (hresult θ hθ).2⟩

theorem growingQueryLag_integrable_mean_zero (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (K l : ℕ) :
    Integrable (growingQueryLag W Z β hβ δ K l) (W.law.prod Z.law) ∧
      (∫ u, growingQueryLag W Z β hβ δ K l u ∂W.law.prod Z.law) = 0 := by
  let := W.isProbability
  let := Z.isProbability
  let t := growingLagDyadicTime δ l
  let q := fun j k => Real.sqrt (actualParisiFullSusceptibilitySquareExpected W β (t j k))
  let h := fun j => (t j (2 ^ l) : ℝ) - t j 0 + 1
  have ht (j : ℕ) : Monotone (t j) := growingLagDyadicTime_monotone δ l j
  have hh (j : ℕ) : 0 < h j := by
    have hs := NNReal.coe_le_coe.mpr (ht j (Nat.zero_le (2 ^ l)))
    dsimp only [h]
    linarith
  have hd (j : ℕ) : (t j (2 ^ l) : ℝ) - t j 0 ≤ h j := by dsimp only [h]; linarith
  have hq (j k : ℕ) : |q j k| ≤ 1 := by
    dsimp only [q]
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt
      (actualParisiFullSusceptibilitySquareExpected_bounds W β (t j k)).2
  have hi (j : ℕ) : Integrable (queryLagSum W Z β hβ (t j) (q j) (2 ^ l)) (W.law.prod Z.law) :=
    (queryLagSum_subgaussian W Z β hβ (t j) (ht j) (q j) (2 ^ l) 1 (h j)
      (by norm_num) (hh j).le (hq j) (hd j)).integrable
  have hz (j : ℕ) : (∫ u, queryLagSum W Z β hβ (t j) (q j) (2 ^ l) u ∂W.law.prod Z.law) = 0 := by
    simpa using queryLagSum_conditional_mean_zero W Z β hβ (t j) (ht j) univ MeasurableSet.univ
      (by simp) (q j) (2 ^ l) 1 (h j) (by norm_num) (hh j) (hq j) (hd j)
  refine ⟨integrable_finsetSum _ (fun j _ => hi j), ?_⟩
  change (∫ u, ∑ j ∈ Finset.range (K + 1), queryLagSum W Z β hβ (t j) (q j) (2 ^ l) u
    ∂W.law.prod Z.law) = 0
  rw [integral_finsetSum _ (fun j _ => hi j)]
  simp only [hz, Finset.sum_const_zero]

end SKConstants.Completion.S76
