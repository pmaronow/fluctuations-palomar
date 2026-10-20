module

public import SKConstants.Completion.Blueprint5a.Statements
public import SKConstants.Completion.LM4b.QueryPredictability

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology BigOperators

namespace SKConstants.Completion.S76
open SKConstantsOAI.ZeroTemperatureSK LJ LJ3 LC1
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]

abbrev PairPast (T : ℝ≥0) := ScalarContinuousPath T × ScalarContinuousPath T

def pairPast (W : BrownianSystem Ω) (Z : BrownianSystem A) (T : ℝ≥0)
    (u : Ω × A) : PairPast T :=
  (brownianFinitePath W T u.1, brownianFinitePath Z T u.2)

theorem measurable_pairPast (W : BrownianSystem Ω) (Z : BrownianSystem A) (T : ℝ≥0) :
    Measurable (pairPast W Z T) :=
  (measurable_brownianFinitePath W T).prodMap (measurable_brownianFinitePath Z T)

theorem brownianFinitePath_restrict (W : BrownianSystem Ω) (S T : ℝ≥0) (hST : S ≤ T) :
    (fun w => scalarContinuousPathRestrict S T hST (brownianFinitePath W T w)) =ᵐ[W.law]
      brownianFinitePath W S := by
  filter_upwards [brownianFinitePath_version W T, brownianFinitePath_version W S] with w hT hS
  apply ContinuousMap.ext
  intro r
  exact (hT ⟨r, r.property.1, r.property.2.trans hST⟩).trans (hS r).symm

def pairRestrict (S T : ℝ≥0) (hST : S ≤ T) : PairPast T → PairPast S :=
  Prod.map (scalarContinuousPathRestrict S T hST) (scalarContinuousPathRestrict S T hST)

theorem measurable_pairRestrict (S T : ℝ≥0) (hST : S ≤ T) :
    Measurable (pairRestrict S T hST) :=
  (measurable_scalarContinuousPathRestrict S T hST).prodMap
    (measurable_scalarContinuousPathRestrict S T hST)

theorem pairPast_restrict (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (S T : ℝ≥0) (hST : S ≤ T) :
    (fun u => pairRestrict S T hST (pairPast W Z T u)) =ᵐ[W.law.prod Z.law]
      pairPast W Z S := by
  let := W.isProbability
  let := Z.isProbability
  filter_upwards [(measurePreserving_fst (μ := W.law) (ν := Z.law)).quasiMeasurePreserving.ae
      (brownianFinitePath_restrict W S T hST),
    (measurePreserving_snd (μ := W.law) (ν := Z.law)).quasiMeasurePreserving.ae
      (brownianFinitePath_restrict Z S T hST)] with u hW hZ
  exact Prod.ext hW hZ

theorem queryIncrement_indep_pairPast (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (t : ℕ → ℝ≥0) (ht : Monotone t) (n : ℕ) :
    IndepFun (pairPast W Z (t n))
      (brownianMeshIncrement (actualParisiQueryBrownianSystem W Z β hβ).B t n)
      (W.law.prod Z.law) := by
  let := W.isProbability
  let := Z.isProbability
  have he : t n + (t (n + 1) - t n) = t (n + 1) :=
    add_tsub_cancel_of_le (ht (Nat.le_succ n))
  have hi := (actualParisiQuery_future_indep_originalPast W Z β hβ (t n)).symm.comp
    ((measurable_scalarPathFromPast (t n)).prodMap (measurable_scalarPathFromPast (t n)))
    (measurable_pi_apply (t (n + 1) - t n))
  apply hi.congr
  · filter_upwards [(measurePreserving_fst (μ := W.law) (ν := Z.law)).quasiMeasurePreserving.ae
        (LM4b.brownianFinitePathFromPast_ae W (t n)),
      (measurePreserving_snd (μ := W.law) (ν := Z.law)).quasiMeasurePreserving.ae
        (LM4b.brownianFinitePathFromPast_ae Z (t n))] with u hW hZ
    exact Prod.ext hW hZ
  · exact ae_of_all _ (fun u => by dsimp only [Function.comp_def]; rw [he]; rfl)

theorem pastQuery_actual (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (T s : ℝ≥0) (hs : s ≤ T) :
    (fun u => LM4b.pastQuery W β hβ T s (pairPast W Z T u)) =ᵐ[W.law.prod Z.law]
      (actualParisiQueryBrownianSystem W Z β hβ).B s := by
  have hv := scalarOrthogonalProcesses_finite_path_version W Z
    (actualParisiNegativeRhoStieltjes W β hβ) (actualParisiSigmaStieltjes W β hβ)
    (continuous_actualParisiNegativeRhoStieltjes W β hβ)
    (continuous_actualParisiSigmaStieltjes W β hβ) T
  filter_upwards [hv] with u hu
  have hm : (s : ℝ) ∈ Icc 0 (T : ℝ) := ⟨s.coe_nonneg, hs⟩
  simp only [LM4b.pastQuery, IccExtend, Function.comp_def, projIcc_of_mem _ hm]
  exact (hu ⟨s, hm⟩).1.symm

abbrev PairCoefficient (t : ℕ → ℝ≥0) := (k : ℕ) → PairPast (t k) → ℝ

def queryCoefficient (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (t : ℕ → ℝ≥0) (H : PairCoefficient t) (k : ℕ) (u : Ω × A) : ℝ :=
  H k (pairPast W Z (t k) u)

def querySum (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (H : PairCoefficient t) : ℕ → Ω × A → ℝ :=
  predictableGaussianSum (brownianMeshIncrement (actualParisiQueryBrownianSystem W Z β hβ).B t)
    (queryCoefficient W Z t H)

def queryVariation (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (t : ℕ → ℝ≥0) (H : PairCoefficient t) : ℕ → Ω × A → ℝ :=
  predictableGaussianVariation (brownianMeshVariance t) (queryCoefficient W Z t H)

def queryPastSum (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (H : PairCoefficient t) (n : ℕ)
    (p : PairPast (t n)) : ℝ :=
  ∑ i : Fin n, H i (pairRestrict (t i) (t n) (ht (by omega)) p) *
    (LM4b.pastQuery W β hβ (t n) (t (i + 1)) p - LM4b.pastQuery W β hβ (t n) (t i) p)

def queryPastVariation (t : ℕ → ℝ≥0) (ht : Monotone t)
    (H : PairCoefficient t) (n : ℕ) (p : PairPast (t n)) : ℝ :=
  ∑ i : Fin n, H i (pairRestrict (t i) (t n) (ht (by omega)) p) ^ 2 *
    (brownianMeshVariance t i : ℝ)

theorem measurable_queryCoefficient (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (t : ℕ → ℝ≥0) (H : PairCoefficient t) (hH : ∀ k, Measurable (H k)) (k : ℕ) :
    Measurable (queryCoefficient W Z t H k) := (hH k).comp (measurable_pairPast W Z (t k))

theorem measurable_querySum (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (t : ℕ → ℝ≥0) (H : PairCoefficient t)
    (hH : ∀ k, Measurable (H k)) (n : ℕ) : Measurable (querySum W Z β hβ t H n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact ih.add ((measurable_queryCoefficient W Z t H hH n).mul
      (((actualParisiQueryBrownianSystem W Z β hβ).measurable _).sub
        ((actualParisiQueryBrownianSystem W Z β hβ).measurable _)))

theorem measurable_queryPastSum (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (H : PairCoefficient t)
    (hH : ∀ k, Measurable (H k)) (n : ℕ) : Measurable (queryPastSum W β hβ t ht H n) := by
  exact Finset.measurable_sum _ (fun i _ =>
    ((hH i).comp (measurable_pairRestrict _ _ _)).mul
      ((LM4b.measurable_pastQuery W β hβ _ _).sub (LM4b.measurable_pastQuery W β hβ _ _)))

theorem measurable_queryPastVariation (t : ℕ → ℝ≥0) (ht : Monotone t)
    (H : PairCoefficient t) (hH : ∀ k, Measurable (H k)) (n : ℕ) :
    Measurable (queryPastVariation t ht H n) := by
  exact Finset.measurable_sum _ (fun i _ =>
    (((hH i).comp (measurable_pairRestrict _ _ _)).pow_const 2).mul_const _)

theorem queryPastSum_actual (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (t : ℕ → ℝ≥0) (ht : Monotone t) (H : PairCoefficient t) (n : ℕ) :
    (fun u => queryPastSum W β hβ t ht H n (pairPast W Z (t n) u)) =ᵐ[W.law.prod Z.law]
      querySum W Z β hβ t H n := by
  have hr := ae_all_iff.mpr (fun i : Fin n => pairPast_restrict W Z (t i) (t n) (ht (by omega)))
  have hb := ae_all_iff.mpr (fun i : Fin (n + 1) => pastQuery_actual W Z β hβ (t n) (t i) (ht (by omega)))
  filter_upwards [hr, hb] with u hR hB
  rw [querySum, predictableGaussianSum_eq_fin_sum]
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [queryPastSum] at *
  rw [hR i, hB ⟨i + 1, by omega⟩, hB ⟨i, by omega⟩]
  rfl

theorem queryPastVariation_actual (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (H : PairCoefficient t) (n : ℕ) :
    (fun u => queryPastVariation t ht H n (pairPast W Z (t n) u)) =ᵐ[W.law.prod Z.law]
      queryVariation W Z t H n := by
  have hr := ae_all_iff.mpr (fun i : Fin n => pairPast_restrict W Z (t i) (t n) (ht (by omega)))
  filter_upwards [hr] with u hR
  rw [queryVariation, predictableGaussianVariation_eq_fin_sum]
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [queryPastVariation] at *
  rw [hR i]
  rfl

theorem query_state_indep_increment (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (H : PairCoefficient t) (hH : ∀ k, Measurable (H k)) (n : ℕ) :
    IndepFun (fun u => (querySum W Z β hβ t H n u, queryCoefficient W Z t H n u,
      queryVariation W Z t H n u))
      (brownianMeshIncrement (actualParisiQueryBrownianSystem W Z β hβ).B t n)
      (W.law.prod Z.law) := by
  have hi := (queryIncrement_indep_pairPast W Z β hβ t ht n).comp
    ((measurable_queryPastSum W β hβ t ht H hH n).prodMk
      ((hH n).prodMk (measurable_queryPastVariation t ht H hH n))) measurable_id
  apply hi.congr _ (ae_of_all _ (fun _ => rfl))
  filter_upwards [queryPastSum_actual W Z β hβ t ht H n,
    queryPastVariation_actual W Z t ht H n] with u hs hv
  exact Prod.ext hs (Prod.ext rfl hv)

theorem querySum_mgf (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (H : PairCoefficient t) (hH : ∀ k, Measurable (H k)) (θ : ℝ) (n : ℕ) (v : ℝ)
    (hv : ∀ᵐ u ∂W.law.prod Z.law, queryVariation W Z t H n u ≤ v) :
    Integrable (fun u => Real.exp (θ * querySum W Z β hβ t H n u)) (W.law.prod Z.law) ∧
      mgf (querySum W Z β hβ t H n) (W.law.prod Z.law) θ ≤ Real.exp (θ ^ 2 * v / 2) := by
  let := W.isProbability
  let := Z.isProbability
  let := (actualParisiQueryBrownianSystem W Z β hβ).isProbability
  exact predictableGaussianSum_mgf_bound _ _ _ _
    (brownianMeshIncrement_hasLaw (actualParisiQueryBrownianSystem W Z β hβ).brownian.toIsPreBrownianReal t ht)
    (fun k => (measurable_queryCoefficient W Z t H hH k).aemeasurable)
    (query_state_indep_increment W Z β hβ t ht H hH) θ n v hv

end SKConstants.Completion.S76
