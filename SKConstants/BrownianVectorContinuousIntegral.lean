module
public import SKConstants.BrownianVectorCoordinateIntegral
public import SKConstants.ScalarProcessRowMGFLimit

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators Topology
namespace SKConstants

lemma brownianVectorPastRestrict_fullPast {ι Ω : Type*} (D : ℝ≥0 → Ω → ℝ)
    {s T : ℝ≥0} (hs : s ≤ T) (ω : ι → Ω) :
    brownianVectorPastRestrict hs (brownianVectorFullPast D T ω) =
      brownianVectorFullPast D s ω := rfl

abbrev BrownianVectorCoordinatePredictableCoefficient (A ι : Type*) (t : ℕ → ℝ≥0) :=
  (k : ℕ) → A × (Iic (t k) → ι → ℝ) → ℝ

def brownianVectorCoordinateCoefficient {A ι Ω : Type*} (D : ℝ≥0 → Ω → ℝ)
    (_idx : ι) (t : ℕ → ℝ≥0) (H : BrownianVectorCoordinatePredictableCoefficient A ι t)
    (k : ℕ) (u : A × (ι → Ω)) : ℝ := H k (u.1,brownianVectorFullPast D (t k) u.2)

def brownianVectorCoordinatePredictableSum {A ι Ω : Type*} (D : ℝ≥0 → Ω → ℝ)
    (idx : ι) (t : ℕ → ℝ≥0) (H : BrownianVectorCoordinatePredictableCoefficient A ι t) :=
  predictableGaussianSum (fun k u => brownianVectorMeshIncrement D t k u.2 idx)
    (brownianVectorCoordinateCoefficient D idx t H)

def brownianVectorCoordinatePredictableVariation {A ι Ω : Type*} (D : ℝ≥0 → Ω → ℝ)
    (idx : ι) (t : ℕ → ℝ≥0) (H : BrownianVectorCoordinatePredictableCoefficient A ι t) :=
  predictableGaussianVariation (brownianMeshVariance t) (brownianVectorCoordinateCoefficient D idx t H)

lemma aemeasurable_brownianVectorCoordinateCoefficient {A ι Ω : Type*} [Fintype ι]
    [MeasurableSpace A] [MeasurableSpace Ω]
    (P : Measure A) [IsProbabilityMeasure P] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (D : ℝ≥0 → Ω → ℝ) (idx : ι) (_hD : IsPreBrownianReal D Q) (hmD : ∀ s, Measurable (D s))
    (t : ℕ → ℝ≥0) (H : BrownianVectorCoordinatePredictableCoefficient A ι t)
    (hH : ∀ k, Measurable (H k)) (k : ℕ) :
    AEMeasurable (brownianVectorCoordinateCoefficient D idx t H k)
      (P.prod (Measure.pi (fun _ : ι => Q))) := by
  exact ((hH k).comp (measurable_fst.prodMk ((Measurable.of_eval (fun s : Iic (t k) =>
    Measurable.of_eval (fun j : ι => (hmD s).comp (measurable_pi_apply j)))).comp
      measurable_snd))).aemeasurable

theorem brownianVectorCoordinatePredictableSum_L2_isometry {A ι Ω : Type*}
    [MeasurableSpace A] [Fintype ι] [MeasurableSpace Ω]
    (P : Measure A) [IsProbabilityMeasure P] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (D : ℝ≥0 → Ω → ℝ) (idx : ι) (hD : IsPreBrownianReal D Q) (hmD : ∀ s, Measurable (D s))
    (t : ℕ → ℝ≥0) (ht : Monotone t) (H : BrownianVectorCoordinatePredictableCoefficient A ι t)
    (hH : ∀ k, Measurable (H k))
    (hHsq : ∀ k, Integrable (fun u => brownianVectorCoordinateCoefficient D idx t H k u ^ 2)
      (P.prod (Measure.pi (fun _ : ι => Q)))) (n : ℕ) :
    Integrable (fun u => brownianVectorCoordinatePredictableSum D idx t H n u ^ 2)
      (P.prod (Measure.pi (fun _ : ι => Q))) ∧
    Integrable (brownianVectorCoordinatePredictableVariation D idx t H n)
      (P.prod (Measure.pi (fun _ : ι => Q))) ∧
    (∫ u, brownianVectorCoordinatePredictableSum D idx t H n u ^ 2 ∂P.prod (Measure.pi (fun _ : ι => Q))) =
      ∫ u, brownianVectorCoordinatePredictableVariation D idx t H n u ∂P.prod (Measure.pi (fun _ : ι => Q)) := by
  let K : BrownianVectorPredictableCoefficient A ι t := fun k u _ => H k u
  have hK : ∀ k, Measurable (K k) := fun k => Measurable.of_eval (fun _ => hH k)
  exact brownianVectorCoordinateSum_L2_isometry P Q D hD hmD t ht K hK idx hHsq n

abbrev BrownianVectorContinuousCoordinatePastCoefficient (A ι : Type*) :=
  (s : ℝ≥0) → A × (Iic s → ι → ℝ) → ℝ

def brownianVectorContinuousCoordinateCoefficient {A ι Ω : Type*} (D : ℝ≥0 → Ω → ℝ)
    (_idx : ι) (H : BrownianVectorContinuousCoordinatePastCoefficient A ι)
    (s : ℝ≥0) (u : A × (ι → Ω)) : ℝ := H s (u.1,brownianVectorFullPast D s u.2)

def brownianVectorContinuousCoordinateMeshCoefficient {A ι : Type*}
    (H : BrownianVectorContinuousCoordinatePastCoefficient A ι) (t : ℕ → ℝ≥0) :
    BrownianVectorCoordinatePredictableCoefficient A ι t := fun k => H (t k)

def brownianVectorContinuousCoordinateLeftSum {A ι Ω : Type*} (D : ℝ≥0 → Ω → ℝ)
    (idx : ι) (H : BrownianVectorContinuousCoordinatePastCoefficient A ι)
    (G : ScalarDyadicNestedGrid) (k l : ℕ) : A × (ι → Ω) → ℝ :=
  brownianVectorCoordinatePredictableSum D idx (G.time l)
    (brownianVectorContinuousCoordinateMeshCoefficient H (G.time l)) (k*2^l)
lemma integrable_brownianVectorCoordinateCoefficient_sq_of_bounded {A ι Ω : Type*} [Fintype ι]
    [MeasurableSpace A] [MeasurableSpace Ω]
    (P : Measure A) [IsProbabilityMeasure P] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (D : ℝ≥0 → Ω → ℝ) (idx : ι) (hD : IsPreBrownianReal D Q) (hmD : ∀ s, Measurable (D s))
    (t : ℕ → ℝ≥0) (H : BrownianVectorCoordinatePredictableCoefficient A ι t)
    (hH : ∀ k, Measurable (H k)) (C : ℝ) (hC : ∀ k u, ‖H k u‖ ≤ C) (k : ℕ) :
    Integrable (fun u => brownianVectorCoordinateCoefficient D idx t H k u ^ 2) (P.prod (Measure.pi (fun _ : ι => Q))) := by
  apply (integrable_const (C^2 : ℝ)).mono'
    ((aemeasurable_brownianVectorCoordinateCoefficient P Q D idx hD hmD t H hH k).pow_const 2).aestronglyMeasurable
  apply ae_of_all
  intro u
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (hC k _) 2

lemma memLp_brownianVectorCoordinatePredictableSum {A ι Ω : Type*} [Fintype ι]
    [MeasurableSpace A] [MeasurableSpace Ω]
    (P : Measure A) [IsProbabilityMeasure P] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (D : ℝ≥0 → Ω → ℝ) (idx : ι) (hD : IsPreBrownianReal D Q) (hmD : ∀ s, Measurable (D s))
    (t : ℕ → ℝ≥0) (ht : Monotone t) (H : BrownianVectorCoordinatePredictableCoefficient A ι t)
    (hH : ∀ k, Measurable (H k)) (C : ℝ) (hC : ∀ k u, ‖H k u‖ ≤ C) (n : ℕ) :
    MemLp (brownianVectorCoordinatePredictableSum D idx t H n) 2 (P.prod (Measure.pi (fun _ : ι => Q))) := by
  have hi := brownianVectorCoordinatePredictableSum_L2_isometry P Q D idx hD hmD t ht H hH
    (integrable_brownianVectorCoordinateCoefficient_sq_of_bounded P Q D idx hD hmD t H hH C hC) n
  have hm := aemeasurable_predictableGaussianSum (P.prod (Measure.pi (fun _ : ι => Q)))
    (fun k u => brownianVectorMeshIncrement D t k u.2 idx) (brownianVectorCoordinateCoefficient D idx t H)
    (fun k => ((hmD _).sub (hmD _)).comp ((measurable_pi_apply idx).comp measurable_snd) |>.aemeasurable)
    (aemeasurable_brownianVectorCoordinateCoefficient P Q D idx hD hmD t H hH) n
  exact (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).2 hi.1

def brownianVectorContinuousCoordinateDifferenceCoefficient {A ι : Type*}
    (H : BrownianVectorContinuousCoordinatePastCoefficient A ι) (G : ScalarDyadicNestedGrid) (m l : ℕ) :
    BrownianVectorCoordinatePredictableCoefficient A ι (G.time (m+l)) := fun i u =>
  H (G.time m (i/2^l)) (u.1,brownianVectorPastRestrict (G.left_le m l i) u.2) -
    H (G.time l (i/2^m)) (u.1,brownianVectorPastRestrict (by
      simpa only [Nat.add_comm l m] using G.left_le l m i) u.2)

lemma measurable_brownianVectorContinuousCoordinateDifferenceCoefficient {A ι : Type*} [MeasurableSpace A]
    (H : BrownianVectorContinuousCoordinatePastCoefficient A ι) (hH : ∀ s, Measurable (H s))
    (G : ScalarDyadicNestedGrid) (m l i : ℕ) :
    Measurable (brownianVectorContinuousCoordinateDifferenceCoefficient H G m l i) := by
  exact ((hH _).comp (measurable_fst.prodMk
    ((measurable_brownianVectorPastRestrict _).comp measurable_snd))).sub
    ((hH _).comp (measurable_fst.prodMk
      ((measurable_brownianVectorPastRestrict _).comp measurable_snd)))

lemma brownianVectorContinuousCoordinateLeftSum_refinement {A ι Ω : Type*} [Fintype ι] (D : ℝ≥0 → Ω → ℝ) (idx : ι)
    (H : BrownianVectorContinuousCoordinatePastCoefficient A ι) (G : ScalarDyadicNestedGrid) (k l d : ℕ)
    (u : A × (ι → Ω)) :
    brownianVectorContinuousCoordinateLeftSum D idx H G k l u =
      ∑ i ∈ Finset.range (k*2^(l+d)), brownianVectorContinuousCoordinateCoefficient D idx H
        (G.time l (i/2^d)) u * brownianVectorMeshIncrement D (G.time (l+d)) i u.2 idx := by
  let F : ℕ → ℝ := fun a => brownianVectorContinuousCoordinateCoefficient D idx H (G.time l a) u
  let M : ℕ → ℝ := fun i => D (G.time (l+d) i) (u.2 idx)
  calc
    _ = ∑ a ∈ Finset.range (k*2^l), F a * (M ((a+1)*2^d)-M (a*2^d)) := by
      rw [brownianVectorContinuousCoordinateLeftSum,brownianVectorCoordinatePredictableSum,
        predictableGaussianSum_eq_range_sum]
      simp only [F,M,ScalarDyadicNestedGrid.embed]
      rfl
    _ = ∑ i ∈ Finset.range ((k*2^l)*2^d), F (i/2^d)*(M (i+1)-M i) :=
      sum_weighted_refinement F M _ _ (by positivity)
    _ = _ := by simp only [pow_add,← Nat.mul_assoc]; rfl

lemma brownianVectorContinuousCoordinateLeftSum_difference_eq {A ι Ω : Type*} [Fintype ι] (D : ℝ≥0 → Ω → ℝ) (idx : ι)
    (H : BrownianVectorContinuousCoordinatePastCoefficient A ι) (G : ScalarDyadicNestedGrid) (k m l : ℕ)
    (u : A × (ι → Ω)) :
    brownianVectorContinuousCoordinateLeftSum D idx H G k m u - brownianVectorContinuousCoordinateLeftSum D idx H G k l u =
      brownianVectorCoordinatePredictableSum D idx (G.time (m+l))
        (brownianVectorContinuousCoordinateDifferenceCoefficient H G m l) (k*2^(m+l)) u := by
  have hm := brownianVectorContinuousCoordinateLeftSum_refinement D idx H G k m l u
  have hl := brownianVectorContinuousCoordinateLeftSum_refinement D idx H G k l m u
  rw [Nat.add_comm l m] at hl
  rw [hm,hl,brownianVectorCoordinatePredictableSum,predictableGaussianSum_eq_range_sum,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [brownianVectorCoordinateCoefficient,brownianVectorContinuousCoordinateDifferenceCoefficient,
    brownianVectorContinuousCoordinateCoefficient,brownianVectorPastRestrict_fullPast]
  ring

lemma brownianVectorContinuousCoordinateLeftSum_difference_isometry {A ι Ω : Type*} [Fintype ι]
    [MeasurableSpace A] [MeasurableSpace Ω]
    (P : Measure A) [IsProbabilityMeasure P] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (D : ℝ≥0 → Ω → ℝ) (idx : ι) (hD : IsPreBrownianReal D Q) (hmD : ∀ s, Measurable (D s))
    (H : BrownianVectorContinuousCoordinatePastCoefficient A ι) (hH : ∀ s, Measurable (H s))
    (C : ℝ) (hC : ∀ s u, ‖H s u‖ ≤ C)
    (G : ScalarDyadicNestedGrid) (k m l : ℕ) :
    (∫ u, (brownianVectorContinuousCoordinateLeftSum D idx H G k m u -
      brownianVectorContinuousCoordinateLeftSum D idx H G k l u)^2 ∂P.prod (Measure.pi (fun _ : ι => Q))) =
      ∑ i : Fin (k*2^(m+l)), (brownianMeshVariance (G.time (m+l)) i : ℝ) *
        ∫ u, (brownianVectorContinuousCoordinateCoefficient D idx H (G.time m (i/2^l)) u -
          brownianVectorContinuousCoordinateCoefficient D idx H (G.time l (i/2^m)) u)^2 ∂P.prod (Measure.pi (fun _ : ι => Q)) := by
  have hbound : ∀ i u, ‖brownianVectorContinuousCoordinateDifferenceCoefficient H G m l i u‖ ≤ 2*C := by
    intro i u
    exact (norm_sub_le _ _).trans ((add_le_add (hC _ _) (hC _ _)).trans_eq (by ring))
  have hisq := integrable_brownianVectorCoordinateCoefficient_sq_of_bounded P Q D idx hD hmD _ _
    (measurable_brownianVectorContinuousCoordinateDifferenceCoefficient H hH G m l) (2*C) hbound
  simp_rw [brownianVectorContinuousCoordinateLeftSum_difference_eq]
  rw [(brownianVectorCoordinatePredictableSum_L2_isometry P Q D idx hD hmD _ (G.monotone (m+l)) _
    (measurable_brownianVectorContinuousCoordinateDifferenceCoefficient H hH G m l) hisq _).2.2]
  rw [brownianVectorCoordinatePredictableVariation,integral_predictableGaussianVariation _ _ _ hisq]
  rfl

theorem brownianVectorContinuousCoordinateLeftSum_L2_cauchy {A ι Ω : Type*} [Fintype ι]
    [MeasurableSpace A] [MeasurableSpace Ω]
    (P : Measure A) [IsProbabilityMeasure P] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (D : ℝ≥0 → Ω → ℝ) (idx : ι) (hD : IsPreBrownianReal D Q) (hmD : ∀ s, Measurable (D s))
    (H : BrownianVectorContinuousCoordinatePastCoefficient A ι) (hH : ∀ s, Measurable (H s))
    (C : ℝ) (hC : ∀ s u, ‖H s u‖ ≤ C)
    (hc : ∀ᵐ u ∂P.prod (Measure.pi (fun _ : ι => Q)), Continuous (fun s => brownianVectorContinuousCoordinateCoefficient D idx H s u))
    (G : ScalarDyadicNestedGrid) (k : ℕ) (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (hleft : ∀ l d i, i < k*2^(l+d) →
      |(G.time (l+d) i : ℝ)-G.time l (i/2^d)| ≤ δ l) :
    ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ l ≥ N,
      (∫ u, (brownianVectorContinuousCoordinateLeftSum D idx H G k m u-
        brownianVectorContinuousCoordinateLeftSum D idx H G k l u)^2 ∂P.prod (Measure.pi (fun _ : ι => Q))) < ε := by
  intro ε hε
  let T := G.time 0 k
  have hT : 0 < (T : ℝ)+1 := by positivity
  have hm (s : ℝ≥0) : AEStronglyMeasurable (brownianVectorContinuousCoordinateCoefficient D idx H s) (P.prod (Measure.pi (fun _ : ι => Q))) :=
    ((hH s).comp (measurable_fst.prodMk
      ((Measurable.of_eval (fun t : Iic s => Measurable.of_eval (fun j : ι => (hmD t).comp (measurable_pi_apply j)))).comp measurable_snd))).aestronglyMeasurable
  obtain ⟨η,hη,hsmall⟩ := expected_sq_difference_uniform_small_of_bounded (P.prod (Measure.pi (fun _ : ι => Q)))
    (brownianVectorContinuousCoordinateCoefficient D idx H) hm hc C (fun s u => hC s _) T
    (ε/((T : ℝ)+1)) (div_pos hε hT)
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hδ.eventually (eventually_lt_nhds (half_pos hη)))
  refine ⟨N,fun m hm l hl => ?_⟩
  have henergy (i : Fin (k*2^(m+l))) :
      (∫ u, (brownianVectorContinuousCoordinateCoefficient D idx H (G.time m (i/2^l)) u-
        brownianVectorContinuousCoordinateCoefficient D idx H (G.time l (i/2^m)) u)^2 ∂P.prod (Measure.pi (fun _ : ι => Q))) ≤
          ε/((T : ℝ)+1) := by
    let s := G.time m (i/2^l)
    let t := G.time l (i/2^m)
    let v := G.time (m+l) i
    have hs : s ≤ T := (G.left_le m l i).trans (G.le_duration i.isLt.le)
    have ht : t ≤ T := (show t ≤ v from by
      simpa only [Nat.add_comm l m] using G.left_le l m i).trans (G.le_duration i.isLt.le)
    have hvs : |(v : ℝ)-s| ≤ δ m := hleft m l i i.isLt
    have hvt : |(v : ℝ)-t| ≤ δ l := by
      simpa only [Nat.add_comm l m] using hleft l m i (by
        simpa only [Nat.add_comm l m] using i.isLt)
    have hst : |(s : ℝ)-t| < η := by
      have htri := abs_sub_le (s : ℝ) v t
      rw [abs_sub_comm (s : ℝ) v] at htri
      have hnm := hN m hm
      have hnl := hN l hl
      linarith
    exact (hsmall s hs t ht hst).le
  rw [brownianVectorContinuousCoordinateLeftSum_difference_isometry P Q D idx hD hmD H hH C hC G k m l]
  calc
    _ ≤ ∑ i : Fin (k*2^(m+l)), (brownianMeshVariance (G.time (m+l)) i : ℝ) *
        (ε/((T : ℝ)+1)) := Finset.sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_left (henergy i) (NNReal.coe_nonneg _))
    _ = (T : ℝ)*(ε/((T : ℝ)+1)) := by
      rw [← Finset.sum_mul]
      congr 1
      rw [Fin.sum_univ_eq_sum_range (fun i => (brownianMeshVariance (G.time (m+l)) i : ℝ))]
      exact G.variance_sum k (m+l)
    _ < ε := by
      rw [← mul_div_assoc]
      apply (div_lt_iff₀ hT).mpr
      nlinarith

theorem brownianVectorContinuousCoordinateLeftSum_exists_L2_limit {A ι Ω : Type*} [Fintype ι]
    [MeasurableSpace A] [MeasurableSpace Ω]
    (P : Measure A) [IsProbabilityMeasure P] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (D : ℝ≥0 → Ω → ℝ) (idx : ι) (hD : IsPreBrownianReal D Q) (hmD : ∀ s, Measurable (D s))
    (H : BrownianVectorContinuousCoordinatePastCoefficient A ι) (hH : ∀ s, Measurable (H s))
    (C : ℝ) (hC : ∀ s u, ‖H s u‖ ≤ C)
    (hc : ∀ᵐ u ∂P.prod (Measure.pi (fun _ : ι => Q)), Continuous (fun s => brownianVectorContinuousCoordinateCoefficient D idx H s u))
    (G : ScalarDyadicNestedGrid) (k : ℕ) (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (hleft : ∀ l d i, i < k*2^(l+d) →
      |(G.time (l+d) i : ℝ)-G.time l (i/2^d)| ≤ δ l) :
    ∃ I : A × (ι → Ω) → ℝ, MemLp I 2 (P.prod (Measure.pi (fun _ : ι => Q))) ∧
      (∀ l, Integrable (fun u => (brownianVectorContinuousCoordinateLeftSum D idx H G k l u-I u)^2) (P.prod (Measure.pi (fun _ : ι => Q)))) ∧
      Tendsto (fun l => ∫ u, (brownianVectorContinuousCoordinateLeftSum D idx H G k l u-I u)^2 ∂P.prod (Measure.pi (fun _ : ι => Q)))
        atTop (𝓝 0) := by
  have hmem (l : ℕ) : MemLp (brownianVectorContinuousCoordinateLeftSum D idx H G k l) 2 (P.prod (Measure.pi (fun _ : ι => Q))) :=
    memLp_brownianVectorCoordinatePredictableSum P Q D idx hD hmD _ (G.monotone l) _
      (fun i => hH _) C (fun i u => hC _ _) _
  let F : ℕ → Lp ℝ 2 (P.prod (Measure.pi (fun _ : ι => Q))) := fun l => (hmem l).toLp (brownianVectorContinuousCoordinateLeftSum D idx H G k l)
  have hcauchy : CauchySeq F := by
    apply Metric.cauchySeq_iff.2
    intro ε hε
    obtain ⟨N,hN⟩ := brownianVectorContinuousCoordinateLeftSum_L2_cauchy P Q D idx hD hmD H hH C hC hc G k δ hδ hleft
      (ε^2) (sq_pos_of_pos hε)
    refine ⟨N,fun m hm l hl => ?_⟩
    have he : dist (F m) (F l)^2 =
        ∫ u, (brownianVectorContinuousCoordinateLeftSum D idx H G k m u-brownianVectorContinuousCoordinateLeftSum D idx H G k l u)^2
          ∂P.prod (Measure.pi (fun _ : ι => Q)) := by
      rw [dist_eq_norm]
      exact norm_toLp_difference_sq_eq_integral (hmem m) (hmem l)
    have hs := hN m hm l hl
    rw [← he] at hs
    nlinarith [show 0 ≤ dist (F m) (F l) from dist_nonneg]
  obtain ⟨I,hI⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨I,Lp.memLp I,fun l => ((hmem l).sub (Lp.memLp I)).integrable_sq,?_⟩
  have hn : Tendsto (fun l => ‖F l-I‖^2) atTop (𝓝 0) := by
    simpa using ((hI.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => I) atTop (𝓝 I))).norm).pow 2
  have he : (fun l => ∫ u, (brownianVectorContinuousCoordinateLeftSum D idx H G k l u-I u)^2 ∂P.prod (Measure.pi (fun _ : ι => Q))) =
      fun l => ‖F l-I‖^2 := by
    funext l
    exact (norm_toLp_sub_sq_eq_integral (hmem l) I).symm
  rw [he]
  exact hn

abbrev BrownianVectorContinuousPastCoefficient (A ι : Type*) :=
  (s : ℝ≥0) → A × (Iic s → ι → ℝ) → ι → ℝ

def brownianVectorContinuousCoefficient {A ι Ω : Type*} (D : ℝ≥0 → Ω → ℝ)
    (H : BrownianVectorContinuousPastCoefficient A ι) (s : ℝ≥0)
    (u : A × (ι → Ω)) : ι → ℝ := H s (u.1,brownianVectorFullPast D s u.2)

def brownianVectorContinuousMeshCoefficient {A ι : Type*}
    (H : BrownianVectorContinuousPastCoefficient A ι) (t : ℕ → ℝ≥0) :
    BrownianVectorPredictableCoefficient A ι t := fun k => H (t k)

def brownianVectorContinuousLeftSum {A ι Ω : Type*} [Fintype ι] (D : ℝ≥0 → Ω → ℝ)
    (H : BrownianVectorContinuousPastCoefficient A ι) (G : ScalarDyadicNestedGrid)
    (k l : ℕ) : A × (ι → Ω) → ℝ :=
  brownianVectorPredictableSum D (G.time l)
    (brownianVectorContinuousMeshCoefficient H (G.time l)) (k*2^l)

lemma brownianVectorContinuousLeftSum_eq_sum_coordinate {A ι Ω : Type*} [Fintype ι]
    (D : ℝ≥0 → Ω → ℝ) (H : BrownianVectorContinuousPastCoefficient A ι)
    (G : ScalarDyadicNestedGrid) (k l : ℕ) (u : A × (ι → Ω)) :
    brownianVectorContinuousLeftSum D H G k l u = ∑ i,
      brownianVectorContinuousCoordinateLeftSum D i (fun s u => H s u i) G k l u := by
  rw [brownianVectorContinuousLeftSum,brownianVectorPredictableSum_eq_sum_coordinate]
  rfl

lemma memLp_brownianVectorContinuousLeftSum {A ι Ω : Type*}
    [MeasurableSpace A] [Fintype ι] [MeasurableSpace Ω]
    (P : Measure A) [IsProbabilityMeasure P] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (D : ℝ≥0 → Ω → ℝ) (hD : IsPreBrownianReal D Q) (hmD : ∀ s, Measurable (D s))
    (H : BrownianVectorContinuousPastCoefficient A ι) (hH : ∀ s, Measurable (H s))
    (C : ℝ) (hC : ∀ s u i, ‖H s u i‖ ≤ C)
    (G : ScalarDyadicNestedGrid) (k l : ℕ) :
    MemLp (brownianVectorContinuousLeftSum D H G k l) 2
      (P.prod (Measure.pi (fun _ : ι => Q))) := by
  let f : ι → A × (ι → Ω) → ℝ := fun i =>
    brownianVectorContinuousCoordinateLeftSum D i (fun s u => H s u i) G k l
  have hf (i : ι) : MemLp (f i) 2 (P.prod (Measure.pi (fun _ : ι => Q))) :=
    memLp_brownianVectorCoordinatePredictableSum P Q D i hD hmD _ (G.monotone l) _
      (fun j => (measurable_pi_apply i).comp (hH _)) C (fun j u => hC _ u i) (k*2^l)
  convert memLp_finsetSum Finset.univ (fun i _ => hf i) using 1
  funext u
  exact brownianVectorContinuousLeftSum_eq_sum_coordinate D H G k l u

theorem brownianVectorContinuousLeftSum_exists_L2_limit {A ι Ω : Type*}
    [MeasurableSpace A] [Fintype ι] [MeasurableSpace Ω]
    (P : Measure A) [IsProbabilityMeasure P] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (D : ℝ≥0 → Ω → ℝ) (hD : IsPreBrownianReal D Q) (hmD : ∀ s, Measurable (D s))
    (H : BrownianVectorContinuousPastCoefficient A ι) (hH : ∀ s, Measurable (H s))
    (C : ℝ) (hC : ∀ s u i, ‖H s u i‖ ≤ C)
    (hc : ∀ i, ∀ᵐ u ∂P.prod (Measure.pi (fun _ : ι => Q)),
      Continuous (fun s => brownianVectorContinuousCoefficient D H s u i))
    (G : ScalarDyadicNestedGrid) (k : ℕ) (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (hleft : ∀ l d i, i < k*2^(l+d) →
      |(G.time (l+d) i : ℝ)-G.time l (i/2^d)| ≤ δ l) :
    ∃ I : A × (ι → Ω) → ℝ, MemLp I 2 (P.prod (Measure.pi (fun _ : ι => Q))) ∧
      (∀ l, Integrable (fun u => (brownianVectorContinuousLeftSum D H G k l u-I u)^2)
        (P.prod (Measure.pi (fun _ : ι => Q)))) ∧
      Tendsto (fun l => ∫ u, (brownianVectorContinuousLeftSum D H G k l u-I u)^2
        ∂P.prod (Measure.pi (fun _ : ι => Q))) atTop (𝓝 0) := by
  choose I hI hIi hIlim using fun i =>
    brownianVectorContinuousCoordinateLeftSum_exists_L2_limit P Q D i hD hmD
      (fun s u => H s u i) (fun s => (measurable_pi_apply i).comp (hH s)) C
      (fun s u => hC s u i) (hc i) G k δ hδ hleft
  refine ⟨fun u => ∑ i,I i u,memLp_finsetSum Finset.univ (fun i _ => hI i),?_,?_⟩
  · intro l
    simp_rw [brownianVectorContinuousLeftSum_eq_sum_coordinate,← Finset.sum_sub_distrib]
    exact integrable_sq_finset_sum Finset.univ
      (fun i _ => ((memLp_brownianVectorCoordinatePredictableSum P Q D i hD hmD
        _ (G.monotone l) _ (fun k => (measurable_pi_apply i).comp (hH _)) C
          (fun k u => hC _ u i) _).sub (hI i)).aemeasurable)
      (fun i _ => hIi i l)
  · simp_rw [brownianVectorContinuousLeftSum_eq_sum_coordinate,← Finset.sum_sub_distrib]
    exact tendsto_integral_sq_finset_sum Finset.univ
      (fun i _ l => ((memLp_brownianVectorCoordinatePredictableSum P Q D i hD hmD
        _ (G.monotone l) _ (fun k => (measurable_pi_apply i).comp (hH _)) C
          (fun k u => hC _ u i) _).sub (hI i)).aemeasurable)
      (fun i _ l => hIi i l) (fun i _ => hIlim i)

end SKConstants
