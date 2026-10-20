module
public import SKConstants.BrownianFullPastPredictable
public import SKConstants.ScalarProcessNestedIntegral

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators Topology
namespace SKConstants

abbrev BrownianContinuousPastCoefficient (A : Type*) :=
  (s : ℝ≥0) → A × (Iic s → ℝ) → ℝ

def brownianContinuousCoefficient {A Ω : Type*} (D : ℝ≥0 → Ω → ℝ)
    (H : BrownianContinuousPastCoefficient A) (s : ℝ≥0) (u : A × Ω) : ℝ :=
  H s (u.1,brownianFullPast D s u.2)

def brownianContinuousMeshCoefficient {A : Type*} (H : BrownianContinuousPastCoefficient A)
    (t : ℕ → ℝ≥0) : BrownianStaticPredictableCoefficient A t := fun k => H (t k)

def brownianContinuousLeftSum {A Ω : Type*} (D : ℝ≥0 → Ω → ℝ)
    (H : BrownianContinuousPastCoefficient A) (G : ScalarDyadicNestedGrid) (k l : ℕ) : A × Ω → ℝ :=
  brownianStaticPredictableSum D (G.time l)
    (brownianContinuousMeshCoefficient H (G.time l)) (k*2^l)

lemma integrable_brownianStaticCoefficient_sq_of_bounded {A Ω : Type*}
    [MeasurableSpace A] [MeasurableSpace Ω]
    (P : Measure A) [IsProbabilityMeasure P] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (D : ℝ≥0 → Ω → ℝ) (hD : IsPreBrownianReal D Q) (hmD : ∀ s, Measurable (D s))
    (t : ℕ → ℝ≥0) (H : BrownianStaticPredictableCoefficient A t)
    (hH : ∀ k, Measurable (H k)) (C : ℝ) (hC : ∀ k u, ‖H k u‖ ≤ C) (k : ℕ) :
    Integrable (fun u => brownianStaticCoefficient D t H k u ^ 2) (P.prod Q) := by
  apply (integrable_const (C^2 : ℝ)).mono'
    ((aemeasurable_brownianStaticCoefficient P Q D hD hmD t H hH k).pow_const 2).aestronglyMeasurable
  apply ae_of_all
  intro u
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (hC k _) 2

lemma memLp_brownianStaticPredictableSum {A Ω : Type*}
    [MeasurableSpace A] [MeasurableSpace Ω]
    (P : Measure A) [IsProbabilityMeasure P] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (D : ℝ≥0 → Ω → ℝ) (hD : IsPreBrownianReal D Q) (hmD : ∀ s, Measurable (D s))
    (t : ℕ → ℝ≥0) (ht : Monotone t) (H : BrownianStaticPredictableCoefficient A t)
    (hH : ∀ k, Measurable (H k)) (C : ℝ) (hC : ∀ k u, ‖H k u‖ ≤ C) (n : ℕ) :
    MemLp (brownianStaticPredictableSum D t H n) 2 (P.prod Q) := by
  have hi := brownianStaticPredictableSum_L2_isometry P Q D hD hmD t ht H hH
    (integrable_brownianStaticCoefficient_sq_of_bounded P Q D hD hmD t H hH C hC) n
  have hm := aemeasurable_predictableGaussianSum (P.prod Q)
    (fun k u => brownianMeshIncrement D t k u.2) (brownianStaticCoefficient D t H)
    (fun k => ((hmD _).sub (hmD _)).comp measurable_snd |>.aemeasurable)
    (aemeasurable_brownianStaticCoefficient P Q D hD hmD t H hH) n
  exact (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).2 hi.1

def brownianContinuousDifferenceCoefficient {A : Type*}
    (H : BrownianContinuousPastCoefficient A) (G : ScalarDyadicNestedGrid) (m l : ℕ) :
    BrownianStaticPredictableCoefficient A (G.time (m+l)) := fun i u =>
  H (G.time m (i/2^l)) (u.1,brownianPastRestrict (G.left_le m l i) u.2) -
    H (G.time l (i/2^m)) (u.1,brownianPastRestrict (by
      simpa only [Nat.add_comm l m] using G.left_le l m i) u.2)

lemma measurable_brownianContinuousDifferenceCoefficient {A : Type*} [MeasurableSpace A]
    (H : BrownianContinuousPastCoefficient A) (hH : ∀ s, Measurable (H s))
    (G : ScalarDyadicNestedGrid) (m l i : ℕ) :
    Measurable (brownianContinuousDifferenceCoefficient H G m l i) := by
  exact ((hH _).comp (measurable_fst.prodMk
    ((measurable_brownianPastRestrict _).comp measurable_snd))).sub
    ((hH _).comp (measurable_fst.prodMk
      ((measurable_brownianPastRestrict _).comp measurable_snd)))

lemma brownianContinuousLeftSum_refinement {A Ω : Type*} (D : ℝ≥0 → Ω → ℝ)
    (H : BrownianContinuousPastCoefficient A) (G : ScalarDyadicNestedGrid) (k l d : ℕ)
    (u : A × Ω) :
    brownianContinuousLeftSum D H G k l u =
      ∑ i ∈ Finset.range (k*2^(l+d)), brownianContinuousCoefficient D H
        (G.time l (i/2^d)) u * brownianMeshIncrement D (G.time (l+d)) i u.2 := by
  let F : ℕ → ℝ := fun a => brownianContinuousCoefficient D H (G.time l a) u
  let M : ℕ → ℝ := fun i => D (G.time (l+d) i) u.2
  calc
    _ = ∑ a ∈ Finset.range (k*2^l), F a * (M ((a+1)*2^d)-M (a*2^d)) := by
      rw [brownianContinuousLeftSum,brownianStaticPredictableSum,
        predictableGaussianSum_eq_range_sum]
      simp only [F,M,ScalarDyadicNestedGrid.embed]
      rfl
    _ = ∑ i ∈ Finset.range ((k*2^l)*2^d), F (i/2^d)*(M (i+1)-M i) :=
      sum_weighted_refinement F M _ _ (by positivity)
    _ = _ := by simp only [pow_add,← Nat.mul_assoc]; rfl

lemma brownianContinuousLeftSum_difference_eq {A Ω : Type*} (D : ℝ≥0 → Ω → ℝ)
    (H : BrownianContinuousPastCoefficient A) (G : ScalarDyadicNestedGrid) (k m l : ℕ)
    (u : A × Ω) :
    brownianContinuousLeftSum D H G k m u - brownianContinuousLeftSum D H G k l u =
      brownianStaticPredictableSum D (G.time (m+l))
        (brownianContinuousDifferenceCoefficient H G m l) (k*2^(m+l)) u := by
  have hm := brownianContinuousLeftSum_refinement D H G k m l u
  have hl := brownianContinuousLeftSum_refinement D H G k l m u
  rw [Nat.add_comm l m] at hl
  rw [hm,hl,brownianStaticPredictableSum,predictableGaussianSum_eq_range_sum,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [brownianStaticCoefficient,brownianContinuousDifferenceCoefficient,
    brownianContinuousCoefficient,brownianPastRestrict_fullPast]
  ring

lemma brownianContinuousLeftSum_difference_isometry {A Ω : Type*}
    [MeasurableSpace A] [MeasurableSpace Ω]
    (P : Measure A) [IsProbabilityMeasure P] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (D : ℝ≥0 → Ω → ℝ) (hD : IsPreBrownianReal D Q) (hmD : ∀ s, Measurable (D s))
    (H : BrownianContinuousPastCoefficient A) (hH : ∀ s, Measurable (H s))
    (C : ℝ) (hC : ∀ s u, ‖H s u‖ ≤ C)
    (G : ScalarDyadicNestedGrid) (k m l : ℕ) :
    (∫ u, (brownianContinuousLeftSum D H G k m u -
      brownianContinuousLeftSum D H G k l u)^2 ∂P.prod Q) =
      ∑ i : Fin (k*2^(m+l)), (brownianMeshVariance (G.time (m+l)) i : ℝ) *
        ∫ u, (brownianContinuousCoefficient D H (G.time m (i/2^l)) u -
          brownianContinuousCoefficient D H (G.time l (i/2^m)) u)^2 ∂P.prod Q := by
  have hbound : ∀ i u, ‖brownianContinuousDifferenceCoefficient H G m l i u‖ ≤ 2*C := by
    intro i u
    exact (norm_sub_le _ _).trans ((add_le_add (hC _ _) (hC _ _)).trans_eq (by ring))
  have hisq := integrable_brownianStaticCoefficient_sq_of_bounded P Q D hD hmD _ _
    (measurable_brownianContinuousDifferenceCoefficient H hH G m l) (2*C) hbound
  simp_rw [brownianContinuousLeftSum_difference_eq]
  rw [(brownianStaticPredictableSum_L2_isometry P Q D hD hmD _ (G.monotone (m+l)) _
    (measurable_brownianContinuousDifferenceCoefficient H hH G m l) hisq _).2.2]
  rw [brownianStaticPredictableVariation,integral_predictableGaussianVariation _ _ _ hisq]
  rfl

lemma continuous_expected_sq_difference_of_bounded {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ)
    (hm : ∀ s, AEStronglyMeasurable (X s) P) (hc : ∀ᵐ ω ∂P, Continuous (fun s => X s ω))
    (C : ℝ) (hC : ∀ s ω, ‖X s ω‖ ≤ C) :
    Continuous (fun p : ℝ≥0 × ℝ≥0 => ∫ ω, (X p.1 ω-X p.2 ω)^2 ∂P) := by
  apply continuous_of_dominated (bound := fun _ => (2*C)^2)
  · intro p
    exact ((hm p.1).sub (hm p.2)).pow 2
  · intro p
    apply ae_of_all
    intro ω
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans
      (by linarith [hC p.1 ω,hC p.2 ω])) 2
  · exact integrable_const _
  · filter_upwards [hc] with ω hω
    exact ((hω.comp continuous_fst).sub (hω.comp continuous_snd)).pow 2

lemma expected_sq_difference_uniform_small_of_bounded {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ)
    (hm : ∀ s, AEStronglyMeasurable (X s) P) (hc : ∀ᵐ ω ∂P, Continuous (fun s => X s ω))
    (C : ℝ) (hC : ∀ s ω, ‖X s ω‖ ≤ C) (T : ℝ≥0) (ε : ℝ) (hε : 0 < ε) :
    ∃ η > 0, ∀ s ≤ T, ∀ t ≤ T, |(s : ℝ)-t| < η →
      (∫ ω, (X s ω-X t ω)^2 ∂P) < ε := by
  let F : ℝ≥0 × ℝ≥0 → ℝ := fun p => ∫ ω, (X p.1 ω-X p.2 ω)^2 ∂P
  have hu : UniformContinuousOn F ((Icc 0 T) ×ˢ (Icc 0 T)) :=
    (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous
      (continuous_expected_sq_difference_of_bounded P X hm hc C hC).continuousOn
  obtain ⟨η,hη,hF⟩ := Metric.uniformContinuousOn_iff.mp hu ε hε
  refine ⟨η,hη,fun s hs t ht hst => ?_⟩
  have hdist : dist (s,t) (s,s) < η := by
    rw [Prod.dist_eq,dist_self,NNReal.dist_eq,max_eq_right (abs_nonneg ((t : ℝ)-s)),abs_sub_comm]
    exact hst
  have he := hF (s,t) ⟨⟨by positivity,hs⟩,⟨by positivity,ht⟩⟩
    (s,s) ⟨⟨by positivity,hs⟩,⟨by positivity,hs⟩⟩ hdist
  have hz : F (s,s) = 0 := by simp [F]
  rw [hz,Real.dist_eq,sub_zero] at he
  exact (le_abs_self _).trans_lt he

theorem brownianContinuousLeftSum_L2_cauchy {A Ω : Type*}
    [MeasurableSpace A] [MeasurableSpace Ω]
    (P : Measure A) [IsProbabilityMeasure P] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (D : ℝ≥0 → Ω → ℝ) (hD : IsPreBrownianReal D Q) (hmD : ∀ s, Measurable (D s))
    (H : BrownianContinuousPastCoefficient A) (hH : ∀ s, Measurable (H s))
    (C : ℝ) (hC : ∀ s u, ‖H s u‖ ≤ C)
    (hc : ∀ᵐ u ∂P.prod Q, Continuous (fun s => brownianContinuousCoefficient D H s u))
    (G : ScalarDyadicNestedGrid) (k : ℕ) (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (hleft : ∀ l d i, i < k*2^(l+d) →
      |(G.time (l+d) i : ℝ)-G.time l (i/2^d)| ≤ δ l) :
    ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ l ≥ N,
      (∫ u, (brownianContinuousLeftSum D H G k m u-
        brownianContinuousLeftSum D H G k l u)^2 ∂P.prod Q) < ε := by
  intro ε hε
  let T := G.time 0 k
  have hT : 0 < (T : ℝ)+1 := by positivity
  have hm (s : ℝ≥0) : AEStronglyMeasurable (brownianContinuousCoefficient D H s) (P.prod Q) :=
    ((hH s).comp (measurable_fst.prodMk
      ((Measurable.of_eval (fun t : Iic s => hmD t)).comp measurable_snd))).aestronglyMeasurable
  obtain ⟨η,hη,hsmall⟩ := expected_sq_difference_uniform_small_of_bounded (P.prod Q)
    (brownianContinuousCoefficient D H) hm hc C (fun s u => hC s _) T
    (ε/((T : ℝ)+1)) (div_pos hε hT)
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hδ.eventually (eventually_lt_nhds (half_pos hη)))
  refine ⟨N,fun m hm l hl => ?_⟩
  have henergy (i : Fin (k*2^(m+l))) :
      (∫ u, (brownianContinuousCoefficient D H (G.time m (i/2^l)) u-
        brownianContinuousCoefficient D H (G.time l (i/2^m)) u)^2 ∂P.prod Q) ≤
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
  rw [brownianContinuousLeftSum_difference_isometry P Q D hD hmD H hH C hC G k m l]
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

theorem brownianContinuousLeftSum_exists_L2_limit {A Ω : Type*}
    [MeasurableSpace A] [MeasurableSpace Ω]
    (P : Measure A) [IsProbabilityMeasure P] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (D : ℝ≥0 → Ω → ℝ) (hD : IsPreBrownianReal D Q) (hmD : ∀ s, Measurable (D s))
    (H : BrownianContinuousPastCoefficient A) (hH : ∀ s, Measurable (H s))
    (C : ℝ) (hC : ∀ s u, ‖H s u‖ ≤ C)
    (hc : ∀ᵐ u ∂P.prod Q, Continuous (fun s => brownianContinuousCoefficient D H s u))
    (G : ScalarDyadicNestedGrid) (k : ℕ) (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (hleft : ∀ l d i, i < k*2^(l+d) →
      |(G.time (l+d) i : ℝ)-G.time l (i/2^d)| ≤ δ l) :
    ∃ I : A × Ω → ℝ, MemLp I 2 (P.prod Q) ∧
      (∀ l, Integrable (fun u => (brownianContinuousLeftSum D H G k l u-I u)^2) (P.prod Q)) ∧
      Tendsto (fun l => ∫ u, (brownianContinuousLeftSum D H G k l u-I u)^2 ∂P.prod Q)
        atTop (𝓝 0) := by
  have hmem (l : ℕ) : MemLp (brownianContinuousLeftSum D H G k l) 2 (P.prod Q) :=
    memLp_brownianStaticPredictableSum P Q D hD hmD _ (G.monotone l) _
      (fun i => hH _) C (fun i u => hC _ _) _
  let F : ℕ → Lp ℝ 2 (P.prod Q) := fun l => (hmem l).toLp (brownianContinuousLeftSum D H G k l)
  have hcauchy : CauchySeq F := by
    apply Metric.cauchySeq_iff.2
    intro ε hε
    obtain ⟨N,hN⟩ := brownianContinuousLeftSum_L2_cauchy P Q D hD hmD H hH C hC hc G k δ hδ hleft
      (ε^2) (sq_pos_of_pos hε)
    refine ⟨N,fun m hm l hl => ?_⟩
    have he : dist (F m) (F l)^2 =
        ∫ u, (brownianContinuousLeftSum D H G k m u-brownianContinuousLeftSum D H G k l u)^2
          ∂P.prod Q := by
      rw [dist_eq_norm]
      exact norm_toLp_difference_sq_eq_integral (hmem m) (hmem l)
    have hs := hN m hm l hl
    rw [← he] at hs
    nlinarith [show 0 ≤ dist (F m) (F l) from dist_nonneg]
  obtain ⟨I,hI⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨I,Lp.memLp I,fun l => ((hmem l).sub (Lp.memLp I)).integrable_sq,?_⟩
  have hn : Tendsto (fun l => ‖F l-I‖^2) atTop (𝓝 0) := by
    simpa using ((hI.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => I) atTop (𝓝 I))).norm).pow 2
  have he : (fun l => ∫ u, (brownianContinuousLeftSum D H G k l u-I u)^2 ∂P.prod Q) =
      fun l => ‖F l-I‖^2 := by
    funext l
    exact (norm_toLp_sub_sq_eq_integral (hmem l) I).symm
  rw [he]
  exact hn

end SKConstants
