module
public import SKConstants.Completion.LC0.GaussianReflection
public import SKConstants.Completion.LM1b.Statements

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open SKConstantsOAI.ZeroTemperatureSK
open scoped NNReal Topology BigOperators
namespace SKConstants.M1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]

def aggregateBlocks (d m : ℕ) (p : (Fin (d*m) → ℝ) × (Fin (d*m) → ℝ)) :
    (Fin d ⊕ Fin d) → ℝ :=
  Sum.elim (fun k => ∑ i : Fin m, p.1 (finProdFinEquiv (k,i)))
    (fun k => ∑ i : Fin m, p.2 (finProdFinEquiv (k,i)))

theorem measurable_aggregateBlocks (d m : ℕ) : Measurable (aggregateBlocks d m) := by
  apply Measurable.of_eval
  intro k
  cases k <;> simp only [aggregateBlocks, Sum.elim_inl, Sum.elim_inr] <;> fun_prop

theorem aggregateBlocks_reflect (d m : ℕ) (a b : Fin (d*m) → ℝ)
    (p : (Fin (d*m) → ℝ) × (Fin (d*m) → ℝ)) :
    aggregateBlocks d m (reflect a b p) =
      fun k => ∑ j, scalarBlockSplitCoefficients a b k j * Sum.elim p.1 p.2 j := by
  funext k
  cases k with
  | inl k =>
    simp only [scalarBlockSplitCoefficients, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
    rw [scalarBlockSelected_sum, scalarBlockSelected_sum]
    simp only [aggregateBlocks, reflect, Sum.elim_inl, Finset.sum_add_distrib]
  | inr k =>
    simp only [scalarBlockSplitCoefficients, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
    rw [scalarBlockSelected_sum, scalarBlockSelected_sum]
    simp only [aggregateBlocks, reflect, Sum.elim_inr, sub_eq_add_neg, neg_mul,
      Finset.sum_add_distrib, Finset.sum_neg_distrib]

theorem gaussianReflection_aggregate_graph_law (d m : ℕ) (v : Fin (d*m) → ℝ≥0)
    (a b : Fin (d*m) → ℝ) (hab : ∀ i, (a i)^2+(b i)^2 = 1) :
    let μ := (Measure.pi (fun i => gaussianReal 0 (v i))).prod
      (Measure.pi (fun i => gaussianReal 0 (v i)))
    μ.map (fun p => (aggregateBlocks d m p, aggregateBlocks d m (reflect a b p))) =
      μ.map (fun p => (aggregateBlocks d m (reflect a b p), aggregateBlocks d m p)) := by
  have h := congrArg (fun ν => ν.map (Prod.map (aggregateBlocks d m) (aggregateBlocks d m)))
    (gaussianReflection_graph_law v a b hab)
  have hleft : Measurable (fun p : (Fin (d*m) → ℝ) × (Fin (d*m) → ℝ) => (p, reflect a b p)) :=
    measurable_id.prodMk (measurable_reflect a b)
  have hright : Measurable (fun p : (Fin (d*m) → ℝ) × (Fin (d*m) → ℝ) => (reflect a b p, p)) :=
    (measurable_reflect a b).prodMk measurable_id
  dsimp only at h ⊢
  rw [Measure.map_map ((measurable_aggregateBlocks d m).prodMap
      (measurable_aggregateBlocks d m)) hleft,
    Measure.map_map ((measurable_aggregateBlocks d m).prodMap (measurable_aggregateBlocks d m))
      hright] at h
  exact h

def brownianPairIncrements (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (a h : ℝ≥0) (d : ℕ) (u : Ω × A) : (Fin d → ℝ) × (Fin d → ℝ) :=
  (fun j => brownianMeshIncrement W.B (scalarBrownianAffineTime a h) j u.1,
   fun j => brownianMeshIncrement Z.B (scalarBrownianAffineTime a h) j u.2)

theorem measurable_brownianPairIncrements (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (a h : ℝ≥0) (d : ℕ) : Measurable (brownianPairIncrements W Z a h d) := by
  apply Measurable.prodMk
  · exact Measurable.of_eval fun j => ((W.measurable _).sub (W.measurable _)).comp measurable_fst
  · exact Measurable.of_eval fun j => ((Z.measurable _).sub (Z.measurable _)).comp measurable_snd

theorem brownianPairIncrements_law (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (a h : ℝ≥0) (d : ℕ) :
    (W.law.prod Z.law).map (brownianPairIncrements W Z a h d) =
      (Measure.pi (fun _ : Fin d => gaussianReal 0 h)).prod
        (Measure.pi (fun _ : Fin d => gaussianReal 0 h)) := by
  let := W.isProbability
  let := Z.isProbability
  let X : Ω → Fin d → ℝ := fun ω i => brownianMeshIncrement W.B (scalarBrownianAffineTime a h) i ω
  let Y : A → Fin d → ℝ := fun ω i => brownianMeshIncrement Z.B (scalarBrownianAffineTime a h) i ω
  have hx : HasLaw X (Measure.pi (fun _ : Fin d => gaussianReal 0 h)) W.law := by
    simpa only [brownianMeshVariance_scalarBrownianAffineTime] using
      ((brownianMeshIncrement_iIndepFun W.brownian.toIsPreBrownianReal _ (scalarBrownianAffineTime_mono a h)).precomp
        Fin.val_injective).hasLaw_pi
        (fun i : Fin d => brownianMeshIncrement_hasLaw W.brownian.toIsPreBrownianReal _ (scalarBrownianAffineTime_mono a h) i)
  have hy : HasLaw Y (Measure.pi (fun _ : Fin d => gaussianReal 0 h)) Z.law := by
    simpa only [brownianMeshVariance_scalarBrownianAffineTime] using
      ((brownianMeshIncrement_iIndepFun Z.brownian.toIsPreBrownianReal _ (scalarBrownianAffineTime_mono a h)).precomp
        Fin.val_injective).hasLaw_pi
        (fun i : Fin d => brownianMeshIncrement_hasLaw Z.brownian.toIsPreBrownianReal _ (scalarBrownianAffineTime_mono a h) i)
  exact ((indepFun_prod₀ hx.aemeasurable hy.aemeasurable).hasLaw_prod
    (hx.comp (measurePreserving_fst (μ := W.law) (ν := Z.law)).hasLaw)
    (hy.comp (measurePreserving_snd (μ := W.law) (ν := Z.law)).hasLaw)).map_eq

theorem sum_fineBrownianBlock {S : Type*} (B : ℝ≥0 → S → ℝ) (a h : ℝ≥0)
    (d : ℕ) (k : Fin d) (l : ℕ) (ω : S) :
    (∑ i : Fin (2^l), brownianMeshIncrement B (scalarBrownianAffineTime a (h/2^l))
      (finProdFinEquiv (k,i)) ω) =
      B (scalarBrownianAffineTime a h (k.val+1)) ω - B (scalarBrownianAffineTime a h k.val) ω := by
  change (∑ i : Fin (2^l),
    (B (scalarBrownianAffineTime a (h/2^l) (i.val+2^l*k.val+1)) ω -
      B (scalarBrownianAffineTime a (h/2^l) (i.val+2^l*k.val)) ω)) = _
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ =>
    B (scalarBrownianAffineTime a (h/2^l) (i+2^l*k.val+1)) ω -
      B (scalarBrownianAffineTime a (h/2^l) (i+2^l*k.val)) ω)]
  have he (i : ℕ) : i+2^l*k.val+1 = (i+1)+2^l*k.val := by omega
  simp_rw [he]
  rw [Finset.sum_range_sub (fun i : ℕ => B (scalarBrownianAffineTime a (h/2^l) (i+2^l*k.val)) ω) (2^l)]
  have hEnd : 2^l+2^l*k.val = (k.val+1)*2^l := by ring
  have hStart : 0+2^l*k.val = k.val*2^l := by ring
  rw [hEnd, hStart, scalarBrownianAffineTime_dyadic_end, scalarBrownianAffineTime_dyadic_end]

def rawUniformBlockIncrements {d : ℕ} (a h : ℝ≥0)
    (p : ScalarContinuousPath (scalarBrownianAffineTime a h d) ×
      ScalarContinuousPath (scalarBrownianAffineTime a h d)) : (Fin d ⊕ Fin d) → ℝ :=
  Sum.elim (scalarUniformPathBlockIncrement a h p.1) (scalarUniformPathBlockIncrement a h p.2)

theorem measurable_rawUniformBlockIncrements (d : ℕ) (a h : ℝ≥0) :
    Measurable (rawUniformBlockIncrements (d := d) a h) := by
  apply Measurable.of_eval
  intro k
  cases k <;> exact ((ContinuousMap.measurable_eval _).comp (by fun_prop)).sub
    ((ContinuousMap.measurable_eval _).comp (by fun_prop))

theorem aggregateBrownianBlocks_eq_paths (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (a h : ℝ≥0) (d l : ℕ)
    (F G : ScalarContinuousPath (scalarBrownianAffineTime a h d)) (u : Ω × A)
    (hF : ∀ t : Icc (0 : ℝ) (scalarBrownianAffineTime a h d : ℝ), F t = W.B ⟨t,t.property.1⟩ u.1)
    (hG : ∀ t : Icc (0 : ℝ) (scalarBrownianAffineTime a h d : ℝ), G t = Z.B ⟨t,t.property.1⟩ u.2) :
    aggregateBlocks d (2^l) (brownianPairIncrements W Z a (h/2^l) (d*2^l) u) =
      rawUniformBlockIncrements a h (F,G) := by
  funext k
  cases k with
  | inl k =>
    simp only [aggregateBlocks, brownianPairIncrements, rawUniformBlockIncrements, Sum.elim_inl]
    rw [sum_fineBrownianBlock]
    simp only [scalarUniformPathBlockIncrement, hF]
    congr 2
  | inr k =>
    simp only [aggregateBlocks, brownianPairIncrements, rawUniformBlockIncrements, Sum.elim_inr]
    rw [sum_fineBrownianBlock]
    simp only [scalarUniformPathBlockIncrement, hG]
    congr 2

theorem orthogonalUniformBlocks_graph_law (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (a h : ℝ≥0) (d : ℕ)
    (hunit : ∀ v ∈ Icc (0 : ℝ) (scalarBrownianAffineTime a h d : ℝ), (f v)^2+(g v)^2 = 1)
    (F : Ω → ScalarContinuousPath (scalarBrownianAffineTime a h d))
    (G : A → ScalarContinuousPath (scalarBrownianAffineTime a h d))
    (hFm : Measurable F) (hGm : Measurable G)
    (hF : ∀ᵐ ω ∂W.law, ∀ t : Icc (0 : ℝ) (scalarBrownianAffineTime a h d : ℝ), F ω t = W.B ⟨t,t.property.1⟩ ω)
    (hG : ∀ᵐ ω ∂Z.law, ∀ t : Icc (0 : ℝ) (scalarBrownianAffineTime a h d : ℝ), G ω t = Z.B ⟨t,t.property.1⟩ ω) :
    (W.law.prod Z.law).map (fun u =>
      (rawUniformBlockIncrements a h (F u.1,G u.2),
        scalarOrthogonalUniformBlockIncrements f g hf hg a h (F u.1,G u.2))) =
    (W.law.prod Z.law).map (fun u =>
      (scalarOrthogonalUniformBlockIncrements f g hf hg a h (F u.1,G u.2),
        rawUniformBlockIncrements a h (F u.1,G u.2))) := by
  let := W.isProbability
  let := Z.isProbability
  let R (l : ℕ) := brownianPairIncrements W Z a (h/2^l) (d*2^l)
  let aa (l : ℕ) (i : Fin (d*2^l)) := -f (scalarBrownianAffineTime a (h/2^l) i : ℝ)
  let bb (l : ℕ) (i : Fin (d*2^l)) := g (scalarBrownianAffineTime a (h/2^l) i : ℝ)
  let X (l : ℕ) (u : Ω × A) :=
    (aggregateBlocks d (2^l) (R l u), aggregateBlocks d (2^l) (reflect (aa l) (bb l) (R l u)))
  let Y (l : ℕ) (u : Ω × A) := (X l u).swap
  have hX (l : ℕ) : Measurable (X l) :=
    ((measurable_aggregateBlocks d (2^l)).comp (measurable_brownianPairIncrements W Z a (h/2^l) (d*2^l))).prodMk
      ((measurable_aggregateBlocks d (2^l)).comp ((measurable_reflect (aa l) (bb l)).comp
        (measurable_brownianPairIncrements W Z a (h/2^l) (d*2^l))))
  have hY (l : ℕ) : Measurable (Y l) := measurable_swap.comp (hX l)
  have hlaw (l : ℕ) : (W.law.prod Z.law).map (X l) = (W.law.prod Z.law).map (Y l) := by
    have hc (i : Fin (d*2^l)) :
        (scalarBrownianAffineTime a (h/2^l) i : ℝ) ∈ Icc (0 : ℝ) (scalarBrownianAffineTime a h d : ℝ) := by
      refine ⟨(scalarBrownianAffineTime _ _ i).coe_nonneg, ?_⟩
      rw [← scalarBrownianAffineTime_dyadic_end a h d l]
      exact scalarBrownianAffineTime_mono _ _ i.isLt.le
    have he := gaussianReflection_aggregate_graph_law d (2^l) (fun _ => h/2^l)
      (aa l) (bb l) (fun i => by simpa only [aa, bb, neg_sq] using hunit _ (hc i))
    dsimp only at he
    rw [← brownianPairIncrements_law W Z a (h/2^l) (d*2^l)] at he
    have hLeft : Measurable (fun p : (Fin (d*2^l) → ℝ) × (Fin (d*2^l) → ℝ) =>
        (aggregateBlocks d (2^l) p, aggregateBlocks d (2^l) (reflect (aa l) (bb l) p))) :=
      (measurable_aggregateBlocks d (2^l)).prodMk
        ((measurable_aggregateBlocks d (2^l)).comp (measurable_reflect (aa l) (bb l)))
    have hRight : Measurable (fun p : (Fin (d*2^l) → ℝ) × (Fin (d*2^l) → ℝ) =>
        (aggregateBlocks d (2^l) (reflect (aa l) (bb l) p), aggregateBlocks d (2^l) p)) :=
      ((measurable_aggregateBlocks d (2^l)).comp (measurable_reflect (aa l) (bb l))).prodMk
        (measurable_aggregateBlocks d (2^l))
    rw [Measure.map_map
      hLeft
      (measurable_brownianPairIncrements W Z a (h/2^l) (d*2^l)),
      Measure.map_map
        hRight
        (measurable_brownianPairIncrements W Z a (h/2^l) (d*2^l))] at he
    exact he
  have hIn := hFm.prodMap hGm
  have hraw := (measurable_rawUniformBlockIncrements d a h).comp hIn
  have hweighted := (measurable_scalarOrthogonalUniformBlockIncrements f g hf hg a h).comp hIn
  have hlim : ∀ᵐ u ∂W.law.prod Z.law,
      Tendsto (fun l => X l u) atTop (𝓝
        (rawUniformBlockIncrements a h (F u.1,G u.2),
          scalarOrthogonalUniformBlockIncrements f g hf hg a h (F u.1,G u.2))) := by
    filter_upwards [(measurePreserving_fst (μ := W.law) (ν := Z.law)).quasiMeasurePreserving.ae hF,
      (measurePreserving_snd (μ := W.law) (ν := Z.law)).quasiMeasurePreserving.ae hG] with u huF huG
    have hr (l : ℕ) := aggregateBrownianBlocks_eq_paths W Z a h d l (F u.1) (G u.2) u huF huG
    have hw : Tendsto (fun l => aggregateBlocks d (2^l) (reflect (aa l) (bb l) (R l u))) atTop
        (𝓝 (scalarOrthogonalUniformBlockIncrements f g hf hg a h (F u.1,G u.2))) := by
      apply (scalarOrthogonalDyadicBlocks_pathwise_limit f g hf hg a h (F u.1) (G u.2)).congr'
      exact Filter.Eventually.of_forall fun l => by
        symm
        change aggregateBlocks d (2^l) (reflect (aa l) (bb l) (R l u)) = _
        rw [aggregateBlocks_reflect]
        exact scalarOrthogonalDyadicBlocks_eq_pathSums f g W.B Z.B a h (F u.1) (G u.2) u huF huG l
    have hrLim : Tendsto (fun l => aggregateBlocks d (2^l) (R l u)) atTop
        (𝓝 (rawUniformBlockIncrements a h (F u.1,G u.2))) := by
      simp only [R, hr]
      exact tendsto_const_nhds
    exact hrLim.prodMk_nhds hw
  exact scalarLaw_eq_of_ae_tendsto_comparison (W.law.prod Z.law) (W.law.prod Z.law) X Y _ _
    (fun l => (hX l).aemeasurable) (fun l => (hY l).aemeasurable) hlaw
    (hraw.prodMk hweighted).aemeasurable (hweighted.prodMk hraw).aemeasurable hlim
    (hlim.mono fun u hu => continuous_swap.continuousAt.tendsto.comp hu)

end SKConstants.M1
