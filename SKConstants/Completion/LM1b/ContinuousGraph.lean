module
public import SKConstants.Completion.LM1b.FiniteGraphLimits
public import SKConstants.Completion.LM1b.PathFamilyLaw
public import SKConstants.Completion.LC0.BridgeReconstruction

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

theorem primitiveBrownianPairPath_law (W : BrownianSystem Ω) (Z : BrownianSystem A) (H : ℝ≥0) :
    (W.law.prod Z.law).map
      (Prod.map (scalarPrimitiveBrownianPathVersion W H) (scalarPrimitiveBrownianPathVersion Z H)) =
    (scalarPrimitiveBrownianPathLaw W H).prod (scalarPrimitiveBrownianPathLaw Z H) := by
  let := W.isProbability
  let := Z.isProbability
  exact (Measure.map_prod_map W.law Z.law (measurable_scalarPrimitiveBrownianPathVersion W H)
    (measurable_scalarPrimitiveBrownianPathVersion Z H)).symm

theorem weightedPair_fixedUniform_graph_law (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g) (H : ℝ≥0)
    (hunit : ∀ v ∈ Icc (0 : ℝ) (H : ℝ), (f v)^2+(g v)^2 = 1) (n : ℕ) :
    let μ := (scalarPrimitiveBrownianPathLaw W H).prod (scalarPrimitiveBrownianPathLaw Z H)
    μ.map (fun p => (scalarPathUniformIncrements H n p,
      scalarPathUniformIncrements H n (WeightedPair f g hf hg H p))) =
    μ.map (fun p => (scalarPathUniformIncrements H n (WeightedPair f g hf hg H p),
      scalarPathUniformIncrements H n p)) := by
  let H' := scalarBrownianAffineTime 0 (scalarPathUniformStep H n) (n+1)
  have hH : H' = H := scalarPathUniformStep_affine_horizon H n
  let F : Ω → ScalarContinuousPath H' := fun w => scalarPathHorizonCast hH (scalarPrimitiveBrownianPathVersion W H w)
  let G : A → ScalarContinuousPath H' := fun w => scalarPathHorizonCast hH (scalarPrimitiveBrownianPathVersion Z H w)
  have hF : ∀ᵐ w ∂W.law, ∀ t : Icc (0 : ℝ) (H' : ℝ), F w t = W.B ⟨t,t.property.1⟩ w := by
    filter_upwards [scalarPrimitiveBrownianPathVersion_ae W H] with w hw
    intro t
    rw [show F w t = scalarPrimitiveBrownianPathVersion W H w
      ⟨t,t.property.1,by simpa only [hH] using t.property.2⟩ from scalarPathHorizonCast_eval hH _ t]
    exact hw _
  have hG : ∀ᵐ w ∂Z.law, ∀ t : Icc (0 : ℝ) (H' : ℝ), G w t = Z.B ⟨t,t.property.1⟩ w := by
    filter_upwards [scalarPrimitiveBrownianPathVersion_ae Z H] with w hw
    intro t
    rw [show G w t = scalarPrimitiveBrownianPathVersion Z H w
      ⟨t,t.property.1,by simpa only [hH] using t.property.2⟩ from scalarPathHorizonCast_eval hH _ t]
    exact hw _
  have he := orthogonalUniformBlocks_graph_law W Z f g hf hg 0 (scalarPathUniformStep H n) (n+1)
    (fun v hv => hunit v (by simpa only [scalarPathUniformStep_affine_horizon] using hv)) F G
    ((measurable_scalarPathHorizonCast hH).comp (measurable_scalarPrimitiveBrownianPathVersion W H))
    ((measurable_scalarPathHorizonCast hH).comp (measurable_scalarPrimitiveBrownianPathVersion Z H)) hF hG
  have hraw (p : ScalarContinuousPath H × ScalarContinuousPath H) :
      rawUniformBlockIncrements 0 (scalarPathUniformStep H n)
        (scalarPathHorizonCast hH p.1, scalarPathHorizonCast hH p.2) = scalarPathUniformIncrements H n p := by
    funext j
    cases j <;> simp only [rawUniformBlockIncrements, scalarPathUniformIncrements, Sum.elim_inl, Sum.elim_inr]
    · exact scalarUniformPathBlockIncrement_cast H n p.1 _
    · exact scalarUniformPathBlockIncrement_cast H n p.2 _
  have heNative : (W.law.prod Z.law).map (fun u =>
      (scalarPathUniformIncrements H n (scalarPrimitiveBrownianPathVersion W H u.1, scalarPrimitiveBrownianPathVersion Z H u.2),
        scalarPathUniformIncrements H n (WeightedPair f g hf hg H
          (scalarPrimitiveBrownianPathVersion W H u.1, scalarPrimitiveBrownianPathVersion Z H u.2)))) =
      (W.law.prod Z.law).map (fun u =>
      (scalarPathUniformIncrements H n (WeightedPair f g hf hg H
          (scalarPrimitiveBrownianPathVersion W H u.1, scalarPrimitiveBrownianPathVersion Z H u.2)),
        scalarPathUniformIncrements H n (scalarPrimitiveBrownianPathVersion W H u.1, scalarPrimitiveBrownianPathVersion Z H u.2))) := by
    calc
      _ = (W.law.prod Z.law).map (fun u =>
          (rawUniformBlockIncrements 0 (scalarPathUniformStep H n) (F u.1,G u.2),
            scalarOrthogonalUniformBlockIncrements f g hf hg 0 (scalarPathUniformStep H n) (F u.1,G u.2))) := by
        congr 1
        funext u
        exact Prod.ext (hraw (scalarPrimitiveBrownianPathVersion W H u.1,
          scalarPrimitiveBrownianPathVersion Z H u.2)).symm
          (scalarOrthogonalUniformBlockIncrements_cast H n f g hf hg
            (scalarPrimitiveBrownianPathVersion W H u.1, scalarPrimitiveBrownianPathVersion Z H u.2)).symm
      _ = _ := he
      _ = _ := by
        congr 1
        funext u
        exact Prod.ext (scalarOrthogonalUniformBlockIncrements_cast H n f g hf hg
          (scalarPrimitiveBrownianPathVersion W H u.1, scalarPrimitiveBrownianPathVersion Z H u.2))
          (hraw (scalarPrimitiveBrownianPathVersion W H u.1, scalarPrimitiveBrownianPathVersion Z H u.2))
  have hLeft : Measurable (fun p : ScalarContinuousPath H × ScalarContinuousPath H =>
      (scalarPathUniformIncrements H n p, scalarPathUniformIncrements H n (WeightedPair f g hf hg H p))) :=
    (measurable_scalarPathUniformIncrements H n).prodMk
      ((measurable_scalarPathUniformIncrements H n).comp (measurable_WeightedPair f g hf hg H))
  have hRight : Measurable (fun p : ScalarContinuousPath H × ScalarContinuousPath H =>
      (scalarPathUniformIncrements H n (WeightedPair f g hf hg H p), scalarPathUniformIncrements H n p)) :=
    ((measurable_scalarPathUniformIncrements H n).comp (measurable_WeightedPair f g hf hg H)).prodMk
      (measurable_scalarPathUniformIncrements H n)
  dsimp only
  rw [← primitiveBrownianPairPath_law W Z H,
    Measure.map_map hLeft ((measurable_scalarPrimitiveBrownianPathVersion W H).prodMap
      (measurable_scalarPrimitiveBrownianPathVersion Z H)),
    Measure.map_map hRight ((measurable_scalarPrimitiveBrownianPathVersion W H).prodMap
      (measurable_scalarPrimitiveBrownianPathVersion Z H))]
  exact heNative

def fourPathFamily (H : ℝ≥0)
    (p : (ScalarContinuousPath H × ScalarContinuousPath H) ×
      (ScalarContinuousPath H × ScalarContinuousPath H)) : Bool × Bool → ScalarContinuousPath H
  | (false,false) => p.1.1
  | (false,true) => p.1.2
  | (true,false) => p.2.1
  | (true,true) => p.2.2

theorem fourPathFamily_measurableEmbedding (H : ℝ≥0) : MeasurableEmbedding (fourPathFamily H) := by
  have hsurj : Function.Surjective (fourPathFamily H) := by
    intro z
    refine ⟨((z (false,false), z (false,true)), (z (true,false), z (true,true))), ?_⟩
    funext j
    rcases j with ⟨a,b⟩
    cases a <;> cases b <;> rfl
  apply MeasurableEmbedding.of_measurable_inverse
    (g := fun z => ((z (false,false), z (false,true)), (z (true,false), z (true,true))))
  · apply Measurable.of_eval
    rintro ⟨a,b⟩
    cases a <;> cases b <;> fun_prop [fourPathFamily]
  · rw [hsurj.range_eq]
    exact MeasurableSet.univ
  · fun_prop
  · intro p
    rfl

theorem continuousGraphExchange_holds (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g) (H : ℝ≥0)
    (hunit : ∀ v ∈ Icc (0 : ℝ) (H : ℝ), (f v)^2+(g v)^2 = 1) :
    ContinuousGraphExchangeStatement W Z f g hf hg H := by
  let μ := (scalarPrimitiveBrownianPathLaw W H).prod (scalarPrimitiveBrownianPathLaw Z H)
  let T := WeightedPair f g hf hg H
  have hT := measurable_WeightedPair f g hf hg H
  have hLeft : Measurable (fun p : ScalarContinuousPath H × ScalarContinuousPath H => (p,T p)) :=
    measurable_id.prodMk hT
  have hRight : Measurable (fun p : ScalarContinuousPath H × ScalarContinuousPath H => (T p,p)) :=
    hT.prodMk measurable_id
  have hz : ∀ᵐ p ∂μ, p.1 ⟨0,le_rfl,H.coe_nonneg⟩ = 0 ∧ p.2 ⟨0,le_rfl,H.coe_nonneg⟩ = 0 := by
    filter_upwards [(measurePreserving_fst (μ := scalarPrimitiveBrownianPathLaw W H)
      (ν := scalarPrimitiveBrownianPathLaw Z H)).quasiMeasurePreserving.ae
        (scalarPrimitiveBrownianPathLaw_zero_ae W H),
      (measurePreserving_snd (μ := scalarPrimitiveBrownianPathLaw W H)
        (ν := scalarPrimitiveBrownianPathLaw Z H)).quasiMeasurePreserving.ae
        (scalarPrimitiveBrownianPathLaw_zero_ae Z H)] with p h1 h2
    exact ⟨h1,h2⟩
  change μ.map (fun p => (p,T p)) = μ.map (fun p => (T p,p))
  by_cases hH : 0 < H
  · apply (fourPathFamily_measurableEmbedding H).map_injective
    rw [Measure.map_map (fourPathFamily_measurableEmbedding H).measurable hLeft,
      Measure.map_map (fourPathFamily_measurableEmbedding H).measurable hRight]
    apply pathFamily_law_of_uniform_increments μ μ H hH
      (fourPathFamily H ∘ (fun p => (p,T p))) (fourPathFamily H ∘ (fun p => (T p,p)))
      ((fourPathFamily_measurableEmbedding H).measurable.comp hLeft)
      ((fourPathFamily_measurableEmbedding H).measurable.comp hRight)
    · filter_upwards [hz] with p hp
      rintro ⟨a,b⟩
      cases a <;> cases b <;> simp [fourPathFamily, T, WeightedPair,
        scalarTwoDriverWeightedPath, scalarOrthogonalWeightedAuxPath, scalarStieltjesWeightedPath, hp.1, hp.2]
    · filter_upwards [hz] with p hp
      rintro ⟨a,b⟩
      cases a <;> cases b <;> simp [fourPathFamily, T, WeightedPair,
        scalarTwoDriverWeightedPath, scalarOrthogonalWeightedAuxPath, scalarStieltjesWeightedPath, hp.1, hp.2]
    · intro n
      let J (p : ((Fin (n+1) ⊕ Fin (n+1)) → ℝ) × ((Fin (n+1) ⊕ Fin (n+1)) → ℝ)) :
          (Bool × Bool) × Fin (n+1) → ℝ := fun j => match j.1 with
        | (false,false) => p.1 (.inl j.2)
        | (false,true) => p.1 (.inr j.2)
        | (true,false) => p.2 (.inl j.2)
        | (true,true) => p.2 (.inr j.2)
      have hJ : Measurable J := by
        apply Measurable.of_eval
        rintro ⟨⟨a,b⟩,j⟩
        cases a <;> cases b <;> simp only [J] <;> fun_prop
      have hIncL : Measurable (fun p : ScalarContinuousPath H × ScalarContinuousPath H =>
          (scalarPathUniformIncrements H n p, scalarPathUniformIncrements H n (T p))) :=
        (measurable_scalarPathUniformIncrements H n).prodMk
          ((measurable_scalarPathUniformIncrements H n).comp hT)
      have hIncR : Measurable (fun p : ScalarContinuousPath H × ScalarContinuousPath H =>
          (scalarPathUniformIncrements H n (T p), scalarPathUniformIncrements H n p)) :=
        ((measurable_scalarPathUniformIncrements H n).comp hT).prodMk
          (measurable_scalarPathUniformIncrements H n)
      have he := congrArg (fun ν => ν.map J) (weightedPair_fixedUniform_graph_law W Z f g hf hg H hunit n)
      rw [Measure.map_map hJ hIncL, Measure.map_map hJ hIncR] at he
      convert he using 1 <;> congr 1 <;> funext p j <;> rcases j with ⟨⟨a,b⟩,j⟩ <;>
        cases a <;> cases b <;> rfl
  · have hH0 : H = 0 := le_antisymm (le_of_not_gt hH) zero_le
    apply Measure.map_congr
    filter_upwards [hz] with p hp
    have hTp : T p = p := by
      have ht (t : Icc (0 : ℝ) (H : ℝ)) : t = ⟨0,le_rfl,H.coe_nonneg⟩ := by
        apply Subtype.ext
        have h0 : (H : ℝ) = 0 := congrArg (fun x : ℝ≥0 => (x : ℝ)) hH0
        linarith [t.property.1,t.property.2]
      apply Prod.ext <;> apply ContinuousMap.ext <;> intro t <;>
        simp [T, WeightedPair, scalarTwoDriverWeightedPath, scalarOrthogonalWeightedAuxPath,
          scalarStieltjesWeightedPath, ht t, hp.1, hp.2]
    exact Prod.ext hTp.symm hTp

theorem weightedPairInvolution_holds (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g) (H : ℝ≥0)
    (hunit : ∀ v ∈ Icc (0 : ℝ) (H : ℝ), (f v)^2+(g v)^2 = 1) :
    WeightedPairInvolutionStatement W Z f g hf hg H := by
  let μ := (scalarPrimitiveBrownianPathLaw W H).prod (scalarPrimitiveBrownianPathLaw Z H)
  let T := WeightedPair f g hf hg H
  have hT := measurable_WeightedPair f g hf hg H
  have hLeft : Measurable (fun p : ScalarContinuousPath H × ScalarContinuousPath H => (p,T p)) :=
    measurable_id.prodMk hT
  have hRight : Measurable (fun p : ScalarContinuousPath H × ScalarContinuousPath H => (T p,p)) :=
    hT.prodMk measurable_id
  have hset : MeasurableSet {p : (ScalarContinuousPath H × ScalarContinuousPath H) ×
      (ScalarContinuousPath H × ScalarContinuousPath H) | T p.1 = p.2} :=
    measurableSet_eq_fun (hT.comp measurable_fst) measurable_snd
  have he : ∀ᵐ p ∂μ.map (fun p => (p,T p)), T p.1 = p.2 :=
    (ae_map_iff hLeft.aemeasurable hset).mpr (Filter.Eventually.of_forall fun _ => rfl)
  have hgraph := continuousGraphExchange_holds W Z f g hf hg H hunit
  change μ.map (fun p => (p,T p)) = μ.map (fun p => (T p,p)) at hgraph
  rw [hgraph] at he
  exact (ae_map_iff hRight.aemeasurable hset).mp he

theorem actualParisi_continuousGraphExchange (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (H : ℝ≥0) :
    ContinuousGraphExchangeStatement W Z (actualParisiNegativeRhoStieltjes W β hβ)
      (actualParisiSigmaStieltjes W β hβ) (continuous_actualParisiNegativeRhoStieltjes W β hβ)
      (continuous_actualParisiSigmaStieltjes W β hβ) H :=
  continuousGraphExchange_holds W Z _ _ _ _ H
    (fun v _ => actualParisiStieltjesCoefficients_unit W β hβ v)

theorem actualParisi_weightedPairInvolution (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (H : ℝ≥0) :
    WeightedPairInvolutionStatement W Z (actualParisiNegativeRhoStieltjes W β hβ)
      (actualParisiSigmaStieltjes W β hβ) (continuous_actualParisiNegativeRhoStieltjes W β hβ)
      (continuous_actualParisiSigmaStieltjes W β hβ) H :=
  weightedPairInvolution_holds W Z _ _ _ _ H
    (fun v _ => actualParisiStieltjesCoefficients_unit W β hβ v)

end SKConstants.M1
