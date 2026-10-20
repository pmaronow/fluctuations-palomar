module

public import SKConstants.ParisiPicardReflection
public import SKConstants.ScalarProcessSeedReconstruction
public import SKConstants.ScalarProcessInnovationFiltration
import Mathlib.Tactic

/-!
# Actual measurable forward scalar Picard path callbacks

The finite-horizon solution is the literal convergent bounded-Lipschitz
Picard construction from the vendored OpenAI formalization. It is jointly
measurable in its seed and continuous driver, satisfies the actual integral
equation for every input, and depends only on each input prefix. The actual
`tanh` specialization is a right inverse of the innovation transform on
every continuous path. Genuine Brownian finite-dimensional laws identify
its observation path law with the literal hidden-spin scalar channel.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace SKConstants
open SKConstantsOAI.ZeroTemperatureSK
set_option backward.isDefEq.respectTransparency false

/-- Extend a continuous finite-horizon innovation and add its initial field. -/
def scalarContinuousSeedDriver (T : ℝ≥0) (t : ℝ≥0)
    (p : ℝ × ScalarContinuousPath T) : ℝ :=
  p.1 + IccExtend T.coe_nonneg p.2 (t : ℝ)

theorem continuous_scalarContinuousSeedDriver (T : ℝ≥0) :
    Continuous (fun p : ℝ≥0 × (ℝ × ScalarContinuousPath T) =>
      scalarContinuousSeedDriver T p.1 p.2) := by
  unfold scalarContinuousSeedDriver IccExtend
  exact (continuous_fst.comp continuous_snd).add
    (continuous_eval.comp ((continuous_snd.comp continuous_snd).prodMk
      ((continuous_projIcc (h := T.coe_nonneg)).comp
        (continuous_subtype_val.comp continuous_fst))))

def scalarPathFiltration (T : ℝ≥0) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (ℝ × ScalarContinuousPath T)) :=
  Filtration.const ℝ≥0 _ le_rfl

theorem scalarContinuousSeedDriver_progressive (T : ℝ≥0) :
    IsProgressive (scalarPathFiltration T) (scalarContinuousSeedDriver T) := by
  intro t
  exact (continuous_scalarContinuousSeedDriver T).measurable.comp
    ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd)

/-- The literal convergent Picard solution on a continuous finite driver path. -/
def scalarForwardPicardPath (b : BoundedLipschitzDrift) (T : ℝ≥0)
    (p : ℝ × ScalarContinuousPath T) : ScalarContinuousPath T where
  toFun t := b.solution (scalarContinuousSeedDriver T) ⟨t, t.property.1⟩ p
  continuous_toFun :=
    (b.solution_continuous (scalarPathFiltration T)
      (scalarContinuousSeedDriver_progressive T)
      ((continuous_scalarContinuousSeedDriver T).comp
        (continuous_id.prodMk continuous_const))).comp
      (continuous_subtype_val.subtype_mk (fun t => t.property.1))

theorem measurable_scalarForwardPicardPath (b : BoundedLipschitzDrift) (T : ℝ≥0) :
    Measurable (scalarForwardPicardPath b T) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  exact (b.solution_progressive (scalarPathFiltration T)
    (scalarContinuousSeedDriver_progressive T)).adapted ⟨t,t.property.1⟩

theorem scalarForwardPicardPath_integral_equation (b : BoundedLipschitzDrift) (T : ℝ≥0)
    (p : ℝ × ScalarContinuousPath T) (t : Icc (0 : ℝ) (T : ℝ)) :
    scalarForwardPicardPath b T p t = p.1 + p.2 t +
      ∫ s in (0 : ℝ)..(t : ℝ), b.f s
        (IccExtend T.coe_nonneg (scalarForwardPicardPath b T p) s) := by
  have he := b.solution_eq (scalarPathFiltration T)
    (scalarContinuousSeedDriver_progressive T) (⟨(t : ℝ), t.property.1⟩ : ℝ≥0) p
  change scalarForwardPicardPath b T p t =
    scalarContinuousSeedDriver T (⟨(t : ℝ), t.property.1⟩ : ℝ≥0) p +
      ∫ s in (0 : ℝ)..(t : ℝ), b.f (Real.toNNReal s)
        (b.solution (scalarContinuousSeedDriver T) (Real.toNNReal s) p) at he
  rw [he]
  congr 1
  · change p.1 + p.2 (projIcc 0 (T : ℝ) T.coe_nonneg (t : ℝ)) = p.1 + p.2 t
    rw [projIcc_of_mem _ t.property]
  · apply intervalIntegral.integral_congr
    intro s hs
    have hs0 : 0 ≤ s := by simpa only [min_eq_left t.property.1] using hs.1
    have hsT : s ≤ (T : ℝ) := le_trans
      (by simpa only [max_eq_right t.property.1] using hs.2) t.property.2
    change b.f (Real.toNNReal s)
      (b.solution (scalarContinuousSeedDriver T) (Real.toNNReal s) p) = _
    rw [Real.coe_toNNReal s hs0]
    simp only [IccExtend, Function.comp_apply, projIcc_of_mem _ ⟨hs0,hsT⟩,
      scalarForwardPicardPath, ContinuousMap.coe_mk]
    congr 1
    congr 1
    exact Subtype.ext (Real.coe_toNNReal s hs0)

/-- The actual continuation drift. -/
def scalarTanhDrift : BoundedLipschitzDrift where
  f _ x := Real.tanh x
  bound := 1
  lip := 1
  measurable := lipschitzWith_scalarTanh.continuous.measurable.comp measurable_snd
  bounded _ x := (abs_le.mpr ⟨(Real.neg_one_lt_tanh x).le, (Real.tanh_lt_one x).le⟩)
  lipschitz _ := lipschitzWith_scalarTanh

/-- The Picard callback gives a true right inverse for every continuous
innovation path, rather than relying on an assumed range membership. -/
theorem scalarForwardPicardPath_innovation (T : ℝ≥0) (z : ℝ)
    (f : ScalarContinuousPath T) :
    scalarInnovationPath T z (scalarForwardPicardPath scalarTanhDrift T (z,f)) = f := by
  ext t
  have he := scalarForwardPicardPath_integral_equation scalarTanhDrift T (z,f) t
  change scalarForwardPicardPath scalarTanhDrift T (z,f) t - z -
    (∫ s in (0 : ℝ)..(t : ℝ), Real.tanh
      (IccExtend T.coe_nonneg (scalarForwardPicardPath scalarTanhDrift T (z,f)) s)) = f t
  change scalarForwardPicardPath scalarTanhDrift T (z,f) t = z + f t +
    (∫ s in (0 : ℝ)..(t : ℝ), Real.tanh
      (IccExtend T.coe_nonneg (scalarForwardPicardPath scalarTanhDrift T (z,f)) s)) at he
  linarith

theorem scalarSeedObservationPathFromInnovation_eq_picard (T : ℝ≥0) (z : ℝ)
    (f : ScalarContinuousPath T) :
    scalarSeedObservationPathFromInnovation T (z,f) =
      scalarForwardPicardPath scalarTanhDrift T (z,f) := by
  calc
    _ = scalarSeedObservationPathFromInnovation T
        (z, scalarInnovationPath T z (scalarForwardPicardPath scalarTanhDrift T (z,f))) := by
      rw [scalarForwardPicardPath_innovation]
    _ = _ := scalarSeedObservationPathFromInnovation_leftInverse T z _

/-- Literal Picard iterates on a finite time prefix ignore all future driver
values. This is a deterministic property, with no filtration premise. -/
theorem correctionIter_congr_prefix {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    (b : BoundedLipschitzDrift) (B : ℝ≥0 → Ω → ℝ) (C : ℝ≥0 → Ω' → ℝ)
    (ω : Ω) (ω' : Ω') (T : ℝ≥0) (h : ∀ t ≤ T, B t ω = C t ω')
    (n : ℕ) (t : ℝ≥0) (ht : t ≤ T) :
    b.correctionIter B n t ω = b.correctionIter C n t ω' := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
    simp only [BoundedLipschitzDrift.correctionIter, timePrimitive,
      BoundedLipschitzDrift.action]
    apply intervalIntegral.integral_congr
    intro s hs
    have hs0 : 0 ≤ s := by simpa only [min_eq_left t.coe_nonneg] using hs.1
    have hst : Real.toNNReal s ≤ t := by
      rw [Real.toNNReal_le_iff_le_coe]
      simpa only [max_eq_right t.coe_nonneg] using hs.2
    dsimp only
    rw [h _ (hst.trans ht), ih _ (hst.trans ht)]

/-- The convergent Picard solution has the same exact finite-prefix
causality as every iterate. -/
theorem solution_congr_prefix {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    (b : BoundedLipschitzDrift) (B : ℝ≥0 → Ω → ℝ) (C : ℝ≥0 → Ω' → ℝ)
    (ω : Ω) (ω' : Ω') (T : ℝ≥0) (h : ∀ t ≤ T, B t ω = C t ω')
    (t : ℝ≥0) (ht : t ≤ T) :
    b.solution B t ω = b.solution C t ω' := by
  have he : (fun n => b.correctionIter B n t ω) =
      fun n => b.correctionIter C n t ω' :=
    funext (fun n => correctionIter_congr_prefix b B C ω ω' T h n t ht)
  simp only [BoundedLipschitzDrift.solution, BoundedLipschitzDrift.correction,
    h t ht, he]

/-- The jointly measurable path callback is causal for every finite prefix. -/
theorem scalarForwardPicardPath_congr_prefix (b : BoundedLipschitzDrift)
    (T : ℝ≥0) (z : ℝ) (f g : ScalarContinuousPath T) (a : ℝ≥0) (ha : a ≤ T)
    (hfg : ∀ t : Icc (0 : ℝ) (T : ℝ), (t : ℝ) ≤ a → f t = g t)
    (t : Icc (0 : ℝ) (T : ℝ)) (ht : (t : ℝ) ≤ a) :
    scalarForwardPicardPath b T (z,f) t = scalarForwardPicardPath b T (z,g) t := by
  apply solution_congr_prefix b (scalarContinuousSeedDriver T)
    (scalarContinuousSeedDriver T) (z,f) (z,g) a _
    (⟨t,t.property.1⟩ : ℝ≥0) ht
  intro s hs
  change z + f (projIcc 0 (T : ℝ) T.coe_nonneg s) =
    z + g (projIcc 0 (T : ℝ) T.coe_nonneg s)
  have hsT : (s : ℝ) ≤ T := hs.trans ha
  rw [projIcc_of_mem _ ⟨s.coe_nonneg,hsT⟩]
  exact congrArg (z + ·) (hfg ⟨s,s.coe_nonneg,hsT⟩ hs)

/-- Uniqueness identifies the actual Picard callback with every continuous
solution of the innovation equation. -/
theorem scalarForwardPicardPath_reconstructs (T : ℝ≥0) (z : ℝ)
    (f : ScalarContinuousPath T) :
    scalarForwardPicardPath scalarTanhDrift T (z,scalarInnovationPath T z f) = f := by
  apply scalarInnovationPath_injective T z
  exact scalarForwardPicardPath_innovation T z (scalarInnovationPath T z f)

/-- Sampling an actual Brownian motion at an arbitrary finite family has
its genuine pushed-forward Gaussian finite-dimensional law. -/
theorem scalarBrownian_samples_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (hB : IsPreBrownianReal B P)
    (τ : ℕ → ℝ≥0) (I : Finset ℕ) :
    HasLaw (fun ω (i : I) => B (τ i) ω)
      ((BrownianReal.projectiveFamily (I.image τ)).map
        (fun v (i : I) => v ⟨τ i,Finset.mem_image.mpr ⟨i,i.property,rfl⟩⟩)) P := by
  have hm : Measurable (fun v : (i : I.image τ) → ℝ =>
      fun i : I => v ⟨τ i,Finset.mem_image.mpr ⟨i,i.property,rfl⟩⟩) :=
    Measurable.of_eval (fun _ => measurable_pi_apply _)
  simpa only [Function.comp_def, Finset.restrict_def] using
    (hasLaw_map hm.aemeasurable).comp (hB.hasLaw (I.image τ))

/-- Measurable continuous versions of actual Brownian motions have the same
whole path law, proved from the genuine finite-dimensional Brownian laws. -/
theorem scalarBrownian_continuousPath_law_unique {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Q : Measure Ω') [IsProbabilityMeasure Q]
    (B : ℝ≥0 → Ω → ℝ) (C : ℝ≥0 → Ω' → ℝ)
    (hB : IsPreBrownianReal B P) (hC : IsPreBrownianReal C Q)
    (T : ℝ≥0) (F : Ω → ScalarContinuousPath T) (G : Ω' → ScalarContinuousPath T)
    (hFm : Measurable F) (hGm : Measurable G)
    (hF : ∀ᵐ ω ∂P, ∀ t : Icc (0 : ℝ) (T : ℝ),
      F ω t = B ⟨t,t.property.1⟩ ω)
    (hG : ∀ᵐ ω ∂Q, ∀ t : Icc (0 : ℝ) (T : ℝ),
      G ω t = C ⟨t,t.property.1⟩ ω) : P.map F = Q.map G := by
  let τ : ℕ → ℝ≥0 := fun i =>
    ⟨scalarPathDenseTimes T i,(scalarPathDenseTimes T i).property.1⟩
  let samples := scalarPathDenseSamples T
  have hs : Measurable samples := (scalarPathDenseSamples_measurableEmbedding T).measurable
  have hFp (I : Finset ℕ) := scalarBrownian_samples_hasLaw P B hB τ I
  have hGp (I : Finset ℕ) := scalarBrownian_samples_hasLaw Q C hC τ I
  have he (I : Finset ℕ) :
      P.map (fun ω => I.restrict (samples (F ω))) =
      Q.map (fun ω => I.restrict (samples (G ω))) := by
    have hp := (hFp I).congr (show
        (fun ω (i : I) => (samples (F ω)) i) =ᵐ[P]
          (fun ω (i : I) => B (τ i) ω) from by
      filter_upwards [hF] with ω hω
      funext i
      exact hω (scalarPathDenseTimes T i))
    have hq := (hGp I).congr (show
        (fun ω (i : I) => (samples (G ω)) i) =ᵐ[Q]
          (fun ω (i : I) => C (τ i) ω) from by
      filter_upwards [hG] with ω hω
      funext i
      exact hω (scalarPathDenseTimes T i))
    exact hp.map_eq.trans hq.map_eq.symm
  have hFP : IsProjectiveLimit (P.map (samples ∘ F))
      (fun I : Finset ℕ => P.map (fun ω => I.restrict (samples (F ω)))) :=
    isProjectiveLimit_map (hs.comp hFm).aemeasurable
  have hGQ : IsProjectiveLimit (Q.map (samples ∘ G))
      (fun I : Finset ℕ => P.map (fun ω => I.restrict (samples (F ω)))) := by
    intro I
    rw [Measure.map_map (Finset.measurable_restrict I) (hs.comp hGm)]
    exact (he I).symm
  have hEq := hFP.unique hGQ
  apply (scalarPathDenseSamples_measurableEmbedding T).map_injective
  change (P.map F).map samples = (Q.map G).map samples
  rw [Measure.map_map hs hFm, Measure.map_map hs hGm]
  exact hEq

/-- Driving the proved Picard callback by a genuine Brownian continuous
path reproduces the literal hidden-spin observation path law. Both the
input innovation Brownianity and the equality of laws are derived. -/
theorem scalarForwardPicardPath_actual_hidden_field_law {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) (T : ℝ≥0) (z : ℝ)
    (F : Ω → ScalarContinuousPath T) (hFm : Measurable F)
    (hF : ∀ᵐ ω ∂P, ∀ t : Icc (0 : ℝ) (T : ℝ),
      F ω t = B ⟨t,t.property.1⟩ ω) :
    ∃ Y : Bool × Ω → ScalarContinuousPath T, Measurable Y ∧
      (∀ᵐ u ∂scalarHiddenBrownianLaw z P, ∀ t : Icc (0 : ℝ) (T : ℝ),
        Y u t = scalarHiddenContinuousField z B ⟨t,t.property.1⟩ u) ∧
      (P.map F).map (fun f => scalarForwardPicardPath scalarTanhDrift T (z,f)) =
        (scalarHiddenBrownianLaw z P).map Y := by
  obtain ⟨Y,M,hYm,hMm,hdef,he,_⟩ :=
    scalarHiddenBrownian_actual_pathVersions P T z B hB
  refine ⟨Y,hYm,he.mono (fun u hu t => (hu t).1),?_⟩
  have hM := (scalarContinuousInnovation_isBrownianReal P z B hB).toIsPreBrownianReal
  have hMe : ∀ᵐ u ∂scalarHiddenBrownianLaw z P, ∀ t : Icc (0 : ℝ) (T : ℝ),
      M u t = scalarContinuousInnovation z B ⟨t,t.property.1⟩ u :=
    he.mono (fun u hu t => (hu t).2)
  have hl := scalarBrownian_continuousPath_law_unique P (scalarHiddenBrownianLaw z P)
    B (scalarContinuousInnovation z B) hB.toIsPreBrownianReal hM T F M hFm hMm hF hMe
  have hm : Measurable (fun f : ScalarContinuousPath T =>
      scalarForwardPicardPath scalarTanhDrift T (z,f)) :=
    (measurable_scalarForwardPicardPath scalarTanhDrift T).comp
      (measurable_const.prodMk measurable_id)
  rw [hl,Measure.map_map hm hMm]
  apply Measure.map_congr
  exact Eventually.of_forall (fun u => by
    dsimp only [Function.comp_apply]
    rw [hdef u]
    exact scalarForwardPicardPath_reconstructs T z (Y u))

end SKConstants
