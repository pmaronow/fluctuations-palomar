module

public import SKConstants.ScalarProcessSeedMixture
public import SKConstants.ScalarForwardPicardPaths

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace SKConstants
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω]

def scalarSeedHiddenFieldPath (T : ℝ≥0) (F : Ω → ScalarContinuousPath T)
    (u : ℝ × (Bool × Ω)) : ScalarContinuousPath T where
  toFun t := u.1 + scalarHiddenSign u.2.1 * (t : ℝ) + F u.2.2 t
  continuous_toFun := (continuous_const.add
    (continuous_const.mul continuous_subtype_val)).add (F u.2.2).continuous

theorem measurable_scalarSeedHiddenFieldPath (T : ℝ≥0)
    (F : Ω → ScalarContinuousPath T) (hFm : Measurable F) :
    Measurable (scalarSeedHiddenFieldPath T F) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  exact (measurable_fst.add
    (((measurable_of_finite scalarHiddenSign).comp measurable_snd.fst).mul_const _)).add
      ((ContinuousMap.measurable_eval t).comp (hFm.comp measurable_snd.snd))

theorem scalarSeedHiddenFieldPath_actual_field
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (F : Ω → ScalarContinuousPath T)
    (hF : ∀ᵐ ω ∂P, ∀ t : Set.Icc (0 : ℝ) (T : ℝ),
      F ω t = B ⟨t,t.property.1⟩ ω) :
    ∀ᵐ u ∂scalarSeedHiddenBrownianLaw ν P, ∀ t : Set.Icc (0 : ℝ) (T : ℝ),
      scalarSeedHiddenFieldPath T F u t =
        scalarSeedHiddenContinuousField B ⟨t,t.property.1⟩ u := by
  obtain ⟨N,hNsub,hNm,hNzero⟩ := exists_measurable_superset_of_null (ae_iff.mp hF)
  have hgood : ∀ᵐ ω ∂P, ω ∉ N := ae_iff.mpr (by simpa using hNzero)
  have hm : MeasurableSet {u : ℝ × (Bool × Ω) | u.2.2 ∉ N} :=
    hNm.compl.preimage measurable_snd.snd
  have hg : ∀ᵐ u ∂scalarSeedHiddenBrownianLaw ν P, u.2.2 ∉ N := by
    apply Measure.ae_compProd_of_ae_ae hm
    apply ae_of_all
    intro z
    exact (measurePreserving_snd (μ := scalarHiddenPriorBool z) (ν := P)).quasiMeasurePreserving.ae hgood
  filter_upwards [hg] with u hu
  have hfu : ∀ t : Set.Icc (0 : ℝ) (T : ℝ), F u.2.2 t = B ⟨t,t.property.1⟩ u.2.2 :=
    not_not.mp (fun hn => hu (hNsub hn))
  intro t
  change u.1 + scalarHiddenSign u.2.1 * (t : ℝ) + F u.2.2 t =
    u.1 + scalarHiddenSign u.2.1 * (t : ℝ) + B ⟨t,t.property.1⟩ u.2.2
  rw [hfu t]

theorem scalarForwardPicardPath_actual_hidden_field_law_joint_version
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (T : ℝ≥0) (z : ℝ)
    (F : Ω → ScalarContinuousPath T) (hFm : Measurable F)
    (hF : ∀ᵐ ω ∂P, ∀ t : Set.Icc (0 : ℝ) (T : ℝ),
      F ω t = B ⟨t,t.property.1⟩ ω) :
    (P.map F).map (fun f => scalarForwardPicardPath scalarTanhDrift T (z,f)) =
      (scalarHiddenBrownianLaw z P).map (fun u => scalarSeedHiddenFieldPath T F (z,u)) := by
  obtain ⟨Y,hYm,hY,hl⟩ := scalarForwardPicardPath_actual_hidden_field_law
    P B hB T z F hFm hF
  rw [hl]
  apply Measure.map_congr
  have hf := (measurePreserving_snd (μ := scalarHiddenPriorBool z) (ν := P)).quasiMeasurePreserving.ae hF
  filter_upwards [hY,hf] with u hu hfu
  ext t
  rw [hu t]
  change z + scalarHiddenSign u.1 * (t : ℝ) + B ⟨t,t.property.1⟩ u.2 =
    z + scalarHiddenSign u.1 * (t : ℝ) + F u.2 t
  rw [hfu t]

theorem scalarForwardPicardPath_seedMixture_hidden_field_law
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) (T : ℝ≥0)
    (F : Ω → ScalarContinuousPath T) (hFm : Measurable F)
    (hF : ∀ᵐ ω ∂P, ∀ t : Set.Icc (0 : ℝ) (T : ℝ),
      F ω t = B ⟨t,t.property.1⟩ ω) :
    (ν.prod (P.map F)).map (fun p =>
        (p.1, scalarForwardPicardPath scalarTanhDrift T p)) =
      (scalarSeedHiddenBrownianLaw ν P).map (fun u =>
        (u.1, scalarSeedHiddenFieldPath T F u)) := by
  have hm : Measurable (fun p : ℝ × ScalarContinuousPath T =>
      (p.1, scalarForwardPicardPath scalarTanhDrift T p)) :=
    measurable_fst.prodMk (measurable_scalarForwardPicardPath scalarTanhDrift T)
  have hn : Measurable (fun u : ℝ × (Bool × Ω) =>
      (u.1, scalarSeedHiddenFieldPath T F u)) :=
    measurable_fst.prodMk (measurable_scalarSeedHiddenFieldPath T F hFm)
  ext A hA
  rw [Measure.map_apply hm hA, Measure.map_apply hn hA, scalarSeedHiddenBrownianLaw,
    Measure.prod_apply (hm hA), Measure.compProd_apply (hn hA)]
  apply lintegral_congr_ae
  apply ae_of_all
  intro z
  have hc : Measurable (fun f : ScalarContinuousPath T =>
      scalarForwardPicardPath scalarTanhDrift T (z,f)) :=
    (measurable_scalarForwardPicardPath scalarTanhDrift T).comp
      (measurable_const.prodMk measurable_id)
  have hd : Measurable (fun u : Bool × Ω => scalarSeedHiddenFieldPath T F (z,u)) :=
    (measurable_scalarSeedHiddenFieldPath T F hFm).comp
      (measurable_const.prodMk measurable_id)
  have hs : MeasurableSet (Prod.mk z ⁻¹' A) :=
    hA.preimage (measurable_const.prodMk measurable_id)
  have hl := congrArg (fun μ : Measure (ScalarContinuousPath T) => μ (Prod.mk z ⁻¹' A))
    (scalarForwardPicardPath_actual_hidden_field_law_joint_version P B hB T z F hFm hF)
  rw [Measure.map_apply hc hs, Measure.map_apply hd hs] at hl
  exact hl

theorem scalarSeedInnovationPath_hidden_mixture_law
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) (T : ℝ≥0)
    (F : Ω → ScalarContinuousPath T) (hFm : Measurable F)
    (hF : ∀ᵐ ω ∂P, ∀ t : Set.Icc (0 : ℝ) (T : ℝ),
      F ω t=B ⟨t,t.property.1⟩ ω) :
    (scalarSeedHiddenBrownianLaw ν P).map (fun u =>
      (u.1,scalarInnovationPath T u.1 (scalarSeedHiddenFieldPath T F u))) = ν.prod (P.map F) := by
  have hm : Measurable (fun p : ℝ × ScalarContinuousPath T =>
      (p.1,scalarForwardPicardPath scalarTanhDrift T p)) :=
    measurable_fst.prodMk (measurable_scalarForwardPicardPath scalarTanhDrift T)
  have hn : Measurable (fun u : ℝ × (Bool × Ω) =>
      (u.1,scalarSeedHiddenFieldPath T F u)) :=
    measurable_fst.prodMk (measurable_scalarSeedHiddenFieldPath T F hFm)
  have he := congrArg (fun μ : Measure (ℝ × ScalarContinuousPath T) =>
      μ.map (scalarSeedInnovationPath T))
    (scalarForwardPicardPath_seedMixture_hidden_field_law ν P B hB T F hFm hF)
  rw [Measure.map_map (measurable_scalarSeedInnovationPath T) hm,
    Measure.map_map (measurable_scalarSeedInnovationPath T) hn] at he
  have hi : (scalarSeedInnovationPath T ∘ fun p : ℝ × ScalarContinuousPath T =>
      (p.1,scalarForwardPicardPath scalarTanhDrift T p)) = id := by
    funext p
    cases p with
    | mk z f =>
      simp only [Function.comp_apply,scalarSeedInnovationPath,scalarForwardPicardPath_innovation,id_eq]
  rw [hi,Measure.map_id] at he
  exact he.symm

end SKConstants
