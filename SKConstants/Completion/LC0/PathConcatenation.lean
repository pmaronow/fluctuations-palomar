module
public import SKConstants.Completion.LC0.BridgeReconstruction
public import SKConstants.ParisiBrownianMarkov

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal Topology
namespace SKConstants.M1
open SKConstantsOAI.ZeroTemperatureSK
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω]

def scalarConcatPath (a h : ℝ≥0)
    (p : ScalarContinuousPath a × ScalarContinuousPath h) : ScalarContinuousPath (a+h) :=
  ⟨fun t => p.1 (projIcc 0 (a : ℝ) a.coe_nonneg t) +
    p.2 (projIcc 0 (h : ℝ) h.coe_nonneg ((t : ℝ)-a)) -
    p.2 ⟨0,le_rfl,h.coe_nonneg⟩,
    ((p.1.continuous.comp ((continuous_projIcc (h := a.coe_nonneg)).comp
      continuous_subtype_val)).add
      (p.2.continuous.comp ((continuous_projIcc (h := h.coe_nonneg)).comp
        (continuous_subtype_val.sub continuous_const)))).sub continuous_const⟩

theorem measurable_scalarConcatPath (a h : ℝ≥0) : Measurable (scalarConcatPath a h) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  exact (((ContinuousMap.measurable_eval _).comp measurable_fst).add
    ((ContinuousMap.measurable_eval _).comp measurable_snd)).sub
      ((ContinuousMap.measurable_eval _).comp measurable_snd)

def scalarSplitPath (a h : ℝ≥0) (c : ScalarContinuousPath (a+h)) :
    ScalarContinuousPath a × ScalarContinuousPath h :=
  (scalarInitialAuxiliaryRestriction (a+h) a (by exact le_self_add) c,
   ⟨fun t => c ⟨(a : ℝ)+t,add_nonneg a.coe_nonneg t.property.1,
      by simp only [NNReal.coe_add]; linarith [t.property.2]⟩ -
     c ⟨a,a.coe_nonneg,by simp only [NNReal.coe_add]; exact le_add_of_nonneg_right h.coe_nonneg⟩,
     (c.continuous.comp (by fun_prop)).sub continuous_const⟩)

theorem measurable_scalarSplitPath (a h : ℝ≥0) : Measurable (scalarSplitPath a h) := by
  apply Measurable.prodMk
  · exact measurable_scalarInitialAuxiliaryRestriction _ _ _
  · apply ContinuousMap.measurable_iff_eval.mpr
    intro t
    exact (ContinuousMap.measurable_eval _).sub (ContinuousMap.measurable_eval _)

theorem scalarConcatPath_split (a h : ℝ≥0) (c : ScalarContinuousPath (a+h)) :
    scalarConcatPath a h (scalarSplitPath a h c) = c := by
  ext t
  by_cases ht : (t : ℝ) ≤ a
  · have hta : (t : ℝ) ∈ Icc (0 : ℝ) (a : ℝ) := ⟨t.property.1,ht⟩
    simp only [scalarConcatPath, scalarSplitPath, scalarInitialAuxiliaryRestriction,
      ContinuousMap.coe_mk, projIcc_of_mem _ hta,
      projIcc_of_le_left h.coe_nonneg (sub_nonpos.mpr ht), add_zero]
    ring
  · have hat : (a : ℝ) ≤ t := (le_of_not_ge ht)
    have hth : (t : ℝ) - a ∈ Icc (0 : ℝ) (h : ℝ) :=
      ⟨sub_nonneg.mpr hat, by have := t.property.2; simp only [NNReal.coe_add] at this; linarith⟩
    simp only [scalarConcatPath, scalarSplitPath, scalarInitialAuxiliaryRestriction,
      ContinuousMap.coe_mk, projIcc_of_right_le a.coe_nonneg hat,
      projIcc_of_mem _ hth, add_sub_cancel, add_zero]
    ring

theorem scalarSplitPath_concat (a h : ℝ≥0)
    (p : ScalarContinuousPath a × ScalarContinuousPath h)
    (hp : p.2 ⟨0,le_rfl,h.coe_nonneg⟩ = 0) :
    scalarSplitPath a h (scalarConcatPath a h p) = p := by
  apply Prod.ext
  · ext t
    simp only [scalarSplitPath, scalarConcatPath, scalarInitialAuxiliaryRestriction,
      ContinuousMap.coe_mk, projIcc_of_mem _ t.property,
      projIcc_of_le_left h.coe_nonneg (sub_nonpos.mpr t.property.2)]
    ring
  · ext t
    have hat : (a : ℝ) ≤ (a : ℝ)+t := le_add_of_nonneg_right t.property.1
    simp only [scalarSplitPath, scalarConcatPath, ContinuousMap.coe_mk,
      projIcc_of_right_le a.coe_nonneg hat, add_sub_cancel_left,
      projIcc_of_mem _ t.property, projIcc_right, sub_self, projIcc_left,
      hp, add_zero, sub_zero]

theorem scalarPrimitiveBrownianPast_future_independent (W : BrownianSystem Ω)
    (a h : ℝ≥0) :
    IndepFun (scalarPrimitiveBrownianPathVersion W a)
      (scalarPrimitiveBrownianPathVersion (shiftedBrownianSystem W a) h) W.law := by
  have hi := (brownian_indepFun_shift_scalarPathVersion W.law a W.B
    W.brownian.toIsPreBrownianReal (scalarPrimitiveBrownianPathVersion W a)
    (scalarPrimitiveBrownianPathVersion_ae W a)).symm
  have hm : Measurable (fun f : ℝ≥0 → ℝ => fun t : Iic h => f t.1) :=
    Measurable.of_eval fun t => measurable_pi_apply t.1
  exact indepFun_scalarPathVersion_of_past W.law h
    (fun s ω => W.B (a+s) ω-W.B a ω)
    (scalarPrimitiveBrownianPathVersion (shiftedBrownianSystem W a) h)
    (scalarPrimitiveBrownianPathVersion W a)
    (scalarPrimitiveBrownianPathVersion_ae (shiftedBrownianSystem W a) h)
    (hi.comp measurable_id hm)

theorem scalarPrimitiveBrownianPathLaw_shift (W : BrownianSystem Ω) (a h : ℝ≥0) :
    scalarPrimitiveBrownianPathLaw (shiftedBrownianSystem W a) h =
      scalarPrimitiveBrownianPathLaw W h := by
  let := W.isProbability
  exact scalarBrownian_continuousPath_law_unique W.law W.law
    (shiftedBrownianSystem W a).B W.B
    (shiftedBrownianSystem W a).brownian.toIsPreBrownianReal W.brownian.toIsPreBrownianReal h
    (scalarPrimitiveBrownianPathVersion (shiftedBrownianSystem W a) h)
    (scalarPrimitiveBrownianPathVersion W h)
    (measurable_scalarPrimitiveBrownianPathVersion _ _) (measurable_scalarPrimitiveBrownianPathVersion _ _)
    (scalarPrimitiveBrownianPathVersion_ae _ _) (scalarPrimitiveBrownianPathVersion_ae _ _)

theorem scalarBrownianSplit_law (W : BrownianSystem Ω) (a h : ℝ≥0) :
    (scalarPrimitiveBrownianPathLaw W (a+h)).map (scalarSplitPath a h) =
      (scalarPrimitiveBrownianPathLaw W a).prod (scalarPrimitiveBrownianPathLaw W h) := by
  let := W.isProbability
  have he : scalarSplitPath a h ∘ scalarPrimitiveBrownianPathVersion W (a+h) =ᵐ[W.law]
      (fun ω => (scalarPrimitiveBrownianPathVersion W a ω,
        scalarPrimitiveBrownianPathVersion (shiftedBrownianSystem W a) h ω)) := by
    filter_upwards [scalarPrimitiveBrownianPathVersion_ae W (a+h),
      scalarPrimitiveBrownianPathVersion_ae W a,
      scalarPrimitiveBrownianPathVersion_ae (shiftedBrownianSystem W a) h] with ω hfull ha hh
    apply Prod.ext
    · ext t
      exact (hfull _).trans (ha t).symm
    · ext t
      change scalarPrimitiveBrownianPathVersion W (a+h) ω _ -
        scalarPrimitiveBrownianPathVersion W (a+h) ω _ = _
      rw [hfull, hfull, hh]
      rfl
  unfold scalarPrimitiveBrownianPathLaw
  rw [Measure.map_map (measurable_scalarSplitPath a h) (measurable_scalarPrimitiveBrownianPathVersion W (a+h)),
    Measure.map_congr he]
  have hind := (scalarPrimitiveBrownianPast_future_independent W a h).map_prod_eq_prod_map_map
    (measurable_scalarPrimitiveBrownianPathVersion W a).aemeasurable
    (measurable_scalarPrimitiveBrownianPathVersion (shiftedBrownianSystem W a) h).aemeasurable
  rw [hind]
  exact congrArg (fun ν => (W.law.map (scalarPrimitiveBrownianPathVersion W a)).prod ν)
    (scalarPrimitiveBrownianPathLaw_shift W a h)

theorem scalarBrownianConcat_law (W : BrownianSystem Ω) (a h : ℝ≥0) :
    ((scalarPrimitiveBrownianPathLaw W a).prod (scalarPrimitiveBrownianPathLaw W h)).map
      (scalarConcatPath a h) = scalarPrimitiveBrownianPathLaw W (a+h) := by
  rw [← scalarBrownianSplit_law W a h,
    Measure.map_map (measurable_scalarConcatPath a h) (measurable_scalarSplitPath a h)]
  have he : scalarConcatPath a h ∘ scalarSplitPath a h = id :=
    funext fun c => scalarConcatPath_split a h c
  rw [he, Measure.map_id]

end SKConstants.M1
