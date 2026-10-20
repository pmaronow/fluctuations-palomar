module

public import SKConstants.Completion.N9c.RowStatistics
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace SKConstants.Completion.N9c
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal M1 LFine
variable {Ω : Type*} [MeasurableSpace Ω]

def freshFutureDrivers (h f : ℝ≥0) (z : ℝ × FreshRowSeed h f) :
    ScalarContinuousPath (h+f) × ScalarContinuousPath (h+f) :=
  (scalarConcatPath h f (scalarQueryBridgeComplete h (z.1,z.2.1),z.2.2.1),z.2.2.2.1)

theorem measurable_freshFutureDrivers (h f : ℝ≥0) :
    Measurable (freshFutureDrivers h f) :=
  ((measurable_scalarConcatPath h f).comp
    (((measurable_scalarQueryBridgeComplete h).comp
      (measurable_fst.prodMk measurable_snd.fst)).prodMk measurable_snd.snd.fst)).prodMk
        measurable_snd.snd.snd.fst

theorem freshFutureDrivers_threshold_law (W : BrownianSystem Ω)
    (h f : ℝ≥0) (hh : 0 < h) :
    ((gaussianReal 0 1).prod (freshRowSeedLaw W h f)).map
      (fun z => (freshFutureDrivers h f z,z.2.2.2.2)) =
    ((scalarPrimitiveBrownianPathLaw W (h+f)).prod
      (scalarPrimitiveBrownianPathLaw W (h+f))).prod SKConstantsOAI.SK.unitIntervalLaw := by
  let E := gaussianReal 0 1
  let C := scalarPrimitiveBridgePathLaw W h
  let B := scalarPrimitiveBrownianPathLaw W f
  let D := scalarPrimitiveBrownianPathLaw W (h+f)
  let U := SKConstantsOAI.SK.unitIntervalLaw
  have h0 := (measurePreserving_prodAssoc E C (B.prod (D.prod U))).symm
  have hc : MeasurePreserving (scalarQueryBridgeComplete h) (E.prod C)
      (scalarPrimitiveBrownianPathLaw W h) :=
    ⟨measurable_scalarQueryBridgeComplete h,scalarQueryBridgeComplete_law W h hh⟩
  have h1 := hc.prod (MeasurePreserving.id (B.prod (D.prod U)))
  have h2 := (measurePreserving_prodAssoc (scalarPrimitiveBrownianPathLaw W h)
    B (D.prod U)).symm
  have hcat : MeasurePreserving (scalarConcatPath h f)
      ((scalarPrimitiveBrownianPathLaw W h).prod B) D :=
    ⟨measurable_scalarConcatPath h f,scalarBrownianConcat_law W h f⟩
  have h3 := hcat.prod (MeasurePreserving.id (D.prod U))
  have h4 := (measurePreserving_prodAssoc D D U).symm
  exact (h4.comp (h3.comp (h2.comp (h1.comp h0)))).map_eq

theorem freshRowDrivers_threshold_law (W : BrownianSystem Ω)
    (a h f : ℝ≥0) (hh : 0 < h) :
    (((scalarPrimitiveBrownianPathLaw W a).prod (scalarPrimitiveBrownianPathLaw W a)).prod
      ((gaussianReal 0 1).prod (freshRowSeedLaw W h f))).map
      (fun u => (freshRowDrivers a h f u.1.1 u.1.2 u.2,u.2.2.2.2.2)) =
    ((scalarPrimitiveBrownianPathLaw W (a+(h+f))).prod
      (scalarPrimitiveBrownianPathLaw W (a+(h+f)))).prod SKConstantsOAI.SK.unitIntervalLaw := by
  let P := scalarPrimitiveBrownianPathLaw W a
  let Q := scalarPrimitiveBrownianPathLaw W (h+f)
  let U := SKConstantsOAI.SK.unitIntervalLaw
  have hF : MeasurePreserving (fun z => (freshFutureDrivers h f z,z.2.2.2.2))
      ((gaussianReal 0 1).prod (freshRowSeedLaw W h f)) ((Q.prod Q).prod U) :=
    ⟨(measurable_freshFutureDrivers h f).prodMk measurable_snd.snd.snd.snd,
      freshFutureDrivers_threshold_law W h f hh⟩
  have h0 := (MeasurePreserving.id (P.prod P)).prod hF
  have h1 := (measurePreserving_prodAssoc (P.prod P) (Q.prod Q) U).symm
  have hshuffle : MeasurePreserving
      (fun z : (ScalarContinuousPath a × ScalarContinuousPath a) ×
        (ScalarContinuousPath (h+f) × ScalarContinuousPath (h+f)) =>
          ((z.1.1,z.2.1),(z.1.2,z.2.2)))
      ((P.prod P).prod (Q.prod Q)) ((P.prod Q).prod (P.prod Q)) :=
    ⟨by fun_prop,prod_quad_shuffle P P Q Q⟩
  have h2 := hshuffle.prod (MeasurePreserving.id U)
  have hcat : MeasurePreserving (scalarConcatPath a (h+f)) (P.prod Q)
      (scalarPrimitiveBrownianPathLaw W (a+(h+f))) :=
    ⟨measurable_scalarConcatPath a (h+f),scalarBrownianConcat_law W a (h+f)⟩
  have h3 := (hcat.prod hcat).prod (MeasurePreserving.id U)
  exact (h3.comp (h2.comp (h1.comp h0))).map_eq

theorem freshRowDrivers_law (W : BrownianSystem Ω)
    (a h f : ℝ≥0) (hh : 0 < h) :
    (((scalarPrimitiveBrownianPathLaw W a).prod (scalarPrimitiveBrownianPathLaw W a)).prod
      ((gaussianReal 0 1).prod (freshRowSeedLaw W h f))).map
      (fun u => freshRowDrivers a h f u.1.1 u.1.2 u.2) =
    (scalarPrimitiveBrownianPathLaw W (a+(h+f))).prod
      (scalarPrimitiveBrownianPathLaw W (a+(h+f))) := by
  have hm : Measurable (fun u : (ScalarContinuousPath a × ScalarContinuousPath a) ×
      (ℝ × FreshRowSeed h f) => freshRowDrivers a h f u.1.1 u.1.2 u.2) :=
    N9b.measurable_freshRowDrivers_param a h f _ _ _
      measurable_fst.fst measurable_fst.snd measurable_snd
  have he := congrArg (fun ν => ν.map Prod.fst) (freshRowDrivers_threshold_law W a h f hh)
  rw [Measure.map_map measurable_fst
    (hm.prodMk measurable_snd.snd.snd.snd.snd),
    Measure.map_fst_prod,measure_univ,one_smul] at he
  exact he

theorem freshRowDrivers_past (a h f : ℝ≥0)
    (p : ScalarContinuousPath a × ScalarContinuousPath a) (z : ℝ × FreshRowSeed h f) :
    (scalarInitialAuxiliaryRestriction (a+(h+f)) a (by exact le_self_add)
        (freshRowDrivers a h f p.1 p.2 z).1,
     scalarInitialAuxiliaryRestriction (a+(h+f)) a (by exact le_self_add)
        (freshRowDrivers a h f p.1 p.2 z).2) = p := by
  apply Prod.ext <;> ext t <;>
    simp only [freshRowDrivers,scalarInitialAuxiliaryRestriction,scalarConcatPath,
      ContinuousMap.coe_mk,projIcc_of_mem _ t.property,
      projIcc_of_le_left (h+f).coe_nonneg (sub_nonpos.mpr t.property.2)] <;> ring

theorem freshRowDrivers_jointPast_law (W : BrownianSystem Ω)
    (a h f : ℝ≥0) (hh : 0 < h) :
    (((scalarPrimitiveBrownianPathLaw W a).prod (scalarPrimitiveBrownianPathLaw W a)).prod
      ((gaussianReal 0 1).prod (freshRowSeedLaw W h f))).map
      (fun u => (u.1,freshRowDrivers a h f u.1.1 u.1.2 u.2)) =
    ((scalarPrimitiveBrownianPathLaw W (a+(h+f))).prod
      (scalarPrimitiveBrownianPathLaw W (a+(h+f)))).map
        (fun p => ((scalarInitialAuxiliaryRestriction (a+(h+f)) a (by exact le_self_add) p.1,
          scalarInitialAuxiliaryRestriction (a+(h+f)) a (by exact le_self_add) p.2),p)) := by
  let F := fun p : ScalarContinuousPath (a+(h+f)) × ScalarContinuousPath (a+(h+f)) =>
    ((scalarInitialAuxiliaryRestriction (a+(h+f)) a (by exact le_self_add) p.1,
      scalarInitialAuxiliaryRestriction (a+(h+f)) a (by exact le_self_add) p.2),p)
  have hF : Measurable F :=
    (((measurable_scalarInitialAuxiliaryRestriction _ _ _).comp measurable_fst).prodMk
      ((measurable_scalarInitialAuxiliaryRestriction _ _ _).comp measurable_snd)).prodMk measurable_id
  have hm : Measurable (fun u : (ScalarContinuousPath a × ScalarContinuousPath a) ×
      (ℝ × FreshRowSeed h f) => freshRowDrivers a h f u.1.1 u.1.2 u.2) :=
    N9b.measurable_freshRowDrivers_param a h f _ _ _
      measurable_fst.fst measurable_fst.snd measurable_snd
  rw [← freshRowDrivers_law W a h f hh,Measure.map_map hF hm]
  congr 1
  funext u
  apply Prod.ext
  · exact (freshRowDrivers_past a h f u.1 u.2).symm
  · rfl

end SKConstants.Completion.N9c
