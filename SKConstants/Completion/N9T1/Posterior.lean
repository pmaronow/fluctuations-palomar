module

public import SKConstants.Completion.Blueprint5.FineStatements
public import SKConstants.Completion.LM1b.SourceTrace
import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators Matrix

namespace SKConstants.Completion.N9T1
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal FineInformation LFine N9 LQ M1 Blueprint5
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

theorem scalarStieltjesWeightedPath_restriction (f : StieltjesFunction ℝ)
    (hf : Continuous f) (H a : ℝ≥0) (ha : a ≤ H) (B : ScalarContinuousPath H)
    (t : Icc (0 : ℝ) (a : ℝ)) :
    scalarStieltjesWeightedPath f hf a (scalarInitialAuxiliaryRestriction H a ha B) t =
      scalarStieltjesWeightedPath f hf H B ⟨t,t.property.1,t.property.2.trans ha⟩ := by
  change f t * B ⟨t,t.property.1,t.property.2.trans ha⟩ - _ =
    f t * B ⟨t,t.property.1,t.property.2.trans ha⟩ - _
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  have hs0 : 0 ≤ s := by simpa only [min_eq_left t.property.1] using hs.1
  have hst : s ≤ t := by simpa only [max_eq_right t.property.1] using hs.2
  have hpa : projIcc 0 (a : ℝ) a.coe_nonneg s =
      ⟨s,hs0,hst.trans t.property.2⟩ := projIcc_of_mem _ ⟨hs0,hst.trans t.property.2⟩
  have hpH : projIcc 0 (H : ℝ) H.coe_nonneg s =
      ⟨s,hs0,(hst.trans t.property.2).trans ha⟩ :=
    projIcc_of_mem _ ⟨hs0,(hst.trans t.property.2).trans ha⟩
  exact (congrArg (scalarInitialAuxiliaryRestriction H a ha B) hpa).trans
    (congrArg B hpH).symm

theorem scalarTwoDriverPicardPath_restriction (b : BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (H a : ℝ≥0) (ha : a ≤ H) (z : ℝ) (B D : ScalarContinuousPath H)
    (t : Icc (0 : ℝ) (a : ℝ)) :
    scalarTwoDriverPicardPath b f g hf hg a
        (z,(scalarInitialAuxiliaryRestriction H a ha B,scalarInitialAuxiliaryRestriction H a ha D)) t =
      scalarTwoDriverPicardPath b f g hf hg H (z,(B,D))
        ⟨t,t.property.1,t.property.2.trans ha⟩ := by
  apply solution_congr_prefix b (scalarContinuousSeedDriver a) (scalarContinuousSeedDriver H)
    (z,scalarTwoDriverWeightedPath f g hf hg a
      (scalarInitialAuxiliaryRestriction H a ha B,scalarInitialAuxiliaryRestriction H a ha D))
    (z,scalarTwoDriverWeightedPath f g hf hg H (B,D)) a _
    (⟨t,t.property.1⟩ : ℝ≥0) t.property.2
  intro s hs
  change z + scalarTwoDriverWeightedPath f g hf hg a _
      (projIcc 0 (a : ℝ) a.coe_nonneg s) =
    z + scalarTwoDriverWeightedPath f g hf hg H _ (projIcc 0 (H : ℝ) H.coe_nonneg s)
  have hpa : projIcc 0 (a : ℝ) a.coe_nonneg (s : ℝ) =
      ⟨s,s.coe_nonneg,hs⟩ := projIcc_of_mem _ ⟨s.coe_nonneg,hs⟩
  have hpH : projIcc 0 (H : ℝ) H.coe_nonneg (s : ℝ) =
      ⟨s,s.coe_nonneg,hs.trans ha⟩ := projIcc_of_mem _ ⟨s.coe_nonneg,hs.trans ha⟩
  apply congrArg (z + ·)
  exact (congrArg _ hpa).trans
    ((congrArg₂ (fun x y : ℝ => -x+y)
      (scalarStieltjesWeightedPath_restriction f hf H a ha B ⟨s,s.coe_nonneg,hs⟩)
      (scalarStieltjesWeightedPath_restriction g hg H a ha D ⟨s,s.coe_nonneg,hs⟩)).trans
        (congrArg (scalarTwoDriverWeightedPath f g hf hg H (B,D)) hpH).symm)

variable {Ω : Type*} [MeasurableSpace Ω]

def sourceMeanAt (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) (a : ℝ≥0) (s : SourceInput δ r K) : Fin (r+K) → ℝ :=
  fun i => actualParisiFullMagnetization β a (SourceField W β hβ δ r K a s i)

theorem measurable_sourceMeanAt (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) (a : ℝ≥0) : Measurable (sourceMeanAt W β hβ δ r K a) := by
  apply Measurable.of_eval
  intro i
  have hm : Measurable (fun x : ℝ => actualParisiFullMagnetization β a x) :=
    ((continuous_actualParisiFullMagnetization β).comp (continuous_const.prodMk continuous_id)).measurable
  exact hm.comp ((measurable_pi_apply i).comp (measurable_SourceField W β hβ δ r K a))

theorem fixedPastPosterior_fineCell (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ) (e : Fin K)
    (z : (Fin (r+K) → Bool) × SourceInput δ r K) (i : Fin (r+K)) :
    fixedPastPosterior W β hβ (growingQueryTime δ (e.val+1))
        (fineCellPastB W β hβ δ hδ r K e z i) (fineCellPastD W β hβ δ hδ r K e z i) =
      sourceMeanAt W β hβ δ r K (growingQueryTime δ (e.val+1)) z.2 i := by
  unfold fixedPastPosterior fineCellPastB fineCellPastD
  rw [scalarTwoDriverPicardPath_restriction]
  unfold sourceMeanAt SourceField
  let t : Icc (0 : ℝ) (Horizon δ K : ℝ) :=
    ⟨growingQueryTime δ (e.val+1),(growingQueryTime δ (e.val+1)).coe_nonneg,
      fineCellStart_le_horizon δ hδ K e⟩
  have hp : projIcc 0 (Horizon δ K : ℝ) (Horizon δ K).coe_nonneg
      (growingQueryTime δ (e.val+1) : ℝ) = t :=
    projIcc_of_mem _ ⟨(growingQueryTime δ (e.val+1)).coe_nonneg,
      fineCellStart_le_horizon δ hδ K e⟩
  apply congrArg (actualParisiFullMagnetization β (growingQueryTime δ (e.val+1)))
  exact (congrArg (fun Y : ScalarContinuousPath (Horizon δ K) => Y t)
    (source_observation_eq_driver W β hβ δ r K z.2 i)).symm.trans
      (congrArg _ hp).symm

theorem sourceTargets_eq_mean_increment (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ) (e : Fin K) (s : SourceInput δ r K) :
    SourceTargets W β hβ δ r K s e =
      fun i => (sourceMeanAt W β hβ δ r K (growingQueryTime δ (e.val+1)) s i -
        sourceMeanAt W β hβ δ r K (growingQueryTime δ e.val) s i) /
          actualFineScale W β δ e.val := by
  funext i
  exact targetTraceIdentification_holds W β hβ δ hδ r K s e i

theorem actualGrowingMeanAt_trace_eq_sourceMeanAt (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ)
    (s : SourceInput δ r K) (e : Fin (K+1)) (a : ℝ≥0)
    (ha : a ≤ growingQueryTime δ (e.val+1)) :
    actualGrowingMeanAt W β hβ δ (r+K) K a
        (paperScalarPastTrace r (r+K) (Target W β hβ δ r K) (Update δ r K) K
          (Initial δ r K s,1) (Original δ r K s) e) =
      sourceMeanAt W β hβ δ r K a s := by
  let p := paperScalarPastTrace r (r+K) (Target W β hβ δ r K) (Update δ r K) K
    (Initial δ r K s,1) (Original δ r K s) e
  have hb : growingQueryTime δ (e.val+1) ≤ Horizon δ K :=
    (growingQueryTime_strictMono δ hδ).monotone (by omega)
  have hs : p.1 = (SourcePast δ r K s).1 :=
    (scalarMeshSourceTrace_static _ _ _ r (r+K) K (Target W β hβ δ r K) K
      (Initial δ r K s,1) (Original δ r K s) e).trans
      (scalarMeshSourceRun_static _ _ _ (r+K) K K
        (Initial δ r K s) (Original δ r K s)).symm
  have hp : ScalarMeshPastPrefixEq (Horizon δ K) (growingQueryDuration δ)
      (growingQueryTime δ) (r+K) (growingQueryTime δ (e.val+1)) p (SourcePast δ r K s) :=
    ⟨congrArg Prod.fst hs, congrArg (fun x => x.2.2) hs,
      fun i u hu => growingSource_prefix_eq_terminal W β hβ δ hδ r K s e i u hu,
      fun i u _ => congrArg (fun c : ScalarContinuousPath (Horizon δ K) => c u)
        (congrFun (congrArg (fun x => x.2.1) hs) i)⟩
  ext i
  unfold actualGrowingMeanAt scalarMeshMeanAt sourceMeanAt SourceField
  have ht : projIcc 0 (Horizon δ K : ℝ) (Horizon δ K).coe_nonneg (a : ℝ) =
      ⟨a,a.coe_nonneg,ha.trans hb⟩ := projIcc_of_mem _ ⟨a.coe_nonneg,ha.trans hb⟩
  exact congrArg (actualParisiFullMagnetization β a)
    (scalarMeshPaperObservation_eq_of_prefix _ _ _ _ _ _ _ _ _ _ hb p
      (SourcePast δ r K s) hp i _ (by
        exact (congrArg Subtype.val ht).le.trans ha))

theorem fineCellRemainingProjection_kills_sourceMeanAt_ae (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ) (e : Fin K) :
    ∀ᵐ z ∂SourceLinkedLaw W β hβ δ r K,
      fineCellRemainingProjection W β hβ δ r K e z *ᵥ
        sourceMeanAt W β hβ δ r K (growingQueryTime δ e.val) z.2 = 0 := by
  filter_upwards [actualLinkedSource_projection_kills_posterior_ae W β hβ δ hδ r K]
    with z hz
  have hmean := actualGrowingMeanAt_trace_eq_sourceMeanAt W β hβ δ hδ r K z.2
    e.castSucc (growingQueryTime δ e.val)
    ((growingQueryTime_strictMono δ hδ).monotone (Nat.le_succ _))
  have hz' := hz e.castSucc
  change fineCellRemainingProjection W β hβ δ r K e z *ᵥ
    actualGrowingMeanAt W β hβ δ (r+K) K (growingQueryTime δ e.val)
      (paperScalarPastTrace r (r+K) (Target W β hβ δ r K) (Update δ r K) K
        (Initial δ r K z.2,1) (Original δ r K z.2) e.castSucc) = 0 at hz'
  rw [hmean] at hz'
  exact hz'

end SKConstants.Completion.N9T1
