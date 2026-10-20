module

public import SKConstants.Completion.Y1.StaticMoments
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators

namespace SKConstants.Completion.Y1
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal LFine LQ N9b N9c M1
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]

theorem historyDriverPast_model_ae (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (s H : ℝ≥0) (hs : s ≤ H) :
    (fun u => historyDriverPast s H hs (NDH.modelFullHistory W Z β hβ H u)) =ᵐ[
      actualParisiFullQuerySpinLaw W Z β H]
      (fun u => modelDriverPast W Z β hβ s (u.1.2,u.2)) := by
  have hl := (actualParisiFullQuerySpinLaw_drivers_hasLaw W Z β H).measurePreserving
    (measurable_fst.snd.prodMk measurable_snd)
  filter_upwards [hl.quasiMeasurePreserving.ae
      (brownianFinitePath_version (actualParisiQueryBrownianSystem W Z β hβ) H),
    hl.quasiMeasurePreserving.ae
      (brownianFinitePath_version (actualParisiAuxBrownianSystem W Z β hβ) H),
    hl.quasiMeasurePreserving.ae
      (brownianFinitePath_version (actualParisiQueryBrownianSystem W Z β hβ) s),
    hl.quasiMeasurePreserving.ae
      (brownianFinitePath_version (actualParisiAuxBrownianSystem W Z β hβ) s)] with u hBH hDH hBs hDs
  apply Prod.ext
  · exact ContinuousMap.ext fun t => (hBH ⟨t,t.property.1,t.property.2.trans hs⟩).trans (hBs t).symm
  · exact ContinuousMap.ext fun t => (hDH ⟨t,t.property.1,t.property.2.trans hs⟩).trans (hDs t).symm

theorem sourceHistory_coordinate_hasLaw (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ) (i : Fin (r+K)) :
    HasLaw (fun z => SourceHistories W β hβ δ r K z i)
      ((actualParisiFullQuerySpinLaw W W β (Horizon δ K)).map
        (NDH.modelFullHistory W W β hβ (Horizon δ K))) (SourceLinkedLaw W β hβ δ r K) := by
  let ν := (actualParisiFullQuerySpinLaw W W β (Horizon δ K)).map
    (NDH.modelFullHistory W W β hβ (Horizon δ K))
  have hv : HasLaw (SourceHistories W β hβ δ r K)
      (Measure.pi (fun _ : Fin (r+K) => ν)) (SourceLinkedLaw W β hβ δ r K) :=
    ⟨(measurable_SourceHistories W β hβ δ r K).aemeasurable,
      NDH.literal_linked_source_full_histories_law W β hβ δ hδ r K⟩
  exact (show HasLaw (fun v : Fin (r+K) → ScalarDriverHistory (Horizon δ K) => v i) ν
    (Measure.pi (fun _ : Fin (r+K) => ν)) from
      ⟨(measurable_pi_apply i).aemeasurable,(measurePreserving_eval _ i).map_eq⟩).comp hv

theorem sourcePastTarget_integral_eq_model (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ) (e : Fin K) (i : Fin (r+K))
    (F : (ScalarContinuousPath (growingQueryTime δ e.val) ×
      ScalarContinuousPath (growingQueryTime δ e.val)) × ℝ → ℝ) (hF : Measurable F) :
    (∫ z, F (historyDriverPast (growingQueryTime δ e.val) (Horizon δ K)
        ((growingQueryTime_strictMono δ hδ).monotone (by omega))
        (SourceHistories W β hβ δ r K z i),SourceTargets W β hβ δ r K z.2 e i)
        ∂SourceLinkedLaw W β hβ δ r K) =
      ∫ u, F (modelDriverPast W W β hβ (growingQueryTime δ e.val) u,
        normalizedIncrement W β (growingQueryTime δ e.val)
          (growingQueryTime δ (e.val+1)) u.1) ∂W.law.prod W.law := by
  let a := growingQueryTime δ e.val
  let H := Horizon δ K
  have ha : a ≤ H := (growingQueryTime_strictMono δ hδ).monotone (by omega)
  let G := fun v : ScalarDriverHistory H =>
    F (historyDriverPast a H ha v,NDH.historyMixedRow W β δ K v (LGram.posteriorIndex K e))
  have hG : Measurable G := hF.comp ((measurable_historyDriverPast a H ha).prodMk
    ((EuclideanSpace.proj (LGram.posteriorIndex K e)).continuous.measurable.comp
      (NDH.measurable_historyMixedRow W β δ K)))
  have he := (sourceHistory_coordinate_hasLaw W β hβ δ hδ r K i).integral_comp
    hG.aestronglyMeasurable
  simp only [Function.comp_apply] at he
  have hsrc : (fun z => G (SourceHistories W β hβ δ r K z i)) =
      (fun z => F (historyDriverPast a H ha (SourceHistories W β hβ δ r K z i),
        SourceTargets W β hβ δ r K z.2 e i)) := by
    funext z
    exact congrArg (fun x => F (historyDriverPast a H ha
      (SourceHistories W β hβ δ r K z i),x)) (sourceTarget_eq_history W β hβ δ hδ r K z e i).symm
  rw [hsrc,integral_map (NDH.measurable_modelFullHistory W W β hβ H).aemeasurable
    hG.aestronglyMeasurable] at he
  have hmodel : (fun u => G (NDH.modelFullHistory W W β hβ H u)) =ᵐ[
      actualParisiFullQuerySpinLaw W W β H]
      (fun u => F (modelDriverPast W W β hβ a (u.1.2,u.2),
        normalizedIncrement W β a (growingQueryTime δ (e.val+1)) u.1.2)) := by
    filter_upwards [historyDriverPast_model_ae W W β hβ a H ha,
      NDH.historyMixedRow_model_ae W β hβ δ hδ K] with u hp ht
    have ht' := congrArg (fun v : EuclideanSpace ℝ (Fin (K+(K+1))) =>
      v (LGram.posteriorIndex K e)) ht
    change NDH.historyMixedRow W β δ K (NDH.modelFullHistory W W β hβ H u)
      (LGram.posteriorIndex K e) = _ at ht'
    change F (_,_) = _
    rw [hp,ht']
    simp only [actualParisiFullMixedRow,actualParisiNormalizedPosteriorRow,LGram.posteriorIndex,
      WithLp.ofLp_toLp,Fin.append_left,normalizedIncrement,a]
  rw [integral_congr_ae hmodel] at he
  exact he.trans ((actualParisiFullQuerySpinLaw_drivers_hasLaw W W β H).integral_comp
    (hF.comp ((measurable_modelDriverPast W W β hβ a).prodMk
      ((measurable_normalizedIncrement W β a _).comp measurable_fst))).aestronglyMeasurable)

theorem sourceTarget_past_weighted_moments_le (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ) (e : Fin K) (i : Fin (r+K))
    (F : ScalarContinuousPath (growingQueryTime δ e.val) ×
      ScalarContinuousPath (growingQueryTime δ e.val) → ℝ)
    (hF : Measurable F) (hcap : ∀ p, |F p| ≤ 1) :
    let f := fun z => F (historyDriverPast (growingQueryTime δ e.val) (Horizon δ K)
      ((growingQueryTime_strictMono δ hδ).monotone (by omega))
      (SourceHistories W β hβ δ r K z i))
    (∫ z, (f z*SourceTargets W β hβ δ r K z.2 e i)^2 ∂SourceLinkedLaw W β hβ δ r K) ≤
      (meshDuration δ e.val*(∫ z, f z^2 ∂SourceLinkedLaw W β hβ δ r K)) /
        (actualFineScale W β δ e.val)^2 ∧
    (∫ z, (f z*SourceTargets W β hβ δ r K z.2 e i)^4 ∂SourceLinkedLaw W β hβ δ r K) ≤
      (3*(meshDuration δ e.val)^2*(∫ z, f z^2 ∂SourceLinkedLaw W β hβ δ r K)) /
        (actualFineScale W β δ e.val)^4 := by
  dsimp only
  rw [sourcePastTarget_integral_eq_model W β hβ δ hδ r K e i
      (fun p => (F p.1*p.2)^2) (by fun_prop),
    sourcePastTarget_integral_eq_model W β hβ δ hδ r K e i
      (fun p => (F p.1*p.2)^4) (by fun_prop),
    sourcePastTarget_integral_eq_model W β hβ δ hδ r K e i
      (fun p => F p.1^2) (by fun_prop)]
  simpa only [growingQueryTime_succ,NNReal.coe_add,add_sub_cancel_left,
    actualFineScale,meshDuration] using normalizedIncrement_driverPast_weighted_moments_le W W β hβ
      (growingQueryTime δ e.val) (growingQueryTime δ (e.val+1))
      ((growingQueryTime_strictMono δ hδ).monotone (Nat.le_succ _)) F hF hcap

end SKConstants.Completion.Y1
