module

public import SKConstants.Completion.N9c.FreshHistoryLaw
public import SKConstants.Completion.LC1.QuerySpinMoments
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SKConstants.Completion.N9c
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal FineInformation M1 LFine N9
variable {Ω : Type*} [MeasurableSpace Ω]

def historyCellEndpoint (a h f : ℝ≥0) (u : ScalarDriverHistory (a+(h+f))) : ℝ :=
  (u.2.2.1 ⟨(a : ℝ)+(h : ℝ),add_nonneg a.coe_nonneg h.coe_nonneg,
      by simp only [NNReal.coe_add]; linarith [f.coe_nonneg]⟩ -
    u.2.2.1 ⟨a,a.coe_nonneg,
      by simp only [NNReal.coe_add]; linarith [h.coe_nonneg,f.coe_nonneg]⟩) / Real.sqrt h

theorem measurable_historyCellEndpoint (a h f : ℝ≥0) :
    Measurable (historyCellEndpoint a h f) :=
  (((ContinuousMap.measurable_eval _).comp measurable_snd.snd.fst).sub
    ((ContinuousMap.measurable_eval _).comp measurable_snd.snd.fst)).div_const _

theorem freshRowHistory_cellEndpoint (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (a h f : ℝ≥0) (hh : 0 < h) (u : FreshRowInput a h f) :
    historyCellEndpoint a h f (freshRowHistory W β hβ a h f u) = u.2.1 := by
  have hhf : (h : ℝ) ≤ (h : ℝ)+f := le_add_of_nonneg_right f.coe_nonneg
  have haj : (a : ℝ) ≤ (a : ℝ)+h := le_add_of_nonneg_right h.coe_nonneg
  simp only [historyCellEndpoint,freshRowHistory,NDH.pairFullHistory,freshRowDrivers,
    scalarConcatPath,ContinuousMap.coe_mk,NNReal.coe_add,
    projIcc_of_right_le a.coe_nonneg haj,projIcc_right,add_sub_cancel_left,
    projIcc_of_mem _ ⟨h.coe_nonneg,hhf⟩,sub_self,projIcc_left,
    zero_sub,projIcc_of_le_left f.coe_nonneg (neg_nonpos.mpr h.coe_nonneg),
    scalarQueryBridgeComplete_endpoint h hh,scalarQueryBridgeComplete_zero]
  have hs : Real.sqrt (h : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (NNReal.coe_pos.mpr hh)).ne'
  field_simp
  ring

theorem freshRowMixedProduct_integrable (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (a h f : ℝ≥0) :
    Integrable (fun u : FreshRowInput a h f =>
      (if freshRowSign W β hβ a h f u.1.1 u.1.2 u.2 then (1 : ℝ) else -1) * u.2.1)
      (freshRowInputLaw W a h f) := by
  have he : Integrable (fun z : ℝ × FreshRowSeed h f => z.1)
      ((gaussianReal 0 1).prod (freshRowSeedLaw W h f)) :=
    ((memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable (by norm_num)).comp_fst _
  have hs : Measurable (fun u : FreshRowInput a h f =>
      if freshRowSign W β hβ a h f u.1.1 u.1.2 u.2 then (1 : ℝ) else -1) :=
    (measurable_of_finite (fun b : Bool => if b then (1 : ℝ) else -1)).comp
      (N9b.measurable_freshRowSign_param W β hβ a h f
        (fun u : FreshRowInput a h f => u.1.1) (fun u => u.1.2) (fun u => u.2)
        measurable_fst.fst measurable_fst.snd measurable_snd)
  apply (he.comp_snd _).bdd_mul hs.aestronglyMeasurable (c := 1)
  exact ae_of_all _ fun u => by split <;> norm_num

theorem freshRowMixedMean_integral (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (a h f : ℝ≥0) (hh : 0 < h) :
    (∫ p, freshRowMixedMean W β hβ a h f p
      ∂(scalarPrimitiveBrownianPathLaw W a).prod (scalarPrimitiveBrownianPathLaw W a)) =
      LQ.actualParisiQueryIntervalSpinMean W β a (a+h) := by
  let H := a+(h+f)
  let μ := freshRowInputLaw W a h f
  let F : ScalarDriverHistory H → ℝ := fun v => scalarHiddenSign v.1 * historyCellEndpoint a h f v
  have hF : Measurable F :=
    ((measurable_of_finite scalarHiddenSign).comp measurable_fst).mul
      (measurable_historyCellEndpoint a h f)
  have hlaw : HasLaw (freshRowHistory W β hβ a h f)
      ((actualParisiFullQuerySpinLaw W W β H).map (NDH.modelFullHistory W W β hβ H)) μ :=
    ⟨(measurable_freshRowHistory W β hβ a h f).aemeasurable,
      freshRow_fullHistory_law W β hβ a h f hh⟩
  have hmean : (∫ p, freshRowMixedMean W β hβ a h f p
      ∂(scalarPrimitiveBrownianPathLaw W a).prod (scalarPrimitiveBrownianPathLaw W a)) =
        ∫ u, F (freshRowHistory W β hβ a h f u) ∂μ := by
    have hp := integral_prod _ (freshRowMixedProduct_integrable W β hβ a h f)
    change (∫ u : FreshRowInput a h f,
      (if freshRowSign W β hβ a h f u.1.1 u.1.2 u.2 then (1 : ℝ) else -1) * u.2.1 ∂μ) =
        ∫ p, freshRowMixedMean W β hβ a h f p
          ∂(scalarPrimitiveBrownianPathLaw W a).prod (scalarPrimitiveBrownianPathLaw W a) at hp
    rw [← hp]
    apply integral_congr_ae
    apply ae_of_all
    intro u
    change scalarHiddenSign (freshRowSign W β hβ a h f u.1.1 u.1.2 u.2) * u.2.1 =
      scalarHiddenSign (freshRowSign W β hβ a h f u.1.1 u.1.2 u.2) *
        historyCellEndpoint a h f (freshRowHistory W β hβ a h f u)
    rw [freshRowHistory_cellEndpoint W β hβ a h f hh u]
  have ht := hlaw.integral_comp hF.aestronglyMeasurable
  simp only [Function.comp_apply] at ht
  rw [hmean,ht,
    integral_map (NDH.measurable_modelFullHistory W W β hβ H).aemeasurable
      hF.aestronglyMeasurable]
  let Q := actualParisiQueryBrownianSystem W W β hβ
  have hv := ((actualParisiFullQuerySpinLaw_drivers_hasLaw W W β H).measurePreserving
    (measurable_fst.snd.prodMk measurable_snd)).quasiMeasurePreserving.ae
      (brownianFinitePath_version Q H)
  have he : (fun u => F (NDH.modelFullHistory W W β hβ H u)) =ᵐ[
      actualParisiFullQuerySpinLaw W W β H]
      (fun u => ((Q.B (a+h) (u.1.2,u.2)-Q.B a (u.1.2,u.2))*scalarHiddenSign u.1.1) /
        Real.sqrt h) := by
    filter_upwards [hv] with u hu
    dsimp only [F,NDH.modelFullHistory,historyCellEndpoint]
    rw [hu,hu]
    change scalarHiddenSign u.1.1 *
      ((Q.B (a+h) (u.1.2,u.2)-Q.B a (u.1.2,u.2))/Real.sqrt h) = _
    ring
  have hTH : a+h ≤ H := by
    dsimp [H]
    rw [← add_assoc]
    exact le_self_add
  rw [integral_congr_ae he,integral_div,
    LC1.actualQuerySpinLaw_query_spin_moment W W β hβ a (a+h) H
      (by exact le_self_add) hTH]
  unfold LQ.actualParisiQueryIntervalSpinMean
  simp only [NNReal.coe_add,add_sub_cancel_left]
  congr 1
  apply intervalIntegral.integral_congr
  intro v _
  ring

theorem freshRowHistory_at_horizon_past (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (a h f H : ℝ≥0) (heq : a+(h+f) = H) (ha : a ≤ H) (u : FreshRowInput a h f) :
    historyDriverPast a H ha (castDriverHistory heq (freshRowHistory W β hβ a h f u)) = u.1 := by
  subst H
  exact freshRowDrivers_past a h f u.1 u.2

theorem sourceFreshMixedMean_hasLaw (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ) (a h f : ℝ≥0)
    (hh : 0 < h) (heq : a+(h+f) = Horizon δ K) (ha : a ≤ Horizon δ K) (i : Fin (r+K)) :
    HasLaw (fun u => sourceFreshMixedMean W β hβ δ r K a h f ha u i)
      (((scalarPrimitiveBrownianPathLaw W a).prod (scalarPrimitiveBrownianPathLaw W a)).map
        (freshRowMixedMean W β hβ a h f)) (SourceLinkedLaw W β hβ δ r K) := by
  let H := Horizon δ K
  let F : ScalarDriverHistory H → ℝ :=
    freshRowMixedMean W β hβ a h f ∘ historyDriverPast a H ha
  have hF : Measurable F := (measurable_freshRowMixedMean W β hβ a h f).comp
    (measurable_historyDriverPast a H ha)
  let ν := (actualParisiFullQuerySpinLaw W W β H).map (F ∘ NDH.modelFullHistory W W β hβ H)
  have hνprob : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
  have hEval : HasLaw (fun u : Fin (r+K) → ℝ => u i) ν
      (Measure.pi (fun _ : Fin (r+K) => ν)) :=
    ⟨(measurable_pi_apply i).aemeasurable,(measurePreserving_eval _ i).map_eq⟩
  have hcoord : HasLaw (fun u => sourceFreshMixedMean W β hβ δ r K a h f ha u i) ν
      (SourceLinkedLaw W β hβ δ r K) :=
    hEval.comp (sourceRowStatistics_hasLaw W β hβ δ hδ r K F hF)
  have he := congrArg (fun μ => μ.map F)
    (freshRowHistory_law_at_horizon W β hβ a h f H hh heq)
  rw [Measure.map_map hF ((measurable_castDriverHistory heq).comp
      (measurable_freshRowHistory W β hβ a h f)),
    Measure.map_map hF (NDH.measurable_modelFullHistory W W β hβ H)] at he
  have hfun : F ∘ (castDriverHistory heq ∘ freshRowHistory W β hβ a h f) =
      freshRowMixedMean W β hβ a h f ∘ Prod.fst := by
    funext u
    exact congrArg (freshRowMixedMean W β hβ a h f)
      (freshRowHistory_at_horizon_past W β hβ a h f H heq ha u)
  rw [hfun,← Measure.map_map (measurable_freshRowMixedMean W β hβ a h f) measurable_fst] at he
  change ((freshRowInputLaw W a h f).map Prod.fst).map (freshRowMixedMean W β hβ a h f) = ν at he
  rw [freshRowInputLaw,Measure.map_fst_prod,measure_univ,one_smul] at he
  rw [← he] at hcoord
  exact hcoord

theorem sourceFreshMixedMean_integrable (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ) (a h f : ℝ≥0)
    (hh : 0 < h) (heq : a+(h+f) = Horizon δ K) (ha : a ≤ Horizon δ K) (i : Fin (r+K)) :
    Integrable (fun u => sourceFreshMixedMean W β hβ δ r K a h f ha u i)
      (SourceLinkedLaw W β hβ δ r K) := by
  have hp : Integrable (freshRowMixedMean W β hβ a h f)
      ((scalarPrimitiveBrownianPathLaw W a).prod (scalarPrimitiveBrownianPathLaw W a)) :=
    (freshRowMixedProduct_integrable W β hβ a h f).integral_prod_left
  apply (sourceFreshMixedMean_hasLaw W β hβ δ hδ r K a h f hh heq ha i).integrable
  exact (integrable_map_measure measurable_id.aestronglyMeasurable
    (measurable_freshRowMixedMean W β hβ a h f).aemeasurable).mpr hp

theorem sourceFreshMixedMean_integral (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ) (a h f : ℝ≥0)
    (hh : 0 < h) (heq : a+(h+f) = Horizon δ K) (ha : a ≤ Horizon δ K) (i : Fin (r+K)) :
    (∫ u, sourceFreshMixedMean W β hβ δ r K a h f ha u i ∂SourceLinkedLaw W β hβ δ r K) =
      LQ.actualParisiQueryIntervalSpinMean W β a (a+h) := by
  have he := (sourceFreshMixedMean_hasLaw W β hβ δ hδ r K a h f hh heq ha i).integral_comp
    (show AEStronglyMeasurable (id : ℝ → ℝ) _ from measurable_id.aestronglyMeasurable)
  simp only [Function.comp_apply,id_eq] at he
  rw [he,integral_map (f := fun x : ℝ => x)
    (measurable_freshRowMixedMean W β hβ a h f).aemeasurable
    measurable_id.aestronglyMeasurable]
  exact freshRowMixedMean_integral W β hβ a h f hh

theorem sourceFreshMixedMean_average_integral (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ) (hn : 0 < r+K) (a h f : ℝ≥0)
    (hh : 0 < h) (heq : a+(h+f) = Horizon δ K) (ha : a ≤ Horizon δ K) :
    (∫ u, (((r+K : ℕ) : ℝ)⁻¹ * ∑ i, sourceFreshMixedMean W β hβ δ r K a h f ha u i)
      ∂SourceLinkedLaw W β hβ δ r K) = LQ.actualParisiQueryIntervalSpinMean W β a (a+h) := by
  rw [integral_const_mul,integral_finsetSum _ (fun i _ =>
    sourceFreshMixedMean_integrable W β hβ δ hδ r K a h f hh heq ha i)]
  simp only [sourceFreshMixedMean_integral W β hβ δ hδ r K a h f hh heq ha,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  rw [← mul_assoc,inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hn.ne'),one_mul]

end SKConstants.Completion.N9c
