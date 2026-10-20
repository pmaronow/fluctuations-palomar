module

public import SKConstants.Completion.N9c.Node
public import SKConstants.Completion.Blueprint5.FineStatements
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators

namespace SKConstants.Completion.N9Y2
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal M1 LFine N9c LM3
variable {Ω : Type*} [MeasurableSpace Ω]

theorem earlierCell_horizon_eq (δ : ℝ≥0) (hδ : 0 < δ) (K : ℕ) (e : Fin K) :
    growingQueryTime δ e.val +
      (growingQueryDuration δ e.val + (Horizon δ K-growingQueryTime δ (e.val+1))) =
        Horizon δ K := by
  rw [← add_assoc, ← growingQueryTime_succ]
  exact add_tsub_cancel_of_le ((growingQueryTime_strictMono δ hδ).monotone (by omega))

theorem sourceHistories_productFresh_law (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ) (a h f : ℝ≥0)
    (hh : 0 < h) (heq : a+(h+f) = Horizon δ K) :
    (SourceLinkedLaw W β hβ δ r K).map (SourceHistories W β hβ δ r K) =
    ((Measure.pi (fun _ : Fin (r+K) =>
      (scalarPrimitiveBrownianPathLaw W a).prod (scalarPrimitiveBrownianPathLaw W a))).prod
      (freshRowsLaw W h f (r+K))).map
        (fun u i => castDriverHistory heq (freshRowHistory W β hβ a h f (u.1 i,u.2 i))) := by
  rw [sourceHistories_eq_freshRows W β hβ δ hδ r K a h f hh heq]
  let E := MeasurableEquiv.arrowProdEquivProdArrow
    (ScalarContinuousPath a × ScalarContinuousPath a) (ℝ × FreshRowSeed h f) (Fin (r+K))
  let P := (scalarPrimitiveBrownianPathLaw W a).prod (scalarPrimitiveBrownianPathLaw W a)
  let Q := (gaussianReal 0 1).prod (freshRowSeedLaw W h f)
  let R := fun u : (Fin (r+K) → ScalarContinuousPath a × ScalarContinuousPath a) ×
      (Fin (r+K) → ℝ × FreshRowSeed h f) => fun i =>
        castDriverHistory heq (freshRowHistory W β hβ a h f (u.1 i,u.2 i))
  have hR : Measurable R := Measurable.of_eval fun i =>
    ((measurable_castDriverHistory heq).comp (measurable_freshRowHistory W β hβ a h f)).comp
      (((measurable_pi_apply i).comp measurable_fst).prodMk
        ((measurable_pi_apply i).comp measurable_snd))
  have hp := measurePreserving_arrowProdEquivProdArrow
    (ScalarContinuousPath a × ScalarContinuousPath a) (ℝ × FreshRowSeed h f) (Fin (r+K))
    (fun _ => P) (fun _ => Q)
  have he := congrArg (fun μ => μ.map R) hp.map_eq
  rw [Measure.map_map hR E.measurable] at he
  exact he

theorem fineEarlierSource_factorization_holds (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ) (e : Fin K) :
    (SourceLinkedLaw W β hβ δ r K).map (SourceHistories W β hβ δ r K) =
    ((Measure.pi (fun _ : Fin (r+K) =>
      (scalarPrimitiveBrownianPathLaw W (growingQueryTime δ e.val)).prod
        (scalarPrimitiveBrownianPathLaw W (growingQueryTime δ e.val)))).prod
      (freshRowsLaw W (growingQueryDuration δ e.val)
        (Horizon δ K-growingQueryTime δ (e.val+1)) (r+K))).map
      (fun u i => castDriverHistory (earlierCell_horizon_eq δ hδ K e)
        (freshRowHistory W β hβ (growingQueryTime δ e.val) (growingQueryDuration δ e.val)
          (Horizon δ K-growingQueryTime δ (e.val+1)) (u.1 i,u.2 i))) :=
  sourceHistories_productFresh_law W β hβ δ hδ r K _ _ _
    (growingQueryDuration_pos δ hδ _) (earlierCell_horizon_eq δ hδ K e)

theorem sourceHistories_integral_productFresh (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ) (a h f : ℝ≥0)
    (hh : 0 < h) (heq : a+(h+f) = Horizon δ K)
    (F : (Fin (r+K) → ScalarDriverHistory (Horizon δ K)) → ℝ) (hF : Measurable F)
    (hFi : Integrable (fun z => F (SourceHistories W β hβ δ r K z))
      (SourceLinkedLaw W β hβ δ r K)) :
    (∫ z, F (SourceHistories W β hβ δ r K z) ∂SourceLinkedLaw W β hβ δ r K) =
      ∫ p, ∫ u, F (fun i => castDriverHistory heq
        (freshRowHistory W β hβ a h f (p i,u i))) ∂freshRowsLaw W h f (r+K)
        ∂Measure.pi (fun _ : Fin (r+K) =>
          (scalarPrimitiveBrownianPathLaw W a).prod (scalarPrimitiveBrownianPathLaw W a)) := by
  let P := Measure.pi (fun _ : Fin (r+K) =>
    (scalarPrimitiveBrownianPathLaw W a).prod (scalarPrimitiveBrownianPathLaw W a))
  let Q := freshRowsLaw W h f (r+K)
  have : IsProbabilityMeasure Q := freshRowsLaw_probability W h f (r+K)
  have : IsFiniteMeasure Q := IsZeroOrProbabilityMeasure.toIsFiniteMeasure Q
  have : SigmaFinite Q := IsFiniteMeasure.toSigmaFinite Q
  have : SFinite Q := inferInstance
  let R := fun u : (Fin (r+K) → ScalarContinuousPath a × ScalarContinuousPath a) ×
      (Fin (r+K) → ℝ × FreshRowSeed h f) => fun i =>
        castDriverHistory heq (freshRowHistory W β hβ a h f (u.1 i,u.2 i))
  have hR : Measurable R := Measurable.of_eval fun i =>
    ((measurable_castDriverHistory heq).comp (measurable_freshRowHistory W β hβ a h f)).comp
      (((measurable_pi_apply i).comp measurable_fst).prodMk
        ((measurable_pi_apply i).comp measurable_snd))
  have hlaw : (SourceLinkedLaw W β hβ δ r K).map (SourceHistories W β hβ δ r K) =
      (P.prod Q).map R := sourceHistories_productFresh_law W β hβ δ hδ r K a h f hh heq
  have hi : Integrable F ((P.prod Q).map R) := by
    rw [← hlaw]
    exact (integrable_map_measure hF.aestronglyMeasurable
      (measurable_SourceHistories W β hβ δ r K).aemeasurable).mpr hFi
  have hip : Integrable (fun u => F (R u)) (P.prod Q) :=
    (integrable_map_measure hF.aestronglyMeasurable hR.aemeasurable).mp hi
  calc
    _ = ∫ v, F v ∂(SourceLinkedLaw W β hβ δ r K).map (SourceHistories W β hβ δ r K) :=
      (integral_map (measurable_SourceHistories W β hβ δ r K).aemeasurable
        hF.aestronglyMeasurable).symm
    _ = ∫ v, F v ∂(P.prod Q).map R := by rw [hlaw]
    _ = ∫ u, F (R u) ∂P.prod Q := integral_map hR.aemeasurable hF.aestronglyMeasurable
    _ = _ := integral_prod (μ := P) (ν := Q) (fun u => F (R u)) hip

def earlierFreshTarget (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (K : ℕ) (e : Fin K)
    (p : ScalarContinuousPath (growingQueryTime δ e.val) ×
      ScalarContinuousPath (growingQueryTime δ e.val))
    (u : ℝ × FreshRowSeed (growingQueryDuration δ e.val)
      (Horizon δ K-growingQueryTime δ (e.val+1))) : ℝ :=
  NDH.historyMixedRow W β δ K
    (castDriverHistory (earlierCell_horizon_eq δ hδ K e)
      (freshRowHistory W β hβ (growingQueryTime δ e.val) (growingQueryDuration δ e.val)
        (Horizon δ K-growingQueryTime δ (e.val+1)) (p,u))) (LGram.posteriorIndex K e)

theorem measurable_earlierFreshTarget (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (K : ℕ) (e : Fin K)
    (p : ScalarContinuousPath (growingQueryTime δ e.val) ×
      ScalarContinuousPath (growingQueryTime δ e.val)) :
    Measurable (earlierFreshTarget W β hβ δ hδ K e p) :=
  ((EuclideanSpace.proj (LGram.posteriorIndex K e)).continuous.measurable.comp
    (NDH.measurable_historyMixedRow W β δ K)).comp
      (((measurable_castDriverHistory _).comp (measurable_freshRowHistory W β hβ _ _ _)).comp
        (measurable_const.prodMk measurable_id))

theorem earlierFreshTargets_independent (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (K : ℕ) (e : Fin K) (n : ℕ)
    (p : Fin n → ScalarContinuousPath (growingQueryTime δ e.val) ×
      ScalarContinuousPath (growingQueryTime δ e.val)) :
    iIndepFun (fun i u => earlierFreshTarget W β hβ δ hδ K e (p i) (u i))
      (freshRowsLaw W (growingQueryDuration δ e.val)
        (Horizon δ K-growingQueryTime δ (e.val+1)) n) :=
  iIndepFun_pi (fun i => (measurable_earlierFreshTarget W β hβ δ hδ K e (p i)).aemeasurable)

theorem sourcePastTargets_productFresh_law (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ) (e : Fin K) :
    (SourceLinkedLaw W β hβ δ r K).map
      (fun z => ((fun i => historyDriverPast (growingQueryTime δ e.val) (Horizon δ K)
        ((growingQueryTime_strictMono δ hδ).monotone (by omega))
          (SourceHistories W β hβ δ r K z i)), SourceTargets W β hβ δ r K z.2 e)) =
    ((Measure.pi (fun _ : Fin (r+K) =>
      (scalarPrimitiveBrownianPathLaw W (growingQueryTime δ e.val)).prod
        (scalarPrimitiveBrownianPathLaw W (growingQueryTime δ e.val)))).prod
      (freshRowsLaw W (growingQueryDuration δ e.val)
        (Horizon δ K-growingQueryTime δ (e.val+1)) (r+K))).map
      (fun u => (u.1,fun i => earlierFreshTarget W β hβ δ hδ K e (u.1 i) (u.2 i))) := by
  let a := growingQueryTime δ e.val
  let h := growingQueryDuration δ e.val
  let f := Horizon δ K-growingQueryTime δ (e.val+1)
  have ha : a ≤ Horizon δ K := (growingQueryTime_strictMono δ hδ).monotone (by omega)
  let F := fun v : Fin (r+K) → ScalarDriverHistory (Horizon δ K) =>
    ((fun i => historyDriverPast a (Horizon δ K) ha (v i)),
      fun i => NDH.historyMixedRow W β δ K (v i) (LGram.posteriorIndex K e))
  have hF : Measurable F :=
    (Measurable.of_eval fun i => (measurable_historyDriverPast a _ ha).comp
      (measurable_pi_apply i)).prodMk
    (Measurable.of_eval fun i => ((EuclideanSpace.proj (LGram.posteriorIndex K e)).continuous.measurable.comp
      (NDH.measurable_historyMixedRow W β δ K)).comp (measurable_pi_apply i))
  have hsrc : F ∘ SourceHistories W β hβ δ r K =
      (fun z => ((fun i => historyDriverPast a (Horizon δ K) ha
        (SourceHistories W β hβ δ r K z i)),SourceTargets W β hβ δ r K z.2 e)) := by
    funext z
    apply Prod.ext
    · rfl
    · funext i
      exact (sourceTarget_eq_history W β hβ δ hδ r K z e i).symm
  let R := fun u : (Fin (r+K) → ScalarContinuousPath a × ScalarContinuousPath a) ×
      (Fin (r+K) → ℝ × FreshRowSeed h f) => fun i =>
        castDriverHistory (earlierCell_horizon_eq δ hδ K e)
          (freshRowHistory W β hβ a h f (u.1 i,u.2 i))
  have hR : Measurable R := Measurable.of_eval fun i =>
    ((measurable_castDriverHistory _).comp (measurable_freshRowHistory W β hβ a h f)).comp
      (((measurable_pi_apply i).comp measurable_fst).prodMk
        ((measurable_pi_apply i).comp measurable_snd))
  have he := congrArg (fun μ => μ.map F)
    (fineEarlierSource_factorization_holds W β hβ δ hδ r K e)
  rw [Measure.map_map hF (measurable_SourceHistories W β hβ δ r K),hsrc,
    Measure.map_map hF hR] at he
  refine he.trans ?_
  apply Measure.map_congr
  apply ae_of_all
  intro u
  apply Prod.ext
  · funext i
    exact freshRowHistory_at_horizon_past W β hβ a h f (Horizon δ K)
      (earlierCell_horizon_eq δ hδ K e) ha (u.1 i,u.2 i)
  · rfl

theorem historyTarget_abs_le (W : BrownianSystem Ω) (β : ℝ) (δ : ℝ≥0)
    (K : ℕ) (e : Fin K) (v : ScalarDriverHistory (Horizon δ K)) :
    |NDH.historyMixedRow W β δ K v (LGram.posteriorIndex K e)| ≤
      2/actualFineScale W β δ e.val := by
  simp only [NDH.historyMixedRow,LGram.posteriorIndex,WithLp.ofLp_toLp,Fin.append_left]
  rw [abs_div,abs_of_nonneg (NNReal.coe_nonneg _)]
  apply div_le_div_of_nonneg_right _ (NNReal.coe_nonneg _)
  exact (abs_sub _ _).trans (by
    have h1 := (actualParisiFullMagnetization_curvature_bounds β
      (growingQueryTime δ (e.val+1))
      (historyPathAt (Horizon δ K) v.2.1 (growingQueryTime δ (e.val+1)))).1
    have h0 := (actualParisiFullMagnetization_curvature_bounds β
      (growingQueryTime δ e.val)
      (historyPathAt (Horizon δ K) v.2.1 (growingQueryTime δ e.val))).1
    linarith)

theorem earlierFreshTarget_memLp (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (K : ℕ) (e : Fin K)
    (p : ScalarContinuousPath (growingQueryTime δ e.val) ×
      ScalarContinuousPath (growingQueryTime δ e.val)) (q : ℝ≥0∞) :
    MemLp (earlierFreshTarget W β hβ δ hδ K e p) q
      ((gaussianReal 0 1).prod (freshRowSeedLaw W (growingQueryDuration δ e.val)
        (Horizon δ K-growingQueryTime δ (e.val+1)))) :=
  MemLp.of_bound (measurable_earlierFreshTarget W β hβ δ hδ K e p).aestronglyMeasurable
    (2/actualFineScale W β δ e.val) (ae_of_all _ fun u => by
      rw [Real.norm_eq_abs]
      exact historyTarget_abs_le W β δ K e _)

end SKConstants.Completion.N9Y2
