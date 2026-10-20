module

public import SKConstants.Completion.N9b.Node
public import SKConstants.Completion.NDH.MixedRows
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

def freshRowMixedMean (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (a h f : ℝ≥0) (p : ScalarContinuousPath a × ScalarContinuousPath a) : ℝ :=
  ∫ z : ℝ × FreshRowSeed h f,
    (if freshRowSign W β hβ a h f p.1 p.2 z then (1 : ℝ) else -1) * z.1
      ∂(gaussianReal 0 1).prod (freshRowSeedLaw W h f)

theorem measurable_freshRowMixedMean (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (a h f : ℝ≥0) : Measurable (freshRowMixedMean W β hβ a h f) := by
  let X := ScalarContinuousPath a × ScalarContinuousPath a
  have hs : Measurable (fun u : X × (ℝ × FreshRowSeed h f) =>
      freshRowSign W β hβ a h f u.1.1 u.1.2 u.2) :=
    N9b.measurable_freshRowSign_param W β hβ a h f
      (fun u : X × (ℝ × FreshRowSeed h f) => u.1.1) (fun u => u.1.2) (fun u => u.2)
      measurable_fst.fst measurable_fst.snd measurable_snd
  have hm : Measurable (fun u : X × (ℝ × FreshRowSeed h f) =>
      (if freshRowSign W β hβ a h f u.1.1 u.1.2 u.2 then (1 : ℝ) else -1) * u.2.1) :=
    ((measurable_of_finite (fun b : Bool => if b then (1 : ℝ) else -1)).comp hs).mul
      measurable_snd.fst
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem frozenQueryMixedMean_eq_row (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (a h f : ℝ≥0) (n : ℕ) (B D : Fin n → ScalarContinuousPath a) (i : Fin n) :
    frozenQueryMixedMean W β hβ a h f B D i =
      freshRowMixedMean W β hβ a h f (B i,D i) := by
  change (∫ z : Fin n → ℝ × FreshRowSeed h f,
      (if freshRowSign W β hβ a h f (B i) (D i) (z i) then (1 : ℝ) else -1) * (z i).1
        ∂Measure.pi (fun _ : Fin n => (gaussianReal 0 1).prod (freshRowSeedLaw W h f))) = _
  exact integral_comp_eval (μ := fun _ : Fin n =>
    (gaussianReal 0 1).prod (freshRowSeedLaw W h f)) (i := i)
    (((measurable_of_finite (fun b : Bool => if b then (1 : ℝ) else -1)).comp
      (measurable_freshRowSign W β hβ a h f (B i) (D i))).mul
        measurable_fst).aestronglyMeasurable

def historyDriverPast (a H : ℝ≥0) (ha : a ≤ H) (u : ScalarDriverHistory H) :
    ScalarContinuousPath a × ScalarContinuousPath a :=
  (scalarInitialAuxiliaryRestriction H a ha u.2.2.1,
   scalarInitialAuxiliaryRestriction H a ha u.2.2.2)

theorem measurable_historyDriverPast (a H : ℝ≥0) (ha : a ≤ H) :
    Measurable (historyDriverPast a H ha) :=
  ((measurable_scalarInitialAuxiliaryRestriction H a ha).comp measurable_snd.snd.fst).prodMk
    ((measurable_scalarInitialAuxiliaryRestriction H a ha).comp measurable_snd.snd.snd)

def sourceFreshMixedMean (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) (a h f : ℝ≥0) (ha : a ≤ Horizon δ K)
    (u : (Fin (r+K) → Bool) × SourceInput δ r K) (i : Fin (r+K)) : ℝ :=
  freshRowMixedMean W β hβ a h f
    (historyDriverPast a (Horizon δ K) ha (SourceHistories W β hβ δ r K u i))

theorem measurable_SourceHistories (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) : Measurable (SourceHistories W β hβ δ r K) := by
  rw [sourceHistories_eq_driverHistories W β hβ δ r K]
  exact (measurable_DriverHistories W β hβ δ (Size r K) K).comp
    (measurable_id.prodMap (measurable_SourceDrivers δ r K))

theorem sourceRowStatistics_hasLaw {A : Type*} [MeasurableSpace A]
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ)
    (F : ScalarDriverHistory (Horizon δ K) → A) (hF : Measurable F) :
    HasLaw (fun u : (Fin (r+K) → Bool) × SourceInput δ r K =>
      fun i => F (SourceHistories W β hβ δ r K u i))
      (Measure.pi (fun _ : Fin (r+K) =>
        (actualParisiFullQuerySpinLaw W W β (Horizon δ K)).map
          (F ∘ NDH.modelFullHistory W W β hβ (Horizon δ K))))
      (SourceLinkedLaw W β hβ δ r K) := by
  have hmap : Measurable (fun u : Fin (r+K) → ScalarDriverHistory (Horizon δ K) =>
      fun i => F (u i)) := Measurable.of_eval fun i => hF.comp (measurable_pi_apply i)
  refine ⟨(hmap.comp (measurable_SourceHistories W β hβ δ r K)).aemeasurable, ?_⟩
  change (SourceLinkedLaw W β hβ δ r K).map
    ((fun u : Fin (r+K) → ScalarDriverHistory (Horizon δ K) => fun i => F (u i)) ∘
      SourceHistories W β hβ δ r K) = _
  rw [← Measure.map_map hmap (measurable_SourceHistories W β hβ δ r K),
    NDH.literal_linked_source_full_histories_law W β hβ δ hδ r K,
    Measure.pi_map_pi (fun _ => hF.aemeasurable)]
  congr 1
  funext i
  exact Measure.map_map hF (NDH.measurable_modelFullHistory W W β hβ (Horizon δ K))

theorem sourceRowStatistics_independent {A : Type*} [MeasurableSpace A]
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ)
    (F : ScalarDriverHistory (Horizon δ K) → A) (hF : Measurable F) :
    iIndepFun (fun i (u : (Fin (r+K) → Bool) × SourceInput δ r K) =>
      F (SourceHistories W β hβ δ r K u i)) (SourceLinkedLaw W β hβ δ r K) := by
  have hlaw := sourceRowStatistics_hasLaw W β hβ δ hδ r K F hF
  let ν := (actualParisiFullQuerySpinLaw W W β (Horizon δ K)).map
    (F ∘ NDH.modelFullHistory W W β hβ (Horizon δ K))
  have hν : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
  have hcoord (i : Fin (r+K)) : HasLaw
      (fun u : (Fin (r+K) → Bool) × SourceInput δ r K =>
        F (SourceHistories W β hβ δ r K u i)) ν (SourceLinkedLaw W β hβ δ r K) := by
    have he : HasLaw (fun x : Fin (r+K) → A => x i) ν
        (Measure.pi (fun _ : Fin (r+K) => ν)) :=
      ⟨(measurable_pi_apply i).aemeasurable, (measurePreserving_eval _ i).map_eq⟩
    exact he.comp hlaw
  exact (iIndepFun_iff_hasLaw_pi_pi hcoord).mpr hlaw

theorem sourceTarget_eq_history (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ)
    (u : (Fin (r+K) → Bool) × SourceInput δ r K) (e : Fin K) (i : Fin (r+K)) :
    SourceTargets W β hβ δ r K u.2 e i =
      NDH.historyMixedRow W β δ K (SourceHistories W β hβ δ r K u i)
        (LGram.posteriorIndex K e) := by
  have he := congrFun (congrFun (NDH.literalSourceRows_eq_historyMixedRows
    W β hβ δ hδ r K) u) i
  simpa only [LGram.literalSourceRows, LGram.paperRows, LGram.posteriorIndex,
    WithLp.ofLp_toLp, Fin.append_left, SourceTargets, Function.comp_apply] using
    congrArg (fun v : EuclideanSpace ℝ (Fin (K+(K+1))) =>
      v (LGram.posteriorIndex K e)) he

theorem sourceFreshMixedMean_target_independent (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ)
    (a h f : ℝ≥0) (ha : a ≤ Horizon δ K) (e : Fin K) :
    iIndepFun (fun i (u : (Fin (r+K) → Bool) × SourceInput δ r K) =>
      (sourceFreshMixedMean W β hβ δ r K a h f ha u i,
        SourceTargets W β hβ δ r K u.2 e i)) (SourceLinkedLaw W β hβ δ r K) := by
  let F : ScalarDriverHistory (Horizon δ K) → ℝ × ℝ := fun z =>
    (freshRowMixedMean W β hβ a h f (historyDriverPast a _ ha z),
      NDH.historyMixedRow W β δ K z (LGram.posteriorIndex K e))
  have hF : Measurable F :=
    ((measurable_freshRowMixedMean W β hβ a h f).comp
      (measurable_historyDriverPast a _ ha)).prodMk
        ((EuclideanSpace.proj (LGram.posteriorIndex K e)).continuous.measurable.comp
          (NDH.measurable_historyMixedRow W β δ K))
  have he : (fun i (u : (Fin (r+K) → Bool) × SourceInput δ r K) =>
      (sourceFreshMixedMean W β hβ δ r K a h f ha u i,
        SourceTargets W β hβ δ r K u.2 e i)) =
      (fun i u => F (SourceHistories W β hβ δ r K u i)) := by
    funext i u
    exact Prod.ext rfl (sourceTarget_eq_history W β hβ δ hδ r K u e i)
  rw [he]
  exact sourceRowStatistics_independent W β hβ δ hδ r K F hF

theorem measurable_sourceFreshMixedMean (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (r K : ℕ)
    (a h f : ℝ≥0) (ha : a ≤ Horizon δ K) (i : Fin (r+K)) :
    Measurable (fun u => sourceFreshMixedMean W β hβ δ r K a h f ha u i) :=
  (measurable_freshRowMixedMean W β hβ a h f).comp
    ((measurable_historyDriverPast a _ ha).comp
      ((measurable_pi_apply i).comp (measurable_SourceHistories W β hβ δ r K)))

theorem sourceFreshMixedMean_target_covariance_lower (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ) (hn : 0 < r+K)
    (a h f : ℝ≥0) (ha : a ≤ Horizon δ K) (e : Fin K) (L : ℝ)
    (hζ : ∀ u i, 0 ≤ sourceFreshMixedMean W β hβ δ r K a h f ha u i ∧
      sourceFreshMixedMean W β hβ δ r K a h f ha u i ≤ L) :
    -L/(r+K : ℕ) ≤ ∫ u,
      (((r+K : ℕ) : ℝ)⁻¹ * ∑ i, sourceFreshMixedMean W β hβ δ r K a h f ha u i) *
        (((r+K : ℕ) : ℝ)⁻¹ * ∑ i, (SourceTargets W β hβ δ r K u.2 e i)^2 - 1)
          ∂SourceLinkedLaw W β hβ δ r K := by
  let R := fun i (u : (Fin (r+K) → Bool) × SourceInput δ r K) =>
    (sourceFreshMixedMean W β hβ δ r K a h f ha u i,
      (SourceTargets W β hβ δ r K u.2 e i)^2)
  have hm (i : Fin (r+K)) : Measurable (R i) :=
    (measurable_sourceFreshMixedMean W β hβ δ r K a h f ha i).prodMk
      ((((measurable_pi_apply i).comp ((measurable_pi_apply e).comp
        (measurable_SourceTargets W β hβ δ r K))).comp measurable_snd).pow_const 2)
  have hind : iIndepFun R (SourceLinkedLaw W β hβ δ r K) :=
    (sourceFreshMixedMean_target_independent W β hβ δ hδ r K a h f ha e).comp
      (fun _ p => (p.1,p.2^2)) (fun _ => by fun_prop)
  exact empirical_covariance_lower (SourceLinkedLaw W β hβ δ r K) (r+K) hn R hm hind L
    (fun i u => hζ u i) (fun _ _ => sq_nonneg _)
    (fun i => (N9b.sourceTarget_memLp W β hβ δ hδ r K hn e i 2).integrable_sq)
    (fun i => N9b.sourceTarget_second W β hβ δ hδ r K hn e i)

end SKConstants.Completion.N9c
