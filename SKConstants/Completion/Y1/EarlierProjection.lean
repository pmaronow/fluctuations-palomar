module

public import SKConstants.Completion.N9T1.Causal
public import SKConstants.Completion.N9Y2.EarlierFactorization
public import SKConstants.Completion.N9Y1.ProjectionTrace
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators Matrix

namespace SKConstants.Completion.Y1
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal FineInformation LFine LQ N9 M1 Blueprint5 N9T1
variable {Ω : Type*} [MeasurableSpace Ω]
attribute [local irreducible] M1.Target M1.Update
  fineCellRemainingProjection fineCellRemovedSquare

def earlierCellFrame (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) (e : Fin K)
    (p : OriginalPastRows (growingQueryTime δ e.val) (r+K)) :
    Matrix (Fin (fineCellRank r K e+1)) (Fin (r+K)) ℝ :=
  fun i => (paperStateBefore r (r+K)
    (fun k p => pastTarget W β hβ δ (growingQueryTime δ e.val) (K-1-k) p)
    (fun _ p _ => p) K (p,1) (zeroStoppedNoise (r+K) K) e.castSucc).2
      (Fin.cast (fineCellRank_rows r K e) i)

theorem earlierCellFrame_orthogonal (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) (e : Fin K)
    (p : OriginalPastRows (growingQueryTime δ e.val) (r+K)) :
    ∀ i k, dot (earlierCellFrame W β hβ δ r K e p i)
      (earlierCellFrame W β hβ δ r K e p k) = if i=k then 1 else 0 := by
  intro i k
  have h := paperStateBefore_orthogonal r (r+K)
    (fun k p => pastTarget W β hβ δ (growingQueryTime δ e.val) (K-1-k) p)
    (fun _ p _ => p) K (p,1) (zeroStoppedNoise (r+K) K)
    (by intro i k; simp [dot,Matrix.one_apply]) e.castSucc
  simpa only [earlierCellFrame,Fin.cast_inj] using
    h (Fin.cast (fineCellRank_rows r K e) i) (Fin.cast (fineCellRank_rows r K e) k)

theorem measurable_earlierCellFrame (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) (e : Fin K) : Measurable (earlierCellFrame W β hβ δ r K e) := by
  have hX : Measurable (fun p : OriginalPastRows (growingQueryTime δ e.val) (r+K) =>
      ((p,(1 : Matrix (Fin (r+K)) (Fin (r+K)) ℝ)),zeroStoppedNoise (r+K) K)) :=
    (measurable_id.prodMk measurable_const).prodMk measurable_const
  have hS := (measurable_paperStateBefore r (r+K)
    (fun k p => pastTarget W β hβ δ (growingQueryTime δ e.val) (K-1-k) p)
    (fun _ p _ => p) (fun k i => (measurable_pi_apply i).comp
      (measurable_pastTarget W β hβ δ _ (r+K) (K-1-k))) (fun _ => measurable_fst)
    K e.castSucc).comp hX
  exact Measurable.of_eval fun i =>
    (measurable_pi_apply (Fin.cast (fineCellRank_rows r K e) i)).comp hS.snd

theorem earlierCellFrame_originalPastRows (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ) (e : Fin K)
    (z : (Fin (r+K) → Bool) × SourceInput δ r K) :
    earlierCellFrame W β hβ δ r K e
      (originalPastRows δ r K (growingQueryTime δ e.val)
        ((growingQueryTime_strictMono δ hδ).monotone (by omega)) z.2) =
      fineCellFrame W β hβ δ r K e z := by
  let a := growingQueryTime δ e.val
  have ha : a ≤ Horizon δ K := (growingQueryTime_strictMono δ hδ).monotone (by omega)
  let p := originalPastRows δ r K a ha z.2
  have hi := paperStateBefore_frame_congr r (r+K) (Target W β hβ δ r K) (Update δ r K)
    (fun k p => pastTarget W β hβ δ a (K-1-k) p) (fun _ p _ => p)
    K (Initial δ r K z.2,1) (p,1) (Original δ r K z.2) (zeroStoppedNoise (r+K) K)
    rfl e.castSucc (by
      intro j hj
      have hj' : j.val < e.val := by simpa only [Fin.val_castSucc] using hj
      rw [pastTargetTrace_eq]
      change SourceTargets W β hβ δ r K z.2 j = _
      rw [sourceTargets_eq_mean_increment W β hβ δ hδ r K j z.2]
      unfold pastTarget
      have ht : growingQueryTime δ (j.val+1) ≤ a :=
        (growingQueryTime_strictMono δ hδ).monotone (by omega)
      have ht' : growingQueryTime δ j.val ≤ a :=
        ((growingQueryTime_strictMono δ hδ).monotone (Nat.le_succ _)).trans ht
      rw [pastMeanAt_originalPastRows W β hβ δ r K a ha _ ht z.2,
        pastMeanAt_originalPastRows W β hβ δ r K a ha _ ht' z.2])
  exact congrArg (fun E : Matrix (Fin (r+(K-e.val))) (Fin (r+K)) ℝ =>
    fun i => E (Fin.cast (fineCellRank_rows r K e) i)) hi.symm

def earlierCellProjection (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) (e : Fin K)
    (p : OriginalPastRows (growingQueryTime δ e.val) (r+K)) :
    Matrix (Fin (r+K)) (Fin (r+K)) ℝ :=
  frameProjection (earlierCellFrame W β hβ δ r K e p)

theorem measurable_earlierCellProjection (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) (e : Fin K) : Measurable (earlierCellProjection W β hβ δ r K e) := by
  have hc : Continuous (frameProjection (m := fineCellRank r K e+1) (n := r+K)) := by
    unfold frameProjection
    fun_prop
  exact hc.measurable.comp (measurable_earlierCellFrame W β hβ δ r K e)

theorem earlierCellProjection_source (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ) (e : Fin K)
    (z : (Fin (r+K) → Bool) × SourceInput δ r K) :
    earlierCellProjection W β hβ δ r K e
      (fun i => N9c.historyDriverPast (growingQueryTime δ e.val) (Horizon δ K)
        ((growingQueryTime_strictMono δ hδ).monotone (by omega))
        (SourceHistories W β hβ δ r K z i)) =
      fineCellRemainingProjection W β hβ δ r K e z := by
  unfold earlierCellProjection
  change frameProjection (earlierCellFrame W β hβ δ r K e
    (originalPastRows δ r K (growingQueryTime δ e.val) _ z.2)) = _
  rw [earlierCellFrame_originalPastRows W β hβ δ hδ r K e z]
  exact fineCellFrame_projection W β hβ δ r K e z

theorem earlierCellProjection_trace_deficit (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) (e : Fin K)
    (p : OriginalPastRows (growingQueryTime δ e.val) (r+K)) :
    (∑ i, ((1 : Matrix (Fin (r+K)) (Fin (r+K)) ℝ)-
      earlierCellProjection W β hβ δ r K e p) i i) = (e.val : ℝ) := by
  have ht := N9Y1.frameProjection_trace (earlierCellFrame W β hβ δ r K e p)
    (earlierCellFrame_orthogonal W β hβ δ r K e p)
  have hn := fineCellRank_dimension r K e
  have hnR : (fineCellRank r K e : ℝ)+((e.val : ℝ)+1) = (r+K : ℕ) := by exact_mod_cast hn
  push_cast at hnR
  simp only [Matrix.sub_apply,Matrix.one_apply_eq,Finset.sum_sub_distrib]
  change (∑ _ : Fin (r+K), (1 : ℝ)) - ∑ i, frameProjection
    (earlierCellFrame W β hβ δ r K e p) i i = _
  rw [ht]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,
    Nat.cast_add,Nat.cast_one]
  linarith

theorem sourcePastProjectionTarget_productFresh_law (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ) (e : Fin K) :
    (SourceLinkedLaw W β hβ δ r K).map (fun z =>
      ((fun i => N9c.historyDriverPast (growingQueryTime δ e.val) (Horizon δ K)
          ((growingQueryTime_strictMono δ hδ).monotone (by omega))
          (SourceHistories W β hβ δ r K z i)),
        fineCellRemainingProjection W β hβ δ r K e z,SourceTargets W β hβ δ r K z.2 e)) =
    ((Measure.pi (fun _ : Fin (r+K) =>
      (scalarPrimitiveBrownianPathLaw W (growingQueryTime δ e.val)).prod
        (scalarPrimitiveBrownianPathLaw W (growingQueryTime δ e.val)))).prod
      (freshRowsLaw W (growingQueryDuration δ e.val)
        (Horizon δ K-growingQueryTime δ (e.val+1)) (r+K))).map
      (fun u => (u.1,earlierCellProjection W β hβ δ r K e u.1,
        fun i => N9Y2.earlierFreshTarget W β hβ δ hδ K e (u.1 i) (u.2 i))) := by
  let G := fun v : OriginalPastRows (growingQueryTime δ e.val) (r+K) × (Fin (r+K) → ℝ) =>
    (v.1,earlierCellProjection W β hβ δ r K e v.1,v.2)
  have hG : Measurable G := measurable_fst.prodMk
    (((measurable_earlierCellProjection W β hβ δ r K e).comp measurable_fst).prodMk measurable_snd)
  have hp : Measurable (fun z => ((fun i => N9c.historyDriverPast
      (growingQueryTime δ e.val) (Horizon δ K)
      ((growingQueryTime_strictMono δ hδ).monotone (by omega))
      (SourceHistories W β hβ δ r K z i)),SourceTargets W β hβ δ r K z.2 e)) :=
    (Measurable.of_eval fun i : Fin (r+K) => (N9c.measurable_historyDriverPast
      (growingQueryTime δ e.val) (Horizon δ K)
      ((growingQueryTime_strictMono δ hδ).monotone (by omega))).comp
      ((measurable_pi_apply i).comp (N9c.measurable_SourceHistories W β hβ δ r K))).prodMk
      (((measurable_pi_apply e).comp (measurable_SourceTargets W β hβ δ r K)).comp measurable_snd)
  have hr : Measurable (fun u : OriginalPastRows (growingQueryTime δ e.val) (r+K) ×
      (Fin (r+K) → ℝ × FreshRowSeed (growingQueryDuration δ e.val)
        (Horizon δ K-growingQueryTime δ (e.val+1))) =>
      (u.1,fun i => N9Y2.earlierFreshTarget W β hβ δ hδ K e (u.1 i) (u.2 i))) := by
    apply measurable_fst.prodMk
    apply Measurable.of_eval
    intro i
    exact ((EuclideanSpace.proj (LGram.posteriorIndex K e)).continuous.measurable.comp
      (NDH.measurable_historyMixedRow W β δ K)).comp
      (((N9c.measurable_castDriverHistory _).comp (N9c.measurable_freshRowHistory W β hβ _ _ _)).comp
        (((measurable_pi_apply i).comp measurable_fst).prodMk
          ((measurable_pi_apply i).comp measurable_snd)))
  have he := congrArg (fun μ => μ.map G)
    (N9Y2.sourcePastTargets_productFresh_law W β hβ δ hδ r K e)
  rw [Measure.map_map hG hp,Measure.map_map hG hr] at he
  refine (Measure.map_congr (ae_of_all _ fun z => ?_)).trans he
  exact congrArg (fun P => (_,P,SourceTargets W β hβ δ r K z.2 e))
    (earlierCellProjection_source W β hβ δ hδ r K e z).symm

end SKConstants.Completion.Y1
