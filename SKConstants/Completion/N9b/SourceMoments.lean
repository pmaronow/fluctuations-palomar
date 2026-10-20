module

public import SKConstants.Completion.N9b.ScalarFourth
public import SKConstants.Completion.N4c.Node
public import SKConstants.Completion.LM1b.SourceTrace
public import SKConstants.Completion.LM1b.TraceMeasurability
public import SKConstants.Completion.LFine.EmpiricalNormMoments
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators

namespace SKConstants.Completion.N9b
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal M1 LFine LQ
variable {Ω : Type*} [MeasurableSpace Ω]

theorem linkedSource_field_rows_law (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (r q : ℕ) (hn : 0 < r+q) :
    (SourceLinkedLaw W β hβ δ r q).map (fun u => fun i : Fin (r+q) =>
      (u.1 i, fun t : Iic (Horizon δ q) => SourceField W β hβ δ r q t.1 u.2 i)) =
      Measure.pi (fun _ : Fin (r+q) =>
        (actualParisiFullTerminalSpinLaw β W (Horizon δ q)).map
          (fun u => (u.1, ActualFieldPrefix W β (Horizon δ q) u.2))) := by
  let F := fun u : (Fin (r+q) → Bool) × ReplayInput δ r q => fun i : Fin (r+q) =>
    (u.1 i, fun t : Iic (Horizon δ q) => actualParisiGrowingReplayField W β hβ δ r q t.1 u.2 i)
  have hF : Measurable F := Measurable.of_eval fun i =>
    ((measurable_pi_apply i).comp measurable_fst).prodMk
      (Measurable.of_eval fun t => ((measurable_pi_apply i).comp
        (measurable_ReplayField W β hβ δ r q t.1)).comp measurable_snd)
  have hTo : Measurable (fun u : (Fin (r+q) → Bool) × SourceInput δ r q =>
      (u.1,ToReplay W β hβ δ r q u.2)) :=
    measurable_fst.prodMk ((measurable_ToReplay W β hβ δ r q).comp measurable_snd)
  have he := congrArg (fun μ => μ.map F) (growingSource_toReplay_linked_law W β hβ δ r q hn)
  rw [Measure.map_map hF hTo] at he
  have hcomp : F ∘ (fun u : (Fin (r+q) → Bool) × SourceInput δ r q =>
      (u.1,ToReplay W β hβ δ r q u.2)) =
      (fun u => fun i : Fin (r+q) =>
        (u.1 i, fun t : Iic (Horizon δ q) => SourceField W β hβ δ r q t.1 u.2 i)) := by
    funext u i
    dsimp only [F, Function.comp_apply]
    apply Prod.ext
    · rfl
    funext t
    exact congrFun (growingSource_toReplay_field W β hβ δ r q hn t.1 u.2) i
  rw [hcomp] at he
  exact he.trans (literal_linked_replay_field_rows_law W β hβ δ hδ r q hn)

theorem sourceTargets_hasLaw (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (r q : ℕ) (hn : 0 < r+q)
    (e : Fin q) :
    HasLaw (fun u : (Fin (r+q) → Bool) × SourceInput δ r q =>
      fun i => SourceTargets W β hβ δ r q u.2 e i)
      (Measure.pi (fun _ : Fin (r+q) => W.law.map
        (normalizedIncrement W β (growingQueryTime δ e.val) (growingQueryTime δ (e.val+1)))))
      (SourceLinkedLaw W β hβ δ r q) := by
  let := W.isProbability
  let H := Horizon δ q
  let s := growingQueryTime δ e.val
  let t := growingQueryTime δ (e.val+1)
  have hsH : s ≤ H := (growingQueryTime_strictMono δ hδ).monotone (by omega)
  have htH : t ≤ H := (growingQueryTime_strictMono δ hδ).monotone (by omega)
  let R : Bool × (Iic H → ℝ) → ℝ := fun z =>
    (actualParisiFullMagnetization β t (z.2 ⟨t,htH⟩) -
      actualParisiFullMagnetization β s (z.2 ⟨s,hsH⟩)) /
        (actualParisiPosteriorIntervalScale W β s t : ℝ)
  have hm (v : ℝ) : Measurable (actualParisiFullMagnetization β v) :=
    ((continuous_actualParisiFullMagnetization β).comp
      (continuous_const.prodMk continuous_id)).measurable
  have hR : Measurable R :=
    ((hm t).comp ((measurable_pi_apply _).comp measurable_snd) |>.sub
      ((hm s).comp ((measurable_pi_apply _).comp measurable_snd))).div_const _
  let Rows := fun u : (Fin (r+q) → Bool) × SourceInput δ r q =>
    fun i : Fin (r+q) => (u.1 i, fun v : Iic H => SourceField W β hβ δ r q v.1 u.2 i)
  have hRows : Measurable Rows := Measurable.of_eval fun i =>
    ((measurable_pi_apply i).comp measurable_fst).prodMk
      (Measurable.of_eval fun v => ((measurable_pi_apply i).comp
        (measurable_SourceField W β hβ δ r q v.1)).comp measurable_snd)
  have hF : Measurable (fun z : Fin (r+q) → Bool × (Iic H → ℝ) => fun i => R (z i)) :=
    Measurable.of_eval fun i => hR.comp (measurable_pi_apply i)
  have hrow : ((actualParisiFullTerminalSpinLaw β W H).map
      (fun u => (u.1,ActualFieldPrefix W β H u.2))).map R =
        W.law.map (normalizedIncrement W β s t) := by
    have hG : Measurable (fun u : Bool × Ω => (u.1,ActualFieldPrefix W β H u.2)) :=
      measurable_fst.prodMk ((measurable_ActualFieldPrefix W β H).comp measurable_snd)
    rw [Measure.map_map (f := fun u : Bool × Ω => (u.1,ActualFieldPrefix W β H u.2))
      (g := R) hR hG]
    change (actualParisiFullTerminalSpinLaw β W H).map
      (normalizedIncrement W β s t ∘ Prod.snd) = _
    rw [← Measure.map_map (measurable_normalizedIncrement W β s t) measurable_snd,
      actualParisiFullTerminalSpinLaw_path_marginal]
  have he := congrArg (fun μ => μ.map (fun z : Fin (r+q) → Bool × (Iic H → ℝ) =>
    fun i => R (z i))) (linkedSource_field_rows_law W β hβ δ hδ r q hn)
  rw [Measure.map_map hF hRows, Measure.pi_map_pi (fun _ => hR.aemeasurable)] at he
  rw [hrow] at he
  have htarget : (fun z : Fin (r+q) → Bool × (Iic H → ℝ) => fun i => R (z i)) ∘ Rows =
      (fun u : (Fin (r+q) → Bool) × SourceInput δ r q =>
        fun i => SourceTargets W β hβ δ r q u.2 e i) := by
    funext u i
    exact (targetTraceIdentification_holds W β hβ δ hδ r q u.2 e i).symm
  rw [htarget] at he
  exact ⟨(htarget ▸ hF.comp hRows).aemeasurable, he⟩

theorem sourceTarget_coordinate_hasLaw (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (r q : ℕ) (hn : 0 < r+q)
    (e : Fin q) (i : Fin (r+q)) :
    HasLaw (fun u : (Fin (r+q) → Bool) × SourceInput δ r q => SourceTargets W β hβ δ r q u.2 e i)
      (W.law.map (normalizedIncrement W β (growingQueryTime δ e.val)
        (growingQueryTime δ (e.val+1)))) (SourceLinkedLaw W β hβ δ r q) := by
  let := W.isProbability
  have hEval : HasLaw (fun z : Fin (r+q) → ℝ => z i)
      (W.law.map (normalizedIncrement W β (growingQueryTime δ e.val)
        (growingQueryTime δ (e.val+1))))
      (Measure.pi (fun _ : Fin (r+q) => W.law.map (normalizedIncrement W β
        (growingQueryTime δ e.val) (growingQueryTime δ (e.val+1))))) :=
    ⟨(measurable_pi_apply i).aemeasurable, measurePreserving_eval _ i |>.map_eq⟩
  exact hEval.comp (sourceTargets_hasLaw W β hβ δ hδ r q hn e)

theorem sourceTarget_memLp (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (r q : ℕ) (hn : 0 < r+q)
    (e : Fin q) (i : Fin (r+q)) (p : ℝ≥0∞) :
    MemLp (fun u : (Fin (r+q) → Bool) × SourceInput δ r q => SourceTargets W β hβ δ r q u.2 e i)
      p (SourceLinkedLaw W β hβ δ r q) := by
  have h := sourceTarget_coordinate_hasLaw W β hβ δ hδ r q hn e i
  apply h.memLp
  exact (memLp_map_measure_iff (by fun_prop)
    (measurable_normalizedIncrement W β _ _).aemeasurable).mpr
      (normalizedIncrement_memLp W β _ _ p)

theorem sourceTarget_second (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (r q : ℕ) (hn : 0 < r+q)
    (e : Fin q) (i : Fin (r+q)) :
    (∫ u, (SourceTargets W β hβ δ r q u.2 e i)^2 ∂SourceLinkedLaw W β hβ δ r q) = 1 := by
  have h := sourceTarget_coordinate_hasLaw W β hβ δ hδ r q hn e i
  have he := h.integral_comp (show AEStronglyMeasurable (fun x : ℝ => x^2) _ from by fun_prop)
  simp only [Function.comp_apply] at he
  rw [he,
    integral_map (measurable_normalizedIncrement W β _ _).aemeasurable (by fun_prop)]
  exact normalizedIncrement_second W β hβ _ _ (growingQueryTime_strictMono δ hδ (Nat.lt_succ_self _))

theorem sourceTarget_fourth_le (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (r q : ℕ) (hn : 0 < r+q)
    (e : Fin q) (i : Fin (r+q)) :
    (∫ u, (SourceTargets W β hβ δ r q u.2 e i)^4 ∂SourceLinkedLaw W β hβ δ r q) ≤
      6*meshDuration δ e.val/(actualFineScale W β δ e.val)^2 := by
  have h := sourceTarget_coordinate_hasLaw W β hβ δ hδ r q hn e i
  have he := h.integral_comp (show AEStronglyMeasurable (fun x : ℝ => x^4) _ from by fun_prop)
  simp only [Function.comp_apply] at he
  rw [he,
    integral_map (measurable_normalizedIncrement W β _ _).aemeasurable (by fun_prop)]
  simpa only [growingQueryTime_succ, NNReal.coe_add, add_sub_cancel_left,
    actualFineScale, meshDuration] using normalizedIncrement_fourth_le W β hβ
      (growingQueryTime δ e.val) (growingQueryTime δ (e.val+1))
      (growingQueryTime_strictMono δ hδ (Nat.lt_succ_self _))

theorem sourceTargets_independent (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (r q : ℕ) (hn : 0 < r+q)
    (e : Fin q) :
    iIndepFun (fun i (u : (Fin (r+q) → Bool) × SourceInput δ r q) =>
      SourceTargets W β hβ δ r q u.2 e i) (SourceLinkedLaw W β hβ δ r q) :=
  (iIndepFun_iff_hasLaw_pi_pi (fun i =>
    sourceTarget_coordinate_hasLaw W β hβ δ hδ r q hn e i)).mpr
      (sourceTargets_hasLaw W β hβ δ hδ r q hn e)

theorem sourceTargets_norm_mean (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (r q : ℕ) (hn : 0 < r+q)
    (e : Fin q) :
    (∫ u, ((r+q : ℕ) : ℝ)⁻¹*∑ i, (SourceTargets W β hβ δ r q u.2 e i)^2
      ∂SourceLinkedLaw W β hβ δ r q) = 1 :=
  empirical_norm_square_mean _ (r+q) hn _
    (fun i => sourceTarget_memLp W β hβ δ hδ r q hn e i 2)
    (fun i => sourceTarget_second W β hβ δ hδ r q hn e i)

theorem sourceTargets_norm_fluctuation_le (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (r q : ℕ) (hn : 0 < r+q)
    (e : Fin q) :
    (∫ u, (((r+q : ℕ) : ℝ)⁻¹*∑ i, (SourceTargets W β hβ δ r q u.2 e i)^2 - 1)^2
      ∂SourceLinkedLaw W β hβ δ r q) ≤
      6*meshDuration δ e.val/((r+q : ℕ)*(actualFineScale W β δ e.val)^2) := by
  have h := empirical_norm_square_fluctuation_le _ (r+q) hn _
    (fun i => sourceTarget_memLp W β hβ δ hδ r q hn e i 4)
    (sourceTargets_independent W β hβ δ hδ r q hn e)
    (fun i => sourceTarget_second W β hβ δ hδ r q hn e i)
    (6*meshDuration δ e.val/(actualFineScale W β δ e.val)^2)
    (fun i => sourceTarget_fourth_le W β hβ δ hδ r q hn e i)
  exact h.trans_eq (by ring)

end SKConstants.Completion.N9b
