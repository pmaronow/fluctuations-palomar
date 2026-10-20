module

public import SKConstants.Completion.N9c.FreshDriverLaw
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace SKConstants.Completion.N9c
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal M1 LFine
variable {Ω : Type*} [MeasurableSpace Ω]

theorem realThreshold_probability (m : ℝ) (hm : |m| ≤ 1) (b : Bool) :
    SKConstantsOAI.SK.unitIntervalLaw {u : ℝ | (if u ≤ (1+m)/2 then true else false) = b} =
      ENNReal.ofReal ((1+scalarHiddenSign b*m)/2) := by
  have hp0 : 0 ≤ (1+m)/2 := by linarith [(abs_le.mp hm).1]
  have hp1 : (1+m)/2 ≤ 1 := by linarith [(abs_le.mp hm).2]
  cases b with
  | true =>
    have he : {u : ℝ | (if u ≤ (1+m)/2 then true else false) = true} = Iic ((1+m)/2) := by
      ext u; simp
    rw [he,SKConstantsOAI.SK.unitIntervalLaw,Measure.restrict_apply measurableSet_Iic,inter_comm,
      Ioc_inter_Iic,inf_eq_right.mpr hp1,Real.volume_Ioc]
    simp only [sub_zero,scalarHiddenSign,ite_true,one_mul]
  | false =>
    have he : {u : ℝ | (if u ≤ (1+m)/2 then true else false) = false} = Ioi ((1+m)/2) := by
      ext u; simp
    rw [he,SKConstantsOAI.SK.unitIntervalLaw,Measure.restrict_apply measurableSet_Ioi,inter_comm,
      Ioc_inter_Ioi,sup_eq_right.mpr hp0,Real.volume_Ioc]
    congr 1
    simp only [scalarHiddenSign,Bool.false_eq_true,ite_false,neg_mul,one_mul]
    ring

theorem realThreshold_law (β : ℝ) (H : ℝ≥0) (y : ℝ) :
    SKConstantsOAI.SK.unitIntervalLaw.map
      (fun u : ℝ => if u ≤ (1+actualParisiFullMagnetization β H y)/2 then true else false) =
    (scalarHiddenPriorBool 0).withDensity
      (fun b => ENNReal.ofReal (actualParisiSpinLinkDensity β b H y)) := by
  have hm : Measurable (fun u : ℝ =>
      if u ≤ (1+actualParisiFullMagnetization β H y)/2 then true else false) :=
    Measurable.ite measurableSet_Iic measurable_const measurable_const
  apply Measure.ext_of_singleton
  intro b
  rw [Measure.map_apply hm (measurableSet_singleton b),
    withDensity_apply _ (measurableSet_singleton b),lintegral_singleton]
  have he : (fun u : ℝ => if u ≤ (1+actualParisiFullMagnetization β H y)/2 then true else false)
      ⁻¹' {b} = {u : ℝ | (if u ≤ (1+actualParisiFullMagnetization β H y)/2 then true else false) = b} := rfl
  rw [he,realThreshold_probability _ (actualParisiFullMagnetization_curvature_bounds β H y).1]
  have hp : (scalarHiddenPriorBool 0) {b} = ENNReal.ofReal (1/2 : ℝ) := by
    cases b <;> simp [scalarHiddenPriorBool,scalarPlusWeight,scalarMinusWeight]
  rw [hp,← ENNReal.ofReal_mul (actualParisiSpinLinkDensity_pos β b H y).le]
  congr 1
  unfold actualParisiSpinLinkDensity
  ring

theorem realThreshold_terminalLinkedLaw {S : Type*} [MeasurableSpace S]
    (β : ℝ) (H : ℝ≥0) (μ : Measure S) [IsProbabilityMeasure μ]
    (Y : S → ℝ) (hY : Measurable Y) :
    (μ.prod SKConstantsOAI.SK.unitIntervalLaw).map (fun z =>
      ((if z.2 ≤ (1+actualParisiFullMagnetization β H (Y z.1))/2 then true else false),z.1)) =
      ScalarTerminalLinkedLaw β H μ Y := by
  let G : S × ℝ → Bool × S := fun z =>
    ((if z.2 ≤ (1+actualParisiFullMagnetization β H (Y z.1))/2 then true else false),z.1)
  have hm : Measurable (fun s => actualParisiFullMagnetization β H (Y s)) :=
    ((continuous_actualParisiFullMagnetization β).comp
      (continuous_const.prodMk continuous_id)).measurable.comp hY
  have hG : Measurable G :=
    (Measurable.ite (measurableSet_le measurable_snd
      ((measurable_const.add (hm.comp measurable_fst)).div_const 2))
        measurable_const measurable_const).prodMk measurable_fst
  let D : Bool × S → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (actualParisiSpinLinkDensity β z.1 H (Y z.2))
  have hD : Measurable D := measurable_scalarTerminalDensity β H Y hY
  change (μ.prod SKConstantsOAI.SK.unitIntervalLaw).map G = _
  ext E hE
  rw [Measure.map_apply hG hE]
  change (μ.prod SKConstantsOAI.SK.unitIntervalLaw) (G ⁻¹' E) =
    (((scalarHiddenPriorBool 0).prod μ).withDensity D) E
  rw [← lintegral_indicator_fun_one (hG hE),
    lintegral_prod _ ((measurable_const (a := (1 : ℝ≥0∞))).indicator (hG hE)).aemeasurable,
    withDensity_apply _ hE,← lintegral_indicator hE,
    lintegral_prod_symm _ (hD.indicator hE).aemeasurable]
  apply lintegral_congr
  intro s
  let T : ℝ → Bool := fun u => if u ≤ (1+actualParisiFullMagnetization β H (Y s))/2 then true else false
  have hT : Measurable T := Measurable.ite measurableSet_Iic measurable_const measurable_const
  have hsection : Measurable (fun b : Bool => E.indicator (fun _ => (1 : ℝ≥0∞)) (b,s)) :=
    (measurable_const.indicator hE).comp (measurable_id.prodMk measurable_const)
  change (∫⁻ u, (fun b : Bool => E.indicator (fun _ => (1 : ℝ≥0∞)) (b,s)) (T u)
      ∂SKConstantsOAI.SK.unitIntervalLaw) = _
  rw [← lintegral_map hsection hT,realThreshold_law β H (Y s),
    lintegral_withDensity_eq_lintegral_mul₀ (measurable_of_finite _).aemeasurable
      hsection.aemeasurable]
  apply lintegral_congr
  intro b
  by_cases hb : (b,s) ∈ E <;> simp [hb,D]

theorem freshRowSign_drivers_law (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (a h f : ℝ≥0) (hh : 0 < h) :
    (((scalarPrimitiveBrownianPathLaw W a).prod (scalarPrimitiveBrownianPathLaw W a)).prod
      ((gaussianReal 0 1).prod (freshRowSeedLaw W h f))).map
      (fun u => (freshRowSign W β hβ a h f u.1.1 u.1.2 u.2,
        freshRowDrivers a h f u.1.1 u.1.2 u.2)) =
    ScalarTerminalLinkedLaw β (a+(h+f))
      ((scalarPrimitiveBrownianPathLaw W (a+(h+f))).prod
        (scalarPrimitiveBrownianPathLaw W (a+(h+f))))
      (fun p => PairObservation W β hβ (a+(h+f)) p ⟨a+(h+f),(a+(h+f)).coe_nonneg,le_rfl⟩) := by
  let H := a+(h+f)
  let Y := fun p : ScalarContinuousPath H × ScalarContinuousPath H =>
    PairObservation W β hβ H p ⟨H,H.coe_nonneg,le_rfl⟩
  have hY : Measurable Y := (ContinuousMap.measurable_eval _).comp
    (measurable_PairObservation W β hβ H)
  let G := fun z : (ScalarContinuousPath H × ScalarContinuousPath H) × ℝ =>
    ((if z.2 ≤ (1+actualParisiFullMagnetization β H (Y z.1))/2 then true else false),z.1)
  have hG : Measurable G :=
    (Measurable.ite (measurableSet_le measurable_snd
      ((measurable_const.add ((((continuous_actualParisiFullMagnetization β).comp
        (continuous_const.prodMk continuous_id)).measurable.comp hY).comp measurable_fst)).div_const 2))
        measurable_const measurable_const).prodMk measurable_fst
  have hF : Measurable (fun u : (ScalarContinuousPath a × ScalarContinuousPath a) ×
      (ℝ × FreshRowSeed h f) =>
        (freshRowDrivers a h f u.1.1 u.1.2 u.2,u.2.2.2.2.2)) :=
    (N9b.measurable_freshRowDrivers_param a h f _ _ _
      measurable_fst.fst measurable_fst.snd measurable_snd).prodMk measurable_snd.snd.snd.snd.snd
  have he := congrArg (fun ν => ν.map G) (freshRowDrivers_threshold_law W a h f hh)
  rw [Measure.map_map hG hF] at he
  exact he.trans (realThreshold_terminalLinkedLaw β H _ Y hY)

theorem freshRow_fullHistory_law (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (a h f : ℝ≥0) (hh : 0 < h) :
    (((scalarPrimitiveBrownianPathLaw W a).prod (scalarPrimitiveBrownianPathLaw W a)).prod
      ((gaussianReal 0 1).prod (freshRowSeedLaw W h f))).map
      (fun u => NDH.pairFullHistory W β hβ (a+(h+f))
        (freshRowSign W β hβ a h f u.1.1 u.1.2 u.2,
          freshRowDrivers a h f u.1.1 u.1.2 u.2)) =
    (actualParisiFullQuerySpinLaw W W β (a+(h+f))).map
      (NDH.modelFullHistory W W β hβ (a+(h+f))) := by
  have hs : Measurable (fun u : (ScalarContinuousPath a × ScalarContinuousPath a) ×
      (ℝ × FreshRowSeed h f) => freshRowSign W β hβ a h f u.1.1 u.1.2 u.2) :=
    N9b.measurable_freshRowSign_param W β hβ a h f _ _ _
      measurable_fst.fst measurable_fst.snd measurable_snd
  have hd : Measurable (fun u : (ScalarContinuousPath a × ScalarContinuousPath a) ×
      (ℝ × FreshRowSeed h f) => freshRowDrivers a h f u.1.1 u.1.2 u.2) :=
    N9b.measurable_freshRowDrivers_param a h f _ _ _
      measurable_fst.fst measurable_fst.snd measurable_snd
  rw [show (fun u : (ScalarContinuousPath a × ScalarContinuousPath a) × (ℝ × FreshRowSeed h f) =>
      NDH.pairFullHistory W β hβ (a+(h+f))
      (freshRowSign W β hβ a h f u.1.1 u.1.2 u.2,freshRowDrivers a h f u.1.1 u.1.2 u.2)) =
      NDH.pairFullHistory W β hβ (a+(h+f)) ∘
        (fun u : (ScalarContinuousPath a × ScalarContinuousPath a) × (ℝ × FreshRowSeed h f) =>
          (freshRowSign W β hβ a h f u.1.1 u.1.2 u.2,
          freshRowDrivers a h f u.1.1 u.1.2 u.2)) from rfl,
    ← Measure.map_map (NDH.measurable_pairFullHistory W β hβ (a+(h+f))) (hs.prodMk hd),
    freshRowSign_drivers_law W β hβ a h f hh]
  exact NDH.pair_linked_full_history_law W W β hβ (a+(h+f))

abbrev FreshRowInput (a h f : ℝ≥0) :=
  (ScalarContinuousPath a × ScalarContinuousPath a) × (ℝ × FreshRowSeed h f)

def freshRowInputLaw (W : BrownianSystem Ω) (a h f : ℝ≥0) : Measure (FreshRowInput a h f) :=
  ((scalarPrimitiveBrownianPathLaw W a).prod (scalarPrimitiveBrownianPathLaw W a)).prod
    ((gaussianReal 0 1).prod (freshRowSeedLaw W h f))

instance freshRowInputLaw_probability (W : BrownianSystem Ω) (a h f : ℝ≥0) :
    IsProbabilityMeasure (freshRowInputLaw W a h f) := by
  unfold freshRowInputLaw
  infer_instance

def freshRowHistory (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (a h f : ℝ≥0)
    (u : FreshRowInput a h f) : ScalarDriverHistory (a+(h+f)) :=
  NDH.pairFullHistory W β hβ (a+(h+f))
    (freshRowSign W β hβ a h f u.1.1 u.1.2 u.2,freshRowDrivers a h f u.1.1 u.1.2 u.2)

theorem measurable_freshRowHistory (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (a h f : ℝ≥0) : Measurable (freshRowHistory W β hβ a h f) :=
  (NDH.measurable_pairFullHistory W β hβ (a+(h+f))).comp
    ((N9b.measurable_freshRowSign_param W β hβ a h f
      (fun u : FreshRowInput a h f => u.1.1) (fun u => u.1.2) (fun u => u.2)
      measurable_fst.fst measurable_fst.snd measurable_snd).prodMk
      (N9b.measurable_freshRowDrivers_param a h f
        (fun u : FreshRowInput a h f => u.1.1) (fun u => u.1.2) (fun u => u.2)
        measurable_fst.fst measurable_fst.snd measurable_snd))

theorem freshRow_jointPast_fullHistory_law (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (a h f : ℝ≥0) (hh : 0 < h) :
    (freshRowInputLaw W a h f).map (fun u => (u.1,freshRowHistory W β hβ a h f u)) =
    (actualParisiFullQuerySpinLaw W W β (a+(h+f))).map
      (fun u => (historyDriverPast a (a+(h+f)) (by exact le_self_add)
        (NDH.modelFullHistory W W β hβ (a+(h+f)) u),
          NDH.modelFullHistory W W β hβ (a+(h+f)) u)) := by
  let F := fun v : ScalarDriverHistory (a+(h+f)) =>
    (historyDriverPast a (a+(h+f)) (by exact le_self_add) v,v)
  have hF : Measurable F := (measurable_historyDriverPast a _ _).prodMk measurable_id
  have he := congrArg (fun ν => ν.map F) (freshRow_fullHistory_law W β hβ a h f hh)
  change ((freshRowInputLaw W a h f).map (freshRowHistory W β hβ a h f)).map F = _ at he
  rw [Measure.map_map hF (measurable_freshRowHistory W β hβ a h f),
    Measure.map_map hF (NDH.measurable_modelFullHistory W W β hβ (a+(h+f)))] at he
  convert he using 1
  · congr 1
    funext u
    apply Prod.ext
    · exact (freshRowDrivers_past a h f u.1 u.2).symm
    · rfl
  · rfl

def castDriverHistory {H V : ℝ≥0} (h : H = V) : ScalarDriverHistory H → ScalarDriverHistory V :=
  h ▸ id

theorem measurable_castDriverHistory {H V : ℝ≥0} (h : H = V) :
    Measurable (castDriverHistory h) := by subst V; exact measurable_id

theorem freshRowHistory_law_at_horizon (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (a h f H : ℝ≥0) (hh : 0 < h) (heq : a+(h+f) = H) :
    (freshRowInputLaw W a h f).map (castDriverHistory heq ∘ freshRowHistory W β hβ a h f) =
    (actualParisiFullQuerySpinLaw W W β H).map (NDH.modelFullHistory W W β hβ H) := by
  subst H
  exact freshRow_fullHistory_law W β hβ a h f hh

theorem sourceHistories_eq_freshRows (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ) (a h f : ℝ≥0)
    (hh : 0 < h) (heq : a+(h+f) = Horizon δ K) :
    (SourceLinkedLaw W β hβ δ r K).map (SourceHistories W β hβ δ r K) =
    (Measure.pi (fun _ : Fin (r+K) => freshRowInputLaw W a h f)).map
      (fun u i => castDriverHistory heq (freshRowHistory W β hβ a h f (u i))) := by
  rw [NDH.literal_linked_source_full_histories_law W β hβ δ hδ r K]
  calc
    _ = Measure.pi (fun _ : Fin (r+K) => (freshRowInputLaw W a h f).map
        (castDriverHistory heq ∘ freshRowHistory W β hβ a h f)) := by
      congr 1
      funext i
      exact (freshRowHistory_law_at_horizon W β hβ a h f (Horizon δ K) hh heq).symm
    _ = _ := (Measure.pi_map_pi (fun _ : Fin (r+K) =>
      ((measurable_castDriverHistory heq).comp
        (measurable_freshRowHistory W β hβ a h f)).aemeasurable)).symm

end SKConstants.Completion.N9c
