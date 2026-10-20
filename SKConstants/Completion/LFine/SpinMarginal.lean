module

public import SKConstants.Completion.LFine.ActualOutput
public import SKConstants.Completion.LC0.TerminalLinkLaw
public import SKConstants.Completion.LC5.SourceSplitting
public import SKConstants.ProposalGibbsChangeOfMeasure
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal

namespace SKConstants.Completion.LFine
open SKConstantsOAI.ZeroTemperatureSK M1 LC4a

theorem terminalLinkedLaw_spin_marginal_of_rows {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (n : ℕ) (β : ℝ) (H : ℝ≥0)
    (Y : S → Fin n → ℝ) (hY : Measurable Y)
    (hind : iIndepFun (fun i s => actualParisiFullMagnetization β H (Y s i)) μ)
    (hmean : ∀ i, (∫ s, actualParisiFullMagnetization β H (Y s i) ∂μ) = 0) :
    (TerminalLinkedLaw β H μ Y).map Prod.fst = spinPrior n := by
  let M := fun i s => actualParisiFullMagnetization β H (Y s i)
  have hM (i : Fin n) : Measurable (M i) :=
    ((continuous_actualParisiFullMagnetization β).comp
      (continuous_const.prodMk continuous_id)).measurable.comp ((measurable_pi_apply i).comp hY)
  have hMi (i : Fin n) : Integrable (M i) μ := by
    apply Integrable.of_bound (hM i).aestronglyMeasurable 1
    exact ae_of_all _ (fun s => by
      have h := actualParisiFullMagnetization_strict_bounds β H (Y s i)
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨h.1.le,h.2.le⟩)
  have hdensity (x : Fin n → Bool) : (∫ s, TerminalDensity β H Y (x,s) ∂μ) = 1 := by
    have hi := hind.comp (fun i t => 1+scalarHiddenSign (x i)*t) (fun _ => by fun_prop)
    have he := hi.integral_fun_prod_eq_prod_integral
      (fun i => (measurable_const.add ((hM i).const_mul _)).aestronglyMeasurable)
    change (∫ s, ∏ i, (1+scalarHiddenSign (x i)*M i s) ∂μ) =
      ∏ i, ∫ s, (1+scalarHiddenSign (x i)*M i s) ∂μ at he
    change (∫ s, ∏ i, (1+scalarHiddenSign (x i)*M i s) ∂μ) = 1
    rw [he]
    have hsingle (i : Fin n) : (∫ s, (1+scalarHiddenSign (x i)*M i s) ∂μ) = 1 := by
      rw [integral_add (f := fun _ => (1 : ℝ)) (g := fun s => scalarHiddenSign (x i)*M i s)
        (integrable_const 1) ((hMi i).const_mul _), integral_const_mul]
      simp only [M, hmean, integral_const, probReal_univ, one_smul, mul_zero, add_zero]
    simp only [hsingle, Finset.prod_const_one]
  let D := fun z : (Fin n → Bool) × S => ENNReal.ofReal (TerminalDensity β H Y z)
  have hD : Measurable D := (measurable_terminalDensity β H Y hY).ennreal_ofReal
  have hinner (x : Fin n → Bool) : (∫⁻ s, D (x,s) ∂μ) = 1 := by
    rw [show (fun s => D (x,s)) = (fun s => ENNReal.ofReal (TerminalDensity β H Y (x,s))) from rfl,
      ← ofReal_integral_eq_lintegral_ofReal]
    · rw [hdensity, ENNReal.ofReal_one]
    · apply Integrable.of_bound
        ((measurable_terminalDensity β H Y hY).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
          ((2 : ℝ)^n)
      exact ae_of_all _ fun s => by
        change |TerminalDensity β H Y (x,s)| ≤ (2 : ℝ)^n
        rw [abs_of_pos (terminalDensity_pos β H Y (x,s))]
        exact Finset.prod_le_prod₀
          (fun i _ => (actualParisiSpinLinkDensity_pos β (x i) H (Y s i)).le)
          (fun i _ => actualParisiSpinLinkDensity_le_two β (x i) H (Y s i)) |>.trans_eq (by simp)
    · exact ae_of_all _ (fun s => (terminalDensity_pos β H Y (x,s)).le)
  ext A hA
  rw [Measure.map_apply measurable_fst hA]
  change (((spinPrior n).prod μ).withDensity D) (Prod.fst ⁻¹' A) = _
  rw [withDensity_apply _ (measurable_fst hA), ← lintegral_indicator (measurable_fst hA),
    lintegral_prod _ (hD.indicator (measurable_fst hA)).aemeasurable]
  have hsection (x : Fin n → Bool) :
      (∫⁻ s, (Prod.fst ⁻¹' A).indicator D (x,s) ∂μ) = A.indicator (fun _ => 1) x := by
    by_cases hx : x ∈ A
    · have hf (s : S) : (Prod.fst ⁻¹' A).indicator D (x,s) = D (x,s) :=
        Set.indicator_of_mem (show (x,s) ∈ Prod.fst ⁻¹' A from hx) D
      simp_rw [hf]
      rw [hinner, Set.indicator_of_mem hx]
    · simp [hx]
  simp_rw [hsection]
  rw [lintegral_indicator hA]
  simp

variable {Ω : Type*} [MeasurableSpace Ω]

def finePathLaw (W : BrownianSystem Ω) (δ : ℝ≥0) (ranks q : ℕ) :=
  (scalarGrowingReplayStaticLaw W δ (ranks+q) q).prod
    (Measure.pi (fun _ : Fin (ranks+q) => W.law))

def fineTerminalField (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (ranks q : ℕ)
    (p : ScalarGrowingReplayStaticData δ (ranks+q) q × (Fin (ranks+q) → Ω)) :=
  actualParisiGrowingReplayField W β hβ δ ranks q (scalarGrowingSourceHorizon δ q)
    (p.1,fun i => scalarPrimitiveBrownianPathVersion W (scalarGrowingSourceHorizon δ q) (p.2 i))

def ActualFineTerminalRowsStatement (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (ranks q : ℕ) : Prop :=
  let M := fun i p => actualParisiFullMagnetization β (scalarGrowingSourceHorizon δ q)
    (fineTerminalField W β hβ δ ranks q p i)
  iIndepFun M (finePathLaw W δ ranks q) ∧
    ∀ i, (∫ p, M i p ∂finePathLaw W δ ranks q) = 0

theorem spinPrior_eq_uniformSpinLaw (n : ℕ) : spinPrior n = uniformSpinLaw n := by
  have hprior (b : Bool) : (scalarHiddenPriorBool 0) {b} = ENNReal.ofReal (1/2 : ℝ) := by
    cases b <;> simp [scalarHiddenPriorBool, scalarPlusWeight, scalarMinusWeight]
  apply Measure.ext_of_singleton
  intro x
  rw [spinPrior, Measure.pi_singleton]
  simp only [hprior, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [uniformSpinLaw, finiteWeightMeasure_apply _ _ (measurableSet_singleton x)]
  simp only [Set.mem_singleton_iff, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1/2)]
  congr 1
  rw [div_pow, one_pow]

theorem fineReplay_to_terminalLinkedLaw (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) :
    (growingReplayLinkedLaw W β hβ δ ranks q (scalarGrowingSourceHorizon δ q)).map
      (fun u => (u.1.2,(u.1.1,u.2))) =
      TerminalLinkedLaw β (scalarGrowingSourceHorizon δ q) (finePathLaw W δ ranks q)
        (fineTerminalField W β hβ δ ranks q) := by
  let := W.isProbability
  let P := scalarGrowingReplayStaticLaw W δ (ranks+q) q
  let S := spinPrior (ranks+q)
  let D := Measure.pi (fun _ : Fin (ranks+q) => W.law)
  let e : GrowingReplaySpace Ω δ ranks q →
      (Fin (ranks+q) → Bool) ×
        (ScalarGrowingReplayStaticData δ (ranks+q) q × (Fin (ranks+q) → Ω)) :=
    fun u => (u.1.2,(u.1.1,u.2))
  have he : Measurable e := measurable_fst.snd.prodMk (measurable_fst.fst.prodMk measurable_snd)
  have hbase : (growingReplayUnlinkedLaw W δ ranks q).map e =
      S.prod (finePathLaw W δ ranks q) :=
    ((measurePreserving_prodAssoc S P D).comp
      ((Measure.measurePreserving_swap (μ := P) (ν := S)).prod (MeasurePreserving.id D))).map_eq
  have hY : Measurable (fineTerminalField W β hβ δ ranks q) :=
    (measurable_growingReplayFieldAt W β hβ δ hδ ranks q _).comp
      ((measurable_fst.prodMk (measurable_const (a := fun _ : Fin (ranks+q) => false))).prodMk measurable_snd)
  have h := LC5.map_withDensity_composition (growingReplayUnlinkedLaw W δ ranks q) e he
    (fun z => ENNReal.ofReal (TerminalDensity β (scalarGrowingSourceHorizon δ q)
      (fineTerminalField W β hβ δ ranks q) z))
    ((measurable_terminalDensity β _ _ hY).ennreal_ofReal)
  rw [hbase] at h
  exact h

theorem fineJointLaw_spin_marginal_of_rows (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ)
    (hrows : ActualFineTerminalRowsStatement W β hβ δ ranks q) :
    (fineJointLaw W β hβ δ ranks q).map Prod.snd = uniformSpinLaw (ranks+q) := by
  let := W.isProbability
  have : IsProbabilityMeasure (finePathLaw W δ ranks q) := by
    unfold finePathLaw
    infer_instance
  have hY : Measurable (fineTerminalField W β hβ δ ranks q) :=
    (measurable_growingReplayFieldAt W β hβ δ hδ ranks q _).comp
      ((measurable_fst.prodMk (measurable_const (a := fun _ : Fin (ranks+q) => false))).prodMk measurable_snd)
  have he : Measurable (fun u : GrowingReplaySpace Ω δ ranks q => (u.1.2,(u.1.1,u.2))) :=
    measurable_fst.snd.prodMk (measurable_fst.fst.prodMk measurable_snd)
  unfold fineJointLaw
  rw [Measure.map_map measurable_snd (measurable_fineReplayOutput δ ranks q)]
  change (growingReplayLinkedLaw W β hβ δ ranks q _).map
    (Prod.fst ∘ (fun u => (u.1.2,(u.1.1,u.2)))) = _
  rw [← Measure.map_map measurable_fst he,
    fineReplay_to_terminalLinkedLaw W β hβ δ hδ ranks q]
  rw [← spinPrior_eq_uniformSpinLaw]
  apply terminalLinkedLaw_spin_marginal_of_rows _ _ _ _ _ hY hrows.1 hrows.2

end SKConstants.Completion.LFine
