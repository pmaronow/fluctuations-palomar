module

public import SKConstants.Completion.LC0.TerminalLinkLaw
public import SKConstants.Completion.LM1a.ProductTools

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators

namespace SKConstants.M1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

theorem map_withDensity_comp {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    (μ : Measure S) (F : S → T) (hF : Measurable F)
    (f : T → ℝ≥0∞) (hf : Measurable f) :
    (μ.withDensity (f ∘ F)).map F = (μ.map F).withDensity f := by
  ext s hs
  rw [Measure.map_apply hF hs, withDensity_apply _ (hF hs), withDensity_apply _ hs,
    setLIntegral_map hs hf hF]
  rfl

theorem pi_withDensity_product {ι : Type*} [Fintype ι] {S : ι → Type*}
    [∀ i, MeasurableSpace (S i)] (μ : (i : ι) → Measure (S i))
    [∀ i, IsProbabilityMeasure (μ i)] (f : (i : ι) → S i → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) [∀ i, SigmaFinite ((μ i).withDensity (f i))] :
    (Measure.pi μ).withDensity (fun x => ∏ i, f i (x i)) =
      Measure.pi (fun i => (μ i).withDensity (f i)) := by
  classical
  apply Eq.symm
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  have he (x : (i : ι) → S i) :
      (univ.pi s).indicator (fun x => ∏ i, f i (x i)) x =
        ∏ i, (s i).indicator (f i) (x i) := by
    by_cases hx : ∀ i, x i ∈ s i
    · rw [Set.indicator_of_mem (show x ∈ univ.pi s from fun i _ => hx i)]
      exact Finset.prod_congr rfl (fun i _ => (Set.indicator_of_mem (hx i) (f i)).symm)
    · rw [Set.indicator_of_notMem (show x ∉ univ.pi s from fun h => hx (fun i => h i (mem_univ i)))]
      obtain ⟨i, hi⟩ := not_forall.mp hx
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi (f i))).symm
  simp_rw [he]
  let X (i : ι) := (s i).indicator (f i)
  have hX (i : ι) : Measurable (X i) := (hf i).indicator (hs i)
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ _
    (iIndepFun_pi (fun i => (hX i).aemeasurable))
    (fun i => (hX i).comp (measurable_pi_apply i))]
  apply Finset.prod_congr rfl
  intro i _
  rw [(measurePreserving_eval μ i).lintegral_comp (hX i),
    lintegral_indicator (hs i), withDensity_apply _ (hs i)]

def ScalarTerminalLinkedLaw {S : Type*} [MeasurableSpace S]
    (β : ℝ) (H : ℝ≥0) (μ : Measure S) (Y : S → ℝ) : Measure (Bool × S) :=
  ((scalarHiddenPriorBool 0).prod μ).withDensity
    (fun u => ENNReal.ofReal (actualParisiSpinLinkDensity β u.1 H (Y u.2)))

theorem measurable_scalarTerminalDensity {S : Type*} [MeasurableSpace S]
    (β : ℝ) (H : ℝ≥0) (Y : S → ℝ) (hY : Measurable Y) :
    Measurable (fun u : Bool × S =>
      ENNReal.ofReal (actualParisiSpinLinkDensity β u.1 H (Y u.2))) := by
  have hm : Measurable (fun y : ℝ => actualParisiFullMagnetization β H y) :=
    ((continuous_actualParisiFullMagnetization β).comp
      (continuous_const.prodMk continuous_id)).measurable
  exact (measurable_const.add
    (((measurable_of_finite scalarHiddenSign).comp measurable_fst).mul
      (hm.comp (hY.comp measurable_snd)))).ennreal_ofReal

theorem scalarTerminalLinkedLaw_probability {S : Type*} [MeasurableSpace S]
    (β : ℝ) (H : ℝ≥0) (μ : Measure S) [IsProbabilityMeasure μ]
    (Y : S → ℝ) (hY : Measurable Y) :
    IsProbabilityMeasure (ScalarTerminalLinkedLaw β H μ Y) := by
  refine ⟨?_⟩
  rw [ScalarTerminalLinkedLaw, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    lintegral_prod_symm _ (measurable_scalarTerminalDensity β H Y hY).aemeasurable]
  simp only [lintegral_actualParisiSpinLinkDensity_bool, lintegral_const, measure_univ, mul_one]

theorem scalarTerminalLinkedLaw_map {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    (β : ℝ) (H : ℝ≥0) (μ : Measure S) [SFinite μ]
    (F : S → T) (hF : Measurable F) (Y : T → ℝ) (hY : Measurable Y) :
    (ScalarTerminalLinkedLaw β H μ (Y ∘ F)).map (Prod.map id F) =
      ScalarTerminalLinkedLaw β H (μ.map F) Y := by
  let f : Bool × T → ℝ≥0∞ :=
    fun u => ENNReal.ofReal (actualParisiSpinLinkDensity β u.1 H (Y u.2))
  change (((scalarHiddenPriorBool 0).prod μ).withDensity (f ∘ Prod.map id F)).map
    (Prod.map id F) = _
  rw [map_withDensity_comp _ _ (measurable_id.prodMap hF) _
    (measurable_scalarTerminalDensity β H Y hY)]
  have hb : ((scalarHiddenPriorBool 0).prod μ).map (Prod.map id F) =
      (scalarHiddenPriorBool 0).prod (μ.map F) := by
    simpa only [Measure.map_id] using
      (Measure.map_prod_map (scalarHiddenPriorBool 0) μ measurable_id hF).symm
  rw [hb]
  rfl

theorem terminalLinkedLaw_pi {S : Type*} [MeasurableSpace S]
    (β : ℝ) (H : ℝ≥0) (μ : Measure S) [IsProbabilityMeasure μ]
    (Y : S → ℝ) (hY : Measurable Y) (n : ℕ) :
    (TerminalLinkedLaw β H (Measure.pi (fun _ : Fin n => μ))
      (fun b i => Y (b i))).map (fun u i => (u.1 i, u.2 i)) =
      Measure.pi (fun _ : Fin n => ScalarTerminalLinkedLaw β H μ Y) := by
  let := scalarTerminalLinkedLaw_probability β H μ Y hY
  let e := dependentPiProd (fun _ : Fin n => Bool) (fun _ : Fin n => S)
  let f : Bool × S → ℝ≥0∞ :=
    fun u => ENNReal.ofReal (actualParisiSpinLinkDensity β u.1 H (Y u.2))
  have hf : Measurable f := measurable_scalarTerminalDensity β H Y hY
  have hb : ((spinPrior n).prod (Measure.pi (fun _ : Fin n => μ))).map e.symm =
      Measure.pi (fun _ : Fin n => (scalarHiddenPriorBool 0).prod μ) :=
    ((MeasurableEquiv.map_apply_eq_iff_map_symm_apply_eq e).mp
      (dependentPiProd_law (fun _ : Fin n => scalarHiddenPriorBool 0) (fun _ : Fin n => μ)).map_eq).symm
  have hd : (fun u : (Fin n → Bool) × (Fin n → S) =>
      ENNReal.ofReal (TerminalDensity β H (fun b i => Y (b i)) u)) =
      (fun b => ∏ i, f (b i)) ∘ e.symm := by
    funext u
    exact ENNReal.ofReal_prod_of_nonneg
      (fun i _ => (actualParisiSpinLinkDensity_pos β (u.1 i) H (Y (u.2 i))).le)
  change (((spinPrior n).prod (Measure.pi (fun _ : Fin n => μ))).withDensity
    (fun u => ENNReal.ofReal (TerminalDensity β H (fun b i => Y (b i)) u))).map e.symm = _
  have hprod : Measurable (fun b : Fin n → Bool × S => ∏ i, f (b i)) := by
    apply Finset.measurable_prod
    intro i _
    exact hf.comp (measurable_pi_apply i)
  rw [hd, map_withDensity_comp _ _ e.symm.measurable _ hprod, hb]
  exact pi_withDensity_product (fun _ : Fin n => (scalarHiddenPriorBool 0).prod μ)
    (fun _ => f) (fun _ => hf)

end SKConstants.M1
