module

public import ComparisonWholeCapEndpoints
public import Mathlib.MeasureTheory.Measure.Portmanteau

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal
open OAI.SKFluctuations.WholeUnitSideKernel

theorem weak_open_measure_le_of_vanishing_error
    {ι : Type*} {L : Filter ι} [L.NeBot]
    (μs : ι → FiniteMeasure ℝ) (μ : FiniteMeasure ℝ)
    (hweak : Tendsto μs L (𝓝 μ)) {G : Set ℝ} (hG : IsOpen G)
    (R : ℝ≥0∞) (error : ι → ℝ≥0∞)
    (herr : Tendsto error L (𝓝 0))
    (hbound : ∀ᶠ j : ι in L, (μs j : Measure ℝ) G ≤ R + error j) :
    (μ : Measure ℝ) G ≤ R := by
  let fs : ℕ → BoundedContinuousFunction ℝ ℝ≥0 := fun k => 1 - hG.isClosed_compl.apprSeq k
  have hfs (k : ℕ) (x : ℝ) : fs k x ≤ G.indicator (fun _ => (1 : ℝ≥0)) x := by
    by_cases hx : x ∈ G
    · simp only [indicator_of_mem hx]
      exact tsub_le_self
    · have hc : x ∈ Gᶜ := hx
      rw [indicator_of_notMem hx]
      change (1 : ℝ≥0) - hG.isClosed_compl.apprSeq k x ≤ 0
      rw [HasOuterApproxClosed.apprSeq_apply_eq_one hG.isClosed_compl k hc, tsub_self]
  have htest (k : ℕ) : (∫⁻ x, fs k x ∂(μ : Measure ℝ)) ≤ R := by
    have ht := FiniteMeasure.tendsto_iff_forall_lintegral_tendsto.mp hweak (fs k)
    have he : ∀ᶠ j : ι in L, (∫⁻ x, fs k x ∂(μs j : Measure ℝ)) ≤ R + error j := by
      filter_upwards [hbound] with j hj
      apply le_trans (lintegral_mono (fun x => ENNReal.coe_le_coe.mpr (hfs k x)))
      simpa only [ENNReal.coe_indicator, ENNReal.coe_one,
        lintegral_indicator hG.measurableSet, lintegral_one,
        Measure.restrict_apply MeasurableSet.univ, univ_inter] using hj
    simpa only [add_zero] using le_of_tendsto_of_tendsto ht (tendsto_const_nhds.add herr) he
  have hlim : Tendsto (fun k => ∫⁻ x, fs k x ∂(μ : Measure ℝ)) atTop
      (𝓝 ((μ : Measure ℝ) G)) := by
    apply measure_of_cont_bdd_of_tendsto_filter_indicator (μ : Measure ℝ)
      hG.measurableSet fs
    · exact Eventually.of_forall (fun k => ae_of_all _ (fun x => tsub_le_self))
    · apply ae_of_all
      intro x
      have ht := (tendsto_pi_nhds.mp (HasOuterApproxClosed.tendsto_apprSeq hG.isClosed_compl)) x
      have hh := (tendsto_const_nhds (x := (1 : ℝ≥0))).sub ht
      convert hh using 1
      · rfl
      · by_cases hx : x ∈ G <;> simp [hx]
  exact le_of_tendsto hlim (Eventually.of_forall htest)

theorem open_subset_measure_le_of_interval_bounds
    (μ ν : Measure ℝ) {a b : ℝ}
    (hbound : ∀ p q : ℝ, a ≤ p → p < q → q ≤ b → μ (Ioo p q) ≤ ν (Ioo p q))
    {G : Set ℝ} (hG : IsOpen G) (hsub : G ⊆ Ioo a b) : μ G ≤ ν G := by
  have hc := wholeCap_representatives_countable hG
  have hd := wholeCap_representatives_pairwiseDisjoint G
  have hm : ∀ r ∈ ordConnectedSection G, MeasurableSet (ordConnectedComponent G r) :=
    fun r _ => (wholeCap_component_isOpen hG r).measurableSet
  rw [← wholeCap_representatives_union G, measure_biUnion hc hd hm,
    measure_biUnion hc hd hm]
  apply ENNReal.tsum_le_tsum
  intro r
  obtain ⟨hlo,hlr,hrz,hhi,heq,_,_⟩ := wholeCap_component_endpoints hG
    (hsub.trans Ioo_subset_Icc_self) (ordConnectedSection_subset r.property)
  rw [heq]
  exact hbound _ _ hlo (hlr.trans hrz) hhi

theorem restrict_measure_le_of_interval_bounds
    (μ ν : Measure ℝ) [ν.OuterRegular] {a b : ℝ}
    (hbound : ∀ p q : ℝ, a ≤ p → p < q → q ≤ b → μ (Ioo p q) ≤ ν (Ioo p q)) :
    μ.restrict (Ioo a b) ≤ ν.restrict (Ioo a b) := by
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.restrict_apply hA, Measure.restrict_apply hA,
    Set.measure_eq_iInf_isOpen (A ∩ Ioo a b) ν]
  apply le_iInf
  intro G
  apply le_iInf
  intro hAG
  apply le_iInf
  intro hG
  calc
    μ (A ∩ Ioo a b) ≤ μ (G ∩ Ioo a b) := measure_mono (subset_inter hAG inter_subset_right)
    _ ≤ ν (G ∩ Ioo a b) := open_subset_measure_le_of_interval_bounds μ ν hbound
      (hG.inter isOpen_Ioo) inter_subset_right
    _ ≤ ν G := measure_mono inter_subset_left

theorem weak_interval_measure_domination
    {ι : Type*} {L : Filter ι} [L.NeBot]
    (μs : ι → FiniteMeasure ℝ) (μ : FiniteMeasure ℝ)
    (hweak : Tendsto μs L (𝓝 μ)) (ν : Measure ℝ) [ν.OuterRegular]
    {a b : ℝ} (error : ℝ → ℝ → ι → ℝ≥0∞)
    (herr : ∀ p q : ℝ, a ≤ p → p < q → q ≤ b → Tendsto (error p q) L (𝓝 0))
    (hbound : ∀ p q : ℝ, a ≤ p → p < q → q ≤ b →
      ∀ᶠ j : ι in L, (μs j : Measure ℝ) (Ioo p q) ≤ ν (Ioo p q) + error p q j) :
    (μ : Measure ℝ).restrict (Ioo a b) ≤ ν.restrict (Ioo a b) := by
  apply restrict_measure_le_of_interval_bounds
  intro p q hap hpq hqb
  exact weak_open_measure_le_of_vanishing_error μs μ hweak isOpen_Ioo _ (error p q)
    (herr p q hap hpq hqb) (hbound p q hap hpq hqb)

theorem weighted_contact_lintegral_le_of_domination
    (μ ρ : Measure ℝ) (f weight : ℝ → ℝ≥0∞)
    (hf : Measurable f) (hw : Measurable weight) {D A : Set ℝ}
    (hA : MeasurableSet A) (hAD : A ⊆ D)
    (hdom : μ.restrict D ≤ (ρ.withDensity f).restrict D) :
    (∫⁻ r in A, weight r ∂μ) ≤ ∫⁻ r in A, f r * weight r ∂ρ := by
  have hd := Measure.restrict_mono (Subset.refl A) hdom
  rw [Measure.restrict_restrict_of_subset hAD,
    Measure.restrict_restrict_of_subset hAD] at hd
  calc
    (∫⁻ r in A, weight r ∂μ) ≤ ∫⁻ r in A, weight r ∂ρ.withDensity f :=
      lintegral_mono' hd le_rfl
    _ = ∫⁻ r in A, f r * weight r ∂ρ :=
      setLIntegral_withDensity_eq_setLIntegral_mul ρ hf hw hA

theorem weighted_contact_lintegral_le_const
    (μ ρ : Measure ℝ) (f weight : ℝ → ℝ≥0∞)
    (hf : Measurable f) (hw : Measurable weight) {D A : Set ℝ}
    (hA : MeasurableSet A) (hAD : A ⊆ D)
    (hdom : μ.restrict D ≤ (ρ.withDensity f).restrict D) (C : ℝ≥0∞)
    (hcontact : ∀ᵐ r ∂ρ.restrict A, f r ≤ C) :
    (∫⁻ r in A, weight r ∂μ) ≤ C * (∫⁻ r in A, weight r ∂ρ) := by
  calc
    (∫⁻ r in A, weight r ∂μ) ≤ ∫⁻ r in A, f r * weight r ∂ρ :=
      weighted_contact_lintegral_le_of_domination μ ρ f weight hf hw hA hAD hdom
    _ ≤ ∫⁻ r in A, C * weight r ∂ρ := lintegral_mono_ae
      (hcontact.mono (fun r hr => by gcongr))
    _ = C * (∫⁻ r in A, weight r ∂ρ) := lintegral_const_mul C hw

end OAI.SKFluctuations.LaplaceWindowFormalization
