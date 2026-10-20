module

public import WeakDominatedContactWeights

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

theorem finite_contact_trace_budget_eventually
    (μs : ℕ → FiniteMeasure ℝ) (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    {K : Set ℝ} (hK : IsCompact K) (hρK : ρ Kᶜ = 0)
    (hdom : ∀ j : ℕ, (μs j : Measure ℝ) ≤ ρ)
    (ν : Measure ℝ) [ν.OuterRegular] {a b : ℝ}
    (error : ℝ → ℝ → ℕ → ℝ≥0∞)
    (herr : ∀ p q : ℝ, a ≤ p → p < q → q ≤ b → Tendsto (error p q) atTop (𝓝 0))
    (hbound : ∀ p q : ℝ, a ≤ p → p < q → q ≤ b →
      ∀ᶠ j : ℕ in atTop, (μs j : Measure ℝ) (Ioo p q) ≤ ν (Ioo p q) + error p q j)
    (weight : ℝ → ℝ) {A : Set ℝ} (hA : MeasurableSet A) (hAD : A ⊆ Ioo a b)
    (hwρ : IntegrableOn weight A ρ) (hwν : IntegrableOn weight A ν)
    (hw0 : ∀ r ∈ A, 0 ≤ weight r) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ j : ℕ in atTop,
      (∫ r in A, weight r ∂(μs j : Measure ℝ)) ≤ (∫ r in A, weight r ∂ν) + ε := by
  by_contra hbad
  have hfreq : ∃ᶠ j : ℕ in atTop,
      (∫ r in A, weight r ∂ν) + ε < (∫ r in A, weight r ∂(μs j : Measure ℝ)) := by
    simpa only [not_eventually, not_le] using hbad
  let bad : Set ℕ := {j | (∫ r in A, weight r ∂ν) + ε <
    (∫ r in A, weight r ∂(μs j : Measure ℝ))}
  let F : Filter ℕ := atTop ⊓ 𝓟 bad
  have hF : F.NeBot := frequently_mem_iff_neBot.mp hfreq
  let := hF
  obtain ⟨μ,L,hL,hLF,hweak,_⟩ := exists_weak_trace_limit_of_compact_domination
    (F := F) μs ρ hK hρK hdom
  let := hL
  have hLat : L ≤ atTop := hLF.trans inf_le_left
  have hinterval : (μ : Measure ℝ).restrict (Ioo a b) ≤ ν.restrict (Ioo a b) := by
    apply weak_interval_measure_domination μs μ hweak ν error
    · intro p q hap hpq hqb
      exact (herr p q hap hpq hqb).mono_left hLat
    · intro p q hap hpq hqb
      exact (hbound p q hap hpq hqb).filter_mono hLat
  have hrestrict := Measure.restrict_mono (Subset.refl A) hinterval
  rw [Measure.restrict_restrict_of_subset hAD,
    Measure.restrict_restrict_of_subset hAD] at hrestrict
  have hmean : (∫ r in A, weight r ∂(μ : Measure ℝ)) ≤ ∫ r in A, weight r ∂ν :=
    integral_mono_measure hrestrict
      ((ae_restrict_mem hA).mono (fun r hr => hw0 r hr)) hwν
  have ht := weak_contact_weighted_integral_tendsto μs μ hweak ρ hdom weight hA hwρ
  have hev : ∀ᶠ j : ℕ in L, (∫ r in A, weight r ∂ν) + ε ≤
      (∫ r in A, weight r ∂(μs j : Measure ℝ)) := by
    have hprincipal : L ≤ 𝓟 bad := hLF.trans inf_le_right
    have hh : bad ∈ L := le_principal_iff.mp hprincipal
    change ∀ᶠ j : ℕ in L, j ∈ bad at hh
    exact hh.mono (fun j hj => hj.le)
  have hlower := le_of_tendsto_of_tendsto tendsto_const_nhds ht hev
  linarith

end OAI.SKFluctuations.LaplaceWindowFormalization
