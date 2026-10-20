module

public import WeakContactMeasureDomination
public import Mathlib.MeasureTheory.Measure.Prokhorov

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

theorem weak_limit_le_of_uniform_domination
    {ι : Type*} {L : Filter ι} [L.NeBot]
    (μs : ι → FiniteMeasure ℝ) (μ : FiniteMeasure ℝ)
    (hweak : Tendsto μs L (𝓝 μ)) (ρ : Measure ℝ) [ρ.OuterRegular]
    (hdom : ∀ᶠ j : ι in L, (μs j : Measure ℝ) ≤ ρ) : (μ : Measure ℝ) ≤ ρ := by
  apply Measure.le_iff.mpr
  intro A _
  rw [Set.measure_eq_iInf_isOpen A ρ]
  apply le_iInf
  intro G
  apply le_iInf
  intro hAG
  apply le_iInf
  intro hG
  apply (measure_mono hAG).trans
  apply weak_open_measure_le_of_vanishing_error μs μ hweak hG (ρ G) (fun _ => 0)
    tendsto_const_nhds
  exact hdom.mono (fun j hj => by simpa only [add_zero] using Measure.le_iff'.mp hj G)

theorem exists_weak_trace_limit_of_compact_domination
    {ι : Type*} {F : Filter ι} [F.NeBot]
    (μs : ι → FiniteMeasure ℝ) (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    {K : Set ℝ} (hK : IsCompact K) (hρK : ρ Kᶜ = 0)
    (hdom : ∀ j : ι, (μs j : Measure ℝ) ≤ ρ) :
    ∃ (μ : FiniteMeasure ℝ) (L : Filter ι), L.NeBot ∧ L ≤ F ∧
      Tendsto μs L (𝓝 μ) ∧ (μ : Measure ℝ) ≤ ρ := by
  let C : ℝ≥0 := (ρ univ).toNNReal
  have hmem (j : ι) : μs j ∈ {ν : FiniteMeasure ℝ | ν.mass ≤ C ∧ ν Kᶜ = 0} := by
    constructor
    · exact ENNReal.toNNReal_mono (measure_ne_top ρ univ) (Measure.le_iff'.mp (hdom j) univ)
    · have hj := (Measure.le_iff'.mp (hdom j) Kᶜ).trans_eq hρK
      have hz : (μs j : Measure ℝ) Kᶜ = 0 := le_antisymm hj bot_le
      simp only [FiniteMeasure.coeFn_def, hz, ENNReal.toNNReal_zero]
  have hmap : Filter.map μs F ≤ 𝓟 {ν : FiniteMeasure ℝ | ν.mass ≤ C ∧ ν Kᶜ = 0} := by
    rw [Filter.le_principal_iff, Filter.mem_map]
    change ∀ᶠ j : ι in F, μs j ∈ {ν : FiniteMeasure ℝ | ν.mass ≤ C ∧ ν Kᶜ = 0}
    exact Eventually.of_forall hmem
  obtain ⟨μ,_,hcluster⟩ := (isCompact_setOfPred_finiteMeasure_le_of_isCompact C hK).exists_mapClusterPt hmap
  let L := Filter.comap μs (𝓝 μ) ⊓ F
  have hL : L.NeBot := Filter.neBot_inf_comap_iff_map'.mpr hcluster
  let := hL
  have hweak : Tendsto μs L (𝓝 μ) := Filter.map_le_iff_le_comap.mpr inf_le_left
  refine ⟨μ,L,hL,inf_le_right,hweak,?_⟩
  exact weak_limit_le_of_uniform_domination μs μ hweak ρ (Eventually.of_forall hdom)

end OAI.SKFluctuations.LaplaceWindowFormalization
