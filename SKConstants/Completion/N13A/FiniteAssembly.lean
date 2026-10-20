module

public import SKConstants.Completion.N13A.Regularity
public import SKConstants.Completion.N13A.ConditionalTail

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace SKConstants.Completion.N13A
open SKConstantsOAI.ZeroTemperatureSK Blueprint

theorem information_energy_algebra (N β I H Q L Z P A ε η : ℝ)
    (hN : 0 < N) (hβ : 0 ≤ β) (hH : H/N = Q+Z)
    (hobs : I/N - β*L ≤ Real.log 2 - P + A)
    (hQ : |Q-L| ≤ ε) (hZ : |Z| ≤ η) :
    I - N*Real.log 2 - β*H ≤ -N*P + N*(A+β*ε+β*η) := by
  have h1 := mul_le_mul_of_nonneg_left (abs_le.mp hQ).1 hβ
  have h2 := mul_le_mul_of_nonneg_left (abs_le.mp hZ).1 hβ
  have hb : I/N - Real.log 2 - β*(H/N) ≤ -P + (A+β*ε+β*η) := by
    rw [hH]
    nlinarith
  calc
    _ = N*(I/N - Real.log 2 - β*(H/N)) := by field_simp [hN.ne'] <;> ring
    _ ≤ N*(-P+(A+β*ε+β*η)) := mul_le_mul_of_nonneg_left hb hN.le
    _ = _ := by ring

theorem sharp_event_of_four_failures {Ω : Type} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (p : Parameters) (n : ℕ) (hn : 0<n)
    (I : SharpInput p n → ℝ) (B A ε η r : ℝ)
    (h0 : (sharpLinkedLaw W β hβ p n).real
      {y | sharpRows W β hβ p n y ∉ gramGood W β hβ p n} ≤ r)
    (h1 : (sharpLinkedLaw W β hβ p n).real
      {y | B < weightedSq W β hβ (sharpRows W β hβ p n y)} ≤ r)
    (h2 : (sharpLinkedLaw W β hβ p n).real
      {y | (sharpRows W β hβ p n y ∈ gramGood W β hβ p n ∧
        weightedSq W β hβ (sharpRows W β hβ p n y) ≤ B) ∧
          η < |sharpDiscarded W β hβ p n y|} ≤ r)
    (h3 : (sharpLinkedLaw W β hβ p n).real
      {y | Real.log 2 - parisiPressure β + A <
        I y / n - β*linearEnergy W β hβ (sharpRows W β hβ p n y)} ≤ r)
    (henergy : ∀ y : SharpInput p n,
      sharpRows W β hβ p n y ∈ gramGood W β hβ p n →
      weightedSq W β hβ (sharpRows W β hβ p n y) ≤ B →
      |sharpQueryEnergy W β hβ p n y - linearEnergy W β hβ (sharpRows W β hβ p n y)| ≤ ε) :
    ∃ E : Set (SharpInput p n), MeasurableSet E ∧
      (sharpLinkedLaw W β hβ p n).real Eᶜ ≤ 4*r ∧
      ∀ y ∈ E, I y - (n:ℝ)*Real.log 2 -
        β*goeSpinHamiltonian (1/Real.sqrt (2*(n:ℝ))) y.1 y.2.1 ≤
          -(n:ℝ)*parisiPressure β + (n:ℝ)*(A+β*ε+β*η) := by
  let μ := sharpLinkedLaw W β hβ p n
  let B0 : Set (SharpInput p n) := {y | sharpRows W β hβ p n y ∉ gramGood W β hβ p n}
  let B1 : Set (SharpInput p n) := {y | B < weightedSq W β hβ (sharpRows W β hβ p n y)}
  let B2 : Set (SharpInput p n) := {y |
    (sharpRows W β hβ p n y ∈ gramGood W β hβ p n ∧
      weightedSq W β hβ (sharpRows W β hβ p n y) ≤ B) ∧
        η < |sharpDiscarded W β hβ p n y|}
  let B3 : Set (SharpInput p n) := {y | Real.log 2 - parisiPressure β + A <
    I y / n - β*linearEnergy W β hβ (sharpRows W β hβ p n y)}
  let Bad := B0 ∪ B1 ∪ B2 ∪ B3
  have hbad : μ.real Bad ≤ 4*r := by
    have ha := measureReal_union_le (μ := μ) B0 B1
    have hb := measureReal_union_le (μ := μ) (B0 ∪ B1) B2
    have hc := measureReal_union_le (μ := μ) (B0 ∪ B1 ∪ B2) B3
    change μ.real B0 ≤ r at h0
    change μ.real B1 ≤ r at h1
    change μ.real B2 ≤ r at h2
    change μ.real B3 ≤ r at h3
    dsimp only [Bad]
    linarith
  refine ⟨(toMeasurable μ Bad)ᶜ, (measurableSet_toMeasurable μ Bad).compl, ?_, ?_⟩
  · simp only [compl_compl]
    change μ.real (toMeasurable μ Bad) ≤ 4*r
    simpa only [measureReal_def, measure_toMeasurable] using hbad
  · intro y hy
    have hnot : y ∉ Bad := fun h => hy (subset_toMeasurable μ Bad h)
    have hg : sharpRows W β hβ p n y ∈ gramGood W β hβ p n := by
      by_contra h
      exact hnot (by simp [Bad, B0, h])
    have hw : weightedSq W β hβ (sharpRows W β hβ p n y) ≤ B := by
      by_contra h
      exact hnot (by simp [Bad, B1, not_le.mp h])
    have hz : |sharpDiscarded W β hβ p n y| ≤ η := by
      by_contra h
      exact hnot (by simp [Bad, B2, hg, hw, not_le.mp h])
    have hψ : I y / n - β*linearEnergy W β hβ (sharpRows W β hβ p n y) ≤
        Real.log 2 - parisiPressure β + A := by
      by_contra h
      exact hnot (by simp [Bad, B3, not_le.mp h])
    apply information_energy_algebra (n:ℝ) β (I y)
      (goeSpinHamiltonian (1/Real.sqrt (2*(n:ℝ))) y.1 y.2.1)
      (sharpQueryEnergy W β hβ p n y) (linearEnergy W β hβ (sharpRows W β hβ p n y))
      (sharpDiscarded W β hβ p n y) (parisiPressure β) A ε η
      (by exact_mod_cast hn) (by linarith) _ hψ (henergy y hg hw) hz
    unfold sharpDiscarded
    ring

end SKConstants.Completion.N13A
