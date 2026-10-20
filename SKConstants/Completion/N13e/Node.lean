module

public import SKConstants.Completion.N13e.RowEnergy
public import SKConstants.Completion.N13e.Psi
public import SKConstants.Completion.N13e.CompletionTail

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal RealInnerProductSpace Matrix.Norms.L2Operator

namespace SKConstants.Completion.N13e
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal LC5 LGram LM5 LM4b
variable {Ω : Type*} [MeasurableSpace Ω]

def sourceCoarseEnergyEvent (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) (η u : ℝ) : Set ((Fin (r+K) → Bool) × M1.SourceInput δ r K) :=
  sourceWholeGramEvent W β hβ δ r K η ∩
    {z | |growingSourceDiscardedEnergy W β hβ δ r K z| ≤ u}

theorem measurableSet_sourceCoarseEnergyEvent
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0)
    (r K : ℕ) (hN : 0 < r+K) (η u : ℝ) :
    MeasurableSet (sourceCoarseEnergyEvent W β hβ δ r K η u) :=
  (measurableSet_sourceWholeGramEvent W β hβ δ r K η).inter
    (measurableSet_le (measurable_growingSourceDiscardedEnergy W β hβ δ r K hN).abs
      measurable_const)

theorem sourceCoarseEnergyEvent_compl_le
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ) (hN : 0 < r+K)
    (η u : ℝ) (hη : 0 < η) (hu : 0 < u)
    (hrow : SourceMixedRowsLawStatement W β hβ δ r K) :
    (M1.SourceLinkedLaw W β hβ δ r K).real (sourceCoarseEnergyEvent W β hβ δ r K η u)ᶜ ≤
      gramTailBudget (r+K) (K+(K+1))
        (actualParisiFullMixedRowMGFProxy W β (growingQueryTime δ K)) η +
      2*Real.exp (-((r+K:ℕ):ℝ)*u^2) := by
  have hsub : (sourceCoarseEnergyEvent W β hβ δ r K η u)ᶜ ⊆
      (sourceWholeGramEvent W β hβ δ r K η)ᶜ ∪
        {z | u ≤ |growingSourceDiscardedEnergy W β hβ δ r K z|} := by
    intro z hz
    by_cases hg : z ∈ sourceWholeGramEvent W β hβ δ r K η
    · right
      have hn : ¬ |growingSourceDiscardedEnergy W β hβ δ r K z| ≤ u :=
        fun h => hz ⟨hg,h⟩
      exact (lt_of_not_ge hn).le
    · exact Or.inl hg
  calc
    _ ≤ (M1.SourceLinkedLaw W β hβ δ r K).real
        ((sourceWholeGramEvent W β hβ δ r K η)ᶜ ∪
          {z | u ≤ |growingSourceDiscardedEnergy W β hβ δ r K z|}) := measureReal_mono hsub
    _ ≤ _ + _ := measureReal_union_le _ _
    _ ≤ _ := add_le_add (actualSource_wholeGram_compl_le W β hβ δ hδ r K hN η hη hrow)
      (growingSourceDiscardedEnergy_tail W β hβ δ r K hN u hu)

theorem sourceCoarseEnergyEvent_energy_error
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r K R m : ℕ) (hdim : K+m=2^R)
    (hN : 0 < r+K) (η u : ℝ) (hη : 0 ≤ η)
    (hsmall : 16*((R+1:ℕ):ℝ)^2*η ≤ 1)
    (z : (Fin (r+K) → Bool) × M1.SourceInput δ r K)
    (hz : z ∈ sourceCoarseEnergyEvent W β hβ δ r K η u) :
    |quadraticEnergy (r+K:ℕ) (signSpin z.1)
        (actualParisiGrowingSourceAugmentedOutput W β hβ δ r K z.2.1 z.2.2).1 -
      actualCoarseEnergy W β (growingQueryTime δ) K - sourceEnergyLinearPart W β hβ δ r K z| ≤
      u + 1400*((R+1:ℕ):ℝ)^4*η^2 := by
  have h := actualSource_query_energy_quadratic_remainder W β hβ δ hδ r K R m hdim
    hN η hη hsmall z hz.1
  rw [← actualCoarseEnergy_eq_population_pairing W W β hβ _
    (growingQueryTime_strictMono δ hδ) K] at h
  have hZ : growingSourceDiscardedEnergy W β hβ δ r K z =
      quadraticEnergy (r+K:ℕ) (signSpin z.1)
        (actualParisiGrowingSourceAugmentedOutput W β hβ δ r K z.2.1 z.2.2).1 -
      paperQueryEnergy r (r+K) (r+K:ℕ) (M1.Target W β hβ δ r K) (M1.Update δ r K) K
        (M1.Initial δ r K z.2,1) (M1.Original δ r K z.2) (fun i => scalarHiddenSign (z.1 i)) :=
    growingSourceDiscardedEnergy_eq_actual W β hβ δ r K z
  calc
    _ = |growingSourceDiscardedEnergy W β hβ δ r K z +
        (paperQueryEnergy r (r+K) (r+K:ℕ) (M1.Target W β hβ δ r K) (M1.Update δ r K) K
          (M1.Initial δ r K z.2,1) (M1.Original δ r K z.2) (fun i => scalarHiddenSign (z.1 i)) -
          actualCoarseEnergy W β (growingQueryTime δ) K - sourceEnergyLinearPart W β hβ δ r K z)| := by
      rw [hZ]
      congr 1
      ring
    _ ≤ |growingSourceDiscardedEnergy W β hβ δ r K z| +
        |paperQueryEnergy r (r+K) (r+K:ℕ) (M1.Target W β hβ δ r K) (M1.Update δ r K) K
          (M1.Initial δ r K z.2,1) (M1.Original δ r K z.2) (fun i => scalarHiddenSign (z.1 i)) -
          actualCoarseEnergy W β (growingQueryTime δ) K - sourceEnergyLinearPart W β hβ δ r K z| :=
      abs_add_le _ _
    _ ≤ _ := add_le_add hz.2 h

def SourceCoarseEnergyStatement
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0)
    (r K R : ℕ) (η u : ℝ) : Prop :=
  ∃ E : Set ((Fin (r+K) → Bool) × M1.SourceInput δ r K), MeasurableSet E ∧
    (M1.SourceLinkedLaw W β hβ δ r K).real Eᶜ ≤
      gramTailBudget (r+K) (K+(K+1))
        (actualParisiFullMixedRowMGFProxy W β (growingQueryTime δ K)) η +
      2*Real.exp (-((r+K:ℕ):ℝ)*u^2) ∧
    ∀ z ∈ E,
      |quadraticEnergy (r+K:ℕ) (signSpin z.1)
          (actualParisiGrowingSourceAugmentedOutput W β hβ δ r K z.2.1 z.2.2).1 -
        actualCoarseEnergy W β (growingQueryTime δ) K - sourceEnergyLinearPart W β hβ δ r K z| ≤
        u + 1400*((R+1:ℕ):ℝ)^4*η^2

theorem sourceCoarseEnergy_holds
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r K R m : ℕ) (hdim : K+m=2^R)
    (hN : 0 < r+K) (η u : ℝ) (hη : 0 < η) (hu : 0 < u)
    (hsmall : 16*((R+1:ℕ):ℝ)^2*η ≤ 1)
    (hrow : SourceMixedRowsLawStatement W β hβ δ r K) :
    SourceCoarseEnergyStatement W β hβ δ r K R η u :=
  ⟨sourceCoarseEnergyEvent W β hβ δ r K η u,
    measurableSet_sourceCoarseEnergyEvent W β hβ δ r K hN η u,
    sourceCoarseEnergyEvent_compl_le W β hβ δ hδ r K hN η u hη hu hrow,
    fun z hz => sourceCoarseEnergyEvent_energy_error W β hβ δ hδ r K R m hdim hN η u
      hη.le hsmall z hz⟩

end SKConstants.Completion.N13e
