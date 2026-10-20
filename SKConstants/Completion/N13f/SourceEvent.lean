module

public import SKConstants.Completion.N13f.Cost

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology BigOperators

namespace SKConstants.Completion.N13f
open SKConstantsOAI.ZeroTemperatureSK Blueprint LGram N13e LM4b GaussianProposal LC5 LM5
variable {Ω : Type*} [MeasurableSpace Ω]

def stoppedSourceEnergyEvent (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) :
    Set ((Fin (rankCount p.a p.b n+queryCount p.a p.b n) → Bool) ×
      M1.SourceInput (meshSize p.a n) (rankCount p.a p.b n) (queryCount p.a p.b n)) :=
  sourceCoarseEnergyEvent W β hβ (meshSize p.a n) (rankCount p.a p.b n) (queryCount p.a p.b n)
    ((n : ℝ)^(-p.gamma)) ((n : ℝ)^(-p.z))

theorem stoppedSourceEnergyEvent_eventually
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (p : Parameters)
    (hf : FineExponents p) (hb : CoarseExponents p)
    (hrows : ∀ᶠ n : ℕ in atTop, SourceMixedRowsLawStatement W β hβ (meshSize p.a n)
      (rankCount p.a p.b n) (queryCount p.a p.b n)) :
    ∀ᶠ n : ℕ in atTop,
      let δ := meshSize p.a n
      let r := rankCount p.a p.b n
      let k := queryCount p.a p.b n
      let E := stoppedSourceEnergyEvent W β hβ p n
      MeasurableSet E ∧ (M1.SourceLinkedLaw W β hβ δ r k).real Eᶜ ≤
        Real.exp (-((n : ℝ)^(1-p.sb))) ∧
      ∀ z ∈ E,
        |quadraticEnergy (r+k : ℕ) (signSpin z.1)
            (actualParisiGrowingSourceAugmentedOutput W β hβ δ r k z.2.1 z.2.2).1 -
          actualCoarseEnergy W β (growingQueryTime δ) k - sourceEnergyLinearPart W β hβ δ r k z| ≤
          (n : ℝ)^(-p.z)+1400*((coarseDyadicDepth n+1 : ℕ) : ℝ)^4*((n : ℝ)^(-p.gamma))^2 := by
  have hγ : 0 < p.gamma := hb.2.2.2.1
  filter_upwards [hrows, coarseGramTailBudget_eventually W β hβ p hf hb,
    coarseCompletionTailBudget_eventually p hf hb, coarseDyadicDepth_small_eventually p.gamma hγ,
    eventually_ge_atTop 2] with n hrow hgram hcomp hsmall hn
  let δ := meshSize p.a n
  let r := rankCount p.a p.b n
  let k := queryCount p.a p.b n
  have hdim : r+k=n := rankCount_add p.a p.b n
  have hN : 0 < r+k := by omega
  have hδ : 0 < δ := paperGrowingQueryMeshSize_pos p.a n (by omega)
  have hη : 0 < (n : ℝ)^(-p.gamma) := Real.rpow_pos_of_pos (by positivity) _
  have hu : 0 < (n : ℝ)^(-p.z) := Real.rpow_pos_of_pos (by positivity) _
  have hbudget : gramTailBudget (r+k) (k+(k+1))
      (actualParisiFullMixedRowMGFProxy W β (growingQueryTime δ k)) ((n : ℝ)^(-p.gamma)) +
      2*Real.exp (-((r+k : ℕ) : ℝ)*((n : ℝ)^(-p.z))^2) =
      coarseGramTailBudget W β p n+coarseCompletionTailBudget p n := by
    rw [hdim]
    rfl
  have hprob := sourceCoarseEnergyEvent_compl_le W β hβ δ hδ r k hN
    ((n : ℝ)^(-p.gamma)) ((n : ℝ)^(-p.z)) hη hu hrow
  rw [hbudget] at hprob
  refine ⟨measurableSet_sourceCoarseEnergyEvent W β hβ δ r k hN _ _,
    hprob.trans (by linarith [Real.exp_pos (-((n : ℝ)^(1-p.sb)))]), ?_⟩
  intro z hz
  exact sourceCoarseEnergyEvent_energy_error W β hβ δ hδ r k (coarseDyadicDepth n)
    (2^coarseDyadicDepth n-k) (coarseDyadicDepth_padding p n) hN _ _ hη.le hsmall z hz

end SKConstants.Completion.N13f
