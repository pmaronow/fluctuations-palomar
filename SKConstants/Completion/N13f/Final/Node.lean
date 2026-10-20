module

public import SKConstants.Completion.N13f.CanonicalEvent
public import SKConstants.Completion.N13f.SourceEvent
public import SKConstants.Completion.N13f.FinePrefix
public import SKConstants.Completion.N13f.Pointwise

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology BigOperators

namespace SKConstants.Completion.N13f
open SKConstantsOAI.ZeroTemperatureSK Blueprint LC4a LM3 LM4 LM4b

theorem coarseFailureAbsorption_holds
    {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (p : Parameters)
    (hf : FineExponents p) (hb : CoarseExponents p) (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ n : ℕ in atTop,
      coarseGramTailBudget W β p n+coarsePsiTailBudget β p n+coarseCompletionTailBudget p n ≤
        Real.exp (-((n : ℝ)^(1-p.sb))) ∧
      C*coarseLikelihoodCost W β p n ≤ (n : ℝ)^(1-p.kb) ∧
      16*((coarseDyadicDepth n+1 : ℕ) : ℝ)^2*(n : ℝ)^(-p.gamma) ≤ 1 := by
  filter_upwards [coarseFailureBudget_eventually W β hβ p hf hb,
    coarseLikelihoodCost_eventually W β hβ p hf hb C hC,
    coarseDyadicDepth_small_eventually p.gamma hb.2.2.2.1] with n ht hc hs
  exact ⟨ht,hc,hs⟩

theorem coarseScalarRow_holds
    {Ω : Type} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ)
    (r k : ℕ) (i : Fin (r+k))
    (hHist : CanonicalObservationDHistoryStatement W β hβ δ r k
      (growingQueryTime δ (k+1)) le_rfl)
    (hsmall : ∀ j < k, (growingQueryDuration δ (j+1) : ℝ) ≤ 1/8) :
    let V := growingQueryTime δ (k+1)
    let ν := actualParisiFullQuerySpinLaw W W β V
    ∃ J : (Bool × Ω) × Ω → ℝ, Measurable J ∧ IsActualRowDIntegral W W β hβ V J ∧
      (∫ u, N13e.coarsePsi W W β hβ δ k J u ∂ν) =
        actualParisiEntropyReference W β V-β*actualCoarseEnergy W β (growingQueryTime δ) k ∧
      ∀ (n : ℕ), 0 < n → ∀ (η : ℝ), 0 < η →
        (actualParisiFullMixedRowsLaw W W β V n).real {u | (n : ℝ)*η ≤
          |∑ j : Fin n, Concentration.centeredObservable ν (N13e.coarsePsi W W β hβ δ k J) (u j)|} ≤
          2*Real.exp (-(n : ℝ)*min
            (η^2/(8*(psiMomentConstant β*(1+(V : ℝ)))^2))
            (η/(4*(psiMomentConstant β*(1+(V : ℝ)))))) := by
  have htr := actualRowReferenceTransport_of_historyLaw W β hβ δ hδ r k _ le_rfl hHist i
  obtain ⟨J, hJm, hJ⟩ := actualRowDIntegral_exists_of_transport W W β hβ δ hδ r k _ i htr
  exact ⟨J,hJm,hJ,coarsePsi_mean W W β hβ δ hδ k J hJ,
    fun n hn η hη => coarsePsi_iid_abs_of_historyLaw W β hβ δ hδ r k i hHist J hJm hJ hsmall hn hη⟩

end SKConstants.Completion.N13f
