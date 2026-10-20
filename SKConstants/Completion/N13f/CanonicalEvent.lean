module

public import SKConstants.Completion.N13f.HistoryTransport
public import SKConstants.Completion.N13f.Budgets
public import SKConstants.Completion.N7.Node

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology BigOperators

namespace SKConstants.Completion.N13f
open SKConstantsOAI.ZeroTemperatureSK Blueprint LC4a LM4 LM4b
variable {Ω : Type} [MeasurableSpace Ω]

theorem measurable_coarsePsi
    (W : BrownianSystem Ω) (Z : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (k : ℕ) (J : (Bool × Ω) × Ω → ℝ) (hJm : Measurable J) :
    Measurable (N13e.coarsePsi W Z β hβ δ k J) := by
  have hz : Measurable (actualZeta W Z β hβ (growingQueryTime δ)
      (actualCoarseWeight W β (growingQueryTime δ))
      (actualCoarseNoiseWeight W β (growingQueryTime δ)) k
      (actualCoarseEnergy W β (growingQueryTime δ) k)) := by
    rw [actualZeta_eq_parts]
    exact ((measurable_actualZetaDeterministic W β _ _ _).add
      (measurable_actualNoise W Z β hβ _ _ _)).sub measurable_const
  exact (measurable_rowInformation (measurable_actualRowLink β W _)
    hJm (measurable_actualRowDBracket W β _)).sub (hz.const_mul β)

theorem canonicalCoarsePsi_eventually
    (hHistory : N7.ReplayDHistoryLawStatement)
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (p : Parameters)
    (hf : FineExponents p) (hb : CoarseExponents p) :
    ∀ᶠ n : ℕ in atTop,
      let δ := meshSize p.a n
      let k := queryCount p.a p.b n
      let V := readoutTime p.a p.b n
      let ν := actualParisiFullQuerySpinLaw W W β V
      ∃ J : (Bool × Ω) × Ω → ℝ, Measurable J ∧ IsActualRowDIntegral W W β hβ V J ∧
        (∫ u, N13e.coarsePsi W W β hβ δ k J u ∂ν) =
          Real.log 2-parisiPressure β+β^2/4*(actualParisiFullSusceptibilityExpected W β V)^2+
            β*(actualParisiEnergyReference W β V-actualCoarseEnergy W β (growingQueryTime δ) k) ∧
        (actualParisiFullMixedRowsLaw W W β V n).real {u | (n : ℝ)*(n : ℝ)^(-p.z) ≤
          |∑ j : Fin n, Concentration.centeredObservable ν (N13e.coarsePsi W W β hβ δ k J) (u j)|} ≤
          Real.exp (-((n : ℝ)^(1-p.sb)))/4 := by
  have hb0 := hb.1
  have hba : p.b/4 < p.a := by
    have hbf := hb.2.1
    have hfa := hf.1
    linarith
  have hlogev : ∀ᶠ n : ℕ in atTop,
      (parisiEquilibriumPhysicalEndpoint β : ℝ)/p.b ≤ Real.log n :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  have hdurev : ∀ᶠ n : ℕ in atTop, (n : ℝ)^(p.b/4-p.a) ≤ 1/8 := by
    have h := constant_rpow_le_small_rpow (p.b/4-p.a) 0 1 (1/8)
      (by linarith) (by norm_num) (by norm_num)
    simpa only [one_mul, Real.rpow_zero, mul_one] using h
  filter_upwards [coarse_schedule_bounds p hf hb, coarsePsiTailBudget_eventually β hβ p hf hb,
    hlogev, hdurev] with n hn htail hlog hdur
  let δ := meshSize p.a n
  let k := queryCount p.a p.b n
  let r := rankCount p.a p.b n
  let V := readoutTime p.a p.b n
  have hδ : 0 < δ := paperGrowingQueryMeshSize_pos p.a n (by omega)
  have hdim : r+k=n := rankCount_add p.a p.b n
  have hN : 0 < r+k := by omega
  let i : Fin (r+k) := ⟨0,hN⟩
  have hHist := hHistory W β hβ δ hδ r k hn.2.2.1
  have htransport := actualRowReferenceTransport_of_historyLaw W β hβ δ hδ r k V le_rfl hHist i
  obtain ⟨J, hJm, hJ⟩ := actualRowDIntegral_exists_of_transport W W β hβ δ hδ r k V i htransport
  have hsmall : ∀ j < k, (growingQueryDuration δ (j+1) : ℝ) ≤ 1/8 := by
    intro j hj
    exact (duration_bound p.a p.b hb0 n hn.1 hn.2.1 (j+1) (by omega)).trans hdur
  have hV : (parisiEquilibriumPhysicalEndpoint β : ℝ) ≤ V :=
    ((div_le_iff₀ hb0).mp hlog).trans (by simpa [V, mul_comm] using hn.2.2.2.2.1)
  refine ⟨J, hJm, hJ, coarsePsi_mean_pressure W W β hβ δ hδ k hV J hJ, ?_⟩
  have ht := coarsePsi_iid_abs_of_historyLaw W β hβ δ hδ r k i hHist J hJm hJ hsmall
    (show 0 < n by omega) (Real.rpow_pos_of_pos
      (by exact_mod_cast (show 0 < n by omega) : (0 : ℝ) < n) (-p.z))
  exact ht.trans htail

end SKConstants.Completion.N13f
