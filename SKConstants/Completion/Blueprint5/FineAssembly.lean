module

public import SKConstants.Completion.Blueprint5.FineStatements
import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Matrix

namespace SKConstants.Completion.Blueprint5
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal FineInformation LFine N9 LQ M1 LC5 LM5
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem measurable_sourceHistories {Ω : Type*} [MeasurableSpace Ω] (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (r K : ℕ) : Measurable (SourceHistories W β hβ δ r K) := by
  rw [sourceHistories_eq_driverHistories W β hβ δ r K]
  exact (measurable_DriverHistories W β hβ δ (Size r K) K).comp
    (measurable_id.prodMap (measurable_SourceDrivers δ r K))

theorem measurable_fineCellPastB {Ω : Type*} [MeasurableSpace Ω] (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ) (e : Fin K) :
    Measurable (fineCellPastB W β hβ δ hδ r K e) :=
  Measurable.of_eval fun i =>
    (measurable_scalarInitialAuxiliaryRestriction _ _ _).comp
      ((measurable_pi_apply i).comp (measurable_sourceHistories W β hβ δ r K)).snd.snd.fst

theorem measurable_fineCellPastD {Ω : Type*} [MeasurableSpace Ω] (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ) (e : Fin K) :
    Measurable (fineCellPastD W β hβ δ hδ r K e) :=
  Measurable.of_eval fun i =>
    (measurable_scalarInitialAuxiliaryRestriction _ _ _).comp
      ((measurable_pi_apply i).comp (measurable_sourceHistories W β hβ δ r K)).snd.snd.snd

theorem growingSourceQueryEnergy_eq_sum_cells {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (r K : ℕ) :
    growingSourceQueryEnergy W β hβ δ r K = fun z => ∑ e, fineCellQueryEnergy W β hβ δ r K e z :=
  rfl

theorem fineEnergy_of_cells (hI : FineCellIntegrableStatement) (hC : FineCellLowerStatement) :
    Blueprint.FineEnergyStatement := by
  intro Ω _ W β hβ
  obtain ⟨C, hC0, hcell⟩ := hC W β hβ
  refine ⟨fineEnergyQuadratureConstant β + C,
    add_nonneg (fineEnergyQuadratureConstant_nonneg β) hC0, ?_⟩
  intro δ hδ r q hr n h hsmall
  subst h
  have hn : 0 < r+q := by omega
  rw [N9b.replayProposalGen_energy_eq_query W β hβ δ r q hn,
    growingSourceQueryEnergy_eq_sum_cells,
    integral_finsetSum _ (fun e _ => hI W β hβ δ hδ r q hr e)]
  have hN : (0 : ℝ) < ((r+q : ℕ) : ℝ) := by exact_mod_cast hn
  exact fineEnergy_sum_lower_of_cells W β hβ δ hδ q ((r+q : ℕ) : ℝ) hN C hC0
    (fun e => ∫ z, fineCellQueryEnergy W β hβ δ r q e z ∂SourceLinkedLaw W β hβ δ r q)
    hsmall (fun e => hcell δ hδ r q hr hsmall e)

theorem fineCellLower_of_subnodes
    (hT : FineCellFrozenTransportStatement) (hQ : FinePosteriorRestartStatement)
    (hZ : FineMixedEnvelopeStatement) (hR : FineCellRowStatisticsStatement)
    (hY : FineProjectionMomentStatement) : FineCellLowerStatement := by
  intro Ω _ W β hβ
  have hβ0 : 0 ≤ β := by linarith
  refine ⟨((6 : ℝ)+4)*(2*β), by positivity, ?_⟩
  intro δ hδ r K hr hsmall e
  obtain ⟨m, hdim, E, m₀, hEm, hm₀m, hE, hkill, hproj, htarget, hint⟩ :=
    hT W β hβ δ hδ r K hr hsmall e
  obtain ⟨hζm, hind, hmean⟩ := hR W β hβ δ hδ r K hr e
  obtain ⟨hYi, hY2i, hEY, hEY2⟩ := hY W β hβ δ hδ r K hr hsmall e
  have hn : 0 < r+K := by omega
  let μ := SourceLinkedLaw W β hβ δ r K
  let a := growingQueryTime δ (e.val+1)
  let h := growingQueryDuration δ (e.val+1)
  let f := Horizon δ K - growingQueryTime δ (e.val+2)
  let s := actualFineScale W β δ e.val
  let B := fineCellPastB W β hβ δ hδ r K e
  let D := fineCellPastD W β hβ δ hδ r K e
  have hs : 0 < s := actualFineScale_pos W β hβ δ hδ e.val
  have hd : 0 ≤ meshDuration δ e.val := (growingQueryDuration δ e.val).coe_nonneg
  have hh : 0 < h := growingQueryDuration_pos δ hδ _
  have hBm : Measurable B := measurable_fineCellPastB W β hβ δ hδ r K e
  have hDm : Measurable D := measurable_fineCellPastD W β hβ δ hδ r K e
  have key := N9b.fineEnergy_frozenQuery_regular_holds W β hβ μ a h f (r+K) m (e.val+1) hn
    hdim s (meshDuration δ e.val) (2*β) 6
    (actualParisiQueryIntervalSpinMean W β (growingQueryTime δ (e.val+1))
      (growingQueryTime δ (e.val+2)))
    hs hd (by positivity) (by norm_num) E m₀ B D hE hkill hEm hm₀m hBm hDm
    (fun z => hQ W β hβ a h f hh (r+K) (B z) (D z))
  dsimp only at key
  let T := fun z => frozenQueryTarget W β hβ a s (m₀ z) (B z) (D z)
  have hTae (i : Fin (r+K)) : (fun z => SourceTargets W β hβ δ r K z.2 e i) =ᵐ[μ]
      (fun z => T z i) := by
    filter_upwards [htarget] with z hz
    change SourceTargets W β hβ δ r K z.2 e i =
      frozenQueryTarget W β hβ a s (m₀ z) (B z) (D z) i
    exact (hz i).symm
  have hTm (i : Fin (r+K)) : Measurable (fun z => T z i) := by
    change Measurable (fun z => (fixedPastPosterior W β hβ a (B z i) (D z i) - m₀ z i)/s)
    exact ((N9b.measurable_fixedPastPosterior_param W β hβ a (fun z => B z i) (fun z => D z i)
      ((measurable_pi_apply i).comp hBm) ((measurable_pi_apply i).comp hDm)).sub
        ((measurable_pi_apply i).comp hm₀m)).div_const s
  have hYae : (fun z => fineCellRemovedSquare W β hβ δ r K e z) =ᵐ[μ]
      (fun z => N9.queryRemovedSquare ((r+K : ℕ) : ℝ) (E z) (T z)) := by
    filter_upwards [htarget, hproj] with z hz hp
    have hTz : SourceTargets W β hβ δ r K z.2 e = T z := funext fun i => (hz i).symm
    simp only [fineCellRemovedSquare, N9.queryRemovedSquare, hp, hTz]
  have hcast : ((e.val+1 : ℕ) : ℝ) = (e.val : ℝ) + 1 := by push_cast; ring
  have hlow := key
    (fun z i => hZ W β hβ δ hδ r K hr hsmall e z i)
    (fun i => (hζm i).prodMk (hTm i))
    ((iIndepFun_congr (fun i => by
      filter_upwards [hTae i] with z hz
      exact Prod.ext rfl hz)).mp hind)
    (fun i => (N9b.sourceTarget_memLp W β hβ δ hδ r K hn e i 4).ae_eq (hTae i))
    (fun i => by
      rw [← N9b.sourceTarget_second W β hβ δ hδ r K hn e i]
      exact integral_congr_ae (by filter_upwards [hTae i] with z hz; rw [hz]))
    (fun i => by
      refine le_of_eq_of_le ?_ (N9b.sourceTarget_fourth_le W β hβ δ hδ r K hn e i)
      exact integral_congr_ae (by filter_upwards [hTae i] with z hz; rw [hz]))
    hmean
    (hYi.congr hYae)
    (hY2i.congr (hYae.fun_comp (fun x : ℝ => x^2)))
    (by
      refine le_of_eq_of_le (integral_congr_ae hYae).symm ?_
      exact hEY)
    (by
      refine le_of_eq_of_le (integral_congr_ae (hYae.fun_comp (fun x : ℝ => x^2))).symm ?_
      exact hEY2)
  rw [hint]
  rw [hcast] at hlow
  exact hlow

theorem fineEnergy_of_subnodes (hI : FineCellIntegrableStatement)
    (hT : FineCellFrozenTransportStatement) (hQ : FinePosteriorRestartStatement)
    (hZ : FineMixedEnvelopeStatement) (hR : FineCellRowStatisticsStatement)
    (hY : FineProjectionMomentStatement) : Blueprint.FineEnergyStatement :=
  fineEnergy_of_cells hI (fineCellLower_of_subnodes hT hQ hZ hR hY)

end SKConstants.Completion.Blueprint5
