module

public import SKConstants.Completion.Blueprint4.NodesAt
public import SKConstants.Completion.N20.Primitive
public import SKConstants.Completion.N20.Schedule

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

namespace SKConstants.Final
open SKConstantsOAI.ZeroTemperatureSK Blueprint Blueprint4

theorem pinningSchedule_eventually (p : Parameters) (hf : FineExponents p)
    (hb0 : 0 < p.b) (hbf : p.b < p.f) :
    ∀ᶠ n : ℕ in atTop, 0 < n ∧ 0 < rankCount p.a p.f n ∧ 0 < meshSize p.a n ∧
      p.b * Real.log (n : ℝ) ≤ (readoutTime p.a p.b n : ℝ) ∧
      readoutTime p.a p.b n ≤ readoutTime p.a p.f n := by
  have hf0 : 0 < p.f := lt_trans hb0 hbf
  have hfa : p.f / 4 ≤ p.a := hf.1.le
  have hba : p.b / 4 ≤ p.a := by linarith
  have ha1 : p.a < 1 := by linarith [hf.2.1]
  have hlog : ∀ᶠ n : ℕ in atTop, 1 ≤ (p.f - p.b) * Real.log (n : ℝ) :=
    (Filter.Tendsto.const_mul_atTop (sub_pos.mpr hbf)
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
      (eventually_ge_atTop 1)
  filter_upwards [schedule_eventually p.a p.b hb0 hba ha1,
    schedule_eventually p.a p.f hf0 hfa ha1, hlog] with n hB hF hgap
  have hbT := horizon_bounds p.a p.b hb0 hba n hB.1 hB.2.1
  have hfT := horizon_bounds p.a p.f hf0 hfa n hF.1 hF.2.1
  have hn : 0 < n := by omega
  refine ⟨hn, hF.2.2, paperGrowingQueryMeshSize_pos p.a n hn, hbT.1, ?_⟩
  apply NNReal.coe_le_coe.mp
  change (scalarGrowingSourceHorizon (meshSize p.a n) (queryCount p.a p.b n) : ℝ) ≤
    (scalarGrowingSourceHorizon (meshSize p.a n) (queryCount p.a p.f n) : ℝ)
  nlinarith

theorem pinningAt_of_replay_nodes
    (hInput : ReplayInputLawStatement) (hLink : ThresholdLinkStatement)
    (hRow : ReplayRowLawStatement) (p : Parameters) (hf : FineExponents p)
    (hb0 : 0 < p.b) (hbf : p.b < p.f) (hr : p.r < p.b / 2) : PinningAt p := by
  intro Ω _ W β hβ
  have hSchedule := pinningSchedule_eventually p hf hb0 hbf
  have hBudget := N20.logarithmic_radius_budget p.b p.r
    (parisiEquilibriumPhysicalEndpoint β : ℝ) hb0 hr
    (readoutTime p.a p.b) (hSchedule.mono (fun _ h => h.2.2.2.1))
  filter_upwards [hSchedule, hBudget] with n hs hB
  let S := readoutTime p.a p.b n
  let v := S - parisiEquilibriumPhysicalEndpoint β
  have hES : parisiEquilibriumPhysicalEndpoint β ≤ S := by
    apply NNReal.coe_le_coe.mp
    dsimp [S]
    linarith [hB.1]
  have hSv : S = parisiEquilibriumPhysicalEndpoint β + v :=
    (add_tsub_cancel_of_le hES).symm
  have hv : 1 ≤ v := by
    apply NNReal.coe_le_coe.mp
    dsimp [v]
    rw [NNReal.coe_sub hES]
    linarith [hB.1]
  have hR : (0 : ℝ) < (hammingRadius p n : ℝ) := by
    exact_mod_cast (Nat.ceil_pos.mpr (Real.rpow_pos_of_pos
      (show (0 : ℝ) < n by exact_mod_cast hs.1) (1 - p.r)))
  have hBv : 64 * (n : ℝ) * Real.exp (-(v : ℝ) / 2) ≤ (hammingRadius p n : ℝ) := by
    simpa only [v, NNReal.coe_sub hES] using hB.2
  have ht := N20.primitive_pinning_radius_tail hInput hLink hRow W β hβ (meshSize p.a n)
    hs.2.2.1 (rankCount p.a p.f n) (queryCount p.a p.f n) hs.2.1
    (rankCount_add p.a p.f n) S v hSv hv hs.2.2.2.2 hs.1 _ hR hBv
  simpa only [N20.primitiveRunLaw, N20.primitiveMean, runLaw, fineAuxLaw, runMag,
    coarseSpin, fineSpin, coarseMag, fineMag, S, M1.Horizon, readoutTime,
    scalarGrowingSourceHorizon, neg_div] using ht

end SKConstants.Final
