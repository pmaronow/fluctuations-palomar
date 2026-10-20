module

public import SKConstants.Completion.N13t.Node
public import SKConstants.Completion.N13t.Residual
public import SKConstants.Completion.Blueprint.AssemblyFine

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology

namespace SKConstants.Completion.N13t
open SKConstantsOAI.ZeroTemperatureSK LC4a Blueprint Blueprint4

variable {Ω : Type} [MeasurableSpace Ω]

theorem sharpRate_power (a z c : ℝ) (n : ℕ) (hn : 0 < n) :
    c * (n : ℝ) * ((n : ℝ) ^ (-z)) ^ 2 / (meshSize a n : ℝ) =
      c * (n : ℝ) ^ (1 + a - 2 * z) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [paperGrowingQueryMeshSize_coe, ← Real.rpow_natCast _ 2,
    ← Real.rpow_mul hnR.le, div_eq_mul_inv, ← Real.rpow_neg hnR.le, neg_neg]
  calc
    _ = c * ((n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-z * 2) * (n : ℝ) ^ a) := by
      rw [Real.rpow_one]
      ring_nf
    _ = _ := by
      rw [← Real.rpow_add hnR, ← Real.rpow_add hnR]
      exact congrArg (fun e : ℝ => c * (n : ℝ) ^ e) (by ring)

theorem coarseLagMesh_eventually (β : ℝ) (p : Parameters)
    (hf : FineExponents p) (hc : CoarseExponents4 p) :
    ∀ᶠ n : ℕ in atTop, 0 < n ∧
      LagMesh β (meshSize p.a n) (queryCount p.a p.b n) := by
  have ha0 : 0 < p.a := lt_trans hf.2.2.1 hf.2.2.2.1
  have ha1 : p.a < 1 := by linarith [hf.2.1, hc.1, hc.2.1]
  have hlog : ∀ᶠ n : ℕ in atTop,
      (parisiEquilibriumPhysicalEndpoint β : ℝ) ≤ p.b * Real.log (n : ℝ) :=
    (Filter.Tendsto.const_mul_atTop hc.1
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (eventually_ge_atTop _)
  filter_upwards [schedule_eventually p.a p.b hc.1 hc.2.2.1.le ha1, hlog] with n hs htime
  have hn : 0 < n := by omega
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  refine ⟨hn, paperGrowingQueryMeshSize_pos p.a n hn, ?_, ?_, ?_⟩
  · apply NNReal.coe_le_coe.mp
    rw [NNReal.coe_one, paperGrowingQueryMeshSize_coe]
    exact Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith)
  · intro j hj
    apply NNReal.coe_le_coe.mp
    exact (duration_bound p.a p.b hc.1 n hs.1 hs.2.1 j hj).trans
      (Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith [hc.2.2.1]))
  · apply NNReal.coe_le_coe.mp
    exact htime.trans (horizon_bounds p.a p.b hc.1 hc.2.2.1.le n hs.1 hs.2.1).1

theorem susceptibility_log_horizon_bound (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ (b : ℝ) (n : ℕ), 0 < n → ∀ V : ℝ≥0,
      b * Real.log (n : ℝ) ≤ V →
      actualParisiFullSusceptibilityExpected W β V ≤ C * (n : ℝ) ^ (-b / 2) := by
  obtain ⟨C, hC, hmain⟩ := susceptibility_exp_tail W β hβ
  refine ⟨C, hC, ?_⟩
  intro b n hn V hV
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  refine (hmain V V.coe_nonneg).trans (mul_le_mul_of_nonneg_left ?_ hC.le)
  rw [Real.rpow_def_of_pos hnR]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem replaySharpRowConcentration_coarse (hSharp : ReplaySharpRowConcentrationStatement)
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (p : Parameters)
    (hf : FineExponents p) (hc : CoarseExponents4 p) :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      let δ := meshSize p.a n
      let r := rankCount p.a p.b n
      let q := queryCount p.a p.b n
      ReplayFullHistoryLawStatement W β hβ δ r q →
      ∀ (I : GrowingReplaySpace Ω δ r q → ℝ)
        (hδ : 0 < δ), IsGrowingReplayDIntegral W β hβ δ hδ r q (scalarGrowingSourceHorizon δ q) I →
        (growingReplayLinkedLaw W β hβ δ r q (scalarGrowingSourceHorizon δ q)).real
          {u | Real.log 2 - parisiPressure β +
              2 * β ^ 2 * actualParisiFullSusceptibilityExpected W β (scalarGrowingSourceHorizon δ q) +
              C * (n : ℝ) ^ (-p.a) + (n : ℝ) ^ (-p.z) <
            (growingReplayInformation W β hβ δ hδ r q (scalarGrowingSourceHorizon δ q) I u -
              β * ∑ i, finiteHistoryRow W β (scalarGrowingSourceHorizon δ q)
                (growingQueryTime δ) q (replayFullHistories W β hβ δ r q u i)) / (r + q : ℕ)} ≤
          2 * Real.exp (-(c * (n : ℝ) ^ (1 + p.a - 2 * p.z))) := by
  obtain ⟨C, c, hC, hcpos, hmain⟩ := hSharp W β hβ
  refine ⟨C, c, hC, hcpos, ?_⟩
  filter_upwards [coarseLagMesh_eventually β p hf hc] with n hn
  dsimp only
  intro hFull I hδ hI
  have hz0 : 0 < p.z := (common_of_coarseExponents4 hc).2.2.1
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn.1
  have hN : 0 < rankCount p.a p.b n + queryCount p.a p.b n := by
    rw [rankCount_add]
    exact hn.1
  have hb := hmain (meshSize p.a n) hδ (rankCount p.a p.b n) (queryCount p.a p.b n)
    hN hn.2 hFull I hI ((n : ℝ) ^ (-p.z)) (Real.rpow_pos_of_pos hnR _)
    (Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn.1) (by linarith))
  have hrate : c * (rankCount p.a p.b n + queryCount p.a p.b n : ℕ) *
      ((n : ℝ) ^ (-p.z)) ^ 2 / (meshSize p.a n : ℝ) =
      c * (n : ℝ) ^ (1 + p.a - 2 * p.z) := by
    rw [rankCount_add]
    exact sharpRate_power p.a p.z c n hn.1
  rw [hrate] at hb
  simpa only [paperGrowingQueryMeshSize_coe] using hb

theorem replayResidualConcentration_coarse (h3 : JointEndpointIdentityStatement)
    (h7 : GrowingResidualMGFStatement) (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (hf : FineExponents p) (hc : CoarseExponents4 p) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      let δ := meshSize p.a n
      let r := rankCount p.a p.b n
      let q := queryCount p.a p.b n
      ReplayFullHistoryLawStatement W β hβ δ r q →
      ∃ Zv, IsL2Limit (fullHistoryBaseLaw W W β hβ (scalarGrowingSourceHorizon δ q))
          (jointHistoryLeftSum W β (scalarGrowingSourceHorizon δ q)) Zv ∧
        (growingReplayLinkedLaw W β hβ δ r q (scalarGrowingSourceHorizon δ q)).real
          {u | (n : ℝ) ^ (-p.z) ≤ |(∑ i, (residualHistory W β δ q Zv
              (replayFullHistories W β hβ δ r q u i) -
              3 / 2 * (actualParisiEnergyReference W β (scalarGrowingSourceHorizon δ q) -
                LJ.gridEnergy W β (growingQueryTime δ) q))) / (r + q : ℕ)|} ≤
          2 * Real.exp (-(c * (n : ℝ) ^ (1 + p.a - 2 * p.z))) := by
  obtain ⟨c, hcpos, hmain⟩ := replay_growingResidual_concentration h7 W β hβ
  refine ⟨c, hcpos, ?_⟩
  filter_upwards [coarseLagMesh_eventually β p hf hc] with n hn
  dsimp only
  intro hFull
  obtain ⟨Zv, hZv⟩ := jointHistoryIntegral_exists h3 W W β hβ _ hn.2.2.2.2
  refine ⟨Zv, hZv, ?_⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn.1
  have hz0 : 0 < p.z := (common_of_coarseExponents4 hc).2.2.1
  have hN : 0 < rankCount p.a p.b n + queryCount p.a p.b n := by
    rw [rankCount_add]
    exact hn.1
  have hb := hmain (meshSize p.a n) (rankCount p.a p.b n) (queryCount p.a p.b n)
    hN hn.2 hFull Zv hZv ((n : ℝ) ^ (-p.z)) (Real.rpow_pos_of_pos hnR _)
    (Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn.1) (by linarith))
  dsimp only at hb
  have hmean := residualHistory_original_mean h7 W β hβ _ _ hn.2 Zv hZv
  have hrate : c * (rankCount p.a p.b n + queryCount p.a p.b n : ℕ) *
      ((n : ℝ) ^ (-p.z)) ^ 2 / (meshSize p.a n : ℝ) =
      c * (n : ℝ) ^ (1 + p.a - 2 * p.z) := by
    rw [rankCount_add]
    exact sharpRate_power p.a p.z c n hn.1
  rw [hrate] at hb
  simpa only [hmean] using hb

theorem sharpTail_eventually (p : Parameters) (hf : FineExponents p) (hc : CoarseExponents4 p)
    (c M : ℝ) (hcpos : 0 < c) (hM : 0 < M) :
    ∀ᶠ n : ℕ in atTop,
      2 * Real.exp (-(c * (n : ℝ) ^ (1 + p.a - 2 * p.z))) ≤
        Real.exp (-(M * (n : ℝ) ^ (1 - p.sb))) := by
  have hcommon := common_of_coarseExponents4 hc
  have ha0 : 0 < p.a := lt_trans hf.2.2.1 hf.2.2.2.1
  have hgap : 1 - p.sb < 1 + p.a - 2 * p.z := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hz, _, _, _⟩ := hc
    linarith
  have hα : 0 < 1 + p.a - 2 * p.z := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hasb⟩ := hcommon
    linarith
  filter_upwards [constant_rpow_le_small_rpow (1 - p.sb) (1 + p.a - 2 * p.z)
    M (c / 2) hgap hM.le (by positivity),
    constant_rpow_le_small_rpow 0 (1 + p.a - 2 * p.z)
      (Real.log 2) (c / 2) hα (Real.log_nonneg (by norm_num)) (by positivity)] with n hpow hlog
  have hlog' : Real.log 2 ≤ c / 2 * (n : ℝ) ^ (1 + p.a - 2 * p.z) := by simpa using hlog
  have hsum : Real.log 2 + M * (n : ℝ) ^ (1 - p.sb) ≤
      c * (n : ℝ) ^ (1 + p.a - 2 * p.z) :=
    (add_le_add hlog' hpow).trans_eq (by ring)
  calc
    _ = Real.exp (Real.log 2 - c * (n : ℝ) ^ (1 + p.a - 2 * p.z)) := by
      rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2), Real.exp_neg]
      ring
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith only [hsum])

end SKConstants.Completion.N13t
