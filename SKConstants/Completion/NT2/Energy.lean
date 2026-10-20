module

public import SKConstants.Completion.NT2.Rows

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology RealInnerProductSpace

namespace SKConstants.Completion.NT2
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal Blueprint Blueprint4 N13A LGram LC4a LM3

variable {Ω : Type} [MeasurableSpace Ω]

theorem rowH0_upper_zero (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (hn : 0 < n) :
    ∀ i j, i ≤ j → rowH0 W β hβ p n i j = 0 :=
  populationCross_shifted_upper W W β hβ _
    (growingQueryTime_strictMono _ (paperGrowingQueryMeshSize_pos p.a n hn)).monotone _ _

theorem linearEnergy_eq_rowAverage (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (hn : 0 < n) (z : RowArray p n) :
    linearEnergy W β hβ z =
      (∑ i, LM4b.rowLinearEnergy (fun j => rowB W β hβ p n j)
        (fun j => rowS W β hβ p n j) (arrayT z i) (arrayG z i) (arrayX z i)
        (inner (𝕜 := ℝ) (rowS W β hβ p n) (rowB W β hβ p n))) / (n : ℝ) :=
  N13e.empiricalLinearEnergy_eq_rowAverage hn (arrayT z) (arrayG z) (arrayX z)
    (rowS W β hβ p n) (rowB W β hβ p n) (rowH0 W β hβ p n)
    (rowH0_upper_zero W β hβ p n hn)

theorem linearEnergy_eq_zetaAverage (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (hn : 0 < n) (z : RowArray p n) :
    linearEnergy W β hβ z =
      (∑ i, LM4b.rowZeta (fun j => rowB W β hβ p n j / rowS W β hβ p n j)
        (fun j => rowS W β hβ p n j) (arrayT z i) (arrayG z i) (arrayX z i)
        (inner (𝕜 := ℝ) (rowS W β hβ p n) (rowB W β hβ p n))) / (n : ℝ) := by
  apply N13e.empiricalLinearEnergy_eq_zetaAverage hn (arrayT z) (arrayG z) (arrayX z)
    _ (rowS W β hβ p n) (rowB W β hβ p n) _ (rowH0 W β hβ p n)
    (rowH0_upper_zero W β hβ p n hn)
  intro j
  have ht := growingQueryTime_strictMono (coarseMesh p n)
    (paperGrowingQueryMeshSize_pos p.a n hn)
  have hs : rowS W β hβ p n j ≠ 0 := by
    rw [rowS, populationTargetSpin_eq_scale W W β hβ _ ht
      (fun l => growingQueryTime (coarseMesh p n) (l + 1)) (coarseCount p n)
      (coarseTime p n) (ht.monotone (Nat.le_succ (coarseCount p n))) j]
    exact (NNReal.coe_pos.mpr (actualParisiPosteriorIntervalScale_pos W β hβ _ _
      (ht (Nat.lt_succ_self _)))).ne'
  exact (div_mul_cancel₀ _ hs).symm

theorem linearEnergy_eq_historyLinearAverage (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (hn : 0 < n) (z : RowArray p n)
    (a : Fin n → M1.ScalarDriverHistory (coarseTime p n))
    (hz : ∀ i, z i = NDH.historyMixedRow W β (coarseMesh p n) (coarseCount p n) (a i)) :
    linearEnergy W β hβ z =
      (∑ i, N13g.historyLinearRow W β hβ (coarseMesh p n) (coarseCount p n) (a i)) / n := by
  rw [linearEnergy_eq_rowAverage W β hβ p n hn]
  apply congrArg (fun x : ℝ => x / n)
  apply Finset.sum_congr rfl
  intro i _
  have hx : arrayX z i = scalarHiddenSign (a i).1 := by
    simp only [arrayX, hz i, NDH.historyMixedRow, spinIndex,
      WithLp.ofLp_toLp, Fin.append_right]
  dsimp only [N13g.historyLinearRow]
  rw [← hz i, ← hx]
  change LM4b.rowLinearEnergy _ _ _ _ _ _ = LM4b.rowLinearEnergy _ _ _ _ _ _
  rw [N13e.actualCoarseEnergy_eq_population_pairing W W β hβ _
    (growingQueryTime_strictMono _ (paperGrowingQueryMeshSize_pos p.a n hn))]
  rfl

theorem linearEnergy_eq_finiteRowAverage_ae
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (p : Parameters)
    (n : ℕ) (hn : 0 < n) :
    ∀ᵐ y ∂sharpLinkedLaw W β hβ p n,
      linearEnergy W β hβ (sharpRows W β hβ p n y) =
        (∑ i, N13t.finiteHistoryRow W β (coarseTime p n)
          (growingQueryTime (coarseMesh p n)) (coarseCount p n)
          (sharpHistories W β hβ p n y i)) / n := by
  have hδ := paperGrowingQueryMeshSize_pos p.a n hn
  have hp : ∀ᵐ a ∂Measure.pi (fun _ : Fin n =>
      N13t.fullHistoryLinkedLaw W W β hβ (coarseTime p n)), ∀ i,
      N13g.historyLinearRow W β hβ (coarseMesh p n) (coarseCount p n) (a i) =
        N13t.finiteHistoryRow W β (coarseTime p n) (growingQueryTime (coarseMesh p n))
          (coarseCount p n) (a i) := by
    rw [ae_all_iff]
    intro i
    exact (Measure.quasiMeasurePreserving_eval (fun _ : Fin n =>
      N13t.fullHistoryLinkedLaw W W β hβ (coarseTime p n)) i).ae
      (N13g.historyLinearRow_eq_finite_ae W β hβ (coarseMesh p n) hδ (coarseCount p n))
  have hh := ae_of_ae_map (measurable_sharpHistories W β hβ p n).aemeasurable
    ((sharpHistories_linked_hasLaw W β hβ p n hn).map_eq.symm ▸ hp)
  filter_upwards [sharpRows_eq_historyRows_ae W β hβ p n hn, hh] with y hy ha
  rw [linearEnergy_eq_historyLinearAverage W β hβ p n hn _ _ (congrFun hy)]
  exact congrArg (fun x : ℝ => x / n) (Finset.sum_congr rfl (fun i _ => ha i))

end SKConstants.Completion.NT2
