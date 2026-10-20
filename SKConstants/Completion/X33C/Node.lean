module

public import SKConstants.Completion.X33C.PostLikelihood
public import SKConstants.Completion.X33C.JoinedPartitions

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace SKConstants.Completion.X33C
open SKConstantsOAI.ZeroTemperatureSK Blueprint4
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
local instance node_W_probability (W : BrownianSystem Ω) : IsProbabilityMeasure W.law := W.isProbability
local instance node_Z_probability (Z : BrownianSystem A) : IsProbabilityMeasure Z.law := Z.isProbability
attribute [local irreducible] actualParisiFullScalarDrift actualParisiFullMagnetization

theorem postOriginalSum_certified_tendstoInMeasure
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β) (T : ℝ≥0)
    {Q Qs J : (Bool × Ω) × A → ℝ}
    (hQ : SJ3.IsQueryRowIntegral W Z β hβ (parisiEquilibriumPhysicalEndpoint β + T) Q)
    (hQs : SJ3.IsQueryRowIntegral W Z β hβ (parisiEquilibriumPhysicalEndpoint β) Qs)
    (hJ : LM4b.IsActualRowDIntegral W Z β hβ (parisiEquilibriumPhysicalEndpoint β + T) J) :
    TendstoInMeasure (LM4.actualRowBaseLaw W Z) (postOriginalSum W β T) atTop
      (fun u => β * (Q u - Qs u) + J u) := by
  let S := parisiEquilibriumPhysicalEndpoint β
  let F := fun l => originalPartitionSum (A := A) W β (joinedDyadicTime S T l) (2 ^ l + 2 ^ l)
  have hD (l : ℕ) : MemLp (S33aA.originalRowLeftSum (A := A) W β (S + T) l) 2
      (LM4.actualRowBaseLaw W Z) := by
    change MemLp (originalPartitionSum W β ((brownianDyadicGrid (S + T)).time l) (2 ^ l)) 2
      (LM4.actualRowBaseLaw W Z)
    exact originalPartitionSum_memLp W Z β ((brownianDyadicGrid (S + T)).time l)
      ((brownianDyadicGrid (S + T)).monotone l) (2 ^ l)
  have hF (l : ℕ) : MemLp (F l) 2 (LM4.actualRowBaseLaw W Z) := by
    dsimp only [F]
    exact originalPartitionSum_memLp W Z β (joinedDyadicTime S T l)
      (joinedDyadicTime_monotone S T l) (2 ^ l + 2 ^ l)
  have hi (l : ℕ) : Integrable
      (fun u => (F l u - S33aA.originalRowLeftSum W β (S + T) l u) ^ 2)
        (LM4.actualRowBaseLaw W Z) :=
    ((hF l).sub (hD l)).integrable_sq
  have hc : TendstoInMeasure (LM4.actualRowBaseLaw W Z)
      (fun l u => F l u - S33aA.originalRowLeftSum W β (S + T) l u) atTop (fun _ => 0) :=
    tendstoInMeasure_of_tendsto_integral_sq
      (by simpa only [sub_zero] using hi)
      (by simpa only [sub_zero] using joinedOriginalSum_comparison_tendsto W Z β S T)
  have hf : TendstoInMeasure (LM4.actualRowBaseLaw W Z) F atTop (fun u => β * Q u + J u) := by
    have h := inMeasure_add hc (originalRowLeftSum_tendstoInMeasure W Z β hβ (S + T) hQ hJ)
    simpa only [sub_add_cancel, zero_add] using h
  have hs := originalRowLeftSum_tendstoInMeasure W Z β hβ S hQs
    (SJ3.rowDIntegral_zero_pre W Z β hβ S le_rfl)
  have h := inMeasure_sub hf hs
  apply h.congr (fun l => ae_of_all _ (fun u => ?_)) (ae_of_all _ (fun u => ?_))
  · have he := joinedPartitionSum_split
      (fun t => scalarHiddenSign u.1.1 - actualParisiFullPosteriorMean W β t u.1.2)
      (fun t => W.B t u.1.2) S T l
    change F l u - S33aA.originalRowLeftSum W β S l u = postOriginalSum W β T l u
    change F l u = S33aA.originalRowLeftSum W β S l u + postOriginalSum W β T l u at he
    linarith only [he]
  · ring

theorem postSupportInformationIto_holds : Blueprint5a.PostSupportInformationItoStatement := by
  intro Ω A _ _ W Z β hβ V hV J Q Qs hJ hQ hQs
  let S := parisiEquilibriumPhysicalEndpoint β
  let T := V - S
  have hST : S + T = V := add_tsub_cancel_of_le hV
  have hQ' : SJ3.IsQueryRowIntegral W Z β hβ (S + T) Q := by simpa only [hST] using hQ
  have hJ' : LM4b.IsActualRowDIntegral W Z β hβ (S + T) J := by simpa only [hST] using hJ
  have hid := tendstoInMeasure_ae_unique
    (postOriginalSum_certified_tendstoInMeasure W Z β hβ T hQ' hQs hJ')
    (postOriginalSum_likelihood_tendstoInMeasure W Z β hβ T)
  have hbr := S33aA.rowBracket_cancel_ae W Z β hβ V hV
  filter_upwards [hid, hbr] with u hu hb
  change β * (Q u - Qs u) + J u =
    (Real.log (actualParisiFullTerminalSpinDensity β W (S + T) u.1) -
      Real.log (actualParisiFullTerminalSpinDensity β W S u.1)) +
    (∫ t in (S : ℝ)..(S + T : ℝ≥0), actualParisiPinningError W β t.toNNReal u.1) / 2 at hu
  rw [hST] at hu
  change (Real.log (actualParisiFullTerminalSpinDensity β W V u.1) - J u +
      LM4b.actualRowDBracket W β V u / 2) -
      Real.log (actualParisiFullTerminalSpinDensity β W S u.1) - β * (Q u - Qs u) = _
  linarith only [hu, hb]

end SKConstants.Completion.X33C
