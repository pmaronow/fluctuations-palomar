module

public import ComparisonSignedCavityActualConstantChildLongitudinalRestorationRateAlong
public import ComparisonSignedCavityActualLongitudinalCategorySum
public import ComparisonSignedCavityActualConstantSourceChildrenTerminalAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000

theorem eventually_actual_shell_history_constant_child_longitudinal_category_rate_along
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (depth : ℕ) (Bclock Temp Cf Cmass Ccut cK : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut) (hcK : 0 < cK)
    {m delta cl cu Az C0 Ct D Cs c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs) (hc : 0 < c) (hcouter : 2*cu*(Az+1) ≤ c) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀(M : NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
        (Tbase epsilon shell Ttotal : ℝ) (ts : List ComparisonHistoryTerm),
        NativeActualSmallSourceClocks M Temp Cf →
        (∀u,M.b u=historyMatrixClock Tbase epsilon shell ts u) →
        (∀u,M.h u=historyFieldClock ts u) →
        (∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ Ttotal) →
        M.xs^2 ≤ Cs*laplaceComparisonStrength M.context.d M.lam M.xs →
        M.canonicalDirectTestBandScale ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let W:=M.canonicalDirectTestBandScale
        ∀star U : ℕ,∀(hs : star < U) (hU : U ≤ as.length),
        2*c*W ≤ partitionPoint 0 as U → partitionPoint 0 as U ≤ Ccut*W →
        partitionPoint 0 as star ≤ Cmass*W →
        cK*W ≤ nativeContinuumMixedClock (dim n) M.bf M.hf as star → ∀right : Bool,
        let K:=nativeContinuumMixedClock (dim n) M.bf M.hf as
        let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
        |((nativeActualMinimumFourCenteredForest M hs hU W depth
          (nativeActualConstantSourceChildren M as star U hs hU)).map
          (fun Q=>(W⁻¹)^Q.generation*nativeActualOriginalFourOtherCategoryContrast M U Q
            (nativeActualLongitudinalCategory right))).sum|/(chi*K star) ≤
          C*M.context.N^(-(actualMassSavingExponent m delta/256))*M.xs^2 := by
  obtain ⟨C,hC,H⟩:=eventually_actual_shell_history_constant_child_longitudinal_restoration_forest_rate_along
    dim hdim depth Bclock Temp Cf Cmass Ccut cK hTemp hCf hCmass hCcut hcK
    hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter
  refine ⟨C,hC,?_⟩
  filter_upwards [H] with n hn
  intro M Tbase epsilon shell Ttotal ts HS hb hh htotal hsmall hW1 L us hus hret hmesh
  filter_upwards [hn M Tbase epsilon shell Ttotal ts HS hb hh htotal hsmall hW1 L us hus hret hmesh] with jGrid hj
  dsimp only at hj ⊢
  intro star U hs hU hcutlo hcutup hmassstar hstarK right
  let as:=finiteCutMasses us jGrid
  let W:=M.canonicalDirectTestBandScale
  let children:=nativeActualConstantSourceChildren M as star U hs hU
  have ho:=finiteCutMasses_ordered us hus jGrid
  have hxs1:=M.canonical_direct_test_band_ge_scale.trans hW1
  have Hsum:=actual_longitudinal_category_signed_sum_abs_le_error_sum M hCf HS hxs1 ho hs hU
    M.canonical_direct_test_band_pos hcK hstarK
    (nativeActualMinimumFourCenteredForest M hs hU W depth children) right
  apply Hsum.trans
  have Hforest : nativeActualMinimumFourCenteredForest M hs hU W depth children=
      children.flatMap (fun Q=>nativeActualMinimumFourCenteredForest M hs hU W depth [Q]):=by
    unfold nativeActualMinimumFourCenteredForest
    exact nativeActualFourCenteredForest_eq_flatMap_singletons _ _ _ _ _ _
  rw [Hforest]
  exact hj star U hs hU hcutlo hcutup hmassstar hstarK right

end OAI.SKFluctuations.Cavity
