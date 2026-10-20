module

public import ComparisonSignedCavityActualTargetGResponse

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem eventually_actual_minimum_inherited_target_G_thermal_density_along
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (Bclock Temp Cf Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock,
        NativeActualSmallSourceClocks M Temp Cf→M.xs ≤ 1→
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1)→(∀u∈uniformMasses L,u∈us)→((L+1:ℕ):ℝ)⁻¹ ≤ M.xs→
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        ∀(i U : ℕ),i<U→U≤as.length→
        ∀x : ℝ,M.xs ≤ x→partitionPoint 0 as i ≤ Ccut*x→
          let tail:=(∫u in partitionPoint 0 as U..1,
            Real.sqrt (orderedPathB (dim n+1) M.bf M.hf u-(orderedPathS (dim n+1) M.bf M.hf u)^2))+
              3/(dim n+1:ℕ)
          abs (nativeActualTargetLongitudinalResponse M as i U) ≤ C*x*tail ∧
          abs (nativeActualTargetConditionalResponse M as i U) ≤ C*x*tail := by
  obtain ⟨C,hC,H⟩:=eventually_actual_minimum_inherited_target_G_thermal_density
    (D:=D) Bclock Temp Cf Ccut hTemp hCf hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  exact ⟨C,hC,hdim.eventually H⟩

end OAI.SKFluctuations.Cavity
