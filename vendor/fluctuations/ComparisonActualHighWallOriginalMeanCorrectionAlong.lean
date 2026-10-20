module

public import ComparisonActualHighWallOriginalMeanCorrection

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open scoped BigOperators Topology NNReal

theorem eventually_actual_high_wall_original_longitudinal_mean_quartic_price_along
    (r : ℕ) (Bclock : ℝ) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hC0 : 0 < C0) (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock,
      M.xs=M.data.d →
      ∀us : List PositiveMass,(∀u∈us,u.val ≤ 1) → ∀ᶠk in atTop,
        let as:=finiteCutMasses us k
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        ∀(K : ℕ → ℝ) (T : ClockTree (Spin (dim n)×Bool) as) (U : ℕ) (a : T.Slot),
          T.leaves ≤ r →
          |nativeOriginalLongitudinalMean T U K b h
            (nativePhysicalResourceCenter (dim n) M.bf M.hf as) a| ≤ C*M.data.d^4 := by
  obtain ⟨C,hC,H⟩:=eventually_actual_high_wall_original_longitudinal_mean_quartic_price
    (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D) r Bclock hm hC0
  exact ⟨C,hC,hdim.eventually H⟩

theorem eventually_actual_high_wall_original_mean_correction_cubic_price_along
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hC0 : 0 < C0) (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock,
      M.xs=M.data.d →
      ∀us : List PositiveMass,(∀u∈us,u.val ≤ 1) → ∀ᶠk in atTop,
        let as:=finiteCutMasses us k
        ∀i U : ℕ,i < U → U ≤ as.length →
          |actualGeneralTargetOriginalMeanCorrection (n:=dim n) M.bf M.hf as i U| ≤ C*M.data.d^3 := by
  obtain ⟨C,hC,H⟩:=eventually_actual_high_wall_original_mean_correction_cubic_price
    (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D) Bclock hm hC0
  exact ⟨C,hC,hdim.eventually H⟩

end OAI.SKFluctuations.Cavity
