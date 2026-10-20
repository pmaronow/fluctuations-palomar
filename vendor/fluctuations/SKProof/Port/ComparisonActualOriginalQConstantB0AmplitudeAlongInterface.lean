module

public import SKProof.Port.ComparisonActualOriginalQCavityNumericConsumers

@[expose] public section
noncomputable section
set_option autoImplicit false
open OAI.SKFluctuations.LaplaceWindowFormalization.NativeOverlapMinimum
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization Set Filter
open scoped Topology
def ActualSecondLowOriginalConstantB0AmplitudeBoundOnEveryFinalNetAlong_original_q
    {dim : ℕ → ℕ}
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (Couter : ℝ) (eps : ℕ → ℝ)
    (M : (n:ℕ) → ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ → ℝ) (w : ℕ → ActualSlowWindowChoice) : Prop :=
    ∀ᶠn : ℕ in atTop,∀(L : ℕ) (us : List PositiveMass),
      (∀u∈us,u.val ≤ 1) → (w n).star∈us →
      (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let star:=retainedMassPrefixIndex (w n).star.val as
        let b:=fun j=>((M n).sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>((M n).sweepHf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ → RestCoordinate (dim n) → ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let g:=nativeFreshAtSlot (single (S:=Spin (dim n)×Bool) as) 0 (singleSlot as) star
        ∀(U : ℕ),U ≤ as.length → star < U → partitionPoint 0 as U ≤ Couter*W n →
          |nativeSecondLowJointLedger (dim n) q U b h K g.tree (fun _=>1) [g.embed (singleSlot as),g.mark]/2| ≤
            eps n*W n*(M n).xs^2

end OAI.SKFluctuations.Cavity
