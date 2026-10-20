module

public import ComparisonSignedCavityActualMarkedResourceMoments
public import ComparisonSignedCavityActualTerminalGAtom

@[expose] public section

noncomputable section
set_option maxHeartbeats 16000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

def NativeOriginalGMarkedWord.liftResource {n : ℕ} {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (g : NativeOriginalGMarkedWord T)
    {i star : ℕ} (P : NativeResourceTerm i star T) : NativeResourceTerm i star g.tree :=
  ((P.retainOnMarked 0 g.p g.hp).retainOnMarked 0 g.r g.hr).retainOnMarked 0 g.z g.hz

theorem NativeOriginalGMarkedWord.liftResource_coefficient {n : ℕ} {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (g : NativeOriginalGMarkedWord T)
    {i star : ℕ} (P : NativeResourceTerm i star T) :
    (g.liftResource P).coefficient=P.coefficient := rfl

theorem NativeOriginalGMarkedWord.liftResource_frozen {n : ℕ} {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (g : NativeOriginalGMarkedWord T)
    {i star : ℕ} (P : NativeResourceTerm i star T) :
    (g.liftResource P).frozen=P.frozen := rfl

theorem NativeOriginalGMarkedWord.liftResource_resources {n : ℕ} {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (g : NativeOriginalGMarkedWord T)
    {i star : ℕ} (P : NativeResourceTerm i star T) :
    (g.liftResource P).resources=P.resources := by
  exact (((P.retainOnMarked 0 g.p g.hp).retainOnMarked 0 g.r g.hr).retainOnMarked_resources
    0 g.z g.hz).trans (((P.retainOnMarked 0 g.p g.hp).retainOnMarked_resources
      0 g.r g.hr).trans (P.retainOnMarked_resources 0 g.p g.hp))

theorem NativeOriginalGMarkedWord.liftResource_value {n : ℕ} {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (g : NativeOriginalGMarkedWord T)
    {i star : ℕ} (P : NativeResourceTerm i star T)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ)
    (R : (Spin n×Bool)→(Spin n×Bool)→ℝ) (C : ℕ→ℝ) (x₀ : FullCoordinate n→ℝ)
    (σ : g.tree.Assignment) :
    (g.liftResource P).value (fullWeight n) (fullFeature n) v q R C x₀ σ=
      P.value (fullWeight n) (fullFeature n) v q R C x₀
        (g.p.restrict (g.r.restrict (g.z.restrict σ))) := by
  exact (((P.retainOnMarked 0 g.p g.hp).retainOnMarked 0 g.r g.hr).retainOnMarked_value
    0 g.z g.hz (fullWeight n) (fullFeature n) v q R C x₀ σ).trans
      (((P.retainOnMarked 0 g.p g.hp).retainOnMarked_value 0 g.r g.hr
        (fullWeight n) (fullFeature n) v q R C x₀ (g.z.restrict σ)).trans
          (P.retainOnMarked_value 0 g.p g.hp (fullWeight n) (fullFeature n) v q R C x₀
            (g.r.restrict (g.z.restrict σ))))

theorem NativeOriginalGMarkedWord.liftResource_pairMomentBudget
    {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (g : NativeOriginalGMarkedWord T) {i star : ℕ} (P : NativeResourceTerm i star T)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ)
    (R : (Spin n×Bool)→(Spin n×Bool)→ℝ) (C : ℕ→ℝ) (x₀ : FullCoordinate n→ℝ)
    (A x W ε : ℝ)
    (hm : P.PairMomentBudget (fullWeight n) (fullFeature n) v q R C x₀ A x W ε) :
    (g.liftResource P).PairMomentBudget (fullWeight n) (fullFeature n) v q R C x₀ A x W ε := by
  have H1:=P.pairMomentBudget_retainOnMarked 0 g.p g.hp
    (fullWeight n) (fullFeature n) v q R C x₀ A x W ε hm
  have H2:=(P.retainOnMarked 0 g.p g.hp).pairMomentBudget_retainOnMarked 0 g.r g.hr
    (fullWeight n) (fullFeature n) v q R C x₀ A x W ε H1
  exact ((P.retainOnMarked 0 g.p g.hp).retainOnMarked 0 g.r g.hr).pairMomentBudget_retainOnMarked
    0 g.z g.hz (fullWeight n) (fullFeature n) v q R C x₀ A x W ε H2

theorem NativeOriginalGMarkedWord.actual_normalized_resource_pairing_abs_le
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock Temp : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hcl : 0 < cl) (hAz : 0≤Az) (hTemp : 0≤Temp)
    (hb : ∀u,M.b u=Temp) (hh : ∀u,M.h u=0)
    {as : List PositiveMass} {i star U k : ℕ} {seed : List NativeResourceMark}
    {T : ClockTree (Spin n×Bool) as} {P : NativeResourceTerm i star T}
    (g : NativeOriginalGMarkedWord T)
    (hP : NativeActualResourceGenerated i star U seed k T P)
    (ho : MassOrdered 0 as) (a : T.Slot)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x₀ : FullCoordinate n→ℝ)
    (A x W ε : ℝ) (hA : 0<A) (hx : 0<x) (hW : 0<W) (hε : 0<ε)
    (hi : i ≤ star) (hstar : star<as.length)
    (hm : P.PairMomentBudget (fullWeight n) (fullFeature n) v q
      (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
      (nativePhysicalResourceCenter n M.bf M.hf as) x₀ A x W ε) :
    |g.tree.disorderExpect (fullWeight n) (fullFeature n) v q
      (fun σ=>(W⁻¹)^k*((g.liftResource P).value (fullWeight n) (fullFeature n) v q
        (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
        (nativePhysicalResourceCenter n M.bf M.hf as) x₀ σ*g.atom M U a σ)) x₀|≤
      |P.coefficient| *A^(seed.length+k)*nativeResourceScale x W ε seed*ε^k*(2*Temp) := by
  exact hP.normalized_transported_terminal_pairing_abs_le (g.liftResource P)
    (g.liftResource_resources P) (g.liftResource_coefficient P)
    (fullWeight_pos n) (fullFeature n) ho v q
    (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
    (nativePhysicalResourceCenter n M.bf M.hf as) x₀ A x W ε hA hx hW hε hi hstar
    (g.liftResource_pairMomentBudget P v q _ _ x₀ A x W ε hm)
    (g.atom M U a) (2*Temp) (by positivity)
    (g.actual_second_moment_le M hcl hAz hTemp hb hh ho U a v q x₀)

end OAI.SKFluctuations.Cavity
