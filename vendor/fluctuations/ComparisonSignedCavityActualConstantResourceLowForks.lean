module

public import ComparisonSignedCavityActualResourceHistories
public import ComparisonSignedCavityTransientForkCost

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type}
set_option maxHeartbeats 14000000

theorem NativePhysicalResourceGenerated.constant_persistentLowForks
    {i star U : ℕ} {as : List PositiveMass} {T : ClockTree S as}
    {seed : List NativeResourceMark} {k : ℕ} {P : NativeResourceTerm i star T}
    (h : NativePhysicalResourceGenerated i star U seed k T P) (hseed : seed=[]) :
    NativePersistentLowForks star star U T := by
  induction h with
  | constant as hU=>exact native_single_persistentLowForks star star U hU
  | seed as hU a mark hm hl=>simp only [List.cons_ne_nil] at hseed
  | freeze h ih=>exact ih hseed
  | reweight h c ih=>exact ih hseed
  | retarget h a ih=>exact (ih hseed).freshStar a _
  | projection h a hl ih=>exact (ih hseed).freshStar a _
  | switch h a c hs hh ih=>exact (ih hseed).freshStar a _
  | switchFreshHigh h a j hjU hj hs ih=>exact ((ih hseed).highRelative a _ hjU).freshStar a _

theorem NativeActualResourceGenerated.constant_persistentLowForks
    {i star U : ℕ} {as : List PositiveMass} {T : ClockTree S as}
    {seed : List NativeResourceMark} {k : ℕ} {P : NativeResourceTerm i star T}
    (h : NativeActualResourceGenerated i star U seed k T P) (hseed : seed=[]) (hs : star<U) :
    NativePersistentLowForks star star U T := by
  induction h with
  | physical h=>exact h.constant_persistentLowForks hseed
  | freeze h ih=>exact ih hseed
  | reweight h c ih=>exact ih hseed
  | retarget h ih=>exact (ih hseed).freshStar 0 _
  | projection h hl ih=>exact (ih hseed).freshStar 0 _
  | markedSwitch h p hp hs' hh ih=>
    have Hmarked:=(ih hseed).observedHigh (le_refl star) hs 0 p hp _
      (by rwa [p.tree.splitIndex_symm])
    exact Hmarked.freshStar 0 _

theorem NativeActualResourceGenerated.constant_low_forkCost_le
    {i star U : ℕ} {as : List PositiveMass} {T : ClockTree S as}
    {k : ℕ} {P : NativeResourceTerm i star T}
    (h : NativeActualResourceGenerated i star U [] k T P) (hs : star<U)
    (f : ℕ→ℝ) (hf : ∀j,0≤f j) (hhigh : ∀j,U≤j→f j=0) :
    T.forkCost f ≤ ((T.leaves:ℝ)-1)*f star := by
  apply native_forkCost_le_pair_bound
  intro s t _
  rcases h.constant_persistentLowForks rfl hs s t with H|H|H
  · rw [H]
  · rw [H]
  · rw [hhigh _ H]
    exact hf star

end OAI.SKFluctuations.Hierarchy.ClockTree
