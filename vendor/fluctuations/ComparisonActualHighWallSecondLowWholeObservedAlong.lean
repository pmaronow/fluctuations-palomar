module

public import ComparisonActualHighWallSecondLowWholeObservedSavedRate

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open MeasureTheory ProbabilityTheory Filter Set Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 18000000

theorem eventually_actual_high_wall_second_low_whole_observed_saved_rate_along
    (degree rBound : ℕ) (Bclock Cmass : ℝ)
    (hCmass : 0 ≤ Cmass)
    {m delta eta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop) :
    ∃C : ℝ,0<C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock,
        M.xs=M.data.d →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim
          (fun _=>(M.bf (partitionPoint 0 as j):ℝ)) (fun _=>(M.hf (partitionPoint 0 as j):ℝ))
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let K:=nativeContinuumMixedClock (dim n) M.bf M.hf as
        let W:=M.data.d
        ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
          partitionPoint 0 as (pre.length+mid.length) ≤ Cmass*W →
        ∀(T : ClockTree (Spin (dim n)×Bool) (pre++(mid++tail))) (s : T.Slot) (U : ℕ)
          (hU : U ≤ (pre++(mid++tail)).length),0 < mid.length → pre.length+mid.length<U →
          T.leaves ≤ rBound → NativePersistentLowForks pre.length (pre.length+mid.length) U T →
          W ≤ M.data.wallRadius M.alpha (partitionPoint 0 as U) →
          M.data.wallRadius M.alpha (partitionPoint 0 as (pre.length+mid.length)) ≤ M.data.wallRadius M.alpha (partitionPoint 0 as U)/2 →
          M.z ≤ M.data.wallRadius M.alpha (partitionPoint 0 as U)/2 →
        ∀(G : ActualNaturalBoundaryShape (dim n) degree T) (forms : Fin degree→NativeSourceFactorForm)
          (initial : Finset (Fin degree)) (x : ℝ),M.xs ≤ x → x ≤ W →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x W initial e) →
          let g:=nativeFreshAtSlot T 0 s (pre.length+mid.length)
          let P:=(G.canonicalHighWallSource M forms).restProduct
          let Pg:=fun old=>P (g.restRestrict old)
          let χ:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
          |(∑j : Fin 8,nativeSecondLowClassLedger (dim n) q U b h K g.tree hU Pg (g.embed s) g.mark j true/2)-
            χ^2*nativeSecondLowFreshOccupiedUnweightedCSource (dim n) q U b h K T s (pre.length+mid.length) hU P| ≤ 
            C*(dim n:ℝ)^(-eta)*(W*M.xs^2*sourceMonomialScale x W initial) := by
  obtain ⟨C,hC,H⟩:=eventually_actual_high_wall_second_low_whole_observed_saved_rate
    (D:=D) degree rBound Bclock Cmass hCmass hm hdelta hroom hgap hcl hcu hAz hC0 hCt
  exact ⟨C,hC,hdim.eventually H⟩

end OAI.SKFluctuations.Cavity
