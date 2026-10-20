module

public import ComparisonSignedCavityScalarNativeRemainder

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 12000000

private theorem actual_scalar_cut_split
    (as : List PositiveMass) (U : ℕ) (hpos : 0 < U) (hlen : U ≤ as.length) :
    ∃(before after : List PositiveMass) (a : PositiveMass),
      as=before++a::after ∧ before.length+1=U := by
  induction as generalizing U with
  | nil => simp only [List.length_nil] at hlen;omega
  | cons b as ih =>
    cases U with
    | zero => omega
    | succ U =>
      cases U with
      | zero => exact ⟨[],as,b,rfl,rfl⟩
      | succ V =>
        obtain ⟨before,after,a,Hsplit,Hlen⟩:=ih (V+1) (by omega) (by simpa using hlen)
        refine ⟨b::before,after,a,?_,?_⟩
        · simp only [List.cons_append];rw [Hsplit]
        · simp only [List.length_cons];omega

 theorem actual_general_scalar_pair_low_remainder_of_buffer_cut
    {T W A R Ru : ℝ} (hT : 0 < T)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (q : ℕ→ℝ) (hq : Monotone q)
    (hq0 : q 0=0) (htotal : q as.length=T)
    (hW : 0 ≤ W) (hA : 0 ≤ A) (hR : 0 ≤ R) (hRu : 0 ≤ Ru)
    (j U V : ℕ) (hj : j < U) (hUV : U ≤ V) (hV : V ≤ as.length)
    (hgap : q U < q V) (hsize : partitionPoint 0 as V ≤ A*W)
    (hjclock : q j ≤ R*W) (hUclock : q U ≤ Ru*W) (hsmall : q j ≤ 1) :
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 q))).H 0 0
    |nativeOriginalScalarPairMean as q j-chi^2*q j| ≤ nativeScalarLowRemainderConstant A R Ru*W^3 := by
  obtain ⟨before,after,a,Hsplit,Hlen⟩:=actual_scalar_cut_split as U (by omega) (hUV.trans hV)
  subst as
  have H:=native_scalar_pair_low_remainder_uniform_of_buffer hT before after a ho q hq hq0 htotal
    hW hA hR hRu j V (by omega) (by omega) hV (by simpa only [Hlen] using hgap)
    hsize hjclock (by simpa only [Hlen] using hUclock) hsmall
  simpa only [Hlen] using H

end OAI.SKFluctuations.Cavity
