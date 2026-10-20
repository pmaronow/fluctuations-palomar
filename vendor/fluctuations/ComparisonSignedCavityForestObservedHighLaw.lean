module

public import ComparisonSignedCavityForestObservedHighGeometry

@[expose] public section

noncomputable section
set_option maxHeartbeats 8000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree
variable {ι S B : Type} [Fintype ι] [Fintype S] [Nonempty S]
variable [MeasurableSpace S] [StandardBorelSpace S]

def NativeObservedClassifiedFourToothLaw
    (pre mid tail : List PositiveMass) (T : ClockTree (S×B) (pre++(mid++tail)))
    (c : T.Slot) (p : MarkedPlacement T)
    (w : S → ℝ) (φ : S → (ι → ℝ)→L[ℝ]ℝ)
    (v : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι → ℝ) : Prop :=
    ∃(Ei : ClockTree S (mid++tail)) (Es D : ClockTree S tail)
      (read : Ei.Assignment → Es.Assignment → D.Assignment → p.tree.cavityLeft.Assignment)
      (old new : D.Slot),
      (∀η ζ σ,T.cavityLeft.atSlot (p.restRestrict (read η ζ σ)) (T.cavityLeftSlot c)=D.atSlot σ old) ∧
      (∀η ζ σ,p.restSpin (read η ζ σ)=D.atSlot σ new) ∧
      (pre.length+mid.length+D.splitIndex old new=p.tree.splitIndex (p.embed c) p.mark) ∧
      (∀Q : p.tree.cavityLeft.Assignment → ℝ,
        p.tree.cavityLeft.disorderExpect w φ v q Q x=
          ∫z,nativeExteriorForestConditionalTest Ei Es D w φ
            (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+j))
            (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+(mid.length+j)))
            (fun η ζ σ=>Q (read η ζ σ)) (exteriorForestIRoot z) (exteriorForestStarRoot z)
            ∂nativeExteriorForestDisorderRootLaw w φ pre mid tail v q x) ∧
      (∀Q : p.tree.cavityLeft.Assignment → ℝ,
        (nativeExteriorForestTree pre mid (exteriorQuadNative Ei) (exteriorQuadNative Es) D).disorderExpect w φ v q
          (nativeExteriorForestRead pre mid (exteriorQuadNative Ei) (exteriorQuadNative Es) D
            (fun η ζ σ=>Q (read η.1.1 ζ.1.1 σ)*Q (read η.1.2 ζ.1.2 σ)*
              Q (read η.2.1 ζ.2.1 σ)*Q (read η.2.2 ζ.2.2 σ))) x=
          ∫z,nativeExteriorForestAveragedFourth Ei Es D w φ
            (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+j))
            (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+(mid.length+j)))
            (fun η ζ σ=>Q (read η ζ σ)) (exteriorForestIRoot z) (exteriorForestStarRoot z)
            ∂nativeExteriorForestDisorderRootLaw w φ pre mid tail v q x)

theorem native_physical_generated_observed_high_four_tooth
    (pre mid tail : List PositiveMass) {T : ClockTree (S×B) (pre++(mid++tail))}
    {U k : ℕ} {seed : List NativeResourceMark}
    {P : NativeResourceTerm pre.length (pre.length+mid.length) T}
    (hP : NativePhysicalResourceGenerated pre.length (pre.length+mid.length) U seed k T P)
    (hU : pre.length+mid.length<U)
    (a : ℝ) (p : MarkedPlacement T) (hp : p∈T.markedAttach a)
    (c : T.Slot) (hh : U≤p.tree.splitIndex p.mark (p.embed c))
    {w : S → ℝ} (hw : ∀σ,0<w σ) (φ : S → (ι → ℝ)→L[ℝ]ℝ)
    {a₀ : ℝ} (ho : MassOrdered a₀ (pre++(mid++tail)))
    (v : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι → ℝ) :
    NativeObservedClassifiedFourToothLaw pre mid tail T c p w φ v q x := by
  have hSource:=hP.persistentLowForks.observedRestHigh (by omega) hU a p hp c hh
  let old:=p.tree.cavityLeftSlot (p.embed c)
  let new:=p.tree.cavityLeftSlot p.mark
  have hs : pre.length+mid.length<p.tree.cavityLeft.splitIndex old new := by
    dsimp only [old,new]
    rw [cavityLeft_splitIndex,splitIndex_symm]
    omega
  obtain ⟨Ei,Es,D,R,d,ht,hhD,hfirst,hfour⟩:=native_classified_source_and_four_tooth_disorder
    pre mid tail p.tree.cavityLeft old hU hSource hw φ ho v q x
  obtain ⟨f,hf,hsplit⟩:=hhD new hs
  refine ⟨Ei,Es,D,R,d,f,?_,?_,?_,hfirst,hfour⟩
  · intro η ζ σ
    rw [p.restRestrict_at]
    exact ht η ζ σ
  · intro η ζ σ
    exact hf η ζ σ
  · simpa only [old,new,cavityLeft_splitIndex] using hsplit

end OAI.SKFluctuations.Cavity
