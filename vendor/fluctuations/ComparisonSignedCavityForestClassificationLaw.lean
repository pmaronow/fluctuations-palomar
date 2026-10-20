module

public import ComparisonSignedCavityForestClassification

@[expose] public section

noncomputable section
set_option maxHeartbeats 8000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]

theorem native_whole_expect_map_disorder {as : List PositiveMass}
    (T V : ClockTree S as) (read : V.Assignment → T.Assignment)
    {w : S → ℝ} (hw : ∀σ,0<w σ) (φ : S → (ι → ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a as)
    (hLaw : ∀(q : ℕ → ι → ℝ≥0) (Q : T.Assignment → ℝ) (x : ι → ℝ),
      T.expect w φ q Q x=V.expect w φ q (fun σ=>Q (read σ)) x)
    (v : ι → ℝ) (q : ℕ → ι → ℝ) (Q : T.Assignment → ℝ) (x : ι → ℝ) :
    T.disorderExpect w φ v q Q x=V.disorderExpect w φ v q (fun σ=>Q (read σ)) x := by
  rw [T.disorderExpect_integral hw φ ho,V.disorderExpect_integral hw φ ho]
  unfold zeroContinuation
  apply integral_congr_ae
  exact Eventually.of_forall (fun y=>hLaw _ Q (x+y))

end OAI.SKFluctuations.Hierarchy.ClockTree

namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]
variable [MeasurableSpace S] [StandardBorelSpace S]

def nativeClassifiedSourceRead {X : Type} (pre mid : List PositiveMass) {tail : List PositiveMass}
    (Ei : ClockTree S (mid++tail)) (Es D : ClockTree S tail)
    (R : Ei.Assignment → Es.Assignment → D.Assignment → X) :
    (nativeExteriorForestTree pre mid Ei Es D).Assignment → X :=
  fun σ=>
    let z:=exteriorPrependAssignmentEquiv pre (Ei.fork (exteriorPrepend mid (Es.fork D))) σ
    let u:=exteriorPrependAssignmentEquiv mid (Es.fork D) z.2
    R z.1 u.1 u.2

def NativeClassifiedSourceFourToothLaw
    (pre mid tail : List PositiveMass) (T : ClockTree S (pre++(mid++tail))) (s : T.Slot)
    (w : S → ℝ) (φ : S → (ι → ℝ)→L[ℝ]ℝ)
    (v : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι → ℝ) : Prop :=
    ∃(Ei : ClockTree S (mid++tail)) (Es D : ClockTree S tail)
      (read : Ei.Assignment → Es.Assignment → D.Assignment → T.Assignment) (target : D.Slot),
      (∀η ζ σ,T.atSlot (read η ζ σ) s=D.atSlot σ target) ∧
      (∀c,pre.length+mid.length<T.splitIndex s c →
        ∃d : D.Slot,(∀η ζ σ,T.atSlot (read η ζ σ) c=D.atSlot σ d) ∧
          pre.length+mid.length+D.splitIndex target d=T.splitIndex s c) ∧
      (∀Q : T.Assignment → ℝ,
        T.disorderExpect w φ v q Q x=
          ∫z,nativeExteriorForestConditionalTest Ei Es D w φ
            (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+j))
            (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+(mid.length+j)))
            (fun η ζ σ=>Q (read η ζ σ)) (exteriorForestIRoot z) (exteriorForestStarRoot z)
            ∂nativeExteriorForestDisorderRootLaw w φ pre mid tail v q x) ∧
      (∀Q : T.Assignment → ℝ,
        (nativeExteriorForestTree pre mid (exteriorQuadNative Ei) (exteriorQuadNative Es) D).disorderExpect w φ v q
          (nativeExteriorForestRead pre mid (exteriorQuadNative Ei) (exteriorQuadNative Es) D
            (fun η ζ σ=>Q (read η.1.1 ζ.1.1 σ)*Q (read η.1.2 ζ.1.2 σ)*
              Q (read η.2.1 ζ.2.1 σ)*Q (read η.2.2 ζ.2.2 σ))) x=
          ∫z,nativeExteriorForestAveragedFourth Ei Es D w φ
            (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+j))
            (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+(mid.length+j)))
            (fun η ζ σ=>Q (read η ζ σ)) (exteriorForestIRoot z) (exteriorForestStarRoot z)
            ∂nativeExteriorForestDisorderRootLaw w φ pre mid tail v q x)

theorem native_classified_source_and_four_tooth_disorder
    (pre mid tail : List PositiveMass) (T : ClockTree S (pre++(mid++tail))) (s : T.Slot)
    {U : ℕ} (hU : pre.length+mid.length<U)
    (hT : NativePersistentLowForks pre.length (pre.length+mid.length) U T)
    {w : S → ℝ} (hw : ∀σ,0<w σ) (φ : S → (ι → ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a (pre++(mid++tail)))
    (v : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι → ℝ) :
    NativeClassifiedSourceFourToothLaw pre mid tail T s w φ v q x := by
  unfold NativeClassifiedSourceFourToothLaw
  obtain ⟨Ei,Es,D,R,d,ht,hh,hl⟩:=native_two_level_forest_classification_with_high
    pre mid tail T s hU hT hw φ ho
  refine ⟨Ei,Es,D,R,d,ht,hh,?_,?_⟩
  · intro Q
    have HM : T.disorderExpect w φ v q Q x=
        (nativeExteriorForestTree pre mid Ei Es D).disorderExpect w φ v q
          (nativeExteriorForestRead pre mid Ei Es D (fun η ζ σ=>Q (R η ζ σ))) x := by
      exact native_whole_expect_map_disorder T (nativeExteriorForestTree pre mid Ei Es D)
        (nativeClassifiedSourceRead pre mid Ei Es D R) hw φ ho hl v q Q x
    rw [HM]
    exact nativeExteriorForest_disorder_law_eq_conditional pre mid hw φ Ei Es D ho v q _ x
  · intro Q
    exact nativeExteriorForest_four_tooth_disorder_law pre mid hw φ Ei Es D ho v q
      (fun η ζ σ=>Q (R η ζ σ)) x

end OAI.SKFluctuations.Cavity
