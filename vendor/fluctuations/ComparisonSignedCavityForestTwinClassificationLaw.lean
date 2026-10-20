module

public import ComparisonSignedCavityForestTwinClassification
public import ComparisonSignedCavityTwinPrefixNativeLaw

@[expose] public section

noncomputable section
set_option maxHeartbeats 8000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]
variable [MeasurableSpace S] [StandardBorelSpace S]

def nativeClassifiedTwinRead {X : Type} (pre mid : List PositiveMass) {tail : List PositiveMass}
    (A : ClockTree S (mid++tail)) (B D : ClockTree S tail)
    (R : A.Assignment → B.Assignment → D.Assignment → X) :
    (nativeTwinForestTree pre mid A B D).Assignment → X :=
  fun σ=>
    let z:=exteriorPrependAssignmentEquiv pre
      (A.fork ((exteriorPrepend mid B).fork (exteriorPrepend mid D))) σ
    R z.1 (exteriorPrependAssignmentEquiv mid B z.2.1)
      (exteriorPrependAssignmentEquiv mid D z.2.2)

theorem native_classified_two_arm_disorder
    (pre mid tail : List PositiveMass) (T : ClockTree S (pre++(mid++tail))) (s b : T.Slot)
    {U : ℕ} (hmid : 0 < mid.length) (hU : pre.length+mid.length<U)
    (hT : NativePersistentLowForks pre.length (pre.length+mid.length) U T)
    (hsb : T.splitIndex s b=pre.length)
    {w : S → ℝ} (hw : ∀σ,0<w σ) (φ : S → (ι → ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a (pre++(mid++tail)))
    (v : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι → ℝ) :
    ∃(A : ClockTree S (mid++tail)) (B D : ClockTree S tail)
      (read : A.Assignment → B.Assignment → D.Assignment → T.Assignment)
      (targetB : B.Slot) (targetD : D.Slot),
      (∀η β δ,T.atSlot (read η β δ) b=B.atSlot β targetB) ∧
      (∀η β δ,T.atSlot (read η β δ) s=D.atSlot δ targetD) ∧
      (∀c,pre.length+mid.length<T.splitIndex s c → ∃d : D.Slot,
        (∀η β δ,T.atSlot (read η β δ) c=D.atSlot δ d) ∧
        pre.length+mid.length+D.splitIndex targetD d=T.splitIndex s c) ∧
      (∀Q : T.Assignment → ℝ,
        T.disorderExpect w φ v q Q x=
          ∫z,nativeTwinForestConditionalTest A B D w φ
            (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+j))
            (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+(mid.length+j)))
            (fun η β δ=>Q (read η β δ))
            (twinPrefixSharedRoot z) (twinPrefixBRoot z) (twinPrefixDRoot z)
            ∂nativeTwinPrefixDisorderRootLaw w φ pre mid tail v q x) := by
  obtain ⟨A,B,D,R,tb,td,htb,htd,hh,hl⟩:=native_two_arm_forest_classification
    pre mid tail T s b hmid hU hT hsb hw φ ho
  refine ⟨A,B,D,R,tb,td,htb,htd,hh,?_⟩
  intro Q
  have HM : T.disorderExpect w φ v q Q x=
      (nativeTwinForestTree pre mid A B D).disorderExpect w φ v q
        (nativeTwinForestRead pre mid A B D (fun η β δ=>Q (R η β δ))) x :=
    native_whole_expect_map_disorder T (nativeTwinForestTree pre mid A B D)
      (nativeClassifiedTwinRead pre mid A B D R) hw φ ho hl v q Q x
  rw [HM]
  exact nativeTwinForest_disorder_law_eq_conditional pre mid A B D hw φ ho v q
    (fun η β δ=>Q (R η β δ)) x

theorem native_classified_two_arm_source_four_tooth
    (pre mid tail : List PositiveMass) (T : ClockTree S (pre++(mid++tail))) (s b : T.Slot)
    {U : ℕ} (hmid : 0 < mid.length) (hU : pre.length+mid.length<U)
    (hT : NativePersistentLowForks pre.length (pre.length+mid.length) U T)
    (hsb : T.splitIndex s b=pre.length)
    {w : S → ℝ} (hw : ∀σ,0<w σ) (φ : S → (ι → ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a (pre++(mid++tail)))
    (v : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι → ℝ) :
    ∃(A : ClockTree S (mid++tail)) (B D : ClockTree S tail)
      (read : A.Assignment → B.Assignment → D.Assignment → T.Assignment)
      (targetB : B.Slot) (targetD : D.Slot),
      (∀η β δ,T.atSlot (read η β δ) b=B.atSlot β targetB) ∧
      (∀η β δ,T.atSlot (read η β δ) s=D.atSlot δ targetD) ∧
      (∀c,pre.length+mid.length<T.splitIndex s c → ∃d : D.Slot,
        (∀η β δ,T.atSlot (read η β δ) c=D.atSlot δ d) ∧
        pre.length+mid.length+D.splitIndex targetD d=T.splitIndex s c) ∧
      (∀Q : T.Assignment → ℝ,
        T.disorderExpect w φ v q Q x=
          ∫z,nativeTwinForestConditionalTest A B D w φ
            (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+j))
            (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+(mid.length+j)))
            (fun η β δ=>Q (read η β δ))
            (twinPrefixSharedRoot z) (twinPrefixBRoot z) (twinPrefixDRoot z)
            ∂nativeTwinPrefixDisorderRootLaw w φ pre mid tail v q x) ∧
      (∀Q : T.Assignment → ℝ,
        (nativeTwinForestTree pre mid (exteriorQuadNative A) (exteriorQuadNative B) D).disorderExpect w φ v q
          (nativeTwinForestRead pre mid (exteriorQuadNative A) (exteriorQuadNative B) D
            (fun η β δ=>Q (read η.1.1 β.1.1 δ)*Q (read η.1.2 β.1.2 δ)*
              Q (read η.2.1 β.2.1 δ)*Q (read η.2.2 β.2.2 δ))) x=
          ∫z,nativeTwinForestAveragedFourth A B D w φ
            (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+j))
            (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+(mid.length+j)))
            (fun η β δ=>Q (read η β δ))
            (twinPrefixSharedRoot z) (twinPrefixBRoot z) (twinPrefixDRoot z)
            ∂nativeTwinPrefixDisorderRootLaw w φ pre mid tail v q x) := by
  obtain ⟨A,B,D,R,tb,td,htb,htd,hh,hl⟩:=native_classified_two_arm_disorder
    pre mid tail T s b hmid hU hT hsb hw φ ho v q x
  refine ⟨A,B,D,R,tb,td,htb,htd,hh,hl,?_⟩
  intro Q
  exact nativeTwinForest_four_tooth_disorder_law pre mid A B D hw φ ho v q
    (fun η β δ=>Q (R η β δ)) x

end OAI.SKFluctuations.Cavity
