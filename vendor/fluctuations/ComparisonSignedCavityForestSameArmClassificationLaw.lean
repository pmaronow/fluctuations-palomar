module

public import ComparisonSignedCavityForestSameArmClassification
public import ComparisonSignedCavityForestClassificationLaw

@[expose] public section

noncomputable section
set_option maxHeartbeats 8000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]
variable [MeasurableSpace S] [StandardBorelSpace S]

theorem native_classified_same_arm_source_four_tooth
    (pre mid tail : List PositiveMass) (T : ClockTree S (pre++(mid++tail))) (s b : T.Slot)
    {U : ℕ} (hmid : 0 < mid.length) (hU : pre.length+mid.length<U)
    (hlen : U≤pre.length+mid.length+tail.length)
    (hT : NativePersistentLowForks pre.length (pre.length+mid.length) U T)
    (hsb : T.splitIndex s b=pre.length+mid.length)
    {w : S → ℝ} (hw : ∀σ,0<w σ) (φ : S → (ι → ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a (pre++(mid++tail)))
    (v : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι → ℝ) :
    ∃(Ei : ClockTree S (mid++tail)) (Es D : ClockTree S tail)
      (read : Ei.Assignment → Es.Assignment → D.Assignment → T.Assignment)
      (targetB : Es.Slot) (targetD : D.Slot),
      (∀η β δ,T.atSlot (read η β δ) b=Es.atSlot β targetB) ∧
      (∀η β δ,T.atSlot (read η β δ) s=D.atSlot δ targetD) ∧
      (∀c,pre.length+mid.length<T.splitIndex s c → ∃d : D.Slot,
        (∀η β δ,T.atSlot (read η β δ) c=D.atSlot δ d) ∧
        pre.length+mid.length+D.splitIndex targetD d=T.splitIndex s c) ∧
      (∀Q : T.Assignment → ℝ,
        T.disorderExpect w φ v q Q x=
          ∫z,nativeExteriorForestConditionalTest Ei Es D w φ
            (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+j))
            (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+(mid.length+j)))
            (fun η β δ=>Q (read η β δ))
            (exteriorForestIRoot z) (exteriorForestStarRoot z)
            ∂nativeExteriorForestDisorderRootLaw w φ pre mid tail v q x) ∧
      (∀Q : T.Assignment → ℝ,
        (nativeExteriorForestTree pre mid (exteriorQuadNative Ei) (exteriorQuadNative Es) D).disorderExpect w φ v q
          (nativeExteriorForestRead pre mid (exteriorQuadNative Ei) (exteriorQuadNative Es) D
            (fun η β δ=>Q (read η.1.1 β.1.1 δ)*Q (read η.1.2 β.1.2 δ)*
              Q (read η.2.1 β.2.1 δ)*Q (read η.2.2 β.2.2 δ))) x=
          ∫z,nativeExteriorForestAveragedFourth Ei Es D w φ
            (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+j))
            (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+(mid.length+j)))
            (fun η β δ=>Q (read η β δ))
            (exteriorForestIRoot z) (exteriorForestStarRoot z)
            ∂nativeExteriorForestDisorderRootLaw w φ pre mid tail v q x) := by
  obtain ⟨Ei,Es,D,R,tb,td,htb,htd,hh,hl⟩:=native_same_arm_forest_classification
    pre mid tail T s b hmid hU hlen hT hsb hw φ ho
  refine ⟨Ei,Es,D,R,tb,td,htb,htd,hh,?_,?_⟩
  · intro Q
    have HM : T.disorderExpect w φ v q Q x=
        (nativeExteriorForestTree pre mid Ei Es D).disorderExpect w φ v q
          (nativeExteriorForestRead pre mid Ei Es D (fun η β δ=>Q (R η β δ))) x :=
      native_whole_expect_map_disorder T (nativeExteriorForestTree pre mid Ei Es D)
        (nativeClassifiedSourceRead pre mid Ei Es D R) hw φ ho hl v q Q x
    rw [HM]
    exact nativeExteriorForest_disorder_law_eq_conditional pre mid hw φ Ei Es D ho v q
      (fun η β δ=>Q (R η β δ)) x
  · intro Q
    exact nativeExteriorForest_four_tooth_disorder_law pre mid hw φ Ei Es D ho v q
      (fun η β δ=>Q (R η β δ)) x

end OAI.SKFluctuations.Cavity
