module

public import ComparisonSignedCavityTwoLevelExteriorRead
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

omit [Fintype S] [MeasurableSpace S] [StandardBorelSpace S] in
private theorem exterior_payload_assignment_nonempty {as : List PositiveMass}
    (D : ClockTree S as) : Nonempty D.Assignment := by
  induction D with
  | leaf=>exact inferInstance
  | step b D ih=>exact ih
  | fork D E ihD ihE=>exact ⟨(Classical.choice ihD,Classical.choice ihE)⟩

theorem native_two_level_exterior_read_independent
    (pre mid tail : List PositiveMass) (T : ClockTree S (pre++(mid++tail))) (s : T.Slot)
    {U : ℕ} (hU : pre.length+mid.length < U)
    (hT : NativePersistentLowForks pre.length (pre.length+mid.length) U T)
    (Ei : ClockTree S (mid++tail)) (Es D : ClockTree S tail)
    (read : Ei.Assignment → Es.Assignment → D.Assignment → T.Assignment)
    (hi : ∀c,T.splitIndex s c=pre.length → ∃e : Ei.Slot,
      ∀η ζ δ,T.atSlot (read η ζ δ) c=Ei.atSlot η e)
    (hs : ∀c,T.splitIndex s c=pre.length+mid.length → ∃e : Es.Slot,
      ∀η ζ δ,T.atSlot (read η ζ δ) c=Es.atSlot ζ e)
    {J : Type} (labels : J → T.Slot)
    (hlow : ∀j,T.splitIndex s (labels j) ≤ pre.length+mid.length) :
    ∃ outside : Ei.Assignment → Es.Assignment → J → S,
      ∀η ζ δ j,T.atSlot (read η ζ δ) (labels j)=outside η ζ j := by
  classical
  have hD := exterior_payload_assignment_nonempty D
  let δ₀ : D.Assignment := Classical.choice hD
  refine ⟨fun η ζ j=>T.atSlot (read η ζ δ₀) (labels j),?_⟩
  intro η ζ δ j
  rcases hT s (labels j) with hi'|hs'|hh'
  · obtain ⟨e,he⟩:=hi (labels j) hi'
    exact (he η ζ δ).trans (he η ζ δ₀).symm
  · obtain ⟨e,he⟩:=hs (labels j) hs'
    exact (he η ζ δ).trans (he η ζ δ₀).symm
  · have h:=hlow j
    omega

def NativeClassifiedExteriorPayloadLaw
    (pre mid tail : List PositiveMass) (T : ClockTree S (pre++(mid++tail))) (s : T.Slot)
    (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (v : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι → ℝ) : Prop :=
    ∃(Ei : ClockTree S (mid++tail)) (Es D : ClockTree S tail)
      (read : Ei.Assignment → Es.Assignment → D.Assignment → T.Assignment) (target : D.Slot),
      (∀η ζ δ,T.atSlot (read η ζ δ) s=D.atSlot δ target) ∧
      (∀c,T.splitIndex s c=pre.length → ∃e : Ei.Slot,
        ∀η ζ δ,T.atSlot (read η ζ δ) c=Ei.atSlot η e) ∧
      (∀c,T.splitIndex s c=pre.length+mid.length → ∃e : Es.Slot,
        ∀η ζ δ,T.atSlot (read η ζ δ) c=Es.atSlot ζ e) ∧
      (∀c,pre.length+mid.length < T.splitIndex s c → ∃d : D.Slot,
        (∀η ζ δ,T.atSlot (read η ζ δ) c=D.atSlot δ d) ∧
        pre.length+mid.length+D.splitIndex target d=T.splitIndex s c) ∧
      (∀Q : T.Assignment → ℝ,T.disorderExpect w φ v q Q x =
        ∫z,nativeExteriorForestConditionalTest Ei Es D w φ
          (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+j))
          (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+(mid.length+j)))
          (fun η ζ δ=>Q (read η ζ δ)) (exteriorForestIRoot z) (exteriorForestStarRoot z)
          ∂nativeExteriorForestDisorderRootLaw w φ pre mid tail v q x) ∧
      (∀(J : Type) (labels : J → T.Slot),
        (∀j,T.splitIndex s (labels j) ≤ pre.length+mid.length) →
        ∃ outside : Ei.Assignment → Es.Assignment → J → S,
          (∀η ζ δ j,T.atSlot (read η ζ δ) (labels j)=outside η ζ j) ∧
          (∀F : (J → S) → ℝ,
            T.disorderExpect w φ v q (fun σ=>F (fun j=>T.atSlot σ (labels j))) x =
              ∫z,nativeExteriorForestMean Ei Es w φ
                (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+j))
                (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+(mid.length+j)))
                (fun η ζ=>F (outside η ζ)) (exteriorForestIRoot z) (exteriorForestStarRoot z)
                ∂nativeExteriorForestDisorderRootLaw w φ pre mid tail v q x))

theorem native_classified_source_exterior_payload
    (pre mid tail : List PositiveMass) (T : ClockTree S (pre++(mid++tail))) (s : T.Slot)
    {U : ℕ} (hmid : 0 < mid.length) (hU : pre.length+mid.length < U)
    (hlen : U ≤ pre.length+mid.length+tail.length)
    (hT : NativePersistentLowForks pre.length (pre.length+mid.length) U T)
    {w : S → ℝ} (hw : ∀σ,0 < w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {a : ℝ} (ho : MassOrdered a (pre++(mid++tail)))
    (v : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι → ℝ) :
    NativeClassifiedExteriorPayloadLaw pre mid tail T s w φ v q x := by
  unfold NativeClassifiedExteriorPayloadLaw
  obtain ⟨Ei,Es,D,R,d,ht,hi,hs,hh,hl⟩:=native_two_level_forest_classification_with_exterior
    pre mid tail T s hmid hU hlen hT hw φ ho
  have hLaw (Q : T.Assignment → ℝ) : T.disorderExpect w φ v q Q x =
      ∫z,nativeExteriorForestConditionalTest Ei Es D w φ
        (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+j))
        (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+(mid.length+j)))
        (fun η ζ δ=>Q (R η ζ δ)) (exteriorForestIRoot z) (exteriorForestStarRoot z)
        ∂nativeExteriorForestDisorderRootLaw w φ pre mid tail v q x := by
    have HM : T.disorderExpect w φ v q Q x =
        (nativeExteriorForestTree pre mid Ei Es D).disorderExpect w φ v q
          (nativeExteriorForestRead pre mid Ei Es D (fun η ζ δ=>Q (R η ζ δ))) x :=
      native_whole_expect_map_disorder T (nativeExteriorForestTree pre mid Ei Es D)
        (nativeClassifiedSourceRead pre mid Ei Es D R) hw φ ho hl v q Q x
    rw [HM]
    exact nativeExteriorForest_disorder_law_eq_conditional pre mid hw φ Ei Es D ho v q _ x
  refine ⟨Ei,Es,D,R,d,ht,hi,hs,hh,hLaw,?_⟩
  intro J labels hlow
  obtain ⟨outside,hread⟩:=native_two_level_exterior_read_independent pre mid tail T s hU hT
    Ei Es D R hi hs labels hlow
  refine ⟨outside,hread,?_⟩
  intro F
  rw [hLaw]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro z
  have he : (fun η ζ δ=>F (fun j=>T.atSlot (R η ζ δ) (labels j))) =
      fun η ζ (_ : D.Assignment)=>F (outside η ζ) := by
    funext η ζ δ
    congr 1
    funext j
    exact hread η ζ δ j
  rw [he]
  unfold nativeExteriorForestConditionalTest
  exact D.expect_const hw φ ho.suffix_end.suffix_end _ _ _

end OAI.SKFluctuations.Cavity
