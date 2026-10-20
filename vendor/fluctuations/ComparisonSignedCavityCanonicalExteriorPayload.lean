module

public import ComparisonSignedCavityActualExteriorPayloadSource
public import ComparisonSignedCavityCanonicalRestMoments

@[expose] public section

noncomputable section
set_option maxHeartbeats 8000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

namespace ActualNaturalBoundaryShape
variable {n a : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}

def restLabels (G : ActualNaturalBoundaryShape n a T) : Fin a×Bool → T.cavityLeft.Slot :=
  fun eb=>T.cavityLeftSlot (if eb.2 then G.j eb.1 else G.i eb.1)

def exteriorProduct (G : ActualNaturalBoundaryShape n a T) (ξ : Fin a×Bool → Spin n) : ℝ :=
  ∏e,fullBoundaryAffineFactor n (G.α e) (G.β e) (ξ (e,true),false) (ξ (e,false),false)

theorem restProduct_eq_exteriorProduct (G : ActualNaturalBoundaryShape n a T)
    (σ : T.cavityLeft.Assignment) :
    G.restProduct σ=G.exteriorProduct (fun j=>T.cavityLeft.atSlot σ (G.restLabels j)) := by
  simp [restProduct,exteriorProduct,restLabels]

end ActualNaturalBoundaryShape

structure NativeCanonicalExteriorSource
    (n a : ℕ) (pre mid tail : List PositiveMass)
    (T : ClockTree (Spin n×Bool) (pre++(mid++tail)))
    (s : T.cavityLeft.Slot) (G : ActualNaturalBoundaryShape n a T)
    (v : RestCoordinate n → ℝ) (q : ℕ → RestCoordinate n → ℝ)
    (x : RestCoordinate n → ℝ) where
  Ei : ClockTree (Spin n) (mid++tail)
  Es : ClockTree (Spin n) tail
  D : ClockTree (Spin n) tail
  read : Ei.Assignment → Es.Assignment → D.Assignment → T.cavityLeft.Assignment
  target : D.Slot
  H : Ei.Assignment → Es.Assignment → ℝ
  target_read : ∀η ζ δ,T.cavityLeft.atSlot (read η ζ δ) s=D.atSlot δ target
  incoming_i : ∀c,T.cavityLeft.splitIndex s c=pre.length → ∃e : Ei.Slot,
    ∀η ζ δ,T.cavityLeft.atSlot (read η ζ δ) c=Ei.atSlot η e
  incoming_star : ∀c,T.cavityLeft.splitIndex s c=pre.length+mid.length → ∃e : Es.Slot,
    ∀η ζ δ,T.cavityLeft.atSlot (read η ζ δ) c=Es.atSlot ζ e
  high : ∀c,pre.length+mid.length < T.cavityLeft.splitIndex s c → ∃d : D.Slot,
    (∀η ζ δ,T.cavityLeft.atSlot (read η ζ δ) c=D.atSlot δ d) ∧
    pre.length+mid.length+D.splitIndex target d=T.cavityLeft.splitIndex s c
  whole_law : ∀Q : T.cavityLeft.Assignment → ℝ,
    T.cavityLeft.disorderExpect (restWeight n) (restFeature n) v q Q x =
      ∫z,nativeExteriorForestConditionalTest Ei Es D (restWeight n) (restFeature n)
        (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+j))
        (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+(mid.length+j)))
        (fun η ζ δ=>Q (read η ζ δ)) (exteriorForestIRoot z) (exteriorForestStarRoot z)
        ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail v q x
  exterior_read : ∀η ζ δ,G.restProduct (read η ζ δ)=H η ζ
  exterior_law : ∀F : ℝ → ℝ,
    T.cavityLeft.disorderExpect (restWeight n) (restFeature n) v q
      (fun σ=>F (G.restProduct σ)) x =
      ∫z,nativeExteriorForestMean Ei Es (restWeight n) (restFeature n)
        (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+j))
        (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+(mid.length+j)))
        (fun η ζ=>F (H η ζ)) (exteriorForestIRoot z) (exteriorForestStarRoot z)
        ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail v q x

theorem native_canonical_exterior_source
    (n a : ℕ) (pre mid tail : List PositiveMass)
    (T : ClockTree (Spin n×Bool) (pre++(mid++tail)))
    (s : T.cavityLeft.Slot) (G : ActualNaturalBoundaryShape n a T)
    (v : RestCoordinate n → ℝ) (q : ℕ → RestCoordinate n → ℝ) (x : RestCoordinate n → ℝ)
    (hsource : NativeClassifiedExteriorPayloadLaw pre mid tail T.cavityLeft s
      (restWeight n) (restFeature n) v q x)
    (hlow : ∀j,T.cavityLeft.splitIndex s (G.restLabels j) ≤ pre.length+mid.length) :
    Nonempty (NativeCanonicalExteriorSource n a pre mid tail T s G v q x) := by
  obtain ⟨Ei,Es,D,read,target,ht,hi,hs,hh,hlaw,hext⟩:=hsource
  obtain ⟨outside,hread,hmoment⟩:=hext (Fin a×Bool) G.restLabels hlow
  refine ⟨⟨Ei,Es,D,read,target,fun η ζ=>G.exteriorProduct (outside η ζ),ht,hi,hs,hh,hlaw,?_,?_⟩⟩
  · intro η ζ δ
    rw [G.restProduct_eq_exteriorProduct]
    congr 1
    funext j
    exact hread η ζ δ j
  · intro F
    simpa only [G.restProduct_eq_exteriorProduct] using hmoment (fun ξ=>F (G.exteriorProduct ξ))

theorem native_actual_generated_canonical_exterior_source
    (n a : ℕ) (pre mid tail : List PositiveMass)
    {T : ClockTree (Spin n×Bool) (pre++(mid++tail))}
    {U k : ℕ} {seed : List NativeResourceMark}
    {P : NativeResourceTerm pre.length (pre.length+mid.length) T}
    (hP : NativeActualResourceGenerated pre.length (pre.length+mid.length) U seed k T P)
    (hmid : 0 < mid.length) (hU : pre.length+mid.length < U)
    (a₀ : ℝ) (p : MarkedPlacement T) (hp : p∈T.markedAttach a₀)
    (c : T.Slot) (hh : U ≤ p.tree.splitIndex p.mark (p.embed c))
    {a₁ : ℝ} (ho : MassOrdered a₁ (pre++(mid++tail)))
    (G : ActualNaturalBoundaryShape n a p.tree)
    (v : RestCoordinate n → ℝ) (q : ℕ → RestCoordinate n → ℝ) (x : RestCoordinate n → ℝ)
    (hlow : ∀j,p.tree.cavityLeft.splitIndex (p.tree.cavityLeftSlot (p.embed c))
      (G.restLabels j) ≤ pre.length+mid.length) :
    Nonempty (NativeCanonicalExteriorSource n a pre mid tail p.tree
      (p.tree.cavityLeftSlot (p.embed c)) G v q x) :=
  native_canonical_exterior_source n a pre mid tail p.tree _ G v q x
    (native_actual_generated_observed_full_rest_exterior_payload n pre mid tail hP
      hmid hU a₀ p hp c hh ho v q x) hlow

end OAI.SKFluctuations.Cavity
