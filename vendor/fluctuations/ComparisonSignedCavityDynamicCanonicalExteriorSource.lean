module

public import ComparisonSignedCavityStarFieldJointClassification
public import ComparisonSignedCavityCanonicalExteriorPayload

@[expose] public section

noncomputable section
set_option maxHeartbeats 16000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree

structure NativeDynamicCanonicalExteriorSource
    (n a : ℕ) (pre mid tail : List PositiveMass)
    (T : ClockTree (Spin n×Bool) (pre++(mid++tail)))
    (s : T.cavityLeft.Slot) (G : ActualNaturalBoundaryShape n a T)
    (v : RestCoordinate n→ℝ) (q : ℕ→RestCoordinate n→ℝ) (x : RestCoordinate n→ℝ)
    extends NativeCanonicalExteriorSource n a pre mid tail T s G v q x where
  star_field_law : ∀J : (RestCoordinate n→ℝ)→T.cavityLeft.Assignment→ℝ,
    (∀σ,BddSmooth 0 (fun y=>J y σ)) →
    nativeStarFieldDisorderMean (restWeight n) (restFeature n) T.cavityLeft s
      (pre.length+mid.length) v q J x=
      ∫z,nativeExteriorForestConditionalTest Ei Es D (restWeight n) (restFeature n)
        (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+j))
        (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+(mid.length+j)))
        (fun η ζ δ=>J (exteriorForestStarRoot z) (read η ζ δ))
        (exteriorForestIRoot z) (exteriorForestStarRoot z)
        ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail v q x

theorem native_dynamic_canonical_exterior_source
    (n a : ℕ) (pre mid tail : List PositiveMass)
    (T : ClockTree (Spin n×Bool) (pre++(mid++tail))) (s : T.cavityLeft.Slot)
    (G : ActualNaturalBoundaryShape n a T)
    {U : ℕ} (hmid : 0 < mid.length) (hU : pre.length+mid.length<U)
    (hlen : U≤pre.length+mid.length+tail.length)
    (hT : NativePersistentLowForks pre.length (pre.length+mid.length) U T.cavityLeft)
    {a₀ : ℝ} (ho : MassOrdered a₀ (pre++(mid++tail)))
    (v : RestCoordinate n→ℝ) (q : ℕ→RestCoordinate n→ℝ) (x : RestCoordinate n→ℝ)
    (hlow : ∀j,T.cavityLeft.splitIndex s (G.restLabels j)≤pre.length+mid.length) :
    Nonempty (NativeDynamicCanonicalExteriorSource n a pre mid tail T s G v q x) := by
  obtain ⟨Ei,Es,D,read,target,ht,hi,hs,hh,hl,hField⟩:=
    native_two_level_star_field_disorder_classification pre mid tail T.cavityLeft s
      hmid hU hlen hT (restWeight_pos n) (restFeature n) ho v q x
  have hLaw (Q : T.cavityLeft.Assignment→ℝ) :
      T.cavityLeft.disorderExpect (restWeight n) (restFeature n) v q Q x=
        ∫z,nativeExteriorForestConditionalTest Ei Es D (restWeight n) (restFeature n)
          (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+j))
          (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+(mid.length+j)))
          (fun η ζ δ=>Q (read η ζ δ)) (exteriorForestIRoot z) (exteriorForestStarRoot z)
          ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail v q x := by
    rw [native_whole_expect_map_disorder T.cavityLeft (nativeExteriorForestTree pre mid Ei Es D)
      (nativeClassifiedSourceRead pre mid Ei Es D read) (restWeight_pos n) (restFeature n) ho hl v q Q x]
    exact nativeExteriorForest_disorder_law_eq_conditional pre mid (restWeight_pos n)
      (restFeature n) Ei Es D ho v q (fun η ζ δ=>Q (read η ζ δ)) x
  obtain ⟨outside,hRead⟩:=native_two_level_exterior_read_independent pre mid tail T.cavityLeft s
    hU hT Ei Es D read hi hs G.restLabels hlow
  let H:=fun η ζ=>G.exteriorProduct (outside η ζ)
  have hExt : ∀η ζ δ,G.restProduct (read η ζ δ)=H η ζ := by
    intro η ζ δ
    rw [G.restProduct_eq_exteriorProduct]
    apply congrArg G.exteriorProduct
    funext j
    exact hRead η ζ δ j
  have hELaw (F : ℝ→ℝ) :
      T.cavityLeft.disorderExpect (restWeight n) (restFeature n) v q
        (fun σ=>F (G.restProduct σ)) x=
      ∫z,nativeExteriorForestMean Ei Es (restWeight n) (restFeature n)
        (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+j))
        (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+(mid.length+j)))
        (fun η ζ=>F (H η ζ)) (exteriorForestIRoot z) (exteriorForestStarRoot z)
        ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail v q x := by
    rw [hLaw]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro z
    simp_rw [hExt]
    unfold nativeExteriorForestConditionalTest
    exact D.expect_const (restWeight_pos n) (restFeature n) ho.suffix_end.suffix_end _ _ _
  exact ⟨⟨⟨Ei,Es,D,read,target,H,ht,hi,hs,hh,hLaw,hExt,hELaw⟩,hField⟩⟩

theorem native_actual_generated_dynamic_canonical_exterior_source
    (n a : ℕ) (pre mid tail : List PositiveMass)
    {T : ClockTree (Spin n×Bool) (pre++(mid++tail))}
    {U k : ℕ} {seed : List NativeResourceMark}
    {P : NativeResourceTerm pre.length (pre.length+mid.length) T}
    (hP : NativeActualResourceGenerated pre.length (pre.length+mid.length) U seed k T P)
    (hmid : 0 < mid.length) (hU : pre.length+mid.length<U)
    (a₀ : ℝ) (p : MarkedPlacement T) (hp : p∈T.markedAttach a₀)
    (c : T.Slot) (hh : U≤p.tree.splitIndex p.mark (p.embed c))
    {a₁ : ℝ} (ho : MassOrdered a₁ (pre++(mid++tail)))
    (G : ActualNaturalBoundaryShape n a p.tree)
    (v : RestCoordinate n→ℝ) (q : ℕ→RestCoordinate n→ℝ) (x : RestCoordinate n→ℝ)
    (hlow : ∀j,p.tree.cavityLeft.splitIndex (p.tree.cavityLeftSlot (p.embed c))
      (G.restLabels j)≤pre.length+mid.length) :
    Nonempty (NativeDynamicCanonicalExteriorSource n a pre mid tail p.tree
      (p.tree.cavityLeftSlot (p.embed c)) G v q x) := by
  have hSource:=((hP.persistentLowForks (by omega)).observedHigh (by omega) hU a₀ p hp c hh).cavityLeft
  have hlen : U≤pre.length+mid.length+tail.length := by
    have h:=p.tree.splitIndex_le_clockLength p.mark (p.embed c)
    simp only [List.length_append] at h
    omega
  exact native_dynamic_canonical_exterior_source n a pre mid tail p.tree
    (p.tree.cavityLeftSlot (p.embed c)) G hmid hU hlen hSource ho v q x hlow

end OAI.SKFluctuations.Cavity
