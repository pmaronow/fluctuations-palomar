module

public import ComparisonSignedCavityDynamicErrorAllocation
public import ComparisonSignedCavityOriginalPairedAllocation

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree
variable {n a : ℕ} {pre mid tail : List PositiveMass}
  {T : ClockTree (Spin n×Bool) (pre++(mid++tail))} {s : T.cavityLeft.Slot}
  {G : ActualNaturalBoundaryShape n a T} {v : RestCoordinate n→ℝ}
  {q : ℕ→RestCoordinate n→ℝ} {x : RestCoordinate n→ℝ}

theorem NativeDynamicCanonicalExteriorSource.paired_incoming_i_error_allocation
    (E : NativeDynamicCanonicalExteriorSource n a pre mid tail T s G v q x)
    {a₀ : ℝ} (ho : MassOrdered a₀ (pre++(mid++tail)))
    (c e₀ : T.cavityLeft.Slot) (t : E.D.Slot) (e : E.Ei.Slot)
    (hc : ∀η ζ δ,T.cavityLeft.atSlot (E.read η ζ δ) c=E.D.atSlot δ t)
    (he : ∀η ζ δ,T.cavityLeft.atSlot (E.read η ζ δ) e₀=E.Ei.atSlot η e)
    (A B F : T.cavityLeft.Assignment→ℝ) (error : E.D.Assignment→ℝ)
    (herror : ∀η ζ δ,F (E.read η ζ δ)=error δ)
    (hdiff : ∀σ,B σ-A σ=G.restProduct σ*
      (deletedOverlap n (joinSpin (T.cavityLeft.atSlot σ c,false))
          (joinSpin (T.cavityLeft.atSlot σ e₀,false))-
        deletedOverlap n (joinSpin (T.cavityLeft.atSlot σ s,false))
          (joinSpin (T.cavityLeft.atSlot σ e₀,false))))
    (d : ℕ) (center : ℝ) :
    let dq:=cumulativeIncrements (q 0) (fun l=>q (l+1))
    let qi:=fun l=>dq (pre.length+l)
    let qs:=fun l=>dq (pre.length+(mid.length+l))
    let Y:=fun y=>nativeStarCenteredProjection n tail qs center y
    nativeStarFieldDisorderMean (restWeight n) (restFeature n) T.cavityLeft s
      (pre.length+mid.length) v q
      (fun y σ=>(Y y (T.cavityLeft.atSlot σ c)-Y y (T.cavityLeft.atSlot σ s))*
        ((B σ*F σ)*Y y (T.cavityLeft.atSlot σ c)^d-(A σ*F σ)*Y y (T.cavityLeft.atSlot σ s)^d)) x=
      (∫z,nativeTwoLevelIncomingErrorProduct n 0 d E.Ei E.Es E.D E.H e E.target t qi qs center error
        (exteriorForestIRoot z) (exteriorForestStarRoot z)
        ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail v q x)+
      ∑j∈Finset.range d,∫z,nativeTwoLevelPowerErrorProduct n j (d-1-j) E.Ei E.Es E.D
        (fun η ζ δ=>A (E.read η ζ δ)) E.target t qi qs center error
        (exteriorForestIRoot z) (exteriorForestStarRoot z)
        ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail v q x := by
  dsimp only
  rw [E.paired_polynomial_allocation ho c (fun σ=>A σ*F σ) (fun σ=>B σ*F σ) d center]
  apply congrArg₂ (·+·)
  · have H:=E.incoming_i_error_projection_law ho c e₀ t e hc he F error herror 0 d center
    simp only [pow_zero,one_mul] at H
    rw [←H]
    apply congrArg (fun F=>nativeStarFieldDisorderMean (restWeight n) (restFeature n) T.cavityLeft s
      (pre.length+mid.length) v q F x)
    funext y σ
    dsimp only
    rw [show B σ*F σ-A σ*F σ=(B σ-A σ)*F σ by ring,hdiff]
    ring
  · apply Finset.sum_congr rfl
    intro j _
    exact E.power_error_projection_law ho c t hc A F error herror j (d-1-j) center

theorem NativeDynamicCanonicalExteriorSource.paired_incoming_star_error_allocation
    (E : NativeDynamicCanonicalExteriorSource n a pre mid tail T s G v q x)
    {a₀ : ℝ} (ho : MassOrdered a₀ (pre++(mid++tail)))
    (c e₀ : T.cavityLeft.Slot) (t : E.D.Slot) (e : E.Es.Slot)
    (hc : ∀η ζ δ,T.cavityLeft.atSlot (E.read η ζ δ) c=E.D.atSlot δ t)
    (he : ∀η ζ δ,T.cavityLeft.atSlot (E.read η ζ δ) e₀=E.Es.atSlot ζ e)
    (A B F : T.cavityLeft.Assignment→ℝ) (error : E.D.Assignment→ℝ)
    (herror : ∀η ζ δ,F (E.read η ζ δ)=error δ)
    (hdiff : ∀σ,B σ-A σ=G.restProduct σ*
      (deletedOverlap n (joinSpin (T.cavityLeft.atSlot σ c,false))
          (joinSpin (T.cavityLeft.atSlot σ e₀,false))-
        deletedOverlap n (joinSpin (T.cavityLeft.atSlot σ s,false))
          (joinSpin (T.cavityLeft.atSlot σ e₀,false))))
    (d : ℕ) (center : ℝ) :
    let dq:=cumulativeIncrements (q 0) (fun l=>q (l+1))
    let qi:=fun l=>dq (pre.length+l)
    let qs:=fun l=>dq (pre.length+(mid.length+l))
    let Y:=fun y=>nativeStarCenteredProjection n tail qs center y
    nativeStarFieldDisorderMean (restWeight n) (restFeature n) T.cavityLeft s
      (pre.length+mid.length) v q
      (fun y σ=>(Y y (T.cavityLeft.atSlot σ c)-Y y (T.cavityLeft.atSlot σ s))*
        ((B σ*F σ)*Y y (T.cavityLeft.atSlot σ c)^d-(A σ*F σ)*Y y (T.cavityLeft.atSlot σ s)^d)) x=
      (∫z,nativeTwoLevelStarIncomingErrorProduct n 0 d E.Ei E.Es E.D E.H e E.target t qi qs center error
        (exteriorForestIRoot z) (exteriorForestStarRoot z)
        ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail v q x)+
      ∑j∈Finset.range d,∫z,nativeTwoLevelPowerErrorProduct n j (d-1-j) E.Ei E.Es E.D
        (fun η ζ δ=>A (E.read η ζ δ)) E.target t qi qs center error
        (exteriorForestIRoot z) (exteriorForestStarRoot z)
        ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail v q x := by
  dsimp only
  rw [E.paired_polynomial_allocation ho c (fun σ=>A σ*F σ) (fun σ=>B σ*F σ) d center]
  apply congrArg₂ (·+·)
  · have H:=E.incoming_star_error_projection_law ho c e₀ t e hc he F error herror 0 d center
    simp only [pow_zero,one_mul] at H
    rw [←H]
    apply congrArg (fun F=>nativeStarFieldDisorderMean (restWeight n) (restFeature n) T.cavityLeft s
      (pre.length+mid.length) v q F x)
    funext y σ
    dsimp only
    rw [show B σ*F σ-A σ*F σ=(B σ-A σ)*F σ by ring,hdiff]
    ring
  · apply Finset.sum_congr rfl
    intro j _
    exact E.power_error_projection_law ho c t hc A F error herror j (d-1-j) center

theorem NativeDynamicCanonicalExteriorSource.paired_no_incoming_error_allocation
    (E : NativeDynamicCanonicalExteriorSource n a pre mid tail T s G v q x)
    {a₀ : ℝ} (ho : MassOrdered a₀ (pre++(mid++tail)))
    (c : T.cavityLeft.Slot) (t : E.D.Slot)
    (hc : ∀η ζ δ,T.cavityLeft.atSlot (E.read η ζ δ) c=E.D.atSlot δ t)
    (A F : T.cavityLeft.Assignment→ℝ) (error : E.D.Assignment→ℝ)
    (herror : ∀η ζ δ,F (E.read η ζ δ)=error δ) (d : ℕ) (center : ℝ) :
    let dq:=cumulativeIncrements (q 0) (fun l=>q (l+1))
    let qi:=fun l=>dq (pre.length+l)
    let qs:=fun l=>dq (pre.length+(mid.length+l))
    let Y:=fun y=>nativeStarCenteredProjection n tail qs center y
    nativeStarFieldDisorderMean (restWeight n) (restFeature n) T.cavityLeft s
      (pre.length+mid.length) v q
      (fun y σ=>(Y y (T.cavityLeft.atSlot σ c)-Y y (T.cavityLeft.atSlot σ s))*
        ((A σ*F σ)*Y y (T.cavityLeft.atSlot σ c)^d-(A σ*F σ)*Y y (T.cavityLeft.atSlot σ s)^d)) x=
      ∑j∈Finset.range d,∫z,nativeTwoLevelPowerErrorProduct n j (d-1-j) E.Ei E.Es E.D
        (fun η ζ δ=>A (E.read η ζ δ)) E.target t qi qs center error
        (exteriorForestIRoot z) (exteriorForestStarRoot z)
        ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail v q x := by
  dsimp only
  rw [E.paired_polynomial_allocation ho c (fun σ=>A σ*F σ) (fun σ=>A σ*F σ) d center]
  simp only [sub_self,mul_zero,zero_mul,E.mean_zero,zero_add]
  apply Finset.sum_congr rfl
  intro j _
  exact E.power_error_projection_law ho c t hc A F error herror j (d-1-j) center

end OAI.SKFluctuations.Cavity
