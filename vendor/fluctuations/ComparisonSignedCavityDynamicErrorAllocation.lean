module

public import ComparisonSignedCavityDynamicProjectionAllocation
public import ComparisonSignedCavityDynamicErrorProducts

@[expose] public section

noncomputable section
set_option maxHeartbeats 15000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree

variable {n a : ℕ} {pre mid tail : List PositiveMass}
  {T : ClockTree (Spin n×Bool) (pre++(mid++tail))} {s : T.cavityLeft.Slot}
  {G : ActualNaturalBoundaryShape n a T} {v : RestCoordinate n→ℝ}
  {q : ℕ→RestCoordinate n→ℝ} {x : RestCoordinate n→ℝ}

theorem NativeDynamicCanonicalExteriorSource.incoming_i_error_projection_law
    (E : NativeDynamicCanonicalExteriorSource n a pre mid tail T s G v q x)
    {a₀ : ℝ} (ho : MassOrdered a₀ (pre++(mid++tail)))
    (c e₀ : T.cavityLeft.Slot) (t : E.D.Slot) (e : E.Ei.Slot)
    (hc : ∀η ζ δ,T.cavityLeft.atSlot (E.read η ζ δ) c=E.D.atSlot δ t)
    (he : ∀η ζ δ,T.cavityLeft.atSlot (E.read η ζ δ) e₀=E.Ei.atSlot η e)
    (F : T.cavityLeft.Assignment→ℝ) (error : E.D.Assignment→ℝ)
    (herror : ∀η ζ δ,F (E.read η ζ δ)=error δ)
    (j k : ℕ) (center : ℝ) :
    let dq:=cumulativeIncrements (q 0) (fun l=>q (l+1))
    let qi:=fun l=>dq (pre.length+l)
    let qs:=fun l=>dq (pre.length+(mid.length+l))
    nativeStarFieldDisorderMean (restWeight n) (restFeature n) T.cavityLeft s
      (pre.length+mid.length) v q
      (fun y σ=>
        let Y:=nativeStarCenteredProjection n tail qs center y
        (Y (T.cavityLeft.atSlot σ c)-Y (T.cavityLeft.atSlot σ s))*G.restProduct σ*
          (deletedOverlap n (joinSpin (T.cavityLeft.atSlot σ c,false))
              (joinSpin (T.cavityLeft.atSlot σ e₀,false))-
            deletedOverlap n (joinSpin (T.cavityLeft.atSlot σ s,false))
              (joinSpin (T.cavityLeft.atSlot σ e₀,false)))*
          F σ*(Y (T.cavityLeft.atSlot σ s)^j*Y (T.cavityLeft.atSlot σ c)^k)) x=
      ∫z,nativeTwoLevelIncomingErrorProduct n j k E.Ei E.Es E.D E.H e E.target t qi qs center error
        (exteriorForestIRoot z) (exteriorForestStarRoot z)
        ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail v q x := by
  dsimp only
  rw [E.star_field_law _ (by
    intro σ
    have HS:=native_star_centered_projection_smooth n ho.suffix_end.suffix_end
      (fun l=>cumulativeIncrements (q 0) (fun l=>q (l+1)) (pre.length+(mid.length+l)))
      center (T.cavityLeft.atSlot σ s) 0
    have HT:=native_star_centered_projection_smooth n ho.suffix_end.suffix_end
      (fun l=>cumulativeIncrements (q 0) (fun l=>q (l+1)) (pre.length+(mid.length+l)))
      center (T.cavityLeft.atSlot σ c) 0
    exact ((((HT.sub HS).mul_const _).mul_const _).mul_const _).mul ((HS.pow j).mul (HT.pow k)))]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro z
  dsimp only
  rw [native_two_level_incoming_error_product_eq_conditional]
  apply congrArg (fun J=>nativeExteriorForestConditionalTest E.Ei E.Es E.D
    (restWeight n) (restFeature n) _ _ J (exteriorForestIRoot z) (exteriorForestStarRoot z))
  funext η ζ δ
  simp only [E.target_read,hc,he,E.exterior_read,herror]

theorem NativeDynamicCanonicalExteriorSource.incoming_star_error_projection_law
    (E : NativeDynamicCanonicalExteriorSource n a pre mid tail T s G v q x)
    {a₀ : ℝ} (ho : MassOrdered a₀ (pre++(mid++tail)))
    (c e₀ : T.cavityLeft.Slot) (t : E.D.Slot) (e : E.Es.Slot)
    (hc : ∀η ζ δ,T.cavityLeft.atSlot (E.read η ζ δ) c=E.D.atSlot δ t)
    (he : ∀η ζ δ,T.cavityLeft.atSlot (E.read η ζ δ) e₀=E.Es.atSlot ζ e)
    (F : T.cavityLeft.Assignment→ℝ) (error : E.D.Assignment→ℝ)
    (herror : ∀η ζ δ,F (E.read η ζ δ)=error δ)
    (j k : ℕ) (center : ℝ) :
    let dq:=cumulativeIncrements (q 0) (fun l=>q (l+1))
    let qi:=fun l=>dq (pre.length+l)
    let qs:=fun l=>dq (pre.length+(mid.length+l))
    nativeStarFieldDisorderMean (restWeight n) (restFeature n) T.cavityLeft s
      (pre.length+mid.length) v q
      (fun y σ=>
        let Y:=nativeStarCenteredProjection n tail qs center y
        (Y (T.cavityLeft.atSlot σ c)-Y (T.cavityLeft.atSlot σ s))*G.restProduct σ*
          (deletedOverlap n (joinSpin (T.cavityLeft.atSlot σ c,false))
              (joinSpin (T.cavityLeft.atSlot σ e₀,false))-
            deletedOverlap n (joinSpin (T.cavityLeft.atSlot σ s,false))
              (joinSpin (T.cavityLeft.atSlot σ e₀,false)))*
          F σ*(Y (T.cavityLeft.atSlot σ s)^j*Y (T.cavityLeft.atSlot σ c)^k)) x=
      ∫z,nativeTwoLevelStarIncomingErrorProduct n j k E.Ei E.Es E.D E.H e E.target t qi qs center error
        (exteriorForestIRoot z) (exteriorForestStarRoot z)
        ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail v q x := by
  dsimp only
  rw [E.star_field_law _ (by
    intro σ
    have HS:=native_star_centered_projection_smooth n ho.suffix_end.suffix_end
      (fun l=>cumulativeIncrements (q 0) (fun l=>q (l+1)) (pre.length+(mid.length+l)))
      center (T.cavityLeft.atSlot σ s) 0
    have HT:=native_star_centered_projection_smooth n ho.suffix_end.suffix_end
      (fun l=>cumulativeIncrements (q 0) (fun l=>q (l+1)) (pre.length+(mid.length+l)))
      center (T.cavityLeft.atSlot σ c) 0
    exact ((((HT.sub HS).mul_const _).mul_const _).mul_const _).mul ((HS.pow j).mul (HT.pow k)))]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro z
  dsimp only
  rw [native_two_level_star_incoming_error_product_eq_conditional]
  apply congrArg (fun J=>nativeExteriorForestConditionalTest E.Ei E.Es E.D
    (restWeight n) (restFeature n) _ _ J (exteriorForestIRoot z) (exteriorForestStarRoot z))
  funext η ζ δ
  simp only [E.target_read,hc,he,E.exterior_read,herror]

theorem NativeDynamicCanonicalExteriorSource.power_error_projection_law
    (E : NativeDynamicCanonicalExteriorSource n a pre mid tail T s G v q x)
    {a₀ : ℝ} (ho : MassOrdered a₀ (pre++(mid++tail)))
    (c : T.cavityLeft.Slot) (t : E.D.Slot)
    (hc : ∀η ζ δ,T.cavityLeft.atSlot (E.read η ζ δ) c=E.D.atSlot δ t)
    (Z F : T.cavityLeft.Assignment→ℝ) (error : E.D.Assignment→ℝ)
    (herror : ∀η ζ δ,F (E.read η ζ δ)=error δ) (j k : ℕ) (center : ℝ) :
    let dq:=cumulativeIncrements (q 0) (fun l=>q (l+1))
    let qi:=fun l=>dq (pre.length+l)
    let qs:=fun l=>dq (pre.length+(mid.length+l))
    nativeStarFieldDisorderMean (restWeight n) (restFeature n) T.cavityLeft s
      (pre.length+mid.length) v q
      (fun y σ=>
        let Y:=nativeStarCenteredProjection n tail qs center y
        (Y (T.cavityLeft.atSlot σ c)-Y (T.cavityLeft.atSlot σ s))^2*(Z σ*F σ)*
          (Y (T.cavityLeft.atSlot σ s)^j*Y (T.cavityLeft.atSlot σ c)^k)) x=
      ∫z,nativeTwoLevelPowerErrorProduct n j k E.Ei E.Es E.D (fun η ζ δ=>Z (E.read η ζ δ))
        E.target t qi qs center error (exteriorForestIRoot z) (exteriorForestStarRoot z)
        ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail v q x := by
  dsimp only
  rw [E.star_field_law _ (by
    intro σ
    have HS:=native_star_centered_projection_smooth n ho.suffix_end.suffix_end
      (fun l=>cumulativeIncrements (q 0) (fun l=>q (l+1)) (pre.length+(mid.length+l)))
      center (T.cavityLeft.atSlot σ s) 0
    have HT:=native_star_centered_projection_smooth n ho.suffix_end.suffix_end
      (fun l=>cumulativeIncrements (q 0) (fun l=>q (l+1)) (pre.length+(mid.length+l)))
      center (T.cavityLeft.atSlot σ c) 0
    exact (((HT.sub HS).pow 2).mul_const _).mul ((HS.pow j).mul (HT.pow k)))]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro z
  unfold nativeTwoLevelPowerErrorProduct nativeTwoLevelPowerProduct
  apply congrArg (fun J=>nativeExteriorForestConditionalTest E.Ei E.Es E.D
    (restWeight n) (restFeature n) _ _ J (exteriorForestIRoot z) (exteriorForestStarRoot z))
  funext η ζ δ
  simp only [E.target_read,hc,herror]

end OAI.SKFluctuations.Cavity
