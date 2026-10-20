module

public import ComparisonSignedCavityDynamicSourceLinearity

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

theorem NativeDynamicCanonicalExteriorSource.paired_polynomial_allocation
    (E : NativeDynamicCanonicalExteriorSource n a pre mid tail T s G v q x)
    {a₀ : ℝ} (ho : MassOrdered a₀ (pre++(mid++tail)))
    (c : T.cavityLeft.Slot) (A B : T.cavityLeft.Assignment→ℝ) (d : ℕ) (center : ℝ) :
    let qs:=fun l=>cumulativeIncrements (q 0) (fun l=>q (l+1)) (pre.length+(mid.length+l))
    let Y:=fun y=>nativeStarCenteredProjection n tail qs center y
    nativeStarFieldDisorderMean (restWeight n) (restFeature n) T.cavityLeft s
      (pre.length+mid.length) v q
      (fun y σ=>(Y y (T.cavityLeft.atSlot σ c)-Y y (T.cavityLeft.atSlot σ s))*
        (B σ*Y y (T.cavityLeft.atSlot σ c)^d-A σ*Y y (T.cavityLeft.atSlot σ s)^d)) x=
      nativeStarFieldDisorderMean (restWeight n) (restFeature n) T.cavityLeft s
        (pre.length+mid.length) v q
        (fun y σ=>(Y y (T.cavityLeft.atSlot σ c)-Y y (T.cavityLeft.atSlot σ s))*
          (B σ-A σ)*Y y (T.cavityLeft.atSlot σ c)^d) x+
      ∑j∈Finset.range d,nativeStarFieldDisorderMean (restWeight n) (restFeature n) T.cavityLeft s
        (pre.length+mid.length) v q
        (fun y σ=>(Y y (T.cavityLeft.atSlot σ c)-Y y (T.cavityLeft.atSlot σ s))^2*A σ*
          (Y y (T.cavityLeft.atSlot σ s)^j*Y y (T.cavityLeft.atSlot σ c)^(d-1-j))) x := by
  dsimp only
  let qs:=fun l=>cumulativeIncrements (q 0) (fun l=>q (l+1)) (pre.length+(mid.length+l))
  let Y:=fun y=>nativeStarCenteredProjection n tail qs center y
  let J:=fun y σ=>(Y y (T.cavityLeft.atSlot σ c)-Y y (T.cavityLeft.atSlot σ s))*
    (B σ-A σ)*Y y (T.cavityLeft.atSlot σ c)^d
  let K:=fun j y σ=>(Y y (T.cavityLeft.atSlot σ c)-Y y (T.cavityLeft.atSlot σ s))^2*A σ*
    (Y y (T.cavityLeft.atSlot σ s)^j*Y y (T.cavityLeft.atSlot σ c)^(d-1-j))
  have HS (σ) : BddSmooth 0 (fun y=>Y y (T.cavityLeft.atSlot σ s)):=
    native_star_centered_projection_smooth n ho.suffix_end.suffix_end qs center _ 0
  have HT (σ) : BddSmooth 0 (fun y=>Y y (T.cavityLeft.atSlot σ c)):=
    native_star_centered_projection_smooth n ho.suffix_end.suffix_end qs center _ 0
  have hJ (σ) : BddSmooth 0 (fun y=>J y σ):=
    (((HT σ).sub (HS σ)).mul_const _).mul ((HT σ).pow d)
  have hK (j σ) : BddSmooth 0 (fun y=>K j y σ):=
    ((((HT σ).sub (HS σ)).pow 2).mul_const _).mul (((HS σ).pow j).mul ((HT σ).pow (d-1-j)))
  calc
    _=nativeStarFieldDisorderMean (restWeight n) (restFeature n) T.cavityLeft s
        (pre.length+mid.length) v q (fun y σ=>J y σ+∑j∈Finset.range d,K j y σ) x := by
      apply congrArg (fun F=>nativeStarFieldDisorderMean (restWeight n) (restFeature n) T.cavityLeft s
        (pre.length+mid.length) v q F x)
      funext y σ
      exact native_paired_power_difference_algebra d _ _ _ _
    _=_:=by
      rw [E.mean_add ho J (fun y σ=>∑j∈Finset.range d,K j y σ) hJ
        (fun σ=>BddSmooth.sum _ (fun j _=>hK j σ)),
        E.mean_sum ho (Finset.range d) K (fun j _ σ=>hK j σ)]

theorem NativeDynamicCanonicalExteriorSource.paired_incoming_i_allocation
    (E : NativeDynamicCanonicalExteriorSource n a pre mid tail T s G v q x)
    {a₀ : ℝ} (ho : MassOrdered a₀ (pre++(mid++tail)))
    (c e₀ : T.cavityLeft.Slot) (t : E.D.Slot) (e : E.Ei.Slot)
    (hc : ∀η ζ δ,T.cavityLeft.atSlot (E.read η ζ δ) c=E.D.atSlot δ t)
    (he : ∀η ζ δ,T.cavityLeft.atSlot (E.read η ζ δ) e₀=E.Ei.atSlot η e)
    (A B : T.cavityLeft.Assignment→ℝ)
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
        (B σ*Y y (T.cavityLeft.atSlot σ c)^d-A σ*Y y (T.cavityLeft.atSlot σ s)^d)) x=
      (∫z,nativeTwoLevelIncomingProduct n 0 d E.Ei E.Es E.D E.H e E.target t qi qs center
        (exteriorForestIRoot z) (exteriorForestStarRoot z)
        ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail v q x)+
      ∑j∈Finset.range d,∫z,nativeTwoLevelPowerProduct n j (d-1-j) E.Ei E.Es E.D
        (fun η ζ δ=>A (E.read η ζ δ)) E.target t qi qs center
        (exteriorForestIRoot z) (exteriorForestStarRoot z)
        ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail v q x := by
  dsimp only
  rw [E.paired_polynomial_allocation ho c A B d center]
  apply congrArg₂ (·+·)
  · have H:=E.incoming_i_projection_law ho c e₀ t e hc he 0 d center
    simp only [pow_zero,one_mul] at H
    rw [←H]
    apply congrArg (fun F=>nativeStarFieldDisorderMean (restWeight n) (restFeature n) T.cavityLeft s
      (pre.length+mid.length) v q F x)
    funext y σ
    rw [hdiff]
    ring
  · apply Finset.sum_congr rfl
    intro j _
    exact E.power_projection_law ho c t hc A j (d-1-j) center

theorem NativeDynamicCanonicalExteriorSource.paired_no_incoming_allocation
    (E : NativeDynamicCanonicalExteriorSource n a pre mid tail T s G v q x)
    {a₀ : ℝ} (ho : MassOrdered a₀ (pre++(mid++tail)))
    (c : T.cavityLeft.Slot) (t : E.D.Slot)
    (hc : ∀η ζ δ,T.cavityLeft.atSlot (E.read η ζ δ) c=E.D.atSlot δ t)
    (A : T.cavityLeft.Assignment→ℝ) (d : ℕ) (center : ℝ) :
    let dq:=cumulativeIncrements (q 0) (fun l=>q (l+1))
    let qi:=fun l=>dq (pre.length+l)
    let qs:=fun l=>dq (pre.length+(mid.length+l))
    let Y:=fun y=>nativeStarCenteredProjection n tail qs center y
    nativeStarFieldDisorderMean (restWeight n) (restFeature n) T.cavityLeft s
      (pre.length+mid.length) v q
      (fun y σ=>(Y y (T.cavityLeft.atSlot σ c)-Y y (T.cavityLeft.atSlot σ s))*
        (A σ*Y y (T.cavityLeft.atSlot σ c)^d-A σ*Y y (T.cavityLeft.atSlot σ s)^d)) x=
      ∑j∈Finset.range d,∫z,nativeTwoLevelPowerProduct n j (d-1-j) E.Ei E.Es E.D
        (fun η ζ δ=>A (E.read η ζ δ)) E.target t qi qs center
        (exteriorForestIRoot z) (exteriorForestStarRoot z)
        ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail v q x := by
  dsimp only
  rw [E.paired_polynomial_allocation ho c A A d center]
  simp only [sub_self,mul_zero,zero_mul,E.mean_zero,zero_add]
  apply Finset.sum_congr rfl
  intro j _
  exact E.power_projection_law ho c t hc A j (d-1-j) center

end OAI.SKFluctuations.Cavity
