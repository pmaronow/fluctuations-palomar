module

public import ComparisonSignedCavityActualFreshSourceMarginals
public import ComparisonSignedCavityObservedWholeLawScale

@[expose] public section

noncomputable section
set_option maxHeartbeats 8000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree

def nativeOriginalFreshResidual (n : ℕ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (s e b : T.Slot) (a : ℝ) (star : ℕ)
    (v : RestCoordinate n→ℝ) (q : ℕ→RestCoordinate n→ℝ)
    (x : RestCoordinate n→ℝ) (Z : T.cavityLeft.Assignment→ℝ) : ℝ :=
  let p:=nativeFreshAtSlot T a b star
  p.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) v q (fun σ=>
    Z (p.restRestrict σ)*
      (deletedOverlap n (joinSpin (T.cavityLeft.atSlot (p.restRestrict σ) (T.cavityLeftSlot s),false))
          (joinSpin (p.restSpin σ,false))-
        deletedOverlap n (joinSpin (T.cavityLeft.atSlot (p.restRestrict σ) (T.cavityLeftSlot e),false))
          (joinSpin (p.restSpin σ,false)))) x

theorem native_original_fresh_moment_bound
    (n : ℕ) (pre mid tail : List PositiveMass)
    (T : ClockTree (Spin n×Bool) (pre++(mid++tail))) (s e b : T.Slot)
    {a : ℝ} (ho : MassOrdered a (pre++(mid++tail)))
    (v : RestCoordinate n→ℝ) (q : ℕ→RestCoordinate n→ℝ) (x : RestCoordinate n→ℝ)
    (hLaw : NativeActualFullFreshAnchorMomentLaw n pre mid tail T s e b a v q x)
    (Z : T.cavityLeft.Assignment→ℝ) {p r : ℝ} (hp : 0≤p) (hr : 0≤r)
    (hZ : T.cavityLeft.disorderExpect (restWeight n) (restFeature n) v q (fun σ=>Z σ^2) x≤p^2)
    (hJ : ∀(D : ClockTree (Spin n) tail) (td de : D.Slot),td≠de →
      pre.length+mid.length+D.splitIndex td de=T.splitIndex s e →
      let qs:=nativeStarSuffixClock n pre mid q
      (∫z,nativeSubtreeExteriorProjectionFourth n D td de (single tail) (fun _=>1)
        (singleSlot tail) qs qs (twinPrefixBRoot z) (twinPrefixDRoot z)
        ∂nativeTwinPrefixDisorderRootLaw (restWeight n) (restFeature n) pre mid tail v q x)≤r^4) :
    |nativeOriginalFreshResidual n T s e b a (pre.length+mid.length) v q x Z|≤p*r := by
  obtain ⟨A,Bold,D,read,td,de,htd,hde,hsplit,hres,hOld⟩:=hLaw
  let qi:=fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+j)
  let qs:=nativeStarSuffixClock n pre mid q
  let μ:=nativeTwinPrefixDisorderRootLaw (restWeight n) (restFeature n) pre mid tail v q x
  letI : IsProbabilityMeasure μ:=nativeTwinPrefixDisorderRootLaw_probability
    (restWeight_pos n) (restFeature n) pre mid tail ho v q x
  have hZ2 : (∫z,A.expect (restWeight n) (restFeature n) qi (fun η=>
      Bold.expect (restWeight n) (restFeature n) qs (fun β=>
        D.expect (restWeight n) (restFeature n) qs (fun δ=>Z (read η β δ)^2)
          (twinPrefixDRoot z)) (twinPrefixBRoot z)) (twinPrefixSharedRoot z) ∂μ)≤p^2 := by
    dsimp only [qi,qs,μ,nativeStarSuffixClock]
    exact (hOld (fun σ=>Z σ^2)).symm.trans_le hZ
  have hJ4 : (∫z,nativeSubtreeExteriorProjectionFourth n D de td (single tail) (fun _=>1)
      (singleSlot tail) qs qs (twinPrefixBRoot z) (twinPrefixDRoot z) ∂μ)≤r^4 := by
    by_cases heq : td=de
    · subst de
      simp only [native_subtree_projection_same_zero,integral_zero]
      positivity
    · simp_rw [native_subtree_projection_swap n D de td]
      exact hJ D td de heq hsplit
  unfold nativeOriginalFreshResidual
  rw [hres Z]
  exact native_three_root_fresh_anchor_saved_bound n A Bold D de td
    ho.suffix_end ho.suffix_end.suffix_end qi qs μ
    twinPrefixSharedRoot twinPrefixBRoot twinPrefixDRoot
    twinPrefixSharedRoot_measurable twinPrefixBRoot_measurable twinPrefixDRoot_measurable
    (fun η β δ=>Z (read η β δ)) hp hr hZ2 hJ4

end OAI.SKFluctuations.Cavity
