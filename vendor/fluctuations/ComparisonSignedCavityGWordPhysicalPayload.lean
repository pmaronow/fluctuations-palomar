module

public import ComparisonSignedCavityGWordConditionalFold
public import ComparisonSignedCavityPhysicalProjectionFactorization

@[expose] public section

noncomputable section
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
open scoped NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S B : Type} {as : List PositiveMass} {T : ClockTree (S×B) as}

theorem NativeObservedDiagram.restRead_observe (D : NativeObservedDiagram T)
    (p : MarkedPlacement D.tree) (σ : p.tree.cavityLeft.Assignment) :
    (D.observe p).restRead σ=D.restRead (p.restRestrict σ) := by
  apply T.cavityLeft.assignment_ext
  intro c
  obtain ⟨d,rfl⟩:=T.cavityLeftSlot.surjective c
  rw [restRead_at,restRead_at]
  exact (p.restRestrict_at σ (D.embed d)).symm

theorem NativeObservedDiagram.restRead_identity (σ : T.cavityLeft.Assignment) :
    (NativeObservedDiagram.identity T).restRead σ=σ := by
  apply T.cavityLeft.assignment_ext
  intro c
  obtain ⟨d,rfl⟩:=T.cavityLeftSlot.surjective c
  rw [restRead_at]
  rfl

end OAI.SKFluctuations.Hierarchy.ClockTree
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree

theorem native_star_pair_factor_displacement_centered (n : ℕ)
    (pre mid tail : List PositiveMass) (q : ℕ→RestCoordinate n→ℝ≥0)
    (center : ℝ) (y : RestCoordinate n→ℝ) (s t : Spin n) :
    nativeStarPairFactor (restWeight n) (restFeature n) (pre++(mid++tail))
        (pre.length+mid.length) q
        (fun u v=>deletedOverlap n (joinSpin (u,false)) (joinSpin (v,false))) y t-
      nativeStarPairFactor (restWeight n) (restFeature n) (pre++(mid++tail))
        (pre.length+mid.length) q
        (fun u v=>deletedOverlap n (joinSpin (u,false)) (joinSpin (v,false))) y s=
    nativeStarCenteredProjection n tail (fun j=>q (pre.length+(mid.length+j))) center y t-
      nativeStarCenteredProjection n tail (fun j=>q (pre.length+(mid.length+j))) center y s := by
  have H (u : Spin n):=nativeStarPairFactor_two_level_centered_projection n pre mid tail q 0 y u
  simp only [sub_zero] at H
  rw [H t,H s,native_star_centered_projection_difference,native_star_centered_projection_difference]

theorem native_G_word_physical_projected_payload
    {n : ℕ} (pre mid tail : List PositiveMass)
    (T : ClockTree (Spin n×Bool) (pre++(mid++tail))) (base : NativeGeneratedTest T)
    (D : NativeObservedDiagram T) (f e c : D.tree.Slot) (hm : D.marks=[f,e,c])
    (U power : ℕ) (q : ℕ→RestCoordinate n→ℝ) (b h K C : ℕ→ℝ)
    (hKC : ∀j,K j=h j+b j*C j) (hH : U ≤ D.tree.splitIndex e f)
    (y : RestCoordinate n→ℝ) (σ : D.tree.cavityLeft.Assignment) :
    let star:=pre.length+mid.length
    let R:=fun u v=>deletedOverlap n (joinSpin (u,false)) (joinSpin (v,false))
    let Y:=nativeStarCenteredProjection n tail
      (fun j=>cumulativeIncrements (q 0) (fun l=>q (l+1)) (pre.length+(mid.length+j))) (C star) y
    let old:=T.cavityLeft.atSlot (D.restRead σ) (T.cavityLeftSlot base.target)
    let new:=D.tree.cavityLeft.atSlot σ (D.tree.cavityLeftSlot c)
    let A:=nativeRestGeneratedTestValue T base R C (D.restRead σ)
    let B:=nativeRestGeneratedTestValue T base R C
      (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot base.target) (D.restRead σ) new)
    let F:=R (D.tree.cavityLeft.atSlot σ (D.tree.cavityLeftSlot e))
        (D.tree.cavityLeft.atSlot σ (D.tree.cavityLeftSlot f))-C (D.tree.splitIndex e f)
    nativeGWordProjectedPayload T base D star U power q b h K C R R y σ=
      -(b (D.tree.splitIndex e f))*((Y new-Y old)*
        ((B*F)*Y new^power-(A*F)*Y old^power)) := by
  dsimp only
  simp only [nativeGWordProjectedPayload,nativeGWordOldPayload,nativeGWordNewPayload,
    nativeGWordOldSelector,nativeGWordNewSelector,nativeGWordDisplacement,
    nativeGWordNewSpin,nativeGWordError,nativeObservedErrorIndex,NativeObservedDiagram.restMarks,
    hm,List.map_cons,List.map_nil,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  rw [native_star_pair_factor_displacement_centered n pre mid tail _ (C (pre.length+mid.length))]
  simp only [nativeStarPairFactor_two_level_centered_projection]
  have Herr (u v : Spin n) : restHighKernel n U b h K (D.tree.splitIndex e f) u v=
      b (D.tree.splitIndex e f)*(deletedOverlap n (joinSpin (u,false)) (joinSpin (v,false))-
        C (D.tree.splitIndex e f)) := by
    simp only [restHighKernel,not_lt.mpr hH,ite_false,hKC,deletedOverlap,joinSpin,Fin.lastCases_castSucc]
    ring
  rw [Herr]
  ring

end OAI.SKFluctuations.Cavity
