module

public import CavityRestMarkedExchange

@[expose] public section

noncomputable section
set_option maxHeartbeats 1500000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy

def nativeProjectedDeletedOverlap (n : ℕ) (as : List PositiveMass)
    (q : ℕ → RestCoordinate n → ℝ≥0) (x : RestCoordinate n → ℝ) (σ : Spin n) : ℝ :=
  (ClockTree.single (S := Spin n) as).expect (restWeight n) (restFeature n) q
    (fun τ=>deletedOverlap n (joinSpin (σ,false))
      (joinSpin (ClockTree.singleEquiv (S := Spin n) as τ,false))) x

def nativeCenteredProjectedDeletedOverlap (n : ℕ) (as : List PositiveMass)
    (q : ℕ → RestCoordinate n → ℝ≥0) (x : RestCoordinate n → ℝ)
    (center : ℝ) (σ : Spin n) : ℝ :=
  nativeProjectedDeletedOverlap n as q x σ-center

def nativeAttachmentOld {n : ℕ} {as : List PositiveMass}
    (p : ClockTree.MarkedPlacement (ClockTree.single (S := Spin n×Bool) as))
    (σ : p.tree.cavityLeft.Assignment) : Spin n :=
  p.tree.cavityLeft.atSlot σ (ClockTree.cavityLeftSlot p.tree
    (p.embed (ClockTree.singleSlot (S := Spin n×Bool) as)))

def nativeAttachmentGamma {n : ℕ} {as : List PositiveMass}
    (p : ClockTree.MarkedPlacement (ClockTree.single (S := Spin n×Bool) as))
    (U : ℕ) (K : ℕ → ℝ) : ℝ :=
  fullScalarCutGamma p.tree U K
    (p.embed (ClockTree.singleSlot (S := Spin n×Bool) as)) p.mark

def nativeSignedProjectedReplacement (n : ℕ) {as : List PositiveMass}
    (E : ClockTree (Spin n) as) (a : ℝ) (U : ℕ) (K : ℕ → ℝ)
    (q : ℕ → RestCoordinate n → ℝ≥0) (x : RestCoordinate n → ℝ)
    (center : ℝ) (P : E.Assignment → Spin n → ℝ) : ℝ :=
  let Y := nativeCenteredProjectedDeletedOverlap n as q x center
  (((ClockTree.single (S := Spin n×Bool) as).markedAttach a).map fun p=>
    p.coeff*nativeAttachmentGamma p U K*
      (E.fork p.tree.cavityLeft).expect (restWeight n) (restFeature n) q
        (fun σ=>(Y (p.restSpin σ.2)-Y (nativeAttachmentOld p σ.2))*
          P σ.1 (nativeAttachmentOld p σ.2)) x).sum

def nativeSignedProjectedResampling (n : ℕ) {as : List PositiveMass}
    (E : ClockTree (Spin n) as) (a : ℝ) (U : ℕ) (K : ℕ → ℝ)
    (q : ℕ → RestCoordinate n → ℝ≥0) (x : RestCoordinate n → ℝ)
    (center : ℝ) (P : E.Assignment → Spin n → ℝ) : ℝ :=
  let Y := nativeCenteredProjectedDeletedOverlap n as q x center
  (((ClockTree.single (S := Spin n×Bool) as).markedAttach a).map fun p=>
    p.coeff*nativeAttachmentGamma p U K*
      (E.fork p.tree.cavityLeft).expect (restWeight n) (restFeature n) q
        (fun σ=>(Y (p.restSpin σ.2)-Y (nativeAttachmentOld p σ.2))*
          (P σ.1 (nativeAttachmentOld p σ.2)-P σ.1 (p.restSpin σ.2))) x).sum

theorem native_signed_projected_replacement (n : ℕ) {as : List PositiveMass}
    (E : ClockTree (Spin n) as) {a : ℝ} (ho : MassOrdered a as)
    (U : ℕ) (K : ℕ → ℝ) (q : ℕ → RestCoordinate n → ℝ≥0)
    (x : RestCoordinate n → ℝ) (center : ℝ) (P : E.Assignment → Spin n → ℝ) :
    nativeSignedProjectedReplacement n E a U K q x center P=
      (1/2:ℝ)*nativeSignedProjectedResampling n E a U K q x center P := by
  unfold nativeSignedProjectedReplacement nativeSignedProjectedResampling
  dsimp only
  rw [←List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  let Y := nativeCenteredProjectedDeletedOverlap n as q x center
  have he:=ClockTree.single_full_rest_external_exchange (restWeight_pos n) (restFeature n)
    E ho p hp q (fun σ u v=>(Y v-Y u)*P σ u) x
  change (E.fork p.tree.cavityLeft).expect (restWeight n) (restFeature n) q
      (fun σ=>(Y (p.restSpin σ.2)-Y (nativeAttachmentOld p σ.2))*P σ.1 (nativeAttachmentOld p σ.2)) x=
    (E.fork p.tree.cavityLeft).expect (restWeight n) (restFeature n) q
      (fun σ=>(Y (nativeAttachmentOld p σ.2)-Y (p.restSpin σ.2))*P σ.1 (p.restSpin σ.2)) x at he
  have hn : (E.fork p.tree.cavityLeft).expect (restWeight n) (restFeature n) q
      (fun σ=>(Y (nativeAttachmentOld p σ.2)-Y (p.restSpin σ.2))*P σ.1 (p.restSpin σ.2)) x=
    -(E.fork p.tree.cavityLeft).expect (restWeight n) (restFeature n) q
      (fun σ=>(Y (p.restSpin σ.2)-Y (nativeAttachmentOld p σ.2))*P σ.1 (p.restSpin σ.2)) x := by
    unfold ClockTree.expect
    rw [←Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro σ _
    ring
  rw [hn] at he
  have hs : (E.fork p.tree.cavityLeft).expect (restWeight n) (restFeature n) q
      (fun σ=>(Y (p.restSpin σ.2)-Y (nativeAttachmentOld p σ.2))*
        (P σ.1 (nativeAttachmentOld p σ.2)-P σ.1 (p.restSpin σ.2))) x=
    (E.fork p.tree.cavityLeft).expect (restWeight n) (restFeature n) q
      (fun σ=>(Y (p.restSpin σ.2)-Y (nativeAttachmentOld p σ.2))*P σ.1 (nativeAttachmentOld p σ.2)) x-
    (E.fork p.tree.cavityLeft).expect (restWeight n) (restFeature n) q
      (fun σ=>(Y (p.restSpin σ.2)-Y (nativeAttachmentOld p σ.2))*P σ.1 (p.restSpin σ.2)) x := by
    unfold ClockTree.expect
    rw [←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro σ _
    ring
  change p.coeff*nativeAttachmentGamma p U K*
      (E.fork p.tree.cavityLeft).expect (restWeight n) (restFeature n) q
        (fun σ=>(Y (p.restSpin σ.2)-Y (nativeAttachmentOld p σ.2))*P σ.1 (nativeAttachmentOld p σ.2)) x=
    (1/2:ℝ)*(p.coeff*nativeAttachmentGamma p U K*
      (E.fork p.tree.cavityLeft).expect (restWeight n) (restFeature n) q
        (fun σ=>(Y (p.restSpin σ.2)-Y (nativeAttachmentOld p σ.2))*
          (P σ.1 (nativeAttachmentOld p σ.2)-P σ.1 (p.restSpin σ.2))) x)
  rw [hs,he]
  ring

end OAI.SKFluctuations.Cavity
