module

public import CavityNativeWeightedExterior

@[expose] public section

noncomputable section
set_option maxHeartbeats 1500000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations.Cavity
open Hierarchy

def nativeIncomingPowerTest (n k : ℕ) {as : List PositiveMass}
    (E : ClockTree (Spin n) as) (H : E.Assignment → ℝ) (s : E.Slot)
    (q : ℕ → RestCoordinate n → ℝ≥0) (x : RestCoordinate n → ℝ)
    (center incomingCenter : ℝ) (σ : E.Assignment) (τ : Spin n) : ℝ :=
  H σ*(deletedOverlap n (joinSpin (τ,false)) (joinSpin (E.atSlot σ s,false))-incomingCenter)*
    nativeCenteredProjectedDeletedOverlap n as q x center τ^k

def nativeSignedIncomingPowerVariation (n k : ℕ) {as : List PositiveMass}
    (E : ClockTree (Spin n) as) (a : ℝ) (U : ℕ) (K : ℕ → ℝ)
    (H : E.Assignment → ℝ) (s : E.Slot)
    (q : ℕ → RestCoordinate n → ℝ≥0) (x : RestCoordinate n → ℝ)
    (center incomingCenter : ℝ) : ℝ :=
  let Y := nativeCenteredProjectedDeletedOverlap n as q x center
  (((ClockTree.single (S := Spin n×Bool) as).markedAttach a).map fun p=>
    p.coeff*nativeAttachmentGamma p U K*
      (E.fork p.tree.cavityLeft).expect (restWeight n) (restFeature n) q (fun σ=>
        (Y (p.restSpin σ.2)-Y (nativeAttachmentOld p σ.2))*H σ.1*
          (deletedOverlap n (joinSpin (nativeAttachmentOld p σ.2,false))
            (joinSpin (E.atSlot σ.1 s,false))-incomingCenter)*
          (Y (nativeAttachmentOld p σ.2)^k-Y (p.restSpin σ.2)^k)) x).sum

def nativeSignedIncomingAnchorVariation (n k : ℕ) {as : List PositiveMass}
    (E : ClockTree (Spin n) as) (a : ℝ) (U : ℕ) (K : ℕ → ℝ)
    (H : E.Assignment → ℝ) (s : E.Slot)
    (q : ℕ → RestCoordinate n → ℝ≥0) (x : RestCoordinate n → ℝ) (center : ℝ) : ℝ :=
  let Y := nativeCenteredProjectedDeletedOverlap n as q x center
  (((ClockTree.single (S := Spin n×Bool) as).markedAttach a).map fun p=>
    p.coeff*nativeAttachmentGamma p U K*
      p.tree.cavityLeft.expect (restWeight n) (restFeature n) q (fun σ=>
        (Y (p.restSpin σ)-Y (nativeAttachmentOld p σ))*Y (p.restSpin σ)^k*
          inner ℝ (WithLp.toLp 2 (normalizedSpin n (nativeAttachmentOld p σ))-
            WithLp.toLp 2 (normalizedSpin n (p.restSpin σ)))
            (nativeWeightedExteriorAnchor n E H s q x)) x).sum

theorem native_signed_weighted_incoming_decomposition (n k : ℕ) {as : List PositiveMass}
    (E : ClockTree (Spin n) as) {a : ℝ} (ho : MassOrdered a as)
    (U : ℕ) (K : ℕ → ℝ) (H : E.Assignment → ℝ) (s : E.Slot)
    (q : ℕ → RestCoordinate n → ℝ≥0) (x : RestCoordinate n → ℝ)
    (center incomingCenter : ℝ) :
    nativeSignedProjectedReplacement n E a U K q x center
      (nativeIncomingPowerTest n k E H s q x center incomingCenter)=
    (1/2:ℝ)*(nativeSignedIncomingPowerVariation n k E a U K H s q x center incomingCenter+
      nativeSignedIncomingAnchorVariation n k E a U K H s q x center) := by
  rw [native_signed_projected_replacement n E ho]
  congr 1
  unfold nativeSignedProjectedResampling nativeSignedIncomingPowerVariation nativeSignedIncomingAnchorVariation
  dsimp only
  rw [←List.sum_map_add]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  rw [←mul_add]
  congr 1
  let Y := nativeCenteredProjectedDeletedOverlap n as q x center
  have hin:=native_weighted_target_difference n E p.tree.cavityLeft H s q x
    (fun σ=>(Y (p.restSpin σ)-Y (nativeAttachmentOld p σ))*Y (p.restSpin σ)^k)
    (nativeAttachmentOld p) p.restSpin
  rw [←hin]
  have hadd : (E.fork p.tree.cavityLeft).expect (restWeight n) (restFeature n) q
      (fun σ=>
        (Y (p.restSpin σ.2)-Y (nativeAttachmentOld p σ.2))*H σ.1*
          (deletedOverlap n (joinSpin (nativeAttachmentOld p σ.2,false))
            (joinSpin (E.atSlot σ.1 s,false))-incomingCenter)*
          (Y (nativeAttachmentOld p σ.2)^k-Y (p.restSpin σ.2)^k)) x+
    (E.fork p.tree.cavityLeft).expect (restWeight n) (restFeature n) q
      (fun σ=>(Y (p.restSpin σ.2)-Y (nativeAttachmentOld p σ.2))*Y (p.restSpin σ.2)^k*H σ.1*
        (deletedOverlap n (joinSpin (nativeAttachmentOld p σ.2,false))
          (joinSpin (E.atSlot σ.1 s,false))-
          deletedOverlap n (joinSpin (p.restSpin σ.2,false))
            (joinSpin (E.atSlot σ.1 s,false)))) x=
    (E.fork p.tree.cavityLeft).expect (restWeight n) (restFeature n) q
      (fun σ=>(Y (p.restSpin σ.2)-Y (nativeAttachmentOld p σ.2))*
        (nativeIncomingPowerTest n k E H s q x center incomingCenter σ.1 (nativeAttachmentOld p σ.2)-
          nativeIncomingPowerTest n k E H s q x center incomingCenter σ.1 (p.restSpin σ.2))) x := by
    unfold ClockTree.expect
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro σ _
    unfold nativeIncomingPowerTest
    dsimp only [Y]
    ring
  exact hadd.symm

end OAI.SKFluctuations.Cavity
