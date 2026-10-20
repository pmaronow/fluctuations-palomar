module

public import ComparisonSignedCavityActualGCentering
public import ComparisonSignedCavityActualOriginalGPairingTransport
public import ComparisonSignedCavityActualParentRecursionWeight

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S ι : Type} [Fintype S] [Fintype ι] {as : List PositiveMass}

 theorem NativeResourceTerm.reweight_value {i star : ℕ} {T : ClockTree S as}
    (P : NativeResourceTerm i star T) (c : ℝ)
    (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ) (v : ι→ℝ) (q : ℕ→ι→ℝ)
    (R : S→S→ℝ) (C : ℕ→ℝ) (x : ι→ℝ) (σ : T.Assignment) :
    (P.reweight c).value w φ v q R C x σ=c*P.value w φ v q R C x σ := by
  unfold NativeResourceTerm.reweight NativeResourceTerm.value NativeResourceTerm.scalar
  ring

 theorem NativeResourceTerm.projection_value {i star : ℕ} {T : ClockTree S as}
    (P : NativeResourceTerm i star T) (a : ℝ) (k : ℕ) (hl : star≤as.length)
    (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ) (v : ι→ℝ) (q : ℕ→ι→ℝ)
    (R : S→S→ℝ) (C : ℕ→ℝ) (x : ι→ℝ)
    (σ : (nativeFreshAtSlot T a P.live.test.target star).tree.Assignment) :
    let g:=nativeFreshAtSlot T a P.live.test.target star
    (P.projection a k hl).value w φ v q R C x σ=
      P.value w φ v q R C x (g.restrict σ)*
        (R (T.atSlot (g.restrict σ) P.live.test.target) (g.spin σ)-C star) := by
  dsimp only
  change P.scalar w φ v q R C x*(P.live.test.addProjection a star).value R C σ=_
  rw [P.live.test.addProjection_value a hl R C σ]
  change _=(P.scalar w φ v q R C x*_)*_
  ring

end OAI.SKFluctuations.Hierarchy.ClockTree
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

def nativeActualFrozenResourceResponse
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star : ℕ} {T : ClockTree (Spin n×Bool) as}
    (P : NativeResourceTerm i star T) (U k : ℕ)
    (v₀ : FullCoordinate n→ℝ) (q₀ : ℕ→FullCoordinate n→ℝ) (x₀ : FullCoordinate n→ℝ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (W : ℝ) : ℝ :=
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=finitePhysicalMixedClock (n+1) as b h
  let C:=nativePhysicalResourceCenter n M.bf M.hf as
  (W⁻¹)^k*nativeOriginalLongitudinalPairing n v q x U K b C T
    (P.value (fullWeight n) (fullFeature n) v₀ q₀
      (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)) C x₀) P.live.test.target

 theorem native_original_longitudinal_const_mul_test (n : ℕ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (U : ℕ) (K b C : ℕ→ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.Assignment→ℝ) (c : ℝ) (a : T.Slot) :
    nativeOriginalLongitudinalPairing n v q x U K b C T (fun σ=>c*P σ) a=
      c*nativeOriginalLongitudinalPairing n v q x U K b C T P a := by
  unfold nativeOriginalLongitudinalPairing
  simp_rw [mul_assoc,ClockTree.disorderExpect_const_mul (fullWeight_pos n) (fullFeature n) _ ho]
  simp only [←List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  apply congrArg List.sum
  apply List.map_congr_left
  intro r hr
  apply congrArg List.sum
  apply List.map_congr_left
  intro z hz
  ring

 theorem nativeActualResourceGInsertion_eq_frozen_response
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star : ℕ} {T : ClockTree (Spin n×Bool) as}
    (P : NativeResourceTerm i star T) (ho : MassOrdered 0 as) (U k : ℕ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (W : ℝ) :
    nativeActualResourceGInsertion M P U k v q x W=
      nativeActualFrozenResourceResponse M P U k v q x v q x W := by
  have Hatom (g : NativeOriginalGMarkedWord T) :
      g.tree.disorderExpect (fullWeight n) (fullFeature n) v q
        (fun σ=>(W⁻¹)^k*((g.liftResource P).value (fullWeight n) (fullFeature n) v q
          (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
          (nativePhysicalResourceCenter n M.bf M.hf as) x σ*g.atom M U P.live.test.target σ)) x=
        (W⁻¹)^k*g.tree.disorderExpect (fullWeight n) (fullFeature n) v q
          (fun σ=>P.value (fullWeight n) (fullFeature n) v q
            (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
            (nativePhysicalResourceCenter n M.bf M.hf as) x
            (g.p.restrict (g.r.restrict (g.z.restrict σ)))*g.atom M U P.live.test.target σ) x := by
    simp_rw [g.liftResource_value]
    rw [g.tree.disorderExpect_const_mul (fullWeight_pos n) (fullFeature n) ho]
  unfold nativeActualResourceGInsertion
  simp_rw [Hatom]
  unfold nativeActualFrozenResourceResponse
  dsimp only
  have H:=nativeOriginalGMarkedWords_weighted_kernel_sum T
    (fun p r z=>z.tree.disorderExpect (fullWeight n) (fullFeature n) v q
      (fun σ=>P.value (fullWeight n) (fullFeature n) v q
        (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
        (nativePhysicalResourceCenter n M.bf M.hf as) x (p.restrict (r.restrict (z.restrict σ)))*
          nativeOriginalHighGAtom z.tree U
            (finitePhysicalMixedClock (n+1) as
              (fun j=>(M.bf (partitionPoint 0 as j):ℝ))
              (fun j=>(M.hf (partitionPoint 0 as j):ℝ)))
            (fun j=>(M.bf (partitionPoint 0 as j):ℝ))
            (nativePhysicalResourceCenter n M.bf M.hf as)
            (z.embed (r.embed (p.embed P.live.test.target)))
            (z.embed (r.embed p.mark)) (z.embed r.mark) z.mark σ) x)
  conv_rhs =>
    unfold nativeOriginalLongitudinalPairing
    rw [←H,←List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro g hg
  simp only [NativeOriginalGMarkedWord.atom,NativeOriginalGMarkedWord.tree,
    nativeMinimumOriginalHighGAtom]
  ring

 theorem nativeActualFrozenResourceResponse_reweight
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star : ℕ} {T : ClockTree (Spin n×Bool) as}
    (P : NativeResourceTerm i star T) (ho : MassOrdered 0 as) (U k : ℕ) (c : ℝ)
    (v₀ : FullCoordinate n→ℝ) (q₀ : ℕ→FullCoordinate n→ℝ) (x₀ : FullCoordinate n→ℝ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (W : ℝ) :
    nativeActualFrozenResourceResponse M (P.reweight c) U k v₀ q₀ x₀ v q x W=
      c*nativeActualFrozenResourceResponse M P U k v₀ q₀ x₀ v q x W := by
  unfold nativeActualFrozenResourceResponse
  dsimp only
  have HV : (P.reweight c).value (fullWeight n) (fullFeature n) v₀ q₀
      (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
      (nativePhysicalResourceCenter n M.bf M.hf as) x₀=
      fun σ=>c*P.value (fullWeight n) (fullFeature n) v₀ q₀
        (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
        (nativePhysicalResourceCenter n M.bf M.hf as) x₀ σ := by
    funext σ;exact P.reweight_value c _ _ _ _ _ _ _ σ
  rw [HV]
  rw [native_original_longitudinal_const_mul_test n v q x U _ _ _ T ho]
  simp only [NativeResourceTerm.reweight]
  ring

 theorem nativeActualFrozenResourceResponse_weighted_successor
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star : ℕ} {T : ClockTree (Spin n×Bool) as}
    (P : NativeResourceTerm i star T) (ho : MassOrdered 0 as) (U k : ℕ) (alpha : ℝ)
    (v₀ : FullCoordinate n→ℝ) (q₀ : ℕ→FullCoordinate n→ℝ) (x₀ : FullCoordinate n→ℝ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (W : ℝ) (hW : W≠0) :
    nativeActualFrozenResourceResponse M (P.reweight (W*alpha)) U (k+1) v₀ q₀ x₀ v q x W=
      alpha*nativeActualFrozenResourceResponse M P U k v₀ q₀ x₀ v q x W := by
  rw [nativeActualFrozenResourceResponse_reweight M P ho]
  unfold nativeActualFrozenResourceResponse
  dsimp only
  rw [pow_succ]
  field_simp

end OAI.SKFluctuations.Cavity
