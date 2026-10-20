module

public import ComparisonSignedCavityActualCenteredEndpoint

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 14000000

def nativeOriginalFrozenRestoredResourceValue
    {n : ℕ} {as : List PositiveMass} {i star : ℕ} {T : ClockTree (Spin n×Bool) as}
    (P : ClockTree.NativeResourceTerm i star T)
    (v₀ : FullCoordinate n→ℝ) (q₀ : ℕ→FullCoordinate n→ℝ) (x₀ : FullCoordinate n→ℝ)
    (C : ℕ→ℝ) (σ : T.Assignment) : ℝ :=
  P.scalar (fullWeight n) (fullFeature n) v₀ q₀
      (fun s t=>deletedOverlap n (joinSpin s) (joinSpin t)) C x₀*
    P.live.test.value (fun s t=>orderedOverlap (n+1) (joinSpin s) (joinSpin t)) C σ

theorem native_frozen_restored_resource_site_permutation
    {n : ℕ} {as : List PositiveMass} {i star : ℕ} {T : ClockTree (Spin n×Bool) as}
    (P : ClockTree.NativeResourceTerm i star T)
    (v₀ : FullCoordinate n→ℝ) (q₀ : ℕ→FullCoordinate n→ℝ) (x₀ : FullCoordinate n→ℝ)
    (C : ℕ→ℝ) (π : Fin (n+1)≃Fin (n+1)) (σ : T.Assignment) :
    nativeOriginalFrozenRestoredResourceValue P v₀ q₀ x₀ C
      (T.assignmentGauge (nativeFullSiteSpinPerm π) σ)=
      nativeOriginalFrozenRestoredResourceValue P v₀ q₀ x₀ C σ := by
  unfold nativeOriginalFrozenRestoredResourceValue ClockTree.NativeGeneratedTest.value
    ClockTree.nativeGeneratedEdgeProduct
  simp only [ClockTree.atSlot_assignmentGauge,full_orderedOverlap_nativeSitePerm]

theorem native_original_frozen_restored_resource_site_pair_eq_overlap
    {n : ℕ} {as : List PositiveMass} {i star : ℕ} (T : ClockTree (Spin n×Bool) as)
    (ho : MassOrdered 0 as) (P : ClockTree.NativeResourceTerm i star T)
    (v₀ : FullCoordinate n→ℝ) (q₀ : ℕ→FullCoordinate n→ℝ) (x₀ : FullCoordinate n→ℝ)
    (U : ℕ) (b h K C : ℕ→ℝ) (s t : T.Slot) :
    let q:=cavityPath n U 1 1 (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) b h K
    T.disorderExpect (fullWeight n) (fullFeature n) 0 q
      (fun σ=>spinValue (T.atSlot σ s).2*spinValue (T.atSlot σ t).2*
        nativeOriginalFrozenRestoredResourceValue P v₀ q₀ x₀ C σ) 0=
    T.disorderExpect (fullWeight n) (fullFeature n) 0 q
      (fun σ=>orderedOverlap (n+1) (joinSpin (T.atSlot σ s)) (joinSpin (T.atSlot σ t))*
        nativeOriginalFrozenRestoredResourceValue P v₀ q₀ x₀ C σ) 0 := by
  dsimp only
  simpa only [joinSpin_last] using native_actual_full_site_pair_eq_overlap T ho U b h K
    (nativeOriginalFrozenRestoredResourceValue P v₀ q₀ x₀ C)
    (native_frozen_restored_resource_site_permutation P v₀ q₀ x₀ C) s t (Fin.last n)

theorem native_original_frozen_resource_site_pair_eq_overlap_add_omission
    {n : ℕ} {as : List PositiveMass} {i star : ℕ} (T : ClockTree (Spin n×Bool) as)
    (ho : MassOrdered 0 as) (P : ClockTree.NativeResourceTerm i star T)
    (v₀ : FullCoordinate n→ℝ) (q₀ : ℕ→FullCoordinate n→ℝ) (x₀ : FullCoordinate n→ℝ)
    (U : ℕ) (b h K C : ℕ→ℝ) (s t : T.Slot) :
    let q:=cavityPath n U 1 1 (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) b h K
    let F:=P.value (fullWeight n) (fullFeature n) v₀ q₀
      (fun s t=>deletedOverlap n (joinSpin s) (joinSpin t)) C x₀
    T.disorderExpect (fullWeight n) (fullFeature n) 0 q
      (fun σ=>spinValue (T.atSlot σ s).2*spinValue (T.atSlot σ t).2*F σ) 0=
    T.disorderExpect (fullWeight n) (fullFeature n) 0 q
      (fun σ=>orderedOverlap (n+1) (joinSpin (T.atSlot σ s)) (joinSpin (T.atSlot σ t))*F σ) 0+
    T.disorderExpect (fullWeight n) (fullFeature n) 0 q
      (fun σ=>(spinValue (T.atSlot σ s).2*spinValue (T.atSlot σ t).2-
        orderedOverlap (n+1) (joinSpin (T.atSlot σ s)) (joinSpin (T.atSlot σ t)))*
        (F σ-nativeOriginalFrozenRestoredResourceValue P v₀ q₀ x₀ C σ)) 0 := by
  have H:=native_original_frozen_restored_resource_site_pair_eq_overlap T ho P v₀ q₀ x₀ U b h K C s t
  dsimp only [ClockTree.disorderExpect] at H ⊢
  simp only [sub_mul,mul_sub,Finset.sum_sub_distrib]
  simp only [←mul_assoc] at H ⊢
  linear_combination H

theorem native_frozen_resource_omission_eq_scalar_mul_live
    {n : ℕ} {as : List PositiveMass} {i star : ℕ} {T : ClockTree (Spin n×Bool) as}
    (P : ClockTree.NativeResourceTerm i star T)
    (v₀ : FullCoordinate n→ℝ) (q₀ : ℕ→FullCoordinate n→ℝ) (x₀ : FullCoordinate n→ℝ)
    (C : ℕ→ℝ) (σ : T.Assignment) :
    P.value (fullWeight n) (fullFeature n) v₀ q₀
        (fun s t=>deletedOverlap n (joinSpin s) (joinSpin t)) C x₀ σ-
      nativeOriginalFrozenRestoredResourceValue P v₀ q₀ x₀ C σ=
    P.scalar (fullWeight n) (fullFeature n) v₀ q₀
        (fun s t=>deletedOverlap n (joinSpin s) (joinSpin t)) C x₀*
      (P.live.test.value (fun s t=>deletedOverlap n (joinSpin s) (joinSpin t)) C σ-
        P.live.test.value (fun s t=>orderedOverlap (n+1) (joinSpin s) (joinSpin t)) C σ) := by
  unfold ClockTree.NativeResourceTerm.value nativeOriginalFrozenRestoredResourceValue
  ring

end OAI.SKFluctuations.Cavity
