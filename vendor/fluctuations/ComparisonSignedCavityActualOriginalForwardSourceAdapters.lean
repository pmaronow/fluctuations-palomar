module

public import ComparisonSignedCavityActualOriginalForwardSourceContraction
public import ComparisonSignedCavityActualOriginalForwardLeadingContraction
public import ComparisonSignedCavityActualOriginalLowOrientation
public import ComparisonSignedCavityActualOriginalGammaLowOrientation

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem native_original_fresh_reverse_eq_partner_G_source
    (n : ℕ) (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ)
    (x : FullCoordinate n→ℝ) (U : ℕ) (K b C : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (s : T.Slot) (star : ℕ) (P : T.Assignment→ℝ)
    (A : (Spin n×Bool)→(Spin n×Bool)→ℝ) :
    let g:=nativeFreshAtSlot T 0 s star
    nativeOriginalConnectedLowReverse n v q x U K b C g.tree (fun σ=>P (g.restrict σ))
      g.mark (g.embed s) A=
    nativeOriginalFreshPartnerGSource n v q x U K b C T s star (fun σ c d=>P σ*A c d) := by
  dsimp only
  unfold nativeOriginalConnectedLowReverse nativeOriginalFreshPartnerGSource
  dsimp only
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  simp only [←List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro r hr
  rw [fullScalarCutGamma_marked_preserves p.tree ho U K _ _ r hr]
  ring

theorem native_original_fresh_gamma_forward_eq_partner_leading_source
    (n : ℕ) (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ)
    (x : FullCoordinate n→ℝ) (U : ℕ) (K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (s : T.Slot) (star : ℕ) (P : T.Assignment→ℝ)
    (A : (Spin n×Bool)→(Spin n×Bool)→ℝ) :
    let g:=nativeFreshAtSlot T 0 s star
    nativeOriginalGammaLowForward n v q x U K g.tree (fun σ=>P (g.restrict σ))
      (g.embed s) g.mark A=
    nativeOriginalFreshPartnerLeadingSource n v q x U K T s star (fun σ c d=>P σ*A c d) := by
  dsimp only
  unfold nativeOriginalGammaLowForward nativeOriginalGammaWeightedExpectation
    nativeOriginalFreshPartnerLeadingSource
  dsimp only
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  simp only [←List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro r hr
  rw [fullScalarCutGamma_marked_preserves p.tree ho U K _ _ r hr]
  ring

theorem native_original_fresh_forward_G_eq_partner_L_response
    (n : ℕ) (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ)
    (x : FullCoordinate n→ℝ) (U : ℕ) (K b C : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (s : T.Slot) (star : ℕ) (hs : star < U) (hU : U ≤ as.length)
    (hq : ∀i,Monotone (fun j=>q j i)) (hq0 : ∀i,v i ≤ q 0 i)
    (hK : ∀j,0 ≤ K j) (hKm : Monotone K) (P : T.Assignment→ℝ)
    (A : (Spin n×Bool)→(Spin n×Bool)→ℝ) (hA : ∀σ τ,A σ τ=A τ σ) :
    let g:=nativeFreshAtSlot T 0 s star
    nativeOriginalConnectedLowForward n v q x U K b C g.tree (fun σ=>P (g.restrict σ))
      g.mark (g.embed s) A=
    nativeOriginalFreshPartnerLResponse n v q x U K b C T s star (fun σ c d=>P σ*A c d) := by
  dsimp only
  rw [native_original_connected_low_orientations_equal n v q x U K b C _ ho _ _ _ A hA hU
      (by rw [nativeFreshAtSlot_split,T.splitIndex_self,Nat.min_eq_left (hs.le.trans hU)];exact hs),
    native_original_fresh_reverse_eq_partner_G_source n v q x U K b C T ho s star P A]
  exact native_original_fresh_forward_G_source_eq_L_response n v q x U K b C T ho s star hs hU
    hq hq0 hK hKm _

theorem native_original_fresh_gamma_forward_eq_chi_response
    (n : ℕ) (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ)
    (x : FullCoordinate n→ℝ) (U : ℕ) (K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (s : T.Slot) (star : ℕ) (hs : star < U) (hU : U ≤ as.length)
    (P : T.Assignment→ℝ) (A : (Spin n×Bool)→(Spin n×Bool)→ℝ) :
    let g:=nativeFreshAtSlot T 0 s star
    nativeOriginalGammaLowForward n v q x U K g.tree (fun σ=>P (g.restrict σ))
      (g.embed s) g.mark A=
    (scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0*
      nativeOriginalFreshPartnerLeadingResponse n v q x U K T s star (fun σ c d=>P σ*A c d) := by
  dsimp only
  rw [native_original_fresh_gamma_forward_eq_partner_leading_source n v q x U K T ho s star P A]
  exact native_original_fresh_forward_leading_source_eq_chi_response n v q x U K T ho s star hs hU _

end OAI.SKFluctuations.Cavity
