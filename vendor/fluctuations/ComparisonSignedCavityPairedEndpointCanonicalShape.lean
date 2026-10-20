module

public import ComparisonSignedCavityActualGammaPairedCanonicalSource

@[expose] public section

noncomputable section
set_option maxHeartbeats 12000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

def nativeRestEndpointShape {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (b s : T.Slot) (hbs : b≠s) :
    ActualNaturalBoundaryShape n 1 T where
  α:=fun _=>0
  β:=fun _=>1
  i:=fun _=>b
  j:=fun _=>s
  distinct:=fun _=>hbs
  lowInGrid:=fun _=>T.splitIndex_le_clockLength b s

theorem native_rest_endpoint_canonical_difference
    {n : ℕ} {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (b s e : T.Slot) (hbs : b≠s) (hbe : b≠e)
    (hlow : T.splitIndex b s=T.splitIndex b e)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (σ : T.cavityLeft.Assignment) :
    let G:=nativeRestEndpointShape T b s hbs
    (G.canonicalMinimumSource M (fun _=>NativeSourceFactorForm.centered)).restProduct σ-
      ((G.retarget (fun _=>e) (fun _=>hbe)).canonicalMinimumSource M
        (fun _=>NativeSourceFactorForm.centered)).restProduct σ=
      nativeRestEndpointDifference n T b s e σ := by
  dsimp only
  simp only [ActualNaturalBoundaryShape.restProduct,Fin.prod_univ_one,
    ActualNaturalBoundaryShape.canonicalMinimumSource,ActualNaturalBoundaryShape.retarget,
    ActualNaturalBoundaryShape.sourceLowMass,nativeRestEndpointShape,
    NativeSourceFactorForm.intercept,NativeSourceFactorForm.slope,
    fullBoundaryAffineFactor,nativeRestEndpointDifference,hlow,one_mul]
  have Hsymm (u v : Spin (n+1)) : deletedOverlap n u v=deletedOverlap n v u := by
    simp only [deletedOverlap,mul_comm]
  rw [Hsymm (joinSpin (_,false)) (joinSpin (_,false))]
  ring_nf
  simp only [deletedOverlap,mul_comm]

end OAI.SKFluctuations.Cavity
