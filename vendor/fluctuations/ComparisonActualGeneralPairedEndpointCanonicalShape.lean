module

public import ComparisonActualGeneralGammaPairedCanonicalSource
public import ComparisonSignedCavityPairedEndpointCanonicalShape

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
namespace OAI.SKFluctuations.Cavity
open Set MeasureTheory ProbabilityTheory Filter Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped NNReal BigOperators

theorem physical_rest_endpoint_canonical_difference
    {n : ℕ} {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (b s e : T.Slot) (hbs : b≠s) (hbe : b≠e)
    (hlow : T.splitIndex b s=T.splitIndex b e)
    (bf hf : ℝ→ℝ≥0)
    (σ : T.cavityLeft.Assignment) :
    let G:=nativeRestEndpointShape T b s hbs
    (G.canonicalPhysicalSource bf hf (fun _=>NativeSourceFactorForm.centered)).restProduct σ-
      ((G.retarget (fun _=>e) (fun _=>hbe)).canonicalPhysicalSource bf hf
        (fun _=>NativeSourceFactorForm.centered)).restProduct σ=
      nativeRestEndpointDifference n T b s e σ := by
  dsimp only
  simp only [ActualNaturalBoundaryShape.restProduct,Fin.prod_univ_one,
    ActualNaturalBoundaryShape.canonicalPhysicalSource,ActualNaturalBoundaryShape.retarget,
    ActualNaturalBoundaryShape.sourceLowMass,nativeRestEndpointShape,
    NativeSourceFactorForm.intercept,NativeSourceFactorForm.slope,
    fullBoundaryAffineFactor,nativeRestEndpointDifference,hlow,one_mul]
  have Hsymm (u v : Spin (n+1)) : deletedOverlap n u v=deletedOverlap n v u := by
    simp only [deletedOverlap,mul_comm]
  rw [Hsymm (joinSpin (_,false)) (joinSpin (_,false))]
  ring_nf
  simp only [deletedOverlap,mul_comm]

end OAI.SKFluctuations.Cavity
