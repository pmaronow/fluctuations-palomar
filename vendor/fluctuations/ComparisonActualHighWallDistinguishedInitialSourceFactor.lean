module

public import ComparisonActualHighWallSourceMoments
public import ComparisonSignedCavityActualResourceCanonicalShape

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
namespace ActualNaturalBoundaryShape
variable {n a : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}

def withoutDistinguishedInitialFactor (G : ActualNaturalBoundaryShape n (a+1) T)
    (e0 : Fin (a+1)) : ActualNaturalBoundaryShape n a T where
  α e := G.α (e0.succAbove e)
  β e := G.β (e0.succAbove e)
  i e := G.i (e0.succAbove e)
  j e := G.j (e0.succAbove e)
  distinct e := G.distinct (e0.succAbove e)
  lowInGrid e := G.lowInGrid (e0.succAbove e)

theorem without_distinguished_initial_factor_low_mass
    (G : ActualNaturalBoundaryShape n (a+1) T) (e0 : Fin (a+1)) (e : Fin a) :
    (G.withoutDistinguishedInitialFactor e0).sourceLowMass e=G.sourceLowMass (e0.succAbove e) := rfl

theorem canonical_high_wall_product_distinguished_initial_factor
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNaturalBoundaryShape n (a+1) T) (forms : Fin (a+1)→NativeSourceFactorForm)
    (e0 : Fin (a+1)) (hform : forms e0=.centered) (i : ℕ)
    (hcut : T.splitIndex (G.i e0) (G.j e0)=i) (σ : T.Assignment) :
    (G.canonicalHighWallSource M forms).product σ=
      (deletedOverlap n (joinSpin (T.atSlot σ (G.j e0))) (joinSpin (T.atSlot σ (G.i e0)))-
        nativePhysicalResourceCenter n M.bf M.hf as i)*
      ((G.withoutDistinguishedInitialFactor e0).canonicalHighWallSource M
        (fun e=>forms (e0.succAbove e))).product σ := by
  unfold product fullBoundaryAffineProduct
  rw [Fin.prod_univ_succAbove _ e0]
  congr 1
  · simp only [canonicalHighWallSource,canonicalPhysicalSource,sourceLowMass,hcut,hform,
      NativeSourceFactorForm.intercept,NativeSourceFactorForm.slope,nativePhysicalResourceCenter,
      fullBoundaryAffineFactor,one_mul]
    ring

end ActualNaturalBoundaryShape

theorem actual_resource_distinguished_initial_factor_cut
    {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (P : NativeResourceMonomial i star T) (hi : i ≤ star) (hstar : star < as.length)
    (e0 : Fin P.factors.length) (hinitial : (P.factors.get e0).1=.initial) :
    T.splitIndex ((nativeActualResourceCanonicalShape P hi hstar).i e0)
      ((nativeActualResourceCanonicalShape P hi hstar).j e0)=i := by
  have HC:=P.cuts (P.factors.get e0) (List.get_mem _ e0)
  simp only [nativeActualResourceCanonicalShape]
  rw [T.splitIndex_symm]
  simpa only [hinitial,NativeResourceMark.cut] using HC
end OAI.SKFluctuations.Cavity
