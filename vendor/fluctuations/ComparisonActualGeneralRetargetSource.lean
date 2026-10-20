module

public import ComparisonActualHighWallCanonicalRestMoments
public import ComparisonSignedCavityCanonicalRestFactorMoments

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity.ActualNaturalBoundaryShape
open Set Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped NNReal
variable {n a : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}

theorem retarget_canonicalPhysicalSource (bf hf : ℝ→ℝ≥0)
    (G : ActualNaturalBoundaryShape n a T) (f : Fin a→NativeSourceFactorForm)
    (j' : Fin a→T.Slot) (hne : ∀e,G.i e≠j' e)
    (hlow : ∀e,T.splitIndex (G.i e) (G.j e)=T.splitIndex (G.i e) (j' e)) :
    (G.retarget j' hne).canonicalPhysicalSource bf hf f=
      (G.canonicalPhysicalSource bf hf f).retarget j' hne := by
  have H : (G.retarget j' hne).sourceLowMass=G.sourceLowMass:=
    funext (G.retarget_sourceLowMass j' hne hlow)
  unfold canonicalPhysicalSource
  simp only [H]
  rfl

end OAI.SKFluctuations.Cavity.ActualNaturalBoundaryShape
