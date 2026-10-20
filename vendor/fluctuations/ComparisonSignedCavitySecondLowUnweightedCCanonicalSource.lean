module

public import ComparisonSignedCavityCanonicalMarkedOldProduct
public import ComparisonSignedCavityActualRestBoundaryResampling

@[expose] public section

noncomputable section
set_option maxHeartbeats 4000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal ENNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
namespace ActualNaturalBoundaryShape
variable {n a : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}

 def consTwoLowC (G : ActualNaturalBoundaryShape n a T) (f c z : T.Slot)
    (hfc : f≠c) (hzc : z≠c) : ActualNaturalBoundaryShape n ((a+1)+1) T :=
  (G.consLowShape f c hfc).consLowShape z c hzc

 def twoLowCForms (forms : Fin a→NativeSourceFactorForm) : Fin ((a+1)+1)→NativeSourceFactorForm :=
  Fin.cases .row (Fin.cases .row forms)

 def twoLowCOldTargets (G : ActualNaturalBoundaryShape n a T) (c' : T.Slot) : Fin ((a+1)+1)→T.Slot :=
  Fin.cases c' (Fin.cases c' G.j)

 theorem consTwoLowC_canonical_restProduct
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNaturalBoundaryShape n a T) (forms : Fin a→NativeSourceFactorForm)
    (f c z : T.Slot) (hfc : f≠c) (hzc : z≠c) (τ : T.cavityLeft.Assignment) :
    ((G.consTwoLowC f c z hfc hzc).canonicalMinimumSource M (twoLowCForms forms)).restProduct τ=
      canonicalLowRestFactor M z c τ*canonicalLowRestFactor M f c τ*
        (G.canonicalMinimumSource M forms).restProduct τ := by
  unfold consTwoLowC twoLowCForms
  rw [canonical_cons_restProduct,canonical_cons_restProduct]
  ring

 theorem consTwoLowC_old_target_ne (G : ActualNaturalBoundaryShape n a T)
    (f c z c' : T.Slot) (hfc : f≠c) (hzc : z≠c) (hfc' : f≠c') (hzc' : z≠c') :
    ∀e,(G.consTwoLowC f c z hfc hzc).i e≠G.twoLowCOldTargets c' e := by
  intro e
  refine Fin.cases hzc' (fun e=>?_) e
  exact Fin.cases hfc' (fun e=>G.distinct e) e

 theorem consTwoLowC_old_target_same_low (G : ActualNaturalBoundaryShape n a T)
    (f c z c' : T.Slot) (hfc : f≠c) (hzc : z≠c)
    (Hf : T.splitIndex f c=T.splitIndex f c') (Hz : T.splitIndex z c=T.splitIndex z c') :
    ∀e,T.splitIndex ((G.consTwoLowC f c z hfc hzc).i e)
        ((G.consTwoLowC f c z hfc hzc).j e)=
      T.splitIndex ((G.consTwoLowC f c z hfc hzc).i e) (G.twoLowCOldTargets c' e) := by
  intro e
  refine Fin.cases Hz (fun e=>?_) e
  exact Fin.cases Hf (fun e=>rfl) e

 theorem consTwoLowC_retarget_eq_old (G : ActualNaturalBoundaryShape n a T)
    (f c z c' : T.Slot) (hfc : f≠c) (hzc : z≠c) (hfc' : f≠c') (hzc' : z≠c') :
    (G.consTwoLowC f c z hfc hzc).retarget (G.twoLowCOldTargets c')
      (G.consTwoLowC_old_target_ne f c z c' hfc hzc hfc' hzc')=
      G.consTwoLowC f c' z hfc' hzc' := by
  rfl

 theorem consTwoLowC_complete_old_difference
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNaturalBoundaryShape n a T) (forms : Fin a→NativeSourceFactorForm)
    (f c z c' : T.Slot) (hfc : f≠c) (hzc : z≠c) (hfc' : f≠c') (hzc' : z≠c')
    (τ : T.cavityLeft.Assignment) :
    ((G.consTwoLowC f c z hfc hzc).canonicalMinimumSource M (twoLowCForms forms)).restProduct τ-
      ((G.consTwoLowC f c' z hfc' hzc').canonicalMinimumSource M (twoLowCForms forms)).restProduct τ=
      (G.canonicalMinimumSource M forms).restProduct τ*
        (canonicalLowRestFactor M f c τ*canonicalLowRestFactor M z c τ-
          canonicalLowRestFactor M f c' τ*canonicalLowRestFactor M z c' τ) := by
  rw [consTwoLowC_canonical_restProduct,consTwoLowC_canonical_restProduct]
  ring

 theorem consTwoLowC_source_scale (x W : ℝ) (initial : Finset (Fin a)) :
    sourceMonomialScale x W (sourceConsInitial (sourceConsInitial initial))=
      W^2*sourceMonomialScale x W initial := by
  rw [source_cons_monomial,source_cons_monomial]
  ring

end ActualNaturalBoundaryShape
end OAI.SKFluctuations.Cavity
