module

public import ComparisonSignedCavityActualSitePairAveraging
public import CavityEndpointLaw

@[expose] public section

noncomputable section
set_option maxHeartbeats 14000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S V : Type} [Fintype S] [Fintype V]

omit [Fintype S] [Fintype V] in
theorem relabelAssignment_conjugate_gauge
    (e : S≃V) (π : V≃V) {as : List PositiveMass}
    (T : ClockTree S as) (σ : T.Assignment) :
    T.relabelAssignment e (T.assignmentGauge ((e.trans π).trans e.symm) σ)=
      (T.relabelSpin e).assignmentGauge π (T.relabelAssignment e σ) := by
  induction T with
  | leaf=>exact e.apply_symm_apply _
  | step b T ih=>exact ih σ
  | fork T R ihT ihR=>
    change (T.relabelAssignment e (T.assignmentGauge ((e.trans π).trans e.symm) σ.1),
      R.relabelAssignment e (R.assignmentGauge ((e.trans π).trans e.symm) σ.2))=_
    rw [ihT,ihR]
    rfl

end OAI.SKFluctuations.Hierarchy.ClockTree
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree

def nativeFullSiteSpinPerm {n : ℕ} (π : Fin (n+1)≃Fin (n+1)) :
    (Spin n×Bool)≃(Spin n×Bool) :=
  (((spinEquiv n).trans (nativeSiteSpinPerm π)).trans (spinEquiv n).symm)

theorem fullEndpointExpect_eq_physicalCompleted (n U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : (T.relabelSpin (spinEquiv n)).Assignment→ℝ) :
    T.disorderExpect (fullWeight n) (fullFeature n) 0
      (cavityPath n U 1 1 (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) b h K)
      (fun σ=>P (T.relabelAssignment (spinEquiv n) σ)) 0=
    (T.relabelSpin (spinEquiv n)).disorderExpect (uniformWeight (n+1)) (finiteFeature (n+1))
      0 (physicalCompletedClock (n+1) b h) P 0 :=
  (fullEndpointExpect_eq_nullCompleted n U b h K T P).trans
    (completed_scalar_expect_eq (n+1) (T.relabelSpin (spinEquiv n)) ho b h P)

theorem native_actual_full_site_permutation_law
    {n : ℕ} (π : Fin (n+1)≃Fin (n+1)) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (U : ℕ) (b h K : ℕ→ℝ) (P : T.Assignment→ℝ) :
    T.disorderExpect (fullWeight n) (fullFeature n) 0
      (cavityPath n U 1 1 (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) b h K) P 0=
    T.disorderExpect (fullWeight n) (fullFeature n) 0
      (cavityPath n U 1 1 (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) b h K)
      (fun σ=>P (T.assignmentGauge (nativeFullSiteSpinPerm π) σ)) 0 := by
  let e:=T.relabelAssignment (spinEquiv n)
  let R:=T.relabelSpin (spinEquiv n)
  let P':=fun σ : R.Assignment=>P (e.symm σ)
  have HL:=fullEndpointExpect_eq_physicalCompleted n U b h K T ho P'
  have HR:=fullEndpointExpect_eq_physicalCompleted n U b h K T ho
    (fun σ=>P' (R.assignmentGauge (nativeSiteSpinPerm π) σ))
  have H:=native_actual_site_permutation_law π R ho b h P'
  rw [←HL,←HR] at H
  have HF (σ : T.Assignment) :
      P' (R.assignmentGauge (nativeSiteSpinPerm π) (e σ))=
        P (T.assignmentGauge (nativeFullSiteSpinPerm π) σ) := by
    rw [←T.relabelAssignment_conjugate_gauge]
    exact congrArg P (e.symm_apply_apply _)
  dsimp only [e] at HF
  simp_rw [HF] at H
  simpa only [P',e,Equiv.symm_apply_apply] using H

end OAI.SKFluctuations.Cavity
