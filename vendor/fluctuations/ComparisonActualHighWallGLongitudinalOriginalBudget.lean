module

public import ComparisonActualHighWallGRestorationOriginalBudget

public import ComparisonSignedCavityGLongitudinalOriginalBudget
public import ComparisonSignedCavityInheritedErrorTransport

@[expose] public section

noncomputable section
set_option maxHeartbeats 24000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal ENNReal
open Classical
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem eventually_actual_high_wall_canonical_longitudinal_restoration_original_budget
    (aDegree dOrder rBound : ℕ) (hd : 0 < dOrder)
    (p : ℝ) (hp : 2 < p) (hOrder : p/(p-2) ≤ (dOrder:ℝ))
    (Bclock Cmass Ccut : ℝ) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Ch Cl Cq : ℝ,0 < Ch ∧ 0 < Cl ∧ 0 < Cq ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.xs=M.data.d →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=2*M.data.T
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as),U ≤ as.length → T.leaves ≤ rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm),
          partitionPoint 0 as U ≤ Ccut*M.data.d →
          (∀e,G.sourceLowMass e ≤ Cmass*M.data.d) →
        ∀a : T.Slot,
          |nativeOriginalLongitudinalRestoration n q U b h K S T
            (G.canonicalHighWallSource M forms).product a| ≤
            ((nativeOriginalGMarkedWords T).map (fun g=>|g.coefficient| *
              nativeOriginalGWordRestorationCost g U (rBound+3) M.bf M.hf K a Mclock M.data.T p
                (Real.exp (wholeLawRowComparisonConstant (rBound+3)*(2*max Bclock 0))*Ch^aDegree*
                  M.data.d^aDegree)
                (Real.exp (wholeLawRowComparisonConstant (rBound+3)*(2*max Bclock 0))*Cl^aDegree*
                  M.data.d^aDegree) (Cq*M.data.d))).sum := by
  obtain ⟨Ch,Cl,Cq,hCh,hCl,hCq,H⟩:=
    eventually_actual_high_wall_canonical_G_word_restoration_original_budget
      (D:=D) aDegree dOrder rBound hd p hp hOrder Bclock Cmass Ccut hCmass hCcut
      hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Ch,Cl,Cq,hCh,hCl,hCq,?_⟩
  filter_upwards [H] with n hn
  intro M hwork L us hus hret hmesh
  filter_upwards [hn M hwork L us hus hret hmesh] with jGrid hgrid
  dsimp only at hgrid ⊢
  intro U T hU hT G forms hcut hmass a
  rw [native_original_longitudinal_restoration_eq_words]
  exact native_original_G_word_weighted_sum_abs_le T _ _
    (fun g _=>hgrid U T hU hT G forms hcut hmass g a)

end OAI.SKFluctuations.Cavity
