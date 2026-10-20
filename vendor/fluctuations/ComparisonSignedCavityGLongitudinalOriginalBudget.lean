module

public import ComparisonSignedCavityGRestorationOriginalBudget

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

theorem native_original_G_word_weighted_sum_abs_le {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (F B : NativeOriginalGMarkedWord T→ℝ)
    (hF : ∀g∈nativeOriginalGMarkedWords T,|F g|≤B g) :
    |((nativeOriginalGMarkedWords T).map (fun g=>g.coefficient*F g)).sum| ≤
      ((nativeOriginalGMarkedWords T).map (fun g=>|g.coefficient| *B g)).sum := by
  have Habs : ∀L : List (NativeOriginalGMarkedWord T),
      |(L.map (fun g=>g.coefficient*F g)).sum| ≤
        (L.map (fun g=>|g.coefficient*F g|)).sum := by
    intro L
    induction L with
    | nil=>simp
    | cons g L ih=>
      simp only [List.map_cons,List.sum_cons]
      exact (abs_add_le _ _).trans (add_le_add (le_refl _) ih)
  apply (Habs _).trans
  apply List.sum_le_sum
  intro g hg
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hF g hg) (abs_nonneg _)

theorem eventually_actual_minimum_bare_canonical_longitudinal_restoration_original_budget
    (aDegree dOrder rBound : ℕ) (ha : 0 < aDegree) (hd : 0 < dOrder)
    (p : ℝ) (hp : 2 < p) (hOrder : p/(p-2) ≤ (dOrder:ℝ))
    (Bclock Temp Cmass Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Ch Cl Cq : ℝ,0 < Ch ∧ 0 < Cl ∧ 0 < Cq ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        (∀u,M.b u=Temp) → (∀u,M.h u=0) → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=4*NativeOverlapMinimum.bareSourceClockConstant cl Az D+2*Temp
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as),U ≤ as.length → T.leaves ≤ rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (W : ℝ),M.xs ≤ W →
          partitionPoint 0 as U ≤ Ccut*W →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale M.xs W initial e) →
        ∀a : T.Slot,
          |nativeOriginalLongitudinalRestoration n q U b h K S T
            (G.canonicalMinimumSource M forms).product a| ≤
            ((nativeOriginalGMarkedWords T).map (fun g=>|g.coefficient| *
              nativeOriginalGWordRestorationCost g U (rBound+3) M.bf M.hf K a Mclock Temp p
                (Real.exp (wholeLawRowComparisonConstant (rBound+3)*Mclock)*Ch^aDegree*
                  sourceMonomialScale M.xs W initial)
                (Real.exp (wholeLawRowComparisonConstant (rBound+3)*Mclock)*Cl^aDegree*
                  sourceMonomialScale M.xs W initial) (Cq*W))).sum := by
  obtain ⟨Ch,Cl,Cq,hCh,hCl,hCq,H⟩:=
    eventually_actual_minimum_bare_canonical_G_word_restoration_original_budget
      (D:=D) aDegree dOrder rBound ha hd p hp hOrder Bclock Temp Cmass Ccut hTemp hCmass hCcut
      hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Ch,Cl,Cq,hCh,hCl,hCq,?_⟩
  filter_upwards [H] with n hn
  intro M hb hh hxs L us hus hret hmesh
  filter_upwards [hn M hb hh hxs L us hus hret hmesh] with jGrid hgrid
  dsimp only at hgrid ⊢
  intro U T hU hT G forms initial W hxW hcut hmass a
  rw [native_original_longitudinal_restoration_eq_words]
  exact native_original_G_word_weighted_sum_abs_le T _ _
    (fun g _=>hgrid U T hU hT G forms initial W hxW hcut hmass g a)

end OAI.SKFluctuations.Cavity
