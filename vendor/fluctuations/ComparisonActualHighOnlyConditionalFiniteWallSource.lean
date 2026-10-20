module

public import ComparisonActualHighOnlyConditionalWallDoubleOrdinaryError
public import ComparisonActualHighOnlyConditionalFiniteGeometry
public import ComparisonActualHighOnlyConditionalErrorIntegralBounds

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 14000000
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
attribute [local instance] Classical.propDecidable
namespace ActualHighOnlyOverlapMinimum
variable {n:ℕ} {m delta cl cu Az C0 Ct D Bclock:ℝ}
variable {a:ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}

abbrev Potential.ConditionalWallCap (P:a.Potential) (F:Finset (ordConnectedSection P.negativeSet)):=
  {t:F // 0 < (P.capFamily F t).left ∧ a.alpha.val.val (P.capFamily F t).right ≤ min (32*a.data.s) 1}

def Potential.conditionalWallCapFamily (P:a.Potential) (F:Finset (ordConnectedSection P.negativeSet))
    (t:P.ConditionalWallCap F):ShiftedCapInterval a P:=P.capFamily F t.val

def Potential.conditionalWallSupport (P:a.Potential) (F:Finset (ordConnectedSection P.negativeSet)):Set ℝ:=
  P.retainedSupport (P.conditionalWallCapFamily F) 0 (a.R (min (32*a.data.s) 1))

theorem Potential.conditionalWallSupport_measurable (P:a.Potential) (F:Finset (ordConnectedSection P.negativeSet)) :
    MeasurableSet (P.conditionalWallSupport F):=
  P.retainedSupport_measurable _ le_rfl (a.shiftedNativeModel.R_bounds _).2

theorem eventually_actual_conditional_finite_wall_error_high_only
    (ell:ℕ) (hell:2 < ell) (Bclock:ℝ)
    (hm:0 < m) (hdelta:0 < delta) (hroom:delta < 3*m)
    (hcl:0 < cl) (hcu:0 < cu) (hAz:0 ≤ Az) (hC0:0 < C0) (hCt:0 ≤ Ct)
    (horder:(delta+2)/((ell:ℝ)-1) ≤ delta) :
    ∀ᶠn:ℕ in atTop,∀(a:ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
      (hs:a.data.s ≤ 1/4) (hsxs:a.data.s ≤ a.xs) (hUs:a.data.U ≤ a.data.s),
      a.data.d ≤ 1 → a.xs=comparisonConditionalScale a.data.N delta a.data.E a.lam →
      a.xs+1 ≤ a.data.N → ∀(P:a.Potential),
      NativePullbackClockRegularity a.alpha.val.val a.b a.h 0 1 →
      ∀F:Finset (ordConnectedSection P.negativeSet),
      (∫u in 0..1,(P.conditionalWallSupport F).indicator (fun _=>(1:ℝ)) (a.R u)*a.comparisonErrorDensity u) ≤
        a.data.N^(7*delta)*a.data.E := by
  filter_upwards [eventually_actual_conditional_wall_double_ordinary_error_high_only ell hell Bclock
    (D:=D) hm hdelta hroom hcl hcu hAz hC0 hCt horder] with n hn
  intro a hs hsxs hUs hd1 hxs hy P hclock F
  let c:=P.conditionalWallCapFamily F
  have hwhole:∀t,∀r∈Ioo (c t).left (c t).right,wholeUnit P.negativeSet r=Ioo (c t).left (c t).right:=by
    intro t r hr
    exact P.capFamily_wholeUnit F t.val hr
  have hcontacts:∀t,P.H (c t).left=0 ∧ (P.H (c t).right=0 ∨ (c t).right=1):=by
    intro t
    have H:=P.capFamily_contacts F t.val
    refine ⟨?_,H.2⟩
    rcases H.1 with H|H
    · exact H
    · exact False.elim (t.property.1.ne' H)
  have hdisjoint:Pairwise (fun t u=>Disjoint (Ioo (c t).left (c t).right) (Ioo (c u).left (c u).right)):=by
    intro t u htu
    exact P.capFamily_disjoint F (Subtype.val_injective.ne htu)
  exact hn a hs hsxs hUs hd1 hxs hy P _ c hwhole hcontacts hdisjoint hclock
    (fun t=>t.property.1) (fun t=>t.property.2)

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
