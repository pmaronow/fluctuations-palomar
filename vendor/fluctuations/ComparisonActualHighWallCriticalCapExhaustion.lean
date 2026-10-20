module

public import ComparisonActualHighWallCriticalFinitePhysicalThermal

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
namespace ActualHighWallOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem eventually_actual_high_wall_critical_cap_contact_thermal_rate
    {c C : ℝ} (hc : 0 < c) (hC : c < C)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hCt : 0 ≤ Ct) (hD : 0 < D) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (a : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock),
      a.xs=a.data.d → comparisonSmallMass a.data.N a.data.E≤c*a.data.d →
      32*a.data.s<c*a.data.d → 2*a.data.N^(-(10:ℝ))<comparisonSmallMass a.data.N a.data.E →
      1≤Real.log a.data.N →
      ∀ (P : a.Potential) (A : Set ℝ),MeasurableSet A → A⊆Ioo a.data.rmin 1 →
        (∀r∈A,c*a.data.d≤a.alpha.val.val r ∧ a.alpha.val.val r≤C*a.data.d) →
      (∫u in 0..1,(A∩(P.negativeSet∪P.contactSet)).indicator (fun _=>1)
        (a.shiftedNativeModel.R u)*a.shiftedNativeModel.thermal u) ≤
        10*C*a.data.N^(-actualMassSavingExponent m delta)*a.data.d^3*
          (Nat.ceil (Real.log (1/comparisonSmallMass a.data.N a.data.E)/Real.log 2)+1)+
        (∫u in 0..min (8*a.criticalMassCoverBase) 1,a.shiftedNativeModel.thermal u) := by
  have H:=eventually_actual_high_wall_critical_finite_cap_thermal_rate
    (Bclock:=Bclock) hc hC hm hdelta hroom hcl hcu hAz hC0 hCt hD
  filter_upwards [H] with n hn
  intro a hfixed hU hstart hcutU hlog P A hA hAD hscale
  obtain ⟨F,_,_,hlim⟩:=P.cap_contact_thermal_exhaustion A hA
  apply le_of_tendsto hlim
  exact Eventually.of_forall (fun j=>hn a hfixed hU hstart hcutU hlog P (F j) A hA hAD hscale)

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
