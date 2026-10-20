module

public import ComparisonSignedCavityActualFreshResourceHighTaylorReadout

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 18000000

theorem native_actual_centered_resource_fresh_rest_readout
    {n : ℕ} {as : List PositiveMass} {i star U : ℕ}
    (q : ℕ→RestCoordinate n→ℝ) (b h K C : ℕ→ℝ)
    (T : ClockTree (Spin n×Bool) as) (P : NativeResourceTerm i star T)
    (ho : MassOrdered 0 as) :
    let qfull:=cutFullVariance n q U 1 1 b h K
    let g:=nativeFreshAtSlot T 0 P.live.test.target star
    let Pc:=nativeOriginalCenteredRestTest n q U b h K T (nativeActualResourceRestValue P 0 qfull 0 C)
    nativeOriginalCenteredRestTest n q U b h K g.tree
      (nativeActualResourceRestValue (P.retarget 0) 0 qfull 0 C)=fun σ=>Pc (g.restRestrict σ) := by
  let qfull:=cutFullVariance n q U 1 1 b h K
  let g:=nativeFreshAtSlot T 0 P.live.test.target star
  dsimp only
  funext σ
  let τ:=g.tree.cavityAssignment.symm (σ,assignmentOfSlots g.tree.cavityRight (fun _=>false))
  have ht : (g.tree.cavityAssignment τ).1=σ:=by
    dsimp only [τ]
    rw [Equiv.apply_symm_apply]
  have HT:=congrFun (native_actual_resource_original_centered_readout (P.retarget 0)
    0 qfull 0 C q U b h K) τ
  have HF:=native_actual_centered_fresh_resource_readout (U:=U) q b h K C T P ho τ
  dsimp only at HT HF
  rw [show (g.tree.cavityAssignment τ).1=σ from ht] at HT HF
  rw [(P.retarget 0).freeze_value (fullWeight_pos n) (fullFeature n) ho] at HF
  simpa only [qfull,g,sub_eq_add_neg] using HT.trans HF.symm

end OAI.SKFluctuations.Cavity
