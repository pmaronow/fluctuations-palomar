module

public import ComparisonNativeActualWeakSelectedHistoryClocks

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 6000000
namespace NativeOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock c0 : ℝ} {N : ℕ→ℕ}

theorem ActualWeakSelectedHistoryChain.comp
    {root M : (n:ℕ)→NativeOverlapMinimum (N n+1) m delta cl cu Az C0 Ct D Bclock}
    (Hhistory : ActualWeakSelectedHistoryChain c0 root M)
    (phi : ℕ→ℕ) (hphi : Tendsto phi atTop atTop) :
    ActualWeakSelectedHistoryChain c0 (fun n=>root (phi n)) (fun n=>M (phi n)) := by
  induction Hhistory with
  | root => exact .root
  | @child P M history x hx hxunit htarget hcap hweak hd hE hb hh ih =>
    exact .child ih (fun n=>x (phi n)) (fun n=>hx (phi n)) (hphi.eventually hxunit)
      (hphi.eventually htarget) (hphi.eventually hcap) (hweak.comp hphi)
      (hphi.eventually hd) (hphi.eventually hE) (hphi.eventually hb) (hphi.eventually hh)

theorem ActualSelectedBadHistoryChain.toWeak
    {root M : (n:ℕ)→NativeOverlapMinimum (N n+1) m delta cl cu Az C0 Ct D Bclock}
    (Hhistory : ActualSelectedBadHistoryChain c0 root M) :
    ActualWeakSelectedHistoryChain c0 root M := by
  induction Hhistory with
  | root => exact .root
  | @child P M history x hx hxlim htarget hcap hweak hd hE hb hh ih =>
    exact .child ih x hx (hxlim.eventually (eventually_le_nhds zero_lt_one))
      htarget hcap hweak hd hE hb hh

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
