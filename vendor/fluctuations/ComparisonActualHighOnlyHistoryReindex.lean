module

public import ComparisonActualHighOnlyWeakComparableClocks

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Filter
open scoped Topology
set_option autoImplicit false
namespace ActualHighOnlyOverlapMinimum

theorem ActualWeakHighOnlyHistoryChain.comp
    {m delta cl cu Az C0 Ct D Bclock c0 : ℝ} {dim : ℕ→ℕ}
    {root M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}
    (H : ActualWeakHighOnlyHistoryChain c0 root M)
    (phi : ℕ→ℕ) (hphi : Tendsto phi atTop atTop) :
    ActualWeakHighOnlyHistoryChain c0 (fun n=>root (phi n)) (fun n=>M (phi n)) := by
  induction H with
  | root => exact .root
  | @child P M history x hx hxunit htarget hcap hweak hd hE hs hb hh ih =>
    exact .child ih (fun n=>x (phi n)) (fun n=>hx (phi n))
      (hphi.eventually hxunit) (hphi.eventually htarget) (hphi.eventually hcap)
      (hweak.comp hphi) (hphi.eventually hd) (hphi.eventually hE)
      (hphi.eventually hs) (hphi.eventually hb) (hphi.eventually hh)

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
