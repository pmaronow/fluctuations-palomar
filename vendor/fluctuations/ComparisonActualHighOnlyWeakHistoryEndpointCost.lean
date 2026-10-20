module

public import ComparisonActualHighOnlyWeakComparableClocks
public import ComparisonActualHighOnlyMacroscopicChildEndpoint

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option autoImplicit false

namespace ActualHighOnlyOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock c0 T : ℝ} {dim : ℕ→ℕ}

theorem ActualWeakHighOnlyHistoryChain.endpoint_cost_tendsto_zero
    {root M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1)
      m delta cl cu Az C0 Ct D Bclock}
    (H : ActualWeakHighOnlyHistoryChain c0 root M)
    (Hroot : Tendsto (fun n=>comparisonEndpointL1Cost T
      (root n).b (root n).h) atTop (𝓝 0)) :
    Tendsto (fun n=>comparisonEndpointL1Cost T
      (M n).b (M n).h) atTop (𝓝 0) := by
  induction H with
  | root => exact Hroot
  | @child P Q history x hx hxunit htarget hcap hweak hd hE hs hb hh ih =>
    have Hchanged := changed_endpoint_cost_tendsto_zero_of_weak_bounded_call_high_only
      P x hx hxunit hweak ih
    apply Filter.Tendsto.congr' ?_ Hchanged
    filter_upwards [hb,hh] with n hnb hnh
    have hbfun : (Q n).b = fun u => (P n).b u - (P n).coefficient u :=
      funext hnb
    have hhfun : (Q n).h = fun u =>
        (P n).h u + (P n).coefficient u * (P n).R u :=
      funext hnh
    simp only [hbfun,hhfun]

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
