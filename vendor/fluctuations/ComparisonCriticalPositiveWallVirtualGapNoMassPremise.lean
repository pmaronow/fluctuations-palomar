module

public import ComparisonCriticalPositiveWallVirtualGapFromEq19Closure
public import ComparisonGlobalProfileRigidity

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology

theorem critical_positive_wall_virtual_gap_from_Eq19_and_scalar_closure
    {m delta cl cu Az C0 Ct D Bclock T : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hmargin : 2*delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hCt : 0 ≤ Ct) (hD : 0 < D) (hT : 0 < T)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (hxs : Tendsto (fun n=>(M n).xs) atTop (𝓝 0))
    (hsRatio : Tendsto (fun n=>(M n).data.s/(M n).xs) atTop (𝓝 0))
    (V : NonnegativeMassProfile)
    (hnegative : ∀t<0,V.mass t=0)
    (hCDF : ∀r,Tendsto (fun n=>(M n).alpha.val.val ((M n).xs*r)/(M n).xs)
      atTop (𝓝 (V.mass r)))
    (hRadius : ∀r,Tendsto (fun n=>(M n).actualRadiusMassProfile.val
      ((M n).xs*r)/(M n).xs) atTop (𝓝 (V.mass r)))
    (s : NonnegativeMassProfile)
    (hspin : ∀r,Tendsto (fun n=>(M n).actualScaledRadiusSpin r)
      atTop (𝓝 (s.mass r)))
    (g : ℝ→ℝ)
    {a b B : ℝ} (ha : 0 ≤ a) (hab : a < b) (hbB : b < B)
    (hasupport : a∈comparisonIncrementSupport V.mass)
    (hbsupport : b∈comparisonIncrementSupport V.mass)
    (hgap : ∀r∈Ioo a b,r∉comparisonIncrementSupport V.mass)
    (hclosure : ∀ᵐt∂volume.restrict (Ioo a b),
      g (s.mass t)=laplaceComparisonShape t/T*(s.mass t-t)) :
    Nonempty (ComparisonVirtualGapData g a b) := by
  have hmass : 0 < V.mass ((a+b)/2) :=
    comparison_increment_support_positive_cdf_after V.monotone hnegative hasupport
      (by linarith)
  exact critical_positive_wall_virtual_gap_from_Eq19_and_scalar_closure_along
    hm hdelta hmargin hcl hcu hAz hC0 hCt hD hT dim hdim M hfixed hxs hsRatio
    V.mass V.monotone hCDF hRadius s hspin g ha hab hbB hasupport hbsupport
    hgap hmass hclosure

end OAI.SKFluctuations.LaplaceWindowFormalization
