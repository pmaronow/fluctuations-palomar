module

public import ComparisonCriticalPositiveWallGradientL1FromEq19
public import ComparisonCriticalPositiveWallGapFromL1

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology
set_option maxHeartbeats 10000000

theorem critical_positive_wall_gap_primitive_from_Eq19_along
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hmargin : 2*delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (hxs : Tendsto (fun n=>(M n).xs) atTop (𝓝 0))
    (hsRatio : Tendsto (fun n=>(M n).data.s/(M n).xs) atTop (𝓝 0))
    (V : ℝ→ℝ) (hV : Monotone V)
    (hCDF : ∀r,Tendsto (fun n=>(M n).alpha.val.val ((M n).xs*r)/(M n).xs)
      atTop (𝓝 (V r)))
    (s : NonnegativeMassProfile)
    (hspin : ∀r,Tendsto (fun n=>(M n).actualScaledRadiusSpin r)
      atTop (𝓝 (s.mass r)))
    {a b B : ℝ} (ha : 0 ≤ a) (hab : a < b) (hbB : b < B)
    (hasupport : a∈comparisonIncrementSupport V)
    (hbsupport : b∈comparisonIncrementSupport V)
    (hgap : ∀r∈Ioo a b,r∉comparisonIncrementSupport V)
    (hmass : 0 < V ((a+b)/2)) :
    ∃K : ℝ,1 ≤ K ∧ ∃j : ℝ→ℝ,Monotone j ∧
      (∀t∈Icc a b,j t∈Icc (1/K^2) (K^2)) ∧
      Nonempty (ComparisonPinnedGapPrimitive a b (fun t=>j t*
        comparisonScaledStationarity (laplaceComparisonShape t)
          (laplaceComparisonSlope t) t (s.mass t))) := by
  let f := fun t=>comparisonScaledStationarity (laplaceComparisonShape t)
    (laplaceComparisonSlope t) t (s.mass t)
  have hf : IntegrableOn f (Icc a b) := by
    simpa only [f,one_mul] using
      (comparison_bounded_principal_density_integrable (L:=1) (A:=1) s
        (by norm_num) (by norm_num) ha)
  apply critical_positive_wall_gap_primitive_of_gradient_L1_along
    hm hdelta (by linarith only [hmargin,hdelta]) hcl hcu hAz hC0 hCt
    dim hdim M hfixed hxs hsRatio V hV hCDF ha hab hbB
    hasupport hbsupport hgap hmass f hf
  intro u hu v hv huv
  exact critical_positive_wall_gradient_L1_from_Eq19_on_gap_along
    hm hdelta hmargin hcl hcu hAz hC0 hCt dim hdim M hfixed hxs
    V hV hCDF s hspin ha hab hgap hmass hu hv huv

end OAI.SKFluctuations.LaplaceWindowFormalization
