module

public import ComparisonCriticalPositiveWallGapPrimitive
public import ComparisonCriticalPositiveWallUniformGradient

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 10000000

theorem critical_positive_wall_gap_primitive_of_gradient_L1_along
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (hxs : Tendsto (fun n=>(M n).xs) atTop (𝓝 0))
    (hsRatio : Tendsto (fun n=>(M n).data.s/(M n).xs) atTop (𝓝 0))
    (V : ℝ→ℝ) (hV : Monotone V)
    (hCDF : ∀s,Tendsto (fun n=>(M n).alpha.val.val ((M n).xs*s)/(M n).xs)
      atTop (𝓝 (V s)))
    {a b B : ℝ} (ha : 0 ≤ a) (hab : a < b) (hbB : b < B)
    (hasupport : a∈comparisonIncrementSupport V)
    (hbsupport : b∈comparisonIncrementSupport V)
    (hgap : ∀r∈Ioo a b,r∉comparisonIncrementSupport V)
    (hmass : 0 < V ((a+b)/2))
    (f : ℝ→ℝ) (hf : IntegrableOn f (Icc a b))
    (hGlim : ∀s∈Ioo a b,∀t∈Ioo a b,s ≤ t →
      Tendsto (fun n=>∫r in Icc s t,|(M n).actualVirtualScaledGradient r-f r|) atTop (𝓝 0)) :
    ∃K : ℝ,1 ≤ K ∧ ∃j : ℝ→ℝ,Monotone j ∧
      (∀t∈Icc a b,j t∈Icc (1/K^2) (K^2)) ∧
      Nonempty (ComparisonPinnedGapPrimitive a b (fun t=>j t*f t)) := by
  have hB : 0 < B := ha.trans_lt (hab.trans hbB)
  obtain ⟨KG,hKG,Hgradient⟩ := eventually_critical_positive_wall_virtual_gradient_bound_along
    hm hdelta hroom hcl hcu hAz hC0 hCt hB dim hdim M hfixed hxs
  apply critical_positive_wall_gap_primitive_of_gradient_limit_along
    hdelta hcu.le hAz hC0 (by linarith) dim hdim M hxs hsRatio
    V hV hCDF ha hab hbB hasupport hbsupport hgap hmass f hf
    ⟨KG,hKG,Hgradient.mono (fun n hn t ht _=>hn t ht)⟩ hGlim

end OAI.SKFluctuations.LaplaceWindowFormalization
