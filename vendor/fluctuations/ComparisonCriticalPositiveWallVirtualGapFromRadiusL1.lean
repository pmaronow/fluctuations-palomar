module

public import ComparisonCriticalPositiveWallScalarClosureOpenGap
public import ComparisonCriticalPositiveWallVirtualGapNoMassPremise

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology
set_option maxHeartbeats 12000000

theorem critical_positive_wall_virtual_gap_of_physical_radius_L1
    {m delta cl cu Az C0 Ct D Bclock Tloc T : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hmargin : 2*delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hCt : 0 ≤ Ct) (hD : 0 < D)
    (hTloc : 0 < Tloc) (hT : 0 < T)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (hTeq : ∀n,(M n).data.T=T)
    (hx : Tendsto (fun n=>(M n).xs) atTop (𝓝 0))
    (hsRatio : Tendsto (fun n=>(M n).data.s/(M n).xs) atTop (𝓝 0))
    (alpha : ℕ→boundedMassProfiles)
    (V : NonnegativeMassProfile) (hnegative : ∀r<0,V.mass r=0)
    (hCDF : ∀r,Tendsto (fun n=>(M n).alpha.val.val ((M n).xs*r)/(M n).xs)
      atTop (𝓝 (V.mass r)))
    (hRadius : ∀r,Tendsto (fun n=>(M n).actualRadiusMassProfile.val
      ((M n).xs*r)/(M n).xs) atTop (𝓝 (V.mass r)))
    (s : NonnegativeMassProfile)
    (hspin : ∀r,Tendsto (fun n=>(M n).actualScaledRadiusSpin r)
      atTop (𝓝 (s.mass r)))
    (g : ℝ→ℝ)
    (hG : ∀Q>0,TendstoUniformlyOn (fun n=>comparisonRescaledScalarResponse
      (scalarCovarianceResponse hTloc (alpha n)) T (M n).xs) g atTop (Icc (0:ℝ) Q))
    (hgc : ∀Q>0,ContinuousOn g (Icc (0:ℝ) Q))
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hasupport : a∈comparisonIncrementSupport V.mass)
    (hbsupport : b∈comparisonIncrementSupport V.mass)
    (hgap : ∀r∈Ioo a b,r∉comparisonIncrementSupport V.mass)
    (hL1 : ∀u∈Ioo a b,∀v∈Ioo a b,u<v→
      Tendsto (fun n=>(∫r in Ioo ((M n).xs*u) ((M n).xs*v),
        |(M n).radiusS r-scalarCovarianceResponse hTloc (alpha n)
          (actualMixedClock (dim n+1) (M n).bf (M n).hf
            ((M n).alpha.val.val r))|)/(M n).xs^4) atTop (𝓝 0)) :
    Nonempty (ComparisonVirtualGapData g a b) := by
  have hclosure := critical_positive_wall_scalar_closure_open_gap_of_physical_radius_L1
    hm hdelta hmargin hcl hcu hAz hC0 hCt hTloc hT dim hdim M hfixed hTeq hx
    alpha V.mass hCDF s hspin g hG hgc ha hL1
  exact critical_positive_wall_virtual_gap_from_Eq19_and_scalar_closure
    hm hdelta hmargin hcl hcu hAz hC0 hCt hD hT dim hdim M hfixed hx
    hsRatio V hnegative hCDF hRadius s hspin g ha hab
    (show b<b+1 by linarith) hasupport hbsupport hgap hclosure

end OAI.SKFluctuations.LaplaceWindowFormalization
