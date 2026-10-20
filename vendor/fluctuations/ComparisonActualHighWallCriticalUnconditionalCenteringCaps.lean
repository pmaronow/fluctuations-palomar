module

public import ComparisonActualHighWallCriticalFullThermalAlong
public import ComparisonActualHighWallCriticalCenteringL2Along
public import ComparisonActualHighWallCriticalScalarCDFCaps

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 18000000

namespace ActualHighWallOverlapMinimum

theorem actual_high_wall_critical_centering_l2_along
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hCt : 0 ≤ Ct) (hD : 0 < D)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (hxlim : Tendsto (fun n=>(M n).xs) atTop (𝓝 0))
    (hsRatio : Tendsto (fun n=>(M n).data.s/(M n).xs) atTop (𝓝 0)) :
    ∀C : ℝ,1≤C→Tendsto (fun n=>
      (∫u in 0..C*(M n).xs,
        (orderedPathS (dim n+1) (M n).bf (M n).hf u-
          (M n).data.wallRadius (M n).alpha u)^2)/(M n).xs^3)
      atTop (𝓝 0) := by
  intro C hC
  have hdlim : Tendsto (fun n=>(M n).data.d) atTop (𝓝 0) :=
    hxlim.congr' (Eventually.of_forall fun n=>hfixed n)
  have hsRatioD : Tendsto (fun n=>(M n).data.s/(M n).data.d) atTop (𝓝 0) :=
    hsRatio.congr' (Eventually.of_forall fun n=>by rw [hfixed n])
  have HthermalD := actual_high_wall_critical_full_thermal_tendsto_zero_along
    (C:=C) (zero_lt_one.trans_le hC) hm hdelta hroom hcl hcu hAz hC0 hCt hD
    dim hdim M hfixed hdlim hsRatioD
  have Hthermal : Tendsto (fun n=>
      (∫u in 0..C*(M n).xs,
        orderedPathB (dim n+1) (M n).bf (M n).hf u-
          (orderedPathS (dim n+1) (M n).bf (M n).hf u)^2)/(M n).xs^3)
      atTop (𝓝 0) := by
    convert HthermalD using 1
    ext n
    rw [hfixed n]
  exact actual_high_wall_critical_centering_l2_of_thermal_along
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M C hC hfixed hxlim hsRatio Hthermal

theorem actual_high_wall_critical_scalar_cdf_caps_along
    {m delta cl cu Az C0 Ct D Bclock T0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hCt : 0 ≤ Ct) (hD : 0 < D) (hT0 : 0 < T0)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (hxlim : Tendsto (fun n=>(M n).xs) atTop (𝓝 0))
    (hsRatio : Tendsto (fun n=>(M n).data.s/(M n).xs) atTop (𝓝 0))
    (hT : ∀n,T0≤(M n).data.T) :
    ∀R : ℝ,0<R→∃A : ℝ,0≤A ∧ ∀ᶠn in atTop,
      ((M n).data.scalarMassProfile (M n).alpha).val ((M n).xs*R)≤A*(M n).xs := by
  exact actual_high_wall_critical_scalar_cdf_caps_of_centering_along
    hcl hcu hAz hT0 dim M hfixed hxlim hT
      (actual_high_wall_critical_centering_l2_along hm hdelta hroom hcl hcu hAz
        hC0 hCt hD dim hdim M hfixed hxlim hsRatio)

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
