module

public import ComparisonActualHighWallCriticalRadiusCDFCaps
public import ComparisonActualHighWallCriticalScalarCalibrationAlong
public import ComparisonLocalTemperatureScalarGlobalCompactness

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 12000000

theorem actual_high_wall_critical_joint_scalar_radius_compactness_of_calibration
    {m delta cl cu Az C0 Ct D Bclock T c R0 B : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hCt : 0 ≤ Ct) (hD : 0 < D) (hT : 0 < T)
    (hc : 0 < c) (hR0 : 0 < R0) (hB : 0 ≤ B)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (hTeq : ∀n,(M n).data.T=T)
    (hxlim : Tendsto (fun n=>(M n).xs) atTop (𝓝 0))
    (hsRatio : Tendsto (fun n=>(M n).data.s/(M n).xs) atTop (𝓝 0))
    (hcal : ∀ᶠn in atTop,∃q,c*(M n).xs≤q ∧ q≤R0*(M n).xs ∧
      |scalarCovarianceResponse hT ((M n).data.scalarMassProfile (M n).alpha) (T*q)-q|≤
        B*(M n).xs^3) :
    ∃(beta radiusLimit : boundedMassProfiles) (U V : NonnegativeMassProfile)
      (sigma : ℝ) (phi : ℕ→ℕ),
      StrictMono phi ∧
      Tendsto (fun n=>(M (phi n)).data.scalarMassProfile (M (phi n)).alpha)
        atTop (𝓝 beta) ∧
      Tendsto (fun n=>(M (phi n)).actualRadiusMassProfile) atTop (𝓝 radiusLimit) ∧
      (∀t : ℝ,Tendsto (fun n=>
        ((M (phi n)).data.scalarMassProfile (M (phi n)).alpha).val
          ((M (phi n)).xs*t)/(M (phi n)).xs) atTop (𝓝 (U.mass t))) ∧
      (∀t : ℝ,Tendsto (fun n=>
        (M (phi n)).actualRadiusMassProfile.val
          ((M (phi n)).xs*t)/(M (phi n)).xs) atTop (𝓝 (V.mass t))) ∧
      (∀R : ℝ,0<R→
        ContinuousOn (comparisonLocalScalarLimitSlope hT T beta U sigma) (Icc (0:ℝ) R) ∧
        TendstoUniformlyOn (fun n=>comparisonLocalScalarSlope hT T
          ((M (phi n)).data.scalarMassProfile (M (phi n)).alpha) (M (phi n)).xs)
          (comparisonLocalScalarLimitSlope hT T beta U sigma) atTop (Icc (0:ℝ) R) ∧
        TendstoUniformlyOn (fun n=>comparisonLocalScalarResponse hT T
          ((M (phi n)).data.scalarMassProfile (M (phi n)).alpha) (M (phi n)).xs)
          (comparisonLocalScalarLimitResponse hT T beta U sigma) atTop (Icc (0:ℝ) R)) := by
  let alpha : ℕ→boundedMassProfiles := fun n=>(M n).data.scalarMassProfile (M n).alpha
  let radius : ℕ→boundedMassProfiles := fun n=>(M n).actualRadiusMassProfile
  let x : ℕ→ℝ := fun n=>(M n).xs
  have hcap : ∀R : ℝ,0<R→∃A : ℝ,0≤A ∧
      ∀ᶠn in atTop,(alpha n).val ((T/T)*(x n*R))≤A*x n := by
    intro R hR
    obtain ⟨A,hA,HA⟩ := ActualHighWallOverlapMinimum.actual_high_wall_critical_scalar_cdf_caps_along
      hm hdelta hroom hcl hcu hAz hC0 hCt hD hT dim hdim M hfixed hxlim hsRatio
      (fun n=>by rw [hTeq n]) R hR
    refine ⟨A,hA,?_⟩
    simpa only [alpha,x,div_self hT.ne',one_mul] using HA
  have hradiusCap : ∀R : ℝ,0<R→∃A : ℝ,
      ∀ᶠn in atTop,(radius n).val (x n*R)/x n≤A := by
    intro R hR
    simpa only [radius,x] using
      ActualHighWallOverlapMinimum.actual_high_wall_critical_radius_cdf_caps_along
        hcu hAz dim M hxlim R hR
  have hright : ∀n q,ContinuousWithinAt (alpha n).val (Ici q) q := by
    intro n q
    exact quantileMassProfile_right_continuous _ _ _
  obtain ⟨beta,radiusLimit,U,V,sigma,phi,hphi,ha,hr,hU,hV,Hlimits⟩:=
    comparison_local_joint_scalar_radius_compactness hT hT hR0 hc hB alpha radius x
      hxlim (fun n=>(M n).hxs) hright hcap hradiusCap hcal
  refine ⟨beta,radiusLimit,U,V,sigma,phi,hphi,ha,hr,?_,hV,?_⟩
  · intro t
    simpa only [alpha,x,div_self hT.ne',one_mul] using hU t
  · intro R hR
    convert Hlimits R hR using 1 <;> rfl

end OAI.SKFluctuations.LaplaceWindowFormalization
