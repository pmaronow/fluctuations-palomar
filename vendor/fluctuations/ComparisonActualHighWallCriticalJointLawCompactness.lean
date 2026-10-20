module

public import ComparisonActualHighWallCriticalJointCompactness
public import ComparisonActualHighWallCriticalScalarRadiusLawAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 16000000

theorem actual_high_wall_critical_joint_compactness_with_equal_laws_of_calibration
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
      U.mass=ᵐ[volume] V.mass ∧
      (∀R : ℝ,0<R→
        ContinuousOn (comparisonLocalScalarLimitSlope hT T beta U sigma) (Icc (0:ℝ) R) ∧
        TendstoUniformlyOn (fun n=>comparisonLocalScalarSlope hT T
          ((M (phi n)).data.scalarMassProfile (M (phi n)).alpha) (M (phi n)).xs)
          (comparisonLocalScalarLimitSlope hT T beta U sigma) atTop (Icc (0:ℝ) R) ∧
        TendstoUniformlyOn (fun n=>comparisonLocalScalarResponse hT T
          ((M (phi n)).data.scalarMassProfile (M (phi n)).alpha) (M (phi n)).xs)
          (comparisonLocalScalarLimitResponse hT T beta U sigma) atTop (Icc (0:ℝ) R)) := by
  obtain ⟨beta,radiusLimit,U,V,sigma,phi,hphi,ha,hr,hU,hV,Hlimits⟩:=
    actual_high_wall_critical_joint_scalar_radius_compactness_of_calibration
      hm hdelta hroom hcl hcu hAz hC0 hCt hD hT hc hR0 hB
      dim hdim M hfixed hTeq hxlim hsRatio hcal
  let d : ℕ→ℕ:=fun n=>dim (phi n)
  let P : (n : ℕ)→ActualHighWallOverlapMinimum (d n+1) m delta cl cu Az C0 Ct D Bclock:=
    fun n=>M (phi n)
  have hdim' : Tendsto d atTop atTop := hdim.comp hphi.tendsto_atTop
  have hxlim' : Tendsto (fun n=>(P n).xs) atTop (𝓝 0) := hxlim.comp hphi.tendsto_atTop
  have hsRatio' : Tendsto (fun n=>(P n).data.s/(P n).xs) atTop (𝓝 0) :=
    hsRatio.comp hphi.tendsto_atTop
  have hUV := ActualHighWallOverlapMinimum.actual_high_wall_critical_scalar_radius_laws_ae_along
    hm hdelta hroom hcl hcu hAz hC0 hCt hD hT d hdim' P
    (fun n=>hfixed (phi n)) (fun n=>hTeq (phi n)) hxlim' hsRatio' U V hU hV
  exact ⟨beta,radiusLimit,U,V,sigma,phi,hphi,ha,hr,hU,hV,hUV,Hlimits⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
