module

public import ComparisonActualHighWallCriticalScalarLimitFromMassSource
public import ComparisonActualHighWallCriticalMassEq22FromPhysicalReadersAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 24000000

theorem actual_high_wall_critical_fixed_temperature_mass_source_from_physical_readers
    {m delta cl cu Az C0 Ct D Bclock T : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hCt : 0 ≤ Ct) (hD : 0 < D) (hT : 0 < T)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1)
      m delta cl cu Az C0 Ct D Bclock)
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (hTeq : ∀n,(M n).data.T=T)
    (hx : Tendsto (fun n=>(M n).xs) atTop (𝓝 0))
    (hsRatio : Tendsto (fun n=>(M n).data.s/(M n).xs) atTop (𝓝 0)) :
    ∀C>0,Tendsto (fun n=>
      (∫u in 0..C*(M n).xs,
        |orderedPathS (dim n+1) (M n).bf (M n).hf u-
          scalarCovarianceResponse hT
            ((M n).data.scalarMassProfile (M n).alpha)
            (actualMixedClock (dim n+1) (M n).bf (M n).hf u)|)/
        (M n).xs^4) atTop (𝓝 0) := by
  have hdlim : Tendsto (fun n=>(M n).data.d) atTop (𝓝 0) := by
    apply hx.congr'
    exact Eventually.of_forall hfixed
  have hsRatioD : Tendsto (fun n=>(M n).data.s/(M n).data.d)
      atTop (𝓝 0) := by
    simpa only [hfixed] using hsRatio
  have hGammaEq (n : ℕ) :
      scalarCovarianceResponse hT
        ((M n).data.scalarMassProfile (M n).alpha)=
      scalarCovarianceResponse (M n).data.hTpos
        ((M n).data.scalarMassProfile (M n).alpha) := by
    cases hTeq n
    rfl
  intro C hC
  have Hsource := actual_high_wall_critical_mass_Eq22_from_physical_readers_along
    hC hm hdelta hroom hcl hcu hAz hC0 hCt hD hT
    dim hdim M hfixed hdlim hsRatioD (fun n=>(hTeq n).ge)
  apply Hsource.congr'
  filter_upwards [] with n
  simp only [hfixed n,ActualHighWallOverlapMinimum.originalMassScalarResidual,hGammaEq n]

theorem exists_actual_high_wall_critical_scalar_limit_from_physical_readers
    {m delta cl cu Az C0 Ct D Bclock T : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hCt : 0 ≤ Ct) (hD : 0 < D) (hT : 0 < T)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1)
      m delta cl cu Az C0 Ct D Bclock)
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (hTeq : ∀n,(M n).data.T=T)
    (hx : Tendsto (fun n=>(M n).xs) atTop (𝓝 0))
    (hsRatio : Tendsto (fun n=>(M n).data.s/(M n).xs) atTop (𝓝 0)) :
    ∃phi : ℕ→ℕ,StrictMono phi ∧
      ∃htotal : ∀n,∀u∈Icc (0:ℝ) 1,
          ((M (phi n)).hf u:ℝ)+((M (phi n)).bf u:ℝ)≤T,
      ∃d : ActualHighWallLocalScalarLimitData hT T
        (fun n=>M (phi n)) htotal,
        d.U.mass=ᵐ[volume] d.V.mass :=
  exists_actual_high_wall_critical_scalar_limit_of_mass_source
    hm hdelta hroom hcl hcu hAz hC0 hCt hD hT
    dim hdim M hfixed hTeq hx hsRatio
    (actual_high_wall_critical_fixed_temperature_mass_source_from_physical_readers
      hm hdelta hroom hcl hcu hAz hC0 hCt hD hT
      dim hdim M hfixed hTeq hx hsRatio)

end OAI.SKFluctuations.LaplaceWindowFormalization
