module

public import ComparisonActualHighWallCriticalClockLawFromCaps
public import ComparisonActualHighWallCriticalClockRadiusL1Along
public import ComparisonActualHighWallCriticalRadiusCDFCaps
public import ComparisonActualHighWallCriticalUnconditionalCenteringCaps

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 18000000

namespace ActualHighWallOverlapMinimum

theorem actual_high_wall_critical_scalar_radius_laws_ae_along
    {m delta cl cu Az C0 Ct D Bclock T : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hCt : 0 ≤ Ct) (hD : 0 < D) (hT : 0 < T)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (hTeq : ∀n,(M n).data.T=T)
    (hxlim : Tendsto (fun n=>(M n).xs) atTop (𝓝 0))
    (hsRatio : Tendsto (fun n=>(M n).data.s/(M n).xs) atTop (𝓝 0))
    (U V : NonnegativeMassProfile)
    (hU : ∀t : ℝ,Tendsto (fun n=>
      ((M n).data.scalarMassProfile (M n).alpha).val ((M n).xs*t)/(M n).xs)
        atTop (𝓝 (U.mass t)))
    (hV : ∀t : ℝ,Tendsto (fun n=>
      (M n).actualRadiusMassProfile.val ((M n).xs*t)/(M n).xs)
        atTop (𝓝 (V.mass t))) :
    U.mass=ᵐ[volume] V.mass := by
  let q : ℕ→ℝ→ℝ := fun n=>actualScalarClockQuantile T (dim n+1) (M n).bf (M n).hf
  let r : ℕ→ℝ→ℝ := fun n=>(M n).data.wallRadius (M n).alpha
  let x : ℕ→ℝ := fun n=>(M n).xs
  have hqb : ∀n u,u∈Icc (0:ℝ) 1 → q n u∈Icc (0:ℝ) 1 := by
    intro n
    exact actualScalarClockQuantile_bounds hT (dim n+1) (by omega)
      (M n).bf (M n).hf ((M n).data.bf_monotone (M n).alpha)
      ((M n).data.hf_monotone (M n).alpha)
      (by simpa only [hTeq n] using (M n).data.total_clock_le (M n).alpha)
  have hrb : ∀n u,u∈Icc (0:ℝ) 1 → r n u∈Icc (0:ℝ) 1 := by
    intro n u hu
    dsimp only [r]
    exact ⟨(M n).data.hrbounds.1.le.trans ((M n).data.wallRadius_bounds (M n).alpha u).1,
      ((M n).data.wallRadius_bounds (M n).alpha u).2⟩
  have hq : ∀n,MonotoneOn (q n) (Icc (0:ℝ) 1) := fun n=>
    actualScalarClockQuantile_monotone hT (dim n+1) (by omega)
      (M n).bf (M n).hf ((M n).data.bf_monotone (M n).alpha)
      ((M n).data.hf_monotone (M n).alpha)
  have hr : ∀n,MonotoneOn (r n) (Icc (0:ℝ) 1) := fun n=>
    ((M n).data.wallRadius_monotone (M n).alpha).monotoneOn _
  have hqeq n : quantileMassProfile (q n) (hqb n)=
      (M n).data.scalarMassProfile (M n).alpha := by
    simp only [q,ActualHighWallData.scalarMassProfile,actualMixedMassProfile,hTeq n]
  have hreq n : quantileMassProfile (r n) (hrb n)=
      (M n).actualRadiusMassProfile := rfl
  have hqc : ∀R : ℝ,0<R→∃A : ℝ,0≤A ∧ ∀ᶠn in atTop,
      (quantileMassProfile (q n) (hqb n)).val (x n*R)≤A*x n := by
    intro R hR
    obtain ⟨A,hA,HA⟩:=actual_high_wall_critical_scalar_cdf_caps_along
      hm hdelta hroom hcl hcu hAz hC0 hCt hD hT dim hdim M hfixed hxlim hsRatio
      (fun n=>by rw [hTeq n]) R hR
    refine ⟨A,hA,?_⟩
    simpa only [hqeq,x] using HA
  have hrc : ∀R : ℝ,0<R→∃A : ℝ,0≤A ∧ ∀ᶠn in atTop,
      (quantileMassProfile (r n) (hrb n)).val (x n*R)≤A*x n := by
    intro R hR
    obtain ⟨A,HA⟩:=actual_high_wall_critical_radius_cdf_caps_along
      hcu hAz dim M hxlim R hR
    let A':=max A 0
    refine ⟨A',le_max_right _ _,?_⟩
    filter_upwards [HA] with n hn
    have H:=mul_le_mul_of_nonneg_right (le_max_left A 0) (M n).hxs.le
    rw [hreq n]
    dsimp only [x,A']
    have Hcap := (div_le_iff₀ (M n).hxs).mp hn
    exact Hcap.trans H
  have hL1 : ∀C : ℝ,1≤C→Tendsto (fun n=>(∫u in 0..C*x n,
      |q n u-r n u|)/(x n)^2) atTop (𝓝 0) := by
    intro C hC
    have H:=actual_high_wall_critical_clock_radius_l1_along
      hm hdelta hroom hcl hcu hAz hC0 hCt hD hT dim hdim M hfixed
      (fun n=>by rw [hTeq n]) hxlim hsRatio C hC
    apply H.congr'
    filter_upwards [] with n
    dsimp only [q,r,x]
    rw [hTeq n]
  apply comparison_local_clock_laws_ae_of_cdf_caps_and_l1 q r x U.mass V.mass
    hq hr hqb hrb (fun n=>(M n).hxs) hxlim V.monotone
  · intro t
    simpa only [hqeq,x] using hU t
  · intro t
    simpa only [hreq,x] using hV t
  · exact hqc
  · exact hrc
  · exact hL1

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
