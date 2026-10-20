module

public import ComparisonNativeActualMeanRawUpper
public import ComparisonNativeRadiusCDFLimits

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology
set_option maxHeartbeats 4000000

namespace NativeOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem mass_mean_unit_bounds {n : ℕ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {u : ℝ} (hu : u ∈ Icc (0:ℝ) 1) :
    orderedPathS (n+1) M.bf M.hf u ∈ Icc (0:ℝ) 1 := by
  refine ⟨M.mass_mean_nonneg hu,?_⟩
  by_cases hu0 : u=0
  · subst u
    simp only [orderedPathS,orderedPathPair_zero]
    norm_num
  · have had := comparisonVariableEndpoint_clocks_admissible M.context.hc M.context.hk
      M.context.hkc M.context.hm M.context.hM M.b M.h M.context.hd.ne'
      M.hlam.le M.hlb M.hb M.hh M.hh0 M.alpha
    have H := orderedPath_SK_bounds (n+1) (by omega) M.bf M.hf
      (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1)
      ⟨lt_of_le_of_ne hu.1 (Ne.symm hu0),hu.2⟩
    exact H.2.1

variable {N : ℕ → ℕ}

def actualInverseSequence
    (M : (n : ℕ) → NativeOverlapMinimum (N n+1) m delta cl cu Az C0 Ct D Bclock) :
    ComparisonShiftedInverseSequence where
  origin := fun _ => 0
  u0 := fun _ => 0
  c := fun n => (M n).context.floor
  k := fun n => (M n).context.k
  M := fun n => (M n).context.M
  hwork := fun _ => zero_le_one
  hc := fun n => (M n).context.hc
  hk := fun n => (M n).context.hk
  hkc := fun n => (M n).context.hkc
  hm := fun n => (M n).context.hm
  hM := fun n => (M n).context.hM
  alpha := fun n => (M n).alpha

theorem actualInverseSequence_radius
    (M : (n : ℕ) → NativeOverlapMinimum (N n+1) m delta cl cu Az C0 Ct D Bclock)
    (n : ℕ) : (actualInverseSequence M).radius n = (M n).R := rfl

theorem actualInverseSequence_omitted_small
    (M : (n : ℕ) → NativeOverlapMinimum (N n+1) m delta cl cu Az C0 Ct D Bclock)
    (x : ℕ → ℝ) :
    Tendsto (fun n => (actualInverseSequence M).u0 n/x n) atTop (𝓝 0) := by
  simpa only [actualInverseSequence,zero_div] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))

theorem actual_rescaled_cdf_local_caps
    (M : (n : ℕ) → NativeOverlapMinimum (N n+1) m delta cl cu Az C0 Ct D Bclock)
    (x : ℕ → ℝ) (hcu : 0 ≤ cu) (hAz : 0 ≤ Az)
    (hxs : ∀n,(M n).xs ≤ x n) (hx0 : Tendsto x atTop (𝓝 0)) :
    ∀R : ℝ,0 < R → ∃C : ℝ,0 ≤ C ∧
      ∀ᶠn in atTop,(M n).alpha.val.val (x n*R) ≤ C*x n := by
  exact (actualInverseSequence M).rescaled_cdf_local_caps x (fun n => (M n).z)
    hcu (fun n => (M n).hxs.trans_le (hxs n)) hx0
    (Eventually.of_forall fun n => (M n).hzxs.trans
      (mul_le_mul_of_nonneg_left (hxs n) hAz))
    (Eventually.of_forall fun n r hr => ((M n).regular r hr).2)

theorem actual_rescaled_cdf_outer_growth
    (M : (n : ℕ) → NativeOverlapMinimum (N n+1) m delta cl cu Az C0 Ct D Bclock)
    (x : ℕ → ℝ) (V : ℝ → ℝ) (hAz : 0 ≤ Az)
    (hxs : ∀n,(M n).xs ≤ x n) (hx0 : Tendsto x atTop (𝓝 0))
    (hV : ∀t : ℝ,Tendsto (fun n => (M n).alpha.val.val (x n*t)/x n)
      atTop (𝓝 (V t))) :
    ∀t : ℝ,Az ≤ t → cl*t ≤ V t ∧ V t ≤ cu*t := by
  exact (actualInverseSequence M).rescaled_cdf_outer_growth x (fun n => (M n).z) V
    (fun n => (M n).hxs.trans_le (hxs n)) hx0
    (Eventually.of_forall fun n => (M n).hzxs.trans
      (mul_le_mul_of_nonneg_left (hxs n) hAz))
    (Eventually.of_forall fun n => (M n).regular) hV

theorem actual_radius_locally_uniform_of_linear_cdf
    (M : (n : ℕ) → NativeOverlapMinimum (N n+1) m delta cl cu Az C0 Ct D Bclock)
    (x : ℕ → ℝ) {kappa : ℝ} (hkappa : 0 < kappa)
    (hx : ∀n,0 < x n) (hx0 : Tendsto x atTop (𝓝 0))
    (hCDF : ∀t : ℝ,0 < t →
      Tendsto (fun n => (M n).alpha.val.val (x n*t)/x n) atTop (𝓝 (kappa*t))) :
    TendstoLocallyUniformlyOn (fun n v => (M n).R (x n*v)/x n)
      (fun v => v/kappa) atTop (Ioi (0:ℝ)) := by
  exact (actualInverseSequence M).rescaled_inverse_locally_uniform x hkappa hx hx0
    (actualInverseSequence_omitted_small M x) hCDF

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
