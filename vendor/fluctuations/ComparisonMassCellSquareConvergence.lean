module

public import ComparisonNativeRadiusVariance
public import ComparisonPhysicalWeightedGeometry

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 1500000

namespace MassCellAveraging

theorem square_difference_abs_le_energy (a b : ℝ) {t : ℝ} (ht : 0<t) :
    |a^2-b^2| ≤ (a-b)^2/t+t*(a^2+b^2) := by
  have hp : t*(a^2-b^2) ≤ (a-b)^2+t^2*(a^2+b^2) := by
    nlinarith [sq_nonneg (a-b-t*a),sq_nonneg (a-b-t*b),sq_nonneg a,sq_nonneg b]
  have hn : -(t*(a^2-b^2)) ≤ (a-b)^2+t^2*(a^2+b^2) := by
    nlinarith [sq_nonneg (a-b+t*a),sq_nonneg (a-b+t*b),sq_nonneg a,sq_nonneg b]
  have h : |t*(a^2-b^2)| ≤ (a-b)^2+t^2*(a^2+b^2) := abs_le.mpr ⟨by linarith,hp⟩
  have hm : |a^2-b^2| * t ≤ (a-b)^2+t^2*(a^2+b^2) := by
    simpa only [abs_mul,abs_of_pos ht,mul_comm] using h
  calc
    |a^2-b^2| ≤ ((a-b)^2+t^2*(a^2+b^2))/t := (le_div_iff₀ ht).mpr hm
    _ = (a-b)^2/t+t*(a^2+b^2) := by field_simp <;> ring

theorem sample_square_eventually_L1 (f : ℝ→ℝ)
    (hf : MemLp f 2 (volume.restrict (Ioc (0:ℝ) 1)))
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hm : ∀j,PartitionMesh (mesh j) 0 (as j))
    (he : ∀j,partitionEnd 0 (as j)=1) (hlim : Tendsto mesh atTop (𝓝 0))
    {epsilon : ℝ} (hepsilon : 0<epsilon) :
    ∀ᶠ j in atTop,(∫u in (0:ℝ)..1,|(sample f 0 (as j) u)^2-(f u)^2|) ≤ epsilon := by
  have hiF : IntervalIntegrable f volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr (hf.integrable (by norm_num))
  have hiFs : IntervalIntegrable (fun u=>(f u)^2) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr hf.integrable_sq
  let E := ∫u in (0:ℝ)..1,(f u)^2
  have hE : 0≤E := intervalIntegral.integral_nonneg_of_ae zero_le_one
    (Eventually.of_forall (fun u=>sq_nonneg (f u)))
  let t := epsilon/(4*(E+1))
  have ht : 0<t := div_pos hepsilon (by positivity)
  have htc : t*(4*(E+1))=epsilon := div_mul_cancel₀ _ (by positivity)
  have hsmall : t*(2*E) ≤ epsilon/2 := by nlinarith
  have heta : 0<epsilon*t/2 := by positivity
  filter_upwards [sample_memLp_two_eventually_square f hf as mesh ho hm he hlim heta] with j hj
  have hiPs := sample_integrable_comp f 0 (as j) (fun z=>z^2) 0 1
  have hiErr : IntervalIntegrable (fun u=>(sample f 0 (as j) u-f u)^2) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr
      ((sample_memLp_two f 0 (as j)).sub hf).integrable_sq
  have hcontract := sample_square_contraction f (as j) (ho j) (he j) hiF hiFs
  have hbound := intervalIntegral.integral_mono_on zero_le_one (hiPs.sub hiFs).abs
    ((hiErr.div_const t).add ((hiPs.add hiFs).const_mul t))
    (fun u _=>square_difference_abs_le_energy (sample f 0 (as j) u) (f u) ht)
  rw [intervalIntegral.integral_add (hiErr.div_const t) ((hiPs.add hiFs).const_mul t),
    intervalIntegral.integral_div,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add hiPs hiFs] at hbound
  have herror : (∫u in (0:ℝ)..1,(sample f 0 (as j) u-f u)^2)/t ≤ epsilon/2 := by
    apply (div_le_iff₀ ht).mpr
    nlinarith [hj]
  have henergy : t*((∫u in (0:ℝ)..1,(sample f 0 (as j) u)^2)+E) ≤ t*(2*E) :=
    mul_le_mul_of_nonneg_left (by linarith) ht.le
  linarith

theorem sample_square_tendsto_L1 (f : ℝ→ℝ)
    (hf : MemLp f 2 (volume.restrict (Ioc (0:ℝ) 1)))
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hm : ∀j,PartitionMesh (mesh j) 0 (as j))
    (he : ∀j,partitionEnd 0 (as j)=1) (hlim : Tendsto mesh atTop (𝓝 0)) :
    Tendsto (fun j=>∫u in (0:ℝ)..1,|(sample f 0 (as j) u)^2-(f u)^2|) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun j=>ha.trans_le (intervalIntegral.integral_nonneg_of_ae
      zero_le_one (Eventually.of_forall (fun u=>abs_nonneg _))))
  · intro b hb
    filter_upwards [sample_square_eventually_L1 f hf as mesh ho hm he hlim (by linarith : 0<b/2)]
      with j hj
    exact hj.trans_lt (by linarith)

section Sweep
variable {c : ℝ} {k M : ℝ→ℝ}
variable (hc : 0<c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r∈Icc (0:ℝ) 1,c≤k r)
variable (hmM : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0≤M 1)

include hc hk hkc hmM hM in
theorem sample_square_sweep_error_eq (α : inverseIntegralConstraints 0 0 k M)
    (f : ℝ→ℝ) (as : List PositiveMass) :
    (∫r in Icc (0:ℝ) 1,
      |deriv α.val.val r*(sample f 0 as (α.val.val r))^2-
        deriv α.val.val r*(f (α.val.val r))^2|)=
      ∫u in (0:ℝ)..1,|(sample f 0 as u)^2-(f u)^2| := by
  rw [comparisonSweep_mass_substitution hc hk hkc hmM hM α]
  apply setIntegral_congr_fun measurableSet_Icc
  intro r _
  dsimp only
  rw [←mul_sub,abs_mul,abs_of_nonneg (comparisonSweep_density_nonneg α r)]

include hc hk hkc hmM hM in
theorem sample_square_sweep_tendsto_L1 (α : inverseIntegralConstraints 0 0 k M)
    (f : ℝ→ℝ) (hf : MemLp f 2 (volume.restrict (Ioc (0:ℝ) 1)))
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hm : ∀j,PartitionMesh (mesh j) 0 (as j))
    (he : ∀j,partitionEnd 0 (as j)=1) (hlim : Tendsto mesh atTop (𝓝 0)) :
    Tendsto (fun j=>∫r in Icc (0:ℝ) 1,
      |deriv α.val.val r*(sample f 0 (as j) (α.val.val r))^2-
        deriv α.val.val r*(f (α.val.val r))^2|) atTop (𝓝 0) := by
  simp_rw [sample_square_sweep_error_eq hc hk hkc hmM hM α]
  exact sample_square_tendsto_L1 f hf as mesh ho hm he hlim

end Sweep
end MassCellAveraging
end OAI.SKFluctuations.LaplaceWindowFormalization
