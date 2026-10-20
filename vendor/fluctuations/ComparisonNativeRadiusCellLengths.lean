module

public import ComparisonNativeRadiusVarianceAssembly

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 2200000
section
variable {c : ℝ} {k M : ℝ→ℝ}
variable (hc : 0<c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r∈Icc (0:ℝ) 1,c ≤ k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)

theorem comparison_mass_radius_cell_substitution
    (α : inverseIntegralConstraints 0 0 k M) (f : ℝ→ℝ)
    {u v : ℝ} (hu : u∈Icc (0:ℝ) 1) (hv : v∈Icc (0:ℝ) 1) (huv : u ≤ v) :
    let R := comparisonSweepQuantile hc hk hkc hm hM α
    (∫s in u..v,f s)=∫r in Icc (R u) (R v),deriv α.val.val r*f (α.val.val r) := by
  dsimp only
  let R := comparisonSweepQuantile hc hk hkc hm hM α
  have hRu := comparisonSweepQuantile_bounds hc hk hkc hm hM α u
  have hRv := comparisonSweepQuantile_bounds hc hk hkc hm hM α v
  have hrad := comparisonSweepQuantile_monotone hc hk hkc hm hM α huv
  have hsub : Icc (R u) (R v)⊆Icc (0:ℝ) 1 := Icc_subset_Icc hRu.1 hRv.2
  have hLip := (inverseIntegralConstraints_lipschitz hm hM α.property).mono hsub
  have hmassu := comparisonSweepQuantile_mass_spec hc hk hkc hm hM α hu
  have hmassv := comparisonSweepQuantile_mass_spec hc hk hkc hm hM α hv
  have himage : α.val.val '' Icc (R u) (R v)=Icc u v := by
    have ht := hLip.continuousOn.image_Icc_of_monotoneOn hrad (α.val.property.2.monotoneOn _)
    simpa only [hmassu,hmassv] using ht
  have hinj := (inverseConstraint_strictMonoOn hc hk hkc α.property).mono hsub
  rw [intervalIntegral.integral_of_le huv,←integral_Icc_eq_integral_Ioc,
    ←himage,lipschitz_interval_integral_image hrad hLip hinj.injOn]
  apply setIntegral_congr_fun measurableSet_Icc
  intro r _
  dsimp only
  rw [abs_of_nonneg (comparisonSweep_density_nonneg α r)]

theorem comparisonRadiusMassWeight_cell_average_eq_radius_length
    (α : inverseIntegralConstraints 0 0 k M)
    {A : Set ℝ} (hA : MeasurableSet A) (hAD : A⊆Icc (0:ℝ) 1)
    {x kmin : ℝ} (hx : 0<x) (hkmin : 0<kmin) (hfloor : ∀r∈A,kmin ≤ k r)
    {u v : ℝ} (hu : u∈Icc (0:ℝ) 1) (hv : v∈Icc (0:ℝ) 1) (huv : u<v) :
    let R := comparisonSweepQuantile hc hk hkc hm hM α
    MassCellAveraging.average (comparisonRadiusMassWeight R α.val.val A x kmin) u v=
      volume.real (A∩Ioc (R u) (R v))/(x*(v-u)) := by
  dsimp only
  let R := comparisonSweepQuantile hc hk hkc hm hM α
  let f := comparisonRadiusMassWeight R α.val.val A x kmin
  have hsub : Icc (R u) (R v)⊆Icc (0:ℝ) 1 := Icc_subset_Icc
    (comparisonSweepQuantile_bounds hc hk hkc hm hM α u).1
    (comparisonSweepQuantile_bounds hc hk hkc hm hM α v).2
  have hpull := comparisonRadiusMassWeight_linear_pullback hc hk hkc hm hM α hA hAD hx hkmin hfloor
  have hlocal : ∀ᵐ r∂volume.restrict (Icc (R u) (R v)),
      deriv α.val.val r*f (α.val.val r)=A.indicator (fun _ : ℝ=>1/x) r :=
    hpull.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
  have hcell : (∫s in u..v,f s)=volume.real (A∩Ioc (R u) (R v))*(1/x) := by
    rw [comparison_mass_radius_cell_substitution hc hk hkc hm hM α f hu hv huv.le,
      integral_congr_ae hlocal,integral_Icc_eq_integral_Ioc]
    rw [integral_indicator_const _ hA,measureReal_restrict_apply hA,smul_eq_mul]
  unfold MassCellAveraging.average
  rw [hcell]
  dsimp only [R]
  field_simp [hx.ne', (sub_pos.mpr huv).ne']

end
end OAI.SKFluctuations.LaplaceWindowFormalization
