module

public import ScalarMacroStability
public import RescaledScalarFlux

@[expose] public section

noncomputable section
set_option maxHeartbeats 2000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory Filter Set Hierarchy GaussianCalculus Scalar
open scoped Topology NNReal

theorem macro_scalar_minimizers_moving_density {β : ℝ≥0} (hβ : 0<β)
    (hT : 1<(β:ℝ)^2) {α : ℕ→boundedMassProfiles} {a : boundedMassProfiles}
    (hprofiles : ∀n,α n∈scalarProfiles)
    (hmin : ∀n,∀γ∈scalarProfiles,scalarParisiValue (sq_pos_of_pos (NNReal.coe_pos.mpr hβ)) (α n) ≤
      scalarParisiValue (sq_pos_of_pos (NNReal.coe_pos.mpr hβ)) γ)
    (hc : ∀n x,ContinuousWithinAt (α n).val (Ici x) x)
    (hα : Tendsto α atTop (𝓝 a)) {q : ℕ→ℝ}
    (hq : Tendsto q atTop (𝓝 0)) (hqp : ∀ᶠ n in atTop,0<q n) :
    Tendsto (fun n=>(α n).val (q n)/q n) atTop
      (𝓝 (scalarInitialDensityConstant (sq_pos_of_pos (NNReal.coe_pos.mpr hβ)) a)) := by
  let ht : 0<(β:ℝ)^2 := sq_pos_of_pos (NNReal.coe_pos.mpr hβ)
  choose Q hQ hs using fun n=>scalarMinimizer_support_eq_initial_interval hT (α n) (hprofiles n) (hmin n)
  obtain ⟨c,C,ε,hcp,hCp,hε,hfixed⟩ := scalar_near_minimizers_fixed_band hβ hT (a := 1/2) (by norm_num)
  have hQlower (n : ℕ) : c/2 ≤ Q n := by
    have hv : scalarParisiValue ht (α n) ≤ normalizedScalarParisiReference β+ε := by
      rw [scalar_minimizer_value_eq_normalizedScalarParisiReference hβ (α n) (hmin n)]
      linarith
    have hqhalf := (hfixed (α n) (hprofiles n) hv (1/2) (by norm_num) le_rfl).1
    have htop := scalarQuantile_le_support_top (hprofiles n) (hs n) (u := 1/2) (by norm_num)
    linarith
  have hinside : ∀ᶠ n in atTop,q n∈Ioo (0:ℝ) (Q n) := by
    filter_upwards [hqp,hq.eventually (gt_mem_nhds (by linarith : 0<c/2))] with n hn hsmall
    exact ⟨hn,hsmall.trans_le (hQlower n)⟩
  have hmar (n : ℕ) : ∀s∈Icc 0 (Q n),(β:ℝ)^2*scalarPlantedCurvature ht (α n) s=1 := by
    apply scalarSupport_curvature_marginality ht (α n) (hQ n).1 (hQ n).2 (hc n) (hs n)
    intro s hs'
    exact scalarMinimizer_support_self_consistency hT (α n) (hprofiles n) (hmin n) (by rwa [hs n])
  have hnum := scalarPlantedThirdSquare_joint_smallClock_tendsto ht hα hq hqp hc
  have hden := scalarPlantedCurvatureCube_joint_smallClock_tendsto ht hα hq
  have hp : 0<scalarTailSpatialJet ht a 2 0 0 :=
    scalarProfileJet_curvature_pos (rescaledMassProfile a ht) (fun s=>(a.property.1 (s/(β:ℝ)^2)).2) _ _ _
  have hlim := hnum.div (hden.const_mul 2) (mul_pos (by norm_num) (pow_pos hp 3)).ne'
  change Tendsto (fun n=>(scalarPlantedJetPower ht (α n) 2 2 (q n)/q n)/
    (2*scalarPlantedJetPower ht (α n) 1 3 (q n))) atTop
      (𝓝 (scalarInitialDensityConstant ht a)) at hlim
  apply hlim.congr'
  filter_upwards [hinside] with n hn
  rw [scalarSupport_cdf_ratio ht (α n) (hQ n).2 (hc n) (hs n) (hmar n) hn]
  ring

end OAI.SKFluctuations.LaplaceWindowFormalization
