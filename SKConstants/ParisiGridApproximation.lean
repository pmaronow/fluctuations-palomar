module
public import SKConstants.ParisiGridDiffusion

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace SKConstants.ParisiFullSupport
open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.ZeroTemperatureSK.Heat SKConstantsOAI.SK.Analytic

theorem gridCDF_gradient_error (β : ℝ) (α : ℝ → ℝ) (hα : Monotone α)
    (ha : ∀ r, α r ∈ Icc (0:ℝ) 1) (h : ℝ≥0) (hh : 0 < h)
    {r : ℝ} (hr : r ∈ Icc (0:ℝ) 1) (η : ℝ) (hη : 0 < η) (x : ℝ) :
    |scalarCDFGradient β (gridCDF α h) r (Real.toNNReal (1-r)) x-
       scalarCDFGradient β α r (Real.toNNReal (1-r)) x| ≤
      2*(scalarTimeMassConstant β*(h:ℝ))/η+2*η := by
  have ht : Real.toNNReal (1-r) ≤ 1 := by
    rw [Real.toNNReal_le_iff_le_coe,NNReal.coe_one]; linarith [hr.1]
  have H := scalarCDFGradient_cdf_stability β
    (show ∀ z, gridCDF α h z ∈ Icc (0:ℝ) 1 from fun z => ha _)
    (gridCDF_mono hα (by exact_mod_cast hh)) ha hα r _ ht x η hη
  have hi : (∫ z in r..r+Real.toNNReal (1-r), |gridCDF α h z-α z|) ≤ h :=
    gridCDF_interval_integral_abs_error hα ha (by exact_mod_cast hh)
      (le_add_of_nonneg_right (Real.toNNReal (1-r)).coe_nonneg)
  exact H.trans (by gcongr; exact scalarTimeMassConstant_nonneg β)

theorem finiteFeedback_grid_drift_error
    (β : ℝ) (hβ : β ≠ 0) (α : StieltjesFunction ℝ)
    (ha : ∀ r, α r ∈ Icc (0:ℝ) 1) (h1 : α 1=1)
    (h : ℝ≥0) (hh : 0 < h) (N : ℕ) (hN : (N:ℝ≥0)*h=1)
    {v : ℝ} (hv : v ∈ Ico (0:ℝ) (β^2)) (η : ℝ) (hη : 0 < η) (x : ℝ) :
    |(finiteFeedback (regularDatum_softAbs (by norm_num : (1:ℝ) ≠ 0))
      (softAbs_lipschitz (by norm_num : (1:ℝ) ≠ 0))
      (gridCDFCoefficient α h) (Real.toNNReal (β^2)*h) N 0).f v x-
       (finiteTemperatureCDFDrift β α ha h1).f v x| ≤
      |gridCDF α h (v/β^2)-α (v/β^2)|+
        (2*(scalarTimeMassConstant β*(h:ℝ))/η+2*η) := by
  have hβ2 : 0 < β^2 := sq_pos_of_ne_zero hβ
  have hr : v/β^2 ∈ Ico (0:ℝ) 1 :=
    ⟨div_nonneg hv.1 hβ2.le,(div_lt_one hβ2).mpr hv.2⟩
  have he : β^2*(v/β^2)=v := mul_div_cancel₀ v hβ2.ne'
  have Hfield := finiteFeedback_grid_drift_eq α α.mono ha β hβ h hh N hN hr x
  rw [he] at Hfield
  rw [Hfield]
  change |gridCDF α h (v/β^2)*scalarCDFGradient β (gridCDF α h) (v/β^2) _ x-
    α (cdfTimeClamp (v/β^2))*scalarCDFGradient β α (cdfTimeClamp (v/β^2)) _ x| ≤ _
  rw [cdfTimeClamp_eq ⟨hr.1,hr.2.le⟩]
  have ht : Real.toNNReal (1-v/β^2) ≤ 1 := by
    rw [Real.toNNReal_le_iff_le_coe,NNReal.coe_one]; linarith [hr.1]
  have hG := (scalarCDF_derivative_bounds β
    (show ∀ z, gridCDF α h z ∈ Icc (0:ℝ) 1 from fun z => ha _)
    (gridCDF_mono α.mono (by exact_mod_cast hh)) (v/β^2) _ ht x).1
  have hd := gridCDF_gradient_error β α α.mono ha h hh ⟨hr.1,hr.2.le⟩ η hη x
  calc
    _ ≤ |gridCDF α h (v/β^2)*scalarCDFGradient β (gridCDF α h) (v/β^2) _ x-
          α (v/β^2)*scalarCDFGradient β (gridCDF α h) (v/β^2) _ x|+
        |α (v/β^2)*scalarCDFGradient β (gridCDF α h) (v/β^2) _ x-
          α (v/β^2)*scalarCDFGradient β α (v/β^2) _ x| := abs_sub_le _ _ _
    _ = |(gridCDF α h (v/β^2)-α (v/β^2))*scalarCDFGradient β (gridCDF α h) (v/β^2) _ x|+
      |α (v/β^2)*(scalarCDFGradient β (gridCDF α h) (v/β^2) _ x-
        scalarCDFGradient β α (v/β^2) _ x)| := by congr 1 <;> congr 1 <;> ring
    _ ≤ _ := by
      rw [abs_mul,abs_mul,abs_of_nonneg (ha _).1]
      exact add_le_add (mul_le_of_le_one_right (abs_nonneg _) hG)
        ((mul_le_mul_of_nonneg_left hd (ha _).1).trans
          (mul_le_of_le_one_left (by positivity [scalarTimeMassConstant_nonneg β]) (ha _).2))

theorem finiteFeedback_grid_solution_error
    {Ω : Type*} [MeasurableSpace Ω] (W : BrownianSystem Ω)
    (β : ℝ) (hβ : β ≠ 0) (α : StieltjesFunction ℝ)
    (ha : ∀ r, α r ∈ Icc (0:ℝ) 1) (h1 : α 1=1)
    (h : ℝ≥0) (hh : 0 < h) (N : ℕ) (hN : (N:ℝ≥0)*h=1)
    (T : ℝ≥0) (hT : (T:ℝ)<β^2) (η : ℝ) (hη : 0 < η)
    (v : ℝ≥0) (hv : v ≤ T) (w : Ω) :
    |(finiteFeedback (regularDatum_softAbs (by norm_num : (1:ℝ) ≠ 0))
      (softAbs_lipschitz (by norm_num : (1:ℝ) ≠ 0))
      (gridCDFCoefficient α h) (Real.toNNReal (β^2)*h) N 0).solution W.driver v w-
       finiteTemperatureCDFProcess W β α ha h1 v w| ≤
      2*(β^2*(h:ℝ)+(T:ℝ)*(2*(scalarTimeMassConstant β*(h:ℝ))/η+2*η))*Real.exp (3*(v:ℝ)) := by
  let ℱ := Filtration.natural W.B (fun t => (W.measurable t).stronglyMeasurable)
  let a := finiteFeedback (regularDatum_softAbs (by norm_num : (1:ℝ) ≠ 0))
      (softAbs_lipschitz (by norm_num : (1:ℝ) ≠ 0))
      (gridCDFCoefficient α h) (Real.toNNReal (β^2)*h) N 0
  let b := finiteTemperatureCDFDrift β α ha h1
  let D := 2*(scalarTimeMassConstant β*(h:ℝ))/η+2*η
  let e : ℝ → ℝ := fun r => |gridCDF α h (r/β^2)-α (r/β^2)|+D
  let E := β^2*(h:ℝ)+(T:ℝ)*D
  have hβ2 : 0 < β^2 := sq_pos_of_ne_zero hβ
  have hD : 0 ≤ D := by dsimp [D]; positivity [scalarTimeMassConstant_nonneg β]
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hi (t : ℝ) : IntervalIntegrable e volume 0 t := by
    have hdiv : Monotone (fun r : ℝ => r/β^2) := fun _ _ hr => (div_le_div_iff_of_pos_right hβ2).mpr hr
    exact (((gridCDF_mono α.mono (by exact_mod_cast hh)).comp hdiv).intervalIntegrable.sub
      (α.mono.comp hdiv).intervalIntegrable).abs.add intervalIntegrable_const
  have herr : ∀ r ∈ Icc (0:ℝ) T, ∀ x, |a.f r x-b.f r x| ≤ e r := by
    intro r hr x
    exact finiteFeedback_grid_drift_error β hβ α ha h1 h hh N hN ⟨hr.1,hr.2.trans_lt hT⟩ η hη x
  have he : ∀ (Y : ℝ≥0 → Ω → ℝ), IsProgressive ℱ Y → ∀ t ≤ T, ∀ w,
      |timePrimitive (a.action W.driver Y) t w-timePrimitive (b.action W.driver Y) t w| ≤ E := by
    intro Y hY t ht w
    refine (SKConstants.BoundedLipschitzDrift.primitive_error_of_envelope a b ℱ W.driver Y
      W.driver_progressive hY T e (hi T) herr t ht w).trans ?_
    dsimp [e,E]
    rw [intervalIntegral.integral_add
      (by exact (((gridCDF_mono α.mono (by exact_mod_cast hh)).comp
        (show Monotone (fun r : ℝ => r/β^2) from fun _ _ hr => (div_le_div_iff_of_pos_right hβ2).mpr hr)).intervalIntegrable.sub
        (α.mono.comp (show Monotone (fun r : ℝ => r/β^2) from fun _ _ hr => (div_le_div_iff_of_pos_right hβ2).mpr hr)).intervalIntegrable).abs)
      intervalIntegrable_const]
    have hcomp := intervalIntegral.integral_comp_div
      (fun z : ℝ => |gridCDF α h z-α z|) hβ2.ne' (a := (0:ℝ)) (b := (t:ℝ))
    rw [hcomp]
    simp only [zero_div,intervalIntegral.integral_const,sub_zero,smul_eq_mul]
    have H := gridCDF_integral_abs_error α.mono ha (by exact_mod_cast hh) (div_nonneg t.coe_nonneg hβ2.le)
    exact add_le_add (mul_le_mul_of_nonneg_left H hβ2.le) (mul_le_mul_of_nonneg_right ht hD)
  have H := SKConstants.BoundedLipschitzDrift.solution_sub_le_of_primitive_error a b ℱ W.driver
    W.driver_progressive T E hE he v hv w
  have hrate : b.rate = 3 := by norm_num [b,SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift.rate,finiteTemperatureCDFDrift]
  rw [hrate] at H
  simpa only [a,b,E,D,finiteTemperatureCDFProcess] using H

end SKConstants.ParisiFullSupport
