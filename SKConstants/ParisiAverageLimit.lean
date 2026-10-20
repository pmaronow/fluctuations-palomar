module
public import SKConstants.ParisiGridLaw
public import SKConstants.ParisiGridLimit
public import SKConstants.Upstream.OAI.Probability.SKBarriers.Parisi.CDFTerminalStability
public import SKConstants.Upstream.OAI.Probability.SKBarriers.Parisi.CDFTiltedStability

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace SKConstants.ParisiFullSupport
open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.ZeroTemperatureSK.Heat SKConstantsOAI.SK.Analytic

theorem parisiGridCDF_average_tendsto (β : ℝ) (α : ℝ → ℝ)
    (hα : Monotone α) (ha : ∀ r, α r ∈ Icc (0:ℝ) 1)
    {r : ℝ} (hr : r ∈ Ico (0:ℝ) 1) {g : ℝ → ℝ} (hg : BoundedSmooth g) :
    Tendsto (fun n => scalarCDFAverage β (gridCDF α (parisiGridMesh n)) 0 (Real.toNNReal r)
      (scalarCDFValue β (gridCDF α (parisiGridMesh n)) r (Real.toNNReal (1-r))) g 0)
      atTop (𝓝 (scalarCDFAverage β α 0 (Real.toNNReal r)
        (scalarCDFValue β α r (Real.toNNReal (1-r))) g 0)) := by
  let C := scalarTimeMassConstant β
  let B : ℝ≥0 := hg.bound.choose
  let J : ℝ≥0 := hg.deriv.bound.choose
  let K := scalarTimeMassConstantK β (1+B+B)
  let f := scalarCDFValue β α r (Real.toNNReal (1-r))
  let a (n : ℕ) := gridCDF α (parisiGridMesh n)
  let F (n : ℕ) := scalarCDFValue β (a n) r (Real.toNNReal (1-r))
  have hC : 0 ≤ C := scalarTimeMassConstant_nonneg β
  have hK : 0 ≤ K := scalarTimeMassConstantK_nonneg β _
  have ha' n : ∀ z, a n z ∈ Icc (0:ℝ) 1 := fun z => ha _
  have hm n : Monotone (a n) := gridCDF_mono hα (by exact_mod_cast parisiGridMesh_pos n)
  have ht : Real.toNNReal r ≤ 1 := Real.toNNReal_le_iff_le_coe.mpr hr.2.le
  have hrem : Real.toNNReal (1-r) ≤ 1 := Real.toNNReal_le_iff_le_coe.mpr (by simp only [NNReal.coe_one]; linarith [hr.1])
  have hf : BoundedDerivs f := scalarCDFValue_regular β ha hα r _ hrem
  have hfLip : LipschitzWith 1 f := scalarCDFValue_lipschitz β ha hα r _ hrem
  have hF n : BoundedDerivs (F n) := scalarCDFValue_regular β (ha' n) (hm n) r _ hrem
  have hFLip n : LipschitzWith 1 (F n) := scalarCDFValue_lipschitz β (ha' n) (hm n) r _ hrem
  have hB : ∀ x, |g x| ≤ B := hg.bound.choose_spec
  have hJ : ∀ x, |deriv g x| ≤ J := hg.deriv.bound.choose_spec
  have hd : ∀ x, HasDerivAt g (deriv g x) x := fun x => (hg.smooth.differentiable (by simp) x).hasDerivAt
  have hdc : Continuous (deriv g) := hg.deriv.smooth.continuous
  have he n : ∀ x, |F n x-f x| ≤ C*(parisiGridMesh n:ℝ) := by
    intro x
    have H := scalarCDFValue_cdf_lipschitz β (ha' n) (hm n) ha hα r _ hrem x
    have hi := gridCDF_interval_integral_abs_error hα ha
      (s := r) (T := r+Real.toNNReal (1-r)) (by exact_mod_cast parisiGridMesh_pos n) (le_add_of_nonneg_right (Real.toNNReal (1-r)).coe_nonneg)
    exact H.trans (mul_le_mul_of_nonneg_left hi hC)
  have herror n : |scalarCDFAverage β (a n) 0 (Real.toNNReal r) (F n) g 0-
      scalarCDFAverage β α 0 (Real.toNNReal r) f g 0| ≤
      2*(B:ℝ)*(Real.exp (2*C*(parisiGridMesh n:ℝ))-1)+
        2*K*Real.sqrt (parisiGridMesh n:ℝ)+
        2*((J:ℝ)+2*(B:ℝ)^2)*Real.sqrt (parisiGridMesh n:ℝ) := by
    have Ht := scalarCDFAverage_terminal_stability β (ha' n) (hm n)
      (hF n) hf (hFLip n) hfLip hd hd hdc hdc hB hB hJ hJ
      (show 0 ≤ C*(parisiGridMesh n:ℝ) by positivity) (he n)
      (show ∀ x, |g x-g x| ≤ (0:ℝ) by simp) 0 _ ht 0
    have Hc := scalarCDFAverage_cdf_stability_C1 β (ha' n) (hm n) ha hα hf hd hdc
      hfLip hB hJ 0 _ ht 0 (Real.sqrt (parisiGridMesh n:ℝ))
      (Real.sqrt_pos.mpr (by exact_mod_cast parisiGridMesh_pos n))
    have hi := gridCDF_integral_abs_error hα ha (by exact_mod_cast parisiGridMesh_pos n)
      (Real.toNNReal r).coe_nonneg
    simp only [zero_add] at Hc
    have Hc' : |scalarCDFAverage β (a n) 0 (Real.toNNReal r) f g 0-
        scalarCDFAverage β α 0 (Real.toNNReal r) f g 0| ≤
        2*K*(parisiGridMesh n:ℝ)/Real.sqrt (parisiGridMesh n:ℝ)+
          2*((J:ℝ)+2*(B:ℝ)^2)*Real.sqrt (parisiGridMesh n:ℝ) :=
      Hc.trans (by
        apply add_le_add _ le_rfl
        apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
        change 2*(K*(∫ z in (0:ℝ)..(Real.toNNReal r:ℝ≥0), |a n z-α z|)) ≤ 2*K*(parisiGridMesh n:ℝ)
        have Hnum : K*(∫ z in (0:ℝ)..(Real.toNNReal r:ℝ≥0), |a n z-α z|) ≤ K*(parisiGridMesh n:ℝ) :=
          mul_le_mul_of_nonneg_left hi hK
        nlinarith only [Hnum])
    have hquot : (parisiGridMesh n:ℝ)/Real.sqrt (parisiGridMesh n:ℝ)=Real.sqrt (parisiGridMesh n:ℝ) := by
      apply (div_eq_iff (Real.sqrt_pos.mpr (by exact_mod_cast parisiGridMesh_pos n)).ne').mpr
      nlinarith [Real.sq_sqrt (parisiGridMesh n).coe_nonneg]
    have heq : 2*K*(parisiGridMesh n:ℝ)/Real.sqrt (parisiGridMesh n:ℝ)=2*K*Real.sqrt (parisiGridMesh n:ℝ) := by
      calc
        _ = 2*K*((parisiGridMesh n:ℝ)/Real.sqrt (parisiGridMesh n:ℝ)) := by ring
        _ = _ := by rw [hquot]
    rw [heq] at Hc'
    have H := (abs_sub_le (scalarCDFAverage β (a n) 0 (Real.toNNReal r) (F n) g 0)
      (scalarCDFAverage β (a n) 0 (Real.toNNReal r) f g 0)
      (scalarCDFAverage β α 0 (Real.toNNReal r) f g 0)).trans (add_le_add Ht Hc')
    simpa only [zero_add,mul_assoc,add_assoc] using H
  have hs : Tendsto (fun n => Real.sqrt (parisiGridMesh n:ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).comp parisiGridMesh_coe_tendsto
  have hcx : Tendsto (fun n => 2*C*(parisiGridMesh n:ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero] using parisiGridMesh_coe_tendsto.const_mul (2*C)
  have hx : Tendsto (fun n => Real.exp (2*C*(parisiGridMesh n:ℝ))-1) atTop (𝓝 0) := by
    simpa only [Function.comp_def,mul_zero,Real.exp_zero,sub_self] using
      ((Real.continuous_exp.tendsto 0).comp hcx).sub_const 1
  have hu := ((hx.const_mul (2*(B:ℝ))).add (hs.const_mul (2*K))).add
    (hs.const_mul (2*((J:ℝ)+2*(B:ℝ)^2)))
  have H : Tendsto (fun n => |scalarCDFAverage β (a n) 0 (Real.toNNReal r) (F n) g 0-
      scalarCDFAverage β α 0 (Real.toNNReal r) f g 0|) atTop (𝓝 0) :=
    squeeze_zero (fun _ => abs_nonneg _) herror (by simpa only [mul_zero,zero_add] using hu)
  exact tendsto_iff_dist_tendsto_zero.mpr (by simpa only [Real.dist_eq] using H)

end SKConstants.ParisiFullSupport
