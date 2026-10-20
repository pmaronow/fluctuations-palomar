module

public import ComparisonScalarPrimitives

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy
open scoped Topology
set_option maxHeartbeats 2200000

theorem comparison_scalar_subprimitive_bound {R t : ℝ} (ht : t∈Icc (0:ℝ) R)
    (F f : ℝ→ℝ) (hF : IntegrableOn F (Icc (0:ℝ) R))
    (hf : IntegrableOn f (Icc (0:ℝ) R)) :
    |(∫s in 0..t,F s)-(∫s in 0..t,f s)|≤∫s in Icc (0:ℝ) R,|F s-f s| := by
  have hsub : Ioc (0:ℝ) t⊆Icc (0:ℝ) R := fun s hs=>⟨hs.1.le,hs.2.trans ht.2⟩
  have hFi : IntervalIntegrable F volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).mpr (hF.mono_set hsub)
  have hfi : IntervalIntegrable f volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).mpr (hf.mono_set hsub)
  rw [←intervalIntegral.integral_sub hFi hfi]
  have hn := intervalIntegral.norm_integral_le_integral_norm ht.1 (μ:=volume) (f:=fun s=>F s-f s)
  simp only [Real.norm_eq_abs,intervalIntegral.integral_of_le ht.1] at hn
  simpa only [intervalIntegral.integral_of_le ht.1] using hn.trans (setIntegral_mono_set (hF.sub hf).abs
    (Eventually.of_forall fun _=>abs_nonneg _) (Eventually.of_forall fun s hs=>hsub hs))

theorem comparison_scalar_first_primitive_uniform
    {R σ : ℝ} (F : ℕ→ℝ→ℝ) (f : ℝ→ℝ) (σn : ℕ→ℝ)
    (hF : ∀ᶠ n in atTop,IntegrableOn (F n) (Icc (0:ℝ) R))
    (hf : IntegrableOn f (Icc (0:ℝ) R))
    (hL1 : Tendsto (fun n=>∫s in Icc (0:ℝ) R,|F n s-f s|) atTop (𝓝 0))
    (hσ : Tendsto σn atTop (𝓝 σ)) :
    TendstoUniformlyOn (fun n t=>σn n+∫s in 0..t,F n s)
      (fun t=>σ+∫s in 0..t,f s) atTop (Icc (0:ℝ) R) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have he : Tendsto (fun n=>|σn n-σ|+∫s in Icc (0:ℝ) R,|F n s-f s|)
      atTop (𝓝 0) := by simpa using ((hσ.sub_const σ).abs).add hL1
  filter_upwards [hF,he.eventually (gt_mem_nhds hε)] with n hFn hn t ht
  rw [Real.dist_eq,abs_sub_comm]
  calc
    |(σn n+∫s in 0..t,F n s)-(σ+∫s in 0..t,f s)| =
        |(σn n-σ)+((∫s in 0..t,F n s)-(∫s in 0..t,f s))| := by congr 1;ring
    _ ≤ |σn n-σ|+|(∫s in 0..t,F n s)-(∫s in 0..t,f s)| := abs_add_le _ _
    _ ≤ |σn n-σ|+∫s in Icc (0:ℝ) R,|F n s-f s| :=
      add_le_add le_rfl (comparison_scalar_subprimitive_bound ht _ _ hFn hf)
    _ < ε := hn

theorem comparison_scalar_second_primitive_uniform
    {R : ℝ} (hR : 0≤R) (P : ℕ→ℝ→ℝ) (p : ℝ→ℝ)
    (hPi : ∀ᶠ n in atTop,IntegrableOn (P n) (Icc (0:ℝ) R))
    (hpi : IntegrableOn p (Icc (0:ℝ) R))
    (hP : TendstoUniformlyOn P p atTop (Icc (0:ℝ) R)) :
    TendstoUniformlyOn (fun n t=>∫s in 0..t,P n s)
      (fun t=>∫s in 0..t,p s) atTop (Icc (0:ℝ) R) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hd : 0<ε/(R+1) := div_pos hε (by linarith)
  filter_upwards [hPi,(Metric.tendstoUniformlyOn_iff.mp hP) (ε/(R+1)) hd] with n hPin hn t ht
  rw [Real.dist_eq]
  have hsub : Ioc (0:ℝ) t⊆Icc (0:ℝ) R := fun s hs=>⟨hs.1.le,hs.2.trans ht.2⟩
  have hPint : IntervalIntegrable (P n) volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).mpr (hPin.mono_set hsub)
  have hpint : IntervalIntegrable p volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).mpr (hpi.mono_set hsub)
  rw [←intervalIntegral.integral_sub hpint hPint]
  have hdiff : ∀s∈uIoc (0:ℝ) t,‖p s-P n s‖≤ε/(R+1) := by
    intro s hs
    rw [uIoc_of_le ht.1] at hs
    simpa only [Real.norm_eq_abs,Real.dist_eq] using (hn s ⟨hs.1.le,hs.2.trans ht.2⟩).le
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a:=(0:ℝ)) (b:=t) hdiff
  simp only [Real.norm_eq_abs,sub_zero,abs_of_nonneg ht.1] at hi
  apply hi.trans_lt
  have htR : ε/(R+1)*t≤ε/(R+1)*R := mul_le_mul_of_nonneg_left ht.2 hd.le
  apply htR.trans_lt
  calc
    ε/(R+1)*R=ε*R/(R+1) := by ring
    _ < ε := (div_lt_iff₀ (by linarith : 0<R+1)).mpr (by nlinarith)

end OAI.SKFluctuations.LaplaceWindowFormalization
