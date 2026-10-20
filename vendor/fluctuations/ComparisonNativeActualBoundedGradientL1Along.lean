module

public import ComparisonNativeActualBoundedGradientCore

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy NativeOverlapMinimum
open scoped Topology
set_option maxHeartbeats 12000000

theorem actual_selected_bad_history_bounded_radius_gradient_L1_along
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D T c0 c C a b K L A : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hmargin : 2*delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hc : 0 < c) (ha : 0 < a) (hab : a ≤ b) (hK : 0 ≤ K)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hxs : Tendsto (fun n=>(M n).xs) atTop (𝓝 0))
    (epsilon shell : ℝ) (hshell : 0 < shell)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock T epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualSelectedBadHistoryChain c0 root M)
    (hwork : ∀ᶠn in atTop,
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs/(M n).xs^2 ≤ K)
    (hmass : ∀ᶠn in atTop,∀t∈Icc a b,
      c*(M n).xs ≤ (M n).alpha.val.val ((M n).xs*t) ∧
        (M n).alpha.val.val ((M n).xs*t) ≤ C*(M n).xs)
    (s : NonnegativeMassProfile)
    (Hstrength : ∀t∈Icc a b,Tendsto (fun n=>
      laplaceComparisonStrength (M n).context.d (M n).lam ((M n).xs*t)/(M n).xs^2)
      atTop (𝓝 (L*laplaceComparisonShape (A*t))))
    (Hslope : ∀t∈Icc a b,Tendsto (fun n=>comparisonLogSlope
      (laplaceComparisonStrength (M n).context.d (M n).lam) ((M n).xs*t))
      atTop (𝓝 (laplaceComparisonSlope (A*t))))
    (Hspin : ∀t∈Icc a b,Tendsto (fun n=>(M n).actualScaledRadiusSpin t)
      atTop (𝓝 (s.mass t))) :
    Tendsto (fun n=>∫t in Icc a b,|(M n).actualVirtualScaledGradient t-
      comparisonScaledStationarity (L*laplaceComparisonShape (A*t))
        (laplaceComparisonSlope (A*t)) t (s.mass t)|) atTop (𝓝 0) := by
  let F:=fun t=>comparisonScaledStationarity (L*laplaceComparisonShape (A*t))
    (laplaceComparisonSlope (A*t)) t (s.mass t)
  have hFm : Measurable F := by
    have hs:=s.monotone.measurable
    have hh : Measurable (fun t:ℝ=>laplaceComparisonShape (A*t)) :=
      laplaceComparisonShape_contDiff.continuous.measurable.comp
      (measurable_const.mul measurable_id)
    have hp : Measurable (fun t:ℝ=>laplaceComparisonSlope (A*t)) :=
      comparison_shape_slope_continuous.measurable.comp
      (measurable_const.mul measurable_id)
    unfold F comparisonScaledStationarity
    fun_prop
  have hsmall : ∀ᶠn in atTop,(M n).xs*b ≤ 1 := by
    have H : Tendsto (fun n=>(M n).xs*b) atTop (𝓝 0) := by
      simpa only [zero_mul] using hxs.mul_const b
    exact H.eventually (eventually_le_nhds zero_lt_one)
  obtain ⟨B,hB,Hraw⟩:=eventually_actual_minimum_mass_mean_upper Bclock
    hm hdelta (by linarith) hcl hcu hAz hC0 hCt
  let Kbig:=max (K+1) (B*(1+C))
  have Hbounds : ∀ᶠn in atTop,∀t∈Icc a b,
      laplaceComparisonStrength (M n).context.d (M n).lam ((M n).xs*t)/(M n).xs^2∈Icc (0:ℝ) Kbig ∧
      comparisonLogSlope (laplaceComparisonStrength (M n).context.d (M n).lam)
        ((M n).xs*t)∈Icc (0:ℝ) 1 ∧ (M n).actualScaledRadiusSpin t∈Icc (0:ℝ) Kbig := by
    filter_upwards [hwork,hmass,hdim.eventually Hraw] with n hwn hmn hrn
    intro t ht
    have ham:=hmn t ht
    have hau:= (M n).alpha.val.property.1 ((M n).xs*t)
    have hap : 0 < (M n).alpha.val.val ((M n).xs*t) :=
      (mul_pos hc (M n).hxs).trans_le ham.1
    have Hmean:=hrn (M n) _ ⟨hap,hau.2⟩
    have Hspinb : (M n).actualScaledRadiusSpin t ≤ B*(1+C) := by
      apply (div_le_iff₀ (M n).hxs).mpr
      calc
        _ ≤ B*((M n).xs+(M n).alpha.val.val ((M n).xs*t)) := Hmean
        _ ≤ B*((M n).xs+C*(M n).xs) :=
          mul_le_mul_of_nonneg_left (add_le_add le_rfl ham.2) hB.le
        _ = B*(1+C)*(M n).xs := by ring
    have Hstrengthb:=comparison_zero_strength_bound_of_working (M n).context.hd
      (M n).hlam.le (M n).hxs (M n).hld hK hwn
    have hp:=laplaceComparisonStrength_logSlope_mem (M n).context.hd.ne'
      (M n).hlam.ne' ((M n).xs*t)
    refine ⟨⟨div_nonneg (laplaceComparisonStrength_pos _ (M n).hlam _).le (sq_nonneg _),?_⟩,⟨hp.1,hp.2.le⟩,
      ⟨div_nonneg ((M n).mass_mean_nonneg hau) (M n).hxs.le,
        Hspinb.trans (le_max_right _ _)⟩⟩
    exact ((div_le_div_of_nonneg_right
      (laplaceComparisonStrength_le (M n).context.d (M n).hlam.le _) (sq_nonneg _)).trans
      Hstrengthb).trans (le_max_left _ _)
  have HP : Tendsto (fun n=>∫t in Icc a b,|(M n).actualScaledPrincipalGradient t-F t|)
      atTop (𝓝 0) := by
    obtain ⟨n0,Hn0⟩:=eventually_atTop.mp Hbounds
    apply (tendsto_add_atTop_iff_nat n0).mp
    apply comparison_principal_density_L1_tendsto
      (fun n t=>laplaceComparisonStrength (M (n+n0)).context.d (M (n+n0)).lam
        ((M (n+n0)).xs*t)/(M (n+n0)).xs^2)
      (fun n t=>comparisonLogSlope (laplaceComparisonStrength (M (n+n0)).context.d
        (M (n+n0)).lam) ((M (n+n0)).xs*t))
      (fun n=>(M (n+n0)).actualScaledRadiusSpin)
      (fun t=>L*laplaceComparisonShape (A*t)) (fun t=>laplaceComparisonSlope (A*t))
      s.mass (K:=Kbig) ha hab
    · intro n
      exact ((laplaceComparisonStrength_contDiff _ _).continuous.measurable.comp
        (measurable_const.mul measurable_id)).div_const _
    · intro n
      simp_rw [comparison_slope_scaled_parameter_identity (M (n+n0)).context.hd.ne'
        (M (n+n0)).hlam.ne']
      exact comparison_shape_slope_continuous.measurable.comp (measurable_const.mul measurable_id)
    · intro n
      exact (M (n+n0)).actual_scaled_radius_spin_monotone.measurable
    · exact (laplaceComparisonShape_contDiff.continuous.measurable.comp
        (measurable_const.mul measurable_id)).const_mul L
    · exact comparison_shape_slope_continuous.measurable.comp (measurable_const.mul measurable_id)
    · exact s.monotone.measurable
    · intro n t ht
      exact (Hn0 (n+n0) (by omega) t ht).1
    · intro n t ht
      exact (Hn0 (n+n0) (by omega) t ht).2.1
    · intro n t ht
      exact (Hn0 (n+n0) (by omega) t ht).2.2
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact ⟨(Hstrength t ht).comp (tendsto_add_atTop_nat n0),
        (Hslope t ht).comp (tendsto_add_atTop_nat n0),
        (Hspin t ht).comp (tendsto_add_atTop_nat n0)⟩
  have HD:=actual_selected_bad_history_compact_radius_thermal_L1_along Bclock
    hm hdelta hmargin hcl hcu hAz hC0 hCt hc ha.le hab dim hdim root M hxs
    epsilon shell hshell hb hh Hhistory hmass
  have Hlim : Tendsto (fun n=>(∫t in Icc a b,|(M n).actualScaledPrincipalGradient t-F t|)+
      ((K+1)/a)*(∫t in Icc a b,(M n).cavityRadiusPointDefect ((M n).xs*t)/(M n).xs^2))
      atTop (𝓝 0) := by simpa only [mul_zero,add_zero] using HP.add (HD.const_mul ((K+1)/a))
  apply squeeze_zero' (Eventually.of_forall (fun n=>integral_nonneg (fun t=>abs_nonneg _))) _ Hlim
  filter_upwards [Hbounds,hsmall,hwork] with n hbn hsn hwn
  let bound:=Kbig*(2*b+2*Kbig+Kbig^2/a)
  have hPi : IntegrableOn (M n).actualScaledPrincipalGradient (Icc a b) := by
    apply Integrable.of_bound (M n).actual_scaled_principal_gradient_measurable.aestronglyMeasurable bound
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact (by simpa only [Real.norm_eq_abs,actualScaledPrincipalGradient,bound] using
      comparison_scaled_stationarity_bound ha ht (hbn t ht).1 (hbn t ht).2.1 (hbn t ht).2.2)
  have hFi : IntegrableOn F (Icc a b) := by
    apply Integrable.of_bound hFm.aestronglyMeasurable bound
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    apply le_of_tendsto ((comparison_scaled_stationarity_tendsto
      (Hstrength t ht) (Hslope t ht) (Hspin t ht)).abs)
    filter_upwards [Hbounds] with j hj
    simpa only [Real.norm_eq_abs] using comparison_scaled_stationarity_bound ha ht
      (hj t ht).1 (hj t ht).2.1 (hj t ht).2.2
  have hDi:=(M n).actual_scaled_radius_defect_integrable ha.le hsn
  have H:=integral_mono_of_nonneg
    (Eventually.of_forall (fun t=>abs_nonneg ((M n).actualVirtualScaledGradient t-F t)))
    ((hPi.sub hFi).abs.add (hDi.const_mul ((K+1)/a))) (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      have he:=(M n).actual_scaled_gradient_error_bound ha hsn hK hwn ht
      have ht:=(abs_sub_le ((M n).actualVirtualScaledGradient t)
        ((M n).actualScaledPrincipalGradient t) (F t))
      dsimp only [Pi.add_apply,Pi.sub_apply]
      linarith only [he,ht])
  have hadd:=integral_add (hPi.sub hFi).abs (hDi.const_mul ((K+1)/a))
  simp only [Pi.add_apply,Pi.sub_apply] at H hadd
  rw [hadd,integral_const_mul] at H
  exact H

end OAI.SKFluctuations.LaplaceWindowFormalization
