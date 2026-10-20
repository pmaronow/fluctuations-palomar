module

public import ComparisonRadiusFractionalIntegralAbsorptionEventual
public import ComparisonCriticalPositiveWallRadiusDefectFromEq19
public import ComparisonActualHighWallRadiusScalarIntegrability
public import ComparisonActualHighWallHighMassNumerics

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 16000000
set_option linter.style.haveILetI false

theorem actual_high_wall_fractional_radius_eventual_mass_band_scalar_gap_dim_tendsto_zero
    (p : ℕ) (hp : 0<p) (Bclock : ℝ) {m delta cl cu Az C0 Ct D a b ca Cpoint T : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hmargin : 2*delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hab : a ≤ b) (hca : 0 < ca) (hCp : 0 ≤ Cpoint) (hT : 0 < T)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ) → ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (hband : ∀ᶠn in atTop,(M n).data.rmin < (M n).xs*a ∧
      (M n).xs*b ≤ 1 ∧ ca*(M n).xs ≤ (M n).alpha.val.val ((M n).xs*a))
    (alpha : ℕ → boundedMassProfiles) (eta : ℕ → ℝ)
    (heta0 : ∀ᶠn in atTop,0≤eta n) (heta : Tendsto eta atTop (𝓝 0))
    (hpoint : ∀ᶠn in atTop,∀r∈Ioo ((M n).xs*a) ((M n).xs*b),
      |(M n).radiusS r-
        scalarCovarianceResponse hT (alpha n)
          (actualMixedClock (dim n+1) (M n).bf (M n).hf ((M n).alpha.val.val r))| ≤
      Cpoint*(M n).xs^3*(
        (((Real.sqrt ((M n).wallRadiusPointDefect r)+1/(M n).data.N)/(M n).xs)^((8:ℝ)⁻¹))+
        (((Real.sqrt ((M n).wallRadiusPointDefect r)+1/(M n).data.N)/(M n).xs)^((4:ℝ)⁻¹))+
        (((Real.sqrt ((M n).wallRadiusPointDefect r)+1/(M n).data.N)/(M n).xs)^((p:ℝ)⁻¹)))+
          eta n*(M n).xs^3)
    (dphys : ℕ → ℕ) (e : ∀n,Fin (dphys n+1) ≃ FeatureIndex (dim n+1)) :
    Tendsto (fun n=>(∫r in Ioo ((M n).xs*a) ((M n).xs*b),
      |(M n).radiusS r-
        scalarCovarianceResponse hT (alpha n)
          (actualMixedClock (dim n+1) (M n).bf (M n).hf ((M n).alpha.val.val r))|)/
          (M n).xs^4) atTop (𝓝 0) := by
  let L:=max b 1
  have hL : 1≤L:=le_max_right b 1
  let F:=fun n=>Ioo ((M n).xs*a) ((M n).xs*b)
  let mu:=fun n=>(volume.restrict (F n))
  let d:=fun n=>(M n).xs
  let V:=fun n r=>(M n).wallRadiusPointDefect r
  let f:=fun n r=>(Real.sqrt (V n r)+1/(M n).data.N)/d n
  let E:=fun n r=>(M n).radiusS r-
    scalarCovarianceResponse hT (alpha n)
      (actualMixedClock (dim n+1) (M n).bf (M n).hf ((M n).alpha.val.val r))
  have hfinite (n : ℕ) : IsFiniteMeasure (mu n) := by
    dsimp only [mu,F]
    infer_instance
  have hmass : ∀ᶠn in atTop,(mu n).real univ≤L*d n := by
    filter_upwards [hband] with n hn
    dsimp only [mu,F,d]
    rw [measureReal_restrict_apply_univ,measureReal_def,Real.volume_Ioo,
      ENNReal.toReal_ofReal (sub_nonneg.mpr
        (mul_le_mul_of_nonneg_left hab (M n).hxs.le))]
    have ha0 := (M n).data.hrbounds.1.trans hn.1
    have hsize : (M n).xs*b ≤ L*(M n).xs := by
      dsimp only [L]
      nlinarith only [mul_le_mul_of_nonneg_right
        (le_max_left b 1) (M n).hxs.le]
    linarith only [ha0,hsize]
  have hV : Tendsto (fun n=>(∫r,V n r∂mu n)/d n^3) atTop (𝓝 0) := by
    simpa only [V,mu,F,d,integral_Icc_eq_integral_Ioo] using
      critical_positive_wall_radius_defect_L1_of_eventual_mass_band
        Bclock hm hdelta hmargin hcl hcu hAz hC0 hCt hca hab
        dim hdim M hfixed hband dphys e
  have hsite : Tendsto (fun n=>1/((M n).data.N*d n)) atTop (𝓝 0) := by
    have Hpow : Tendsto (fun n=>C0^6*((dim n+1:ℕ):ℝ)^(-6*m)) atTop (𝓝 0) := by
      simpa only [Function.comp_def,mul_zero,neg_mul] using
        ((tendsto_rpow_neg_atTop (by positivity : 0 < 6*m)).comp
          (tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hdim))).const_mul (C0^6)
    apply squeeze_zero' (Eventually.of_forall (fun n=>by
      have hx:=(M n).hxs
      have hN:=(M n).data.hN
      dsimp only [d]
      positivity)) _ Hpow
    filter_upwards [] with n
    have hx1 : (M n).xs ≤ 1 := by rw [hfixed n]; exact (M n).data.hd1
    have hfive : (M n).xs^5 ≤ 1:=pow_le_one₀ (M n).hxs.le hx1
    have hsix : (M n).xs^6 ≤ (M n).xs := by
      nlinarith only [mul_le_mul_of_nonneg_right hfive (M n).hxs.le]
    have Hcritical:=(M n).high_mass_inverse_power hC0 6
    norm_num only [Nat.cast_ofNat,div_self (by norm_num : (6:ℝ) ≠ 0),
      Real.rpow_one] at Hcritical
    have Hle : 1/((M n).data.N*(M n).xs) ≤
        1/((M n).data.N*(M n).xs^6) :=
      div_le_div_of_nonneg_left zero_le_one
        (by have :=(M n).hxs; have :=(M n).data.hN; positivity)
        (mul_le_mul_of_nonneg_left hsix (M n).data.hN.le)
    simpa only [d,ActualHighWallData.N] using Hle.trans Hcritical
  have hF : ∀ᶠn in atTop,F n⊆Icc (M n).data.rmin 1 := by
    filter_upwards [hband] with n hn r hr
    exact ⟨hn.1.le.trans hr.1.le,hr.2.le.trans hn.2.1⟩
  have hfi : ∀ᶠn in atTop,Integrable (f n) (mu n) := by
    filter_upwards [hF] with n hn
    letI : IsFiniteMeasure (mu n) := hfinite n
    have hVi : Integrable (V n) (mu n) :=
      (M n).wall_radius_point_defect_integrableOn.mono_set hn
    have hV0 : 0≤ᵐ[mu n] V n := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      exact (M n).wall_radius_point_defect_nonneg (hn hr)
    have hroot := (coordinate_sqrt_integrable (mu n) (V n) hVi hV0).1
    exact (hroot.add (integrable_const _)).div_const _
  have hf0 : ∀ᶠn in atTop,0≤ᵐ[mu n] f n := by
    filter_upwards [] with n
    exact Eventually.of_forall (fun r=>div_nonneg
      (add_nonneg (Real.sqrt_nonneg _) (one_div_nonneg.mpr (M n).data.hN.le))
      (M n).hxs.le)
  have hsmall : Tendsto (fun n=>(∫r,f n r∂mu n)/d n) atTop (𝓝 0) := by
    let upper:=fun n=>Real.sqrt (L*((∫r,V n r∂mu n)/d n^3))+
      L/((M n).data.N*d n)
    have hupper : Tendsto upper atTop (𝓝 0) := by
      have H:=((hV.const_mul L).sqrt).add (hsite.const_mul L)
      simpa only [upper,mul_zero,Real.sqrt_zero,zero_add,mul_one_div] using H
    apply squeeze_zero' _ _ hupper
    · filter_upwards [hf0] with n hn
      exact div_nonneg (integral_nonneg_of_ae hn) (M n).hxs.le
    · filter_upwards [hF,hmass] with n hn hmn
      letI : IsFiniteMeasure (mu n) := hfinite n
      have hVi : Integrable (V n) (mu n) :=
        (M n).wall_radius_point_defect_integrableOn.mono_set hn
      have hV0 : 0≤ᵐ[mu n] V n := by
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
        exact (M n).wall_radius_point_defect_nonneg (hn hr)
      obtain ⟨hroot,hroot2⟩:=coordinate_sqrt_integrable (mu n) (V n) hVi hV0
      have Hroot:=comparison_original_mass_normalized_L1_le_sqrt (mu n)
        (fun r=>Real.sqrt (V n r)) hroot hroot2 (M n).hxs (zero_le_one.trans hL) hmn
      simp only [abs_of_nonneg (Real.sqrt_nonneg _)] at Hroot
      have heq : (∫r,(Real.sqrt (V n r))^2∂mu n)=∫r,V n r∂mu n :=
        integral_congr_ae (hV0.mono fun r hr=>Real.sq_sqrt hr)
      rw [heq] at Hroot
      have Hmass : (mu n).real univ/((M n).data.N*d n^2) ≤
          L/((M n).data.N*d n) := by
        have H:=div_le_div_of_nonneg_right hmn (by
          have :=(M n).data.hN
          have :=(M n).hxs
          dsimp only [d]
          positivity : 0≤(M n).data.N*d n^2)
        have Hid : (L*d n)/((M n).data.N*d n^2)=L/((M n).data.N*d n) := by
          dsimp only [d]
          field_simp [(M n).data.hN.ne',(M n).hxs.ne']
        exact H.trans_eq Hid
      have Hid : (∫r,f n r∂mu n)/d n =
          (∫r,Real.sqrt (V n r)∂mu n)/d n^2+
            (mu n).real univ/((M n).data.N*d n^2) := by
        dsimp only [f]
        rw [integral_div,integral_add hroot (integrable_const _),integral_const]
        simp only [smul_eq_mul]
        dsimp only [d]
        field_simp [(M n).data.hN.ne',(M n).hxs.ne']
      rw [Hid]
      exact add_le_add Hroot Hmass
  have hEi : ∀ᶠn in atTop,Integrable (E n) (mu n) := by
    filter_upwards [hF] with n hn
    exact ((M n).original_scalar_radius_gap_integrableOn hT (alpha n)).mono_set hn
  have hpoint' : ∀ᶠn in atTop,∀ᵐr∂mu n,
      |E n r|≤Cpoint*(d n)^3*((f n r)^((8:ℝ)⁻¹)+(f n r)^((4:ℝ)⁻¹)+
        (f n r)^((p:ℝ)⁻¹))+
        eta n*(d n)^3 := by
    filter_upwards [hpoint] with n hn
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact hn r hr
  exact fractional_cubic_modulus_normalized_L1_tendsto p hp hCp hL d
    (fun n=>(M n).hxs) mu hfinite hmass f E eta hf0 hfi hEi hsmall
    heta heta0 hpoint'

end OAI.SKFluctuations.LaplaceWindowFormalization
