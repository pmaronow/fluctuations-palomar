module

public import ComparisonRadiusFractionalIntegralAbsorption

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 12000000
set_option linter.style.haveILetI false

theorem normalized_integral_root_tendsto_zero_eventually
    (p : ℕ) (hp : 0 < p) {C : ℝ} (hC : 1 ≤ C)
    (x : ℕ→ℝ) (hx : ∀n,0<x n)
    (mu : ℕ→Measure ℝ) (hfinite : ∀n,IsFiniteMeasure (mu n))
    (hmass : ∀ᶠn in atTop,(mu n).real univ ≤ C*x n)
    (f : ℕ→ℝ→ℝ)
    (hf0 : ∀ᶠn in atTop,0≤ᵐ[mu n] f n)
    (hfi : ∀ᶠn in atTop,Integrable (f n) (mu n))
    (hsmall : Tendsto (fun n=>(∫r,f n r ∂mu n)/x n) atTop (𝓝 0)) :
    Tendsto (fun n=>(∫r,(f n r)^((p:ℝ)⁻¹) ∂mu n)/x n) atTop (𝓝 0) := by
  have hpReal : (1:ℝ) ≤ p := by exact_mod_cast hp
  have hpRealPos : (0:ℝ) < p := by exact_mod_cast hp
  have hExpPos : (0:ℝ) < (p:ℝ)⁻¹ := inv_pos.mpr hpRealPos
  have hExpLe : (p:ℝ)⁻¹ ≤ 1 := by
    rw [inv_eq_one_div,div_le_iff₀ hpRealPos]
    linarith only [hpReal]
  let g : ℕ→ℝ→ℝ := fun n r=>(f n r)^((p:ℝ)⁻¹)
  let upper:=fun n=>(C^(p-1)*((∫r,f n r ∂mu n)/x n))^((p:ℝ)⁻¹)
  have hupper : Tendsto upper atTop (𝓝 0) := by
    have H0 : Tendsto (fun n=>C^(p-1)*((∫r,f n r∂mu n)/x n)) atTop (𝓝 0) := by
      simpa only [mul_zero] using hsmall.const_mul (C^(p-1))
    have H:=((Real.continuous_rpow_const hExpPos.le).tendsto 0).comp
      H0
    simpa only [upper,mul_zero,Real.zero_rpow hExpPos.ne',Function.comp_def] using H
  apply squeeze_zero' _ _ hupper
  · filter_upwards [hf0] with n hn
    exact div_nonneg
      (integral_nonneg_of_ae (hn.mono (fun r hr=>Real.rpow_nonneg hr _)))
      (hx n).le
  · filter_upwards [hf0,hfi,hmass] with n hn hfn hmn
    letI : IsFiniteMeasure (mu n) := hfinite n
    have hgi : Integrable (g n) (mu n) := by
      have Hnorm : Integrable (fun r=>‖f n r‖^((p:ℝ)⁻¹)) (mu n) :=
        integrable_norm_rpow_of_le hfn.aestronglyMeasurable hExpPos.le
          zero_le_one hExpLe (by simpa only [Real.rpow_one] using hfn.norm)
      apply Hnorm.congr
      filter_upwards [hn] with r hr
      simp only [g,Real.norm_eq_abs,abs_of_nonneg hr]
    have hgp : Integrable (fun r=>(g n r)^p) (mu n) := by
      apply hfn.congr
      filter_upwards [hn] with r hr
      exact (Real.rpow_inv_natCast_pow hr hp.ne').symm
    have hgin : 0≤∫r,g n r ∂mu n :=
      integral_nonneg_of_ae (hn.mono (fun r hr=>Real.rpow_nonneg hr _))
    have hfin : 0≤∫r,f n r ∂mu n := integral_nonneg_of_ae hn
    have Hpow:=integral_pow_le_mass (mu n)
      (hn.mono (fun r hr=>Real.rpow_nonneg hr _)) hgi hp hgp
    have Heq : (∫r,(g n r)^p ∂mu n)=∫r,f n r ∂mu n := by
      apply integral_congr_ae
      filter_upwards [hn] with r hr
      exact Real.rpow_inv_natCast_pow hr hp.ne'
    rw [Heq] at Hpow
    have Hmass : (mu n).real univ^(p-1) ≤ (C*x n)^(p-1) :=
      pow_le_pow_left₀ measureReal_nonneg hmn _
    have H:=Hpow.trans (mul_le_mul_of_nonneg_right Hmass hfin)
    have hrootBound :
        ((∫r,g n r ∂mu n)/x n)^p ≤
          C^(p-1)*((∫r,f n r ∂mu n)/x n) := by
      calc
        ((∫r,g n r ∂mu n)/x n)^p =
            (∫r,g n r ∂mu n)^p/(x n)^p := div_pow _ _ _
        _ ≤ ((C*x n)^(p-1)*(∫r,f n r ∂mu n))/(x n)^p :=
          div_le_div_of_nonneg_right H (pow_nonneg (hx n).le p)
        _ = C^(p-1)*((∫r,f n r ∂mu n)/x n) := by
          obtain ⟨k,hk⟩:=Nat.exists_eq_succ_of_ne_zero hp.ne'
          rw [hk]
          simp only [Nat.succ_eq_add_one,Nat.add_sub_cancel,pow_succ,mul_pow]
          field_simp [(hx n).ne']
    have hK : 0≤C^(p-1)*((∫r,f n r ∂mu n)/x n) :=
      mul_nonneg (pow_nonneg (by linarith only [hC]) _)
        (div_nonneg hfin (hx n).le)
    have hupperPow : (upper n)^p=C^(p-1)*((∫r,f n r ∂mu n)/x n) :=
      Real.rpow_inv_natCast_pow hK hp.ne'
    apply le_of_pow_le_pow_left₀ hp.ne' (Real.rpow_nonneg hK _)
    change ((∫r,g n r∂mu n)/x n)^p ≤ (upper n)^p
    rw [hupperPow]
    exact hrootBound

theorem fractional_cubic_modulus_normalized_L1_tendsto
    (p : ℕ) (hp : 0<p) {C L : ℝ} (_hC : 0≤C) (hL : 1≤L)
    (x : ℕ→ℝ) (hx : ∀n,0<x n)
    (mu : ℕ→Measure ℝ) (hfinite : ∀n,IsFiniteMeasure (mu n))
    (hmass : ∀ᶠn in atTop,(mu n).real univ≤L*x n)
    (f E : ℕ→ℝ→ℝ) (eta : ℕ→ℝ)
    (hf0 : ∀ᶠn in atTop,0≤ᵐ[mu n] f n)
    (hfi : ∀ᶠn in atTop,Integrable (f n) (mu n))
    (hEi : ∀ᶠn in atTop,Integrable (E n) (mu n))
    (hsmall : Tendsto (fun n=>(∫r,f n r ∂mu n)/x n) atTop (𝓝 0))
    (heta : Tendsto eta atTop (𝓝 0)) (heta0 : ∀ᶠn in atTop,0≤eta n)
    (hpoint : ∀ᶠn in atTop,∀ᵐr∂mu n,
      |E n r|≤C*(x n)^3*((f n r)^((8:ℝ)⁻¹)+(f n r)^((4:ℝ)⁻¹)+
        (f n r)^((p:ℝ)⁻¹))+
        eta n*(x n)^3) :
    Tendsto (fun n=>(∫r,|E n r|∂mu n)/(x n)^4) atTop (𝓝 0) := by
  let g8 : ℕ→ℝ→ℝ := fun n r=>(f n r)^((8:ℝ)⁻¹)
  let g4 : ℕ→ℝ→ℝ := fun n r=>(f n r)^((4:ℝ)⁻¹)
  let gp : ℕ→ℝ→ℝ := fun n r=>(f n r)^((p:ℝ)⁻¹)
  have H8:=normalized_integral_root_tendsto_zero_eventually 8 (by omega)
    hL x hx mu hfinite hmass f hf0 hfi hsmall
  have H4:=normalized_integral_root_tendsto_zero_eventually 4 (by omega)
    hL x hx mu hfinite hmass f hf0 hfi hsmall
  have Hp:=normalized_integral_root_tendsto_zero_eventually p hp
    hL x hx mu hfinite hmass f hf0 hfi hsmall
  let upper:=fun n=>C*((∫r,g8 n r∂mu n)/x n+
    (∫r,g4 n r∂mu n)/x n+(∫r,gp n r∂mu n)/x n)+L*eta n
  have hupper : Tendsto upper atTop (𝓝 0) := by
    have H:=(((H8.add H4).add Hp).const_mul C).add (heta.const_mul L)
    simpa only [upper,g8,g4,gp,Nat.cast_ofNat,add_zero,mul_zero] using H
  apply squeeze_zero' _ _ hupper
  · exact Eventually.of_forall (fun n=>div_nonneg
      (integral_nonneg (fun r=>abs_nonneg _)) (pow_nonneg (hx n).le 4))
  · filter_upwards [hf0,hfi,hEi,hmass,heta0,hpoint] with n hn hfn hEn hmn hη hnpoint
    letI : IsFiniteMeasure (mu n) := hfinite n
    have hgi8 : Integrable (g8 n) (mu n) := by
      have Hnorm : Integrable (fun r=>‖f n r‖^((8:ℝ)⁻¹)) (mu n) :=
        integrable_norm_rpow_of_le hfn.aestronglyMeasurable (by norm_num)
          zero_le_one (by norm_num) (by simpa only [Real.rpow_one] using hfn.norm)
      apply Hnorm.congr
      filter_upwards [hn] with r hr
      simp only [g8,Real.norm_eq_abs,abs_of_nonneg hr]
    have hgi4 : Integrable (g4 n) (mu n) := by
      have Hnorm : Integrable (fun r=>‖f n r‖^((4:ℝ)⁻¹)) (mu n) :=
        integrable_norm_rpow_of_le hfn.aestronglyMeasurable (by norm_num)
          zero_le_one (by norm_num) (by simpa only [Real.rpow_one] using hfn.norm)
      apply Hnorm.congr
      filter_upwards [hn] with r hr
      simp only [g4,Real.norm_eq_abs,abs_of_nonneg hr]
    have hpReal : (1:ℝ)≤p := by exact_mod_cast hp
    have hpPos : (0:ℝ)<p := by exact_mod_cast hp
    have hpExp : (0:ℝ)<(p:ℝ)⁻¹ := inv_pos.mpr hpPos
    have hpExpLe : (p:ℝ)⁻¹≤1 := by
      rw [inv_eq_one_div,div_le_iff₀ hpPos]
      linarith only [hpReal]
    have hgip : Integrable (gp n) (mu n) := by
      have Hnorm : Integrable (fun r=>‖f n r‖^((p:ℝ)⁻¹)) (mu n) :=
        integrable_norm_rpow_of_le hfn.aestronglyMeasurable hpExp.le
          zero_le_one hpExpLe (by simpa only [Real.rpow_one] using hfn.norm)
      apply Hnorm.congr
      filter_upwards [hn] with r hr
      simp only [gp,Real.norm_eq_abs,abs_of_nonneg hr]
    have hG : Integrable (fun r=>g8 n r+g4 n r+gp n r) (mu n) :=
      (hgi8.add hgi4).add hgip
    have hCG : Integrable (fun r=>C*(x n)^3*(g8 n r+g4 n r+gp n r)) (mu n) :=
      hG.const_mul _
    have hconst : Integrable (fun _ : ℝ=>eta n*(x n)^3) (mu n) := integrable_const _
    have hR : Integrable (fun r=>C*(x n)^3*(g8 n r+g4 n r+gp n r)+eta n*(x n)^3)
        (mu n) := hCG.add hconst
    have H:=integral_mono_ae hEn.abs hR hnpoint
    have Hsum : (∫r,g8 n r+g4 n r+gp n r∂mu n)=
        (∫r,g8 n r∂mu n)+(∫r,g4 n r∂mu n)+(∫r,gp n r∂mu n) := by
      calc
        _ = (∫r,g8 n r+g4 n r∂mu n)+(∫r,gp n r∂mu n) := by
          simpa only [Pi.add_apply] using (integral_add (hgi8.add hgi4) hgip)
        _ = _ := by
          congr 1
          simpa only [Pi.add_apply] using (integral_add hgi8 hgi4)
    have Hsplit :
        (∫r,C*(x n)^3*(g8 n r+g4 n r+gp n r)+eta n*(x n)^3∂mu n)=
          C*(x n)^3*((∫r,g8 n r∂mu n)+(∫r,g4 n r∂mu n)+
            (∫r,gp n r∂mu n))+(mu n).real univ*(eta n*(x n)^3) := by
      calc
        _ = (∫r,C*(x n)^3*(g8 n r+g4 n r+gp n r)∂mu n)+
              (∫_ : ℝ,eta n*(x n)^3∂mu n) := by
                simpa only [Pi.add_apply] using (integral_add hCG hconst)
        _ = _ := by
          rw [integral_const_mul,Hsum,integral_const]
          simp only [smul_eq_mul]
    rw [Hsplit] at H
    have hprice : 0≤eta n*(x n)^3 := mul_nonneg hη (pow_nonneg (hx n).le 3)
    have Hmass:=mul_le_mul_of_nonneg_right hmn hprice
    apply (div_le_iff₀ (pow_pos (hx n) 4)).mpr
    have Hid : (upper n)*(x n)^4 =
        C*(x n)^3*((∫r,g8 n r∂mu n)+(∫r,g4 n r∂mu n)+
          (∫r,gp n r∂mu n))+
          (L*x n)*(eta n*(x n)^3) := by
      dsimp only [upper]
      field_simp [(hx n).ne']
    rw [Hid]
    linarith only [H,Hmass]

end OAI.SKFluctuations.LaplaceWindowFormalization
