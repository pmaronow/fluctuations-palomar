module

public import ComparisonActualHighWallRadiusScalarModulus

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 12000000
set_option linter.style.haveILetI false

theorem normalized_integral_root_tendsto_zero
    (p : ℕ) (hp : 0 < p) {C : ℝ} (hC : 1 ≤ C)
    (x : ℕ→ℝ) (hx : ∀n,0<x n)
    (mu : ℕ→Measure ℝ) (hfinite : ∀n,IsFiniteMeasure (mu n))
    (hmass : ∀n,(mu n).real univ ≤ C*x n)
    (f : ℕ→ℝ→ℝ)
    (hf0 : ∀n,0≤ᵐ[mu n] f n)
    (hfi : ∀n,Integrable (f n) (mu n))
    (hsmall : Tendsto (fun n=>(∫r,f n r ∂mu n)/x n) atTop (𝓝 0)) :
    Tendsto (fun n=>(∫r,(f n r)^((p:ℝ)⁻¹) ∂mu n)/x n) atTop (𝓝 0) := by
  have hpReal : (1:ℝ) ≤ p := by exact_mod_cast hp
  have hpRealPos : (0:ℝ) < p := by exact_mod_cast hp
  have hExpPos : (0:ℝ) < (p:ℝ)⁻¹ := inv_pos.mpr hpRealPos
  have hExpLe : (p:ℝ)⁻¹ ≤ 1 := by
    rw [inv_eq_one_div,div_le_iff₀ hpRealPos]
    linarith only [hpReal]
  let g : ℕ→ℝ→ℝ := fun n r=>(f n r)^((p:ℝ)⁻¹)
  have hgi (n : ℕ) : Integrable (g n) (mu n) := by
    letI : IsFiniteMeasure (mu n) := hfinite n
    have Hnorm : Integrable (fun r=>‖f n r‖^((p:ℝ)⁻¹)) (mu n) :=
      integrable_norm_rpow_of_le (hfi n).aestronglyMeasurable hExpPos.le
        zero_le_one hExpLe (by simpa only [Real.rpow_one] using (hfi n).norm)
    apply Hnorm.congr
    filter_upwards [hf0 n] with r hr
    simp only [g,Real.norm_eq_abs,abs_of_nonneg hr]
  have hgp (n : ℕ) : Integrable (fun r=>(g n r)^p) (mu n) := by
    apply (hfi n).congr
    filter_upwards [hf0 n] with r hr
    exact (Real.rpow_inv_natCast_pow hr hp.ne').symm
  have hgin (n : ℕ) : 0≤∫r,g n r ∂mu n :=
    integral_nonneg_of_ae ((hf0 n).mono (fun r hr=>Real.rpow_nonneg hr _))
  have hfin (n : ℕ) : 0≤∫r,f n r ∂mu n := integral_nonneg_of_ae (hf0 n)
  have hrootBound (n : ℕ) :
      ((∫r,g n r ∂mu n)/x n)^p ≤
        C^(p-1)*((∫r,f n r ∂mu n)/x n) := by
    letI : IsFiniteMeasure (mu n) := hfinite n
    have Hpow:=integral_pow_le_mass (mu n)
      ((hf0 n).mono (fun r hr=>Real.rpow_nonneg hr _)) (hgi n) hp (hgp n)
    have Heq : (∫r,(g n r)^p ∂mu n)=∫r,f n r ∂mu n := by
      apply integral_congr_ae
      filter_upwards [hf0 n] with r hr
      exact Real.rpow_inv_natCast_pow hr hp.ne'
    rw [Heq] at Hpow
    have Hmass : (mu n).real univ^(p-1) ≤ (C*x n)^(p-1) :=
      pow_le_pow_left₀ measureReal_nonneg (hmass n) _
    have H:=Hpow.trans (mul_le_mul_of_nonneg_right Hmass (hfin n))
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
  let upper:=fun n=>(C^(p-1)*((∫r,f n r ∂mu n)/x n))^((p:ℝ)⁻¹)
  have hupper : Tendsto upper atTop (𝓝 0) := by
    have H0 : Tendsto (fun n=>C^(p-1)*((∫r,f n r∂mu n)/x n)) atTop (𝓝 0) := by
      simpa only [mul_zero] using hsmall.const_mul (C^(p-1))
    have H:=((Real.continuous_rpow_const hExpPos.le).tendsto 0).comp
      H0
    simpa only [upper,mul_zero,Real.zero_rpow hExpPos.ne',Function.comp_def] using H
  apply squeeze_zero' (Eventually.of_forall (fun n=>
    div_nonneg (hgin n) (hx n).le)) _ hupper
  filter_upwards [] with n
  have hK : 0≤C^(p-1)*((∫r,f n r ∂mu n)/x n) :=
    mul_nonneg (pow_nonneg (by linarith only [hC]) _) (div_nonneg (hfin n) (hx n).le)
  have hupperPow : (upper n)^p=C^(p-1)*((∫r,f n r ∂mu n)/x n) := by
    exact Real.rpow_inv_natCast_pow hK hp.ne'
  apply le_of_pow_le_pow_left₀ hp.ne' (Real.rpow_nonneg hK _)
  change ((∫r,g n r∂mu n)/x n)^p ≤ (upper n)^p
  rw [hupperPow]
  exact hrootBound n

end OAI.SKFluctuations.LaplaceWindowFormalization
