module

public import ComparisonHighStrengthIdentification

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy
open scoped Topology
set_option maxHeartbeats 2300000

theorem comparison_scalar_density_error_bound {F P g rho zeta T : ℝ}
    (heq : F=-2*T*(P+rho)-2*zeta) :
    |F-(-2*T*g)|≤2*|T| *|P-g|+2*|T| *|rho|+2*|zeta| := by
  have he : F-(-2*T*g)=(-2*T)*(P-g)+(-2*T)*rho+(-2)*zeta := by rw [heq];ring
  rw [he]
  have h1 := abs_add_le ((-2*T)*(P-g)+(-2*T)*rho) ((-2)*zeta)
  have h2 := abs_add_le ((-2*T)*(P-g)) ((-2*T)*rho)
  have hh := h1.trans (add_le_add h2 le_rfl)
  simpa only [abs_mul,abs_neg,abs_of_nonneg (by norm_num : (0:ℝ)≤2)] using hh

section Measure
variable {Ω : Type*} [MeasurableSpace Ω]

theorem comparison_scalar_density_three_L1_tendsto
    (mu : Measure Ω) (F P rho zeta : ℕ→Ω→ℝ) (g : Ω→ℝ) (T : ℝ)
    (hFi : ∀n,Integrable (F n) mu) (hPi : ∀n,Integrable (P n) mu)
    (hri : ∀n,Integrable (rho n) mu) (hzi : ∀n,Integrable (zeta n) mu)
    (hgi : Integrable g mu)
    (heq : ∀ᶠ n in atTop,∀ᵐ t∂mu,F n t=-2*T*(P n t+rho n t)-2*zeta n t)
    (hP : Tendsto (fun n=>∫t,|P n t-g t|∂mu) atTop (𝓝 0))
    (hr : Tendsto (fun n=>∫t,|rho n t|∂mu) atTop (𝓝 0))
    (hz : Tendsto (fun n=>∫t,|zeta n t|∂mu) atTop (𝓝 0)) :
    Tendsto (fun n=>∫t,|F n t-(-2*T*g t)|∂mu) atTop (𝓝 0) := by
  have hbound : ∀ᶠ n in atTop,(∫t,|F n t-(-2*T*g t)|∂mu)≤
      2*|T| *(∫t,|P n t-g t|∂mu)+2*|T| *(∫t,|rho n t|∂mu)+2*(∫t,|zeta n t|∂mu) := by
    filter_upwards [heq] with n hn
    have hi1 := ((hPi n).sub hgi).abs.const_mul (2*|T|)
    have hi2 := (hri n).abs.const_mul (2*|T|)
    have hi3 := (hzi n).abs.const_mul 2
    have hh := integral_mono_ae ((hFi n).sub (hgi.const_mul (-2*T))).abs
      ((hi1.add hi2).add hi3) (by
        filter_upwards [hn] with t ht
        exact comparison_scalar_density_error_bound ht)
    have hadd1 := integral_add (hi1.add hi2) hi3
    have hadd2 := integral_add hi1 hi2
    simp only [Pi.add_apply,Pi.sub_apply] at hadd1 hadd2 hh
    rw [hadd1,hadd2,integral_const_mul,integral_const_mul,integral_const_mul] at hh
    simpa only [Pi.add_apply,Pi.sub_apply] using hh
  have hlim : Tendsto (fun n=>2*|T| *(∫t,|P n t-g t|∂mu)+
      2*|T| *(∫t,|rho n t|∂mu)+2*(∫t,|zeta n t|∂mu)) atTop (𝓝 0) := by
    simpa only [mul_zero,add_zero] using ((hP.const_mul (2*|T|)).add
      (hr.const_mul (2*|T|))).add (hz.const_mul 2)
  exact squeeze_zero' (Eventually.of_forall (fun n=>integral_nonneg (fun t=>abs_nonneg _)))
    hbound hlim
end Measure

theorem comparison_high_native_gradient_L1_tendsto
    (d lam x : ℕ→ℝ) (Gamma alpha S B h0 b0 : ℕ→ℝ→ℝ) (g : ℝ→ℝ)
    {a b T : ℝ} (ha : 0≤a) (hb : 0<b) (hT : T≠0)
    (hdata : ∀ᶠ n in atTop,0<d n ∧ 0<lam n ∧ 0<x n ∧ lam n≤(d n)^2)
    (hlarge : Tendsto (fun n=>laplaceComparisonStrength (d n) (lam n) (x n)/(x n)^2)
      atTop atTop) :
    let K := fun n t=>comparisonNativeScalarClock (h0 n t) (b0 n t) (lam n)
      (x n*t) (S n (alpha n (x n*t)))
    let P := fun n t=>comparisonRescaledScalarResponse (Gamma n) T (x n) (K n t/(T*x n))
    let rho := fun n t=>(S n (alpha n (x n*t))-Gamma n (K n t))/(x n)^3
    let zeta := fun n t=>((b0 n t-T)*S n (alpha n (x n*t))+h0 n t)/(x n)^3
    let F := fun n t=>radiusComparisonGradient (laplaceComparisonStrength (d n) (lam n))
      (alpha n) (S n) (B n) (x n*t)/(x n)^3
    (∀n,IntegrableOn (F n) (Icc a b)) →
    (∀n,IntegrableOn (P n) (Icc a b)) →
    (∀n,IntegrableOn (rho n) (Icc a b)) →
    (∀n,IntegrableOn (zeta n) (Icc a b)) →
    IntegrableOn g (Icc a b) →
    Tendsto (fun n=>∫t in Icc a b,|P n t-g t|) atTop (𝓝 0) →
    Tendsto (fun n=>∫t in Icc a b,|rho n t|) atTop (𝓝 0) →
    Tendsto (fun n=>∫t in Icc a b,|zeta n t|) atTop (𝓝 0) →
    Tendsto (fun n=>∫t in Icc a b,|F n t-(-2*T*g t)|) atTop (𝓝 0) := by
  intro K P rho zeta F hFi hPi hri hzi hgi hP hr hz
  apply comparison_scalar_density_three_L1_tendsto (volume.restrict (Icc a b))
    F P rho zeta g T hFi hPi hri hzi hgi _ hP hr hz
  filter_upwards [hdata,comparison_high_strength_native_closure_eventually
    d lam x Gamma alpha S B h0 b0 hT hb hdata hlarge] with n hn he
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  have hxn : x n≠0 := hn.2.2.1.ne'
  have harg : T*x n*(K n t/(T*x n))=K n t := by field_simp
  have harg' : x n*(K n t/(T*x n))=K n t/T := by field_simp
  have hPexact : P n t=(Gamma n (K n t)-K n t/T)/(x n)^3 := by
    dsimp only [P,comparisonRescaledScalarResponse]
    rw [harg,harg']
  rw [hPexact]
  simpa only [F,K,rho,zeta,mul_div_assoc] using he t ⟨ha.trans ht.1,ht.2⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
