module

public import ComparisonScalarMassClosureOn
public import Mathlib.Analysis.Normed.Group.Bounded

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy
open scoped Topology ENNReal
set_option maxHeartbeats 4000000

theorem comparison_scalar_compact_response_eventually_bounded
    (G : ℕ → ℝ → ℝ) (g : ℝ → ℝ) {R : ℝ}
    (hG : TendstoUniformlyOn G g atTop (Icc (0:ℝ) R))
    (hg : ContinuousOn g (Icc (0:ℝ) R)) :
    ∃M : ℝ, 0 < M ∧ ∀ᶠ n in atTop, ∀r ∈ Icc (0:ℝ) R, |G n r| ≤ M := by
  obtain ⟨B,hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hg
  refine ⟨max B 0+1,by positivity,?_⟩
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hG) 1 (by norm_num)] with n hn r hr
  have hd : |G n r-g r| < 1 := by simpa only [Real.dist_eq,abs_sub_comm] using hn r hr
  have hb : |g r| ≤ B := by simpa only [Real.norm_eq_abs] using hB r hr
  have hh : |G n r| ≤ |G n r-g r|+|g r| := by
    simpa only [sub_add_cancel] using abs_add_le (G n r-g r) (g r)
  linarith [le_max_left B 0]

theorem comparison_scalar_native_clock_scaled_mem_Icc
    {d lam T x h0 b0 S R H A B Bclock : ℝ}
    (hT : 0 < T) (hx : 0 < x) (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hb0 : lam ≤ b0) (hb0max : b0 ≤ Bclock) (hBclock : 0 ≤ Bclock)
    (hh0 : 0 ≤ h0) (hh0max : h0 ≤ H*x)
    (hS : 0 ≤ S) (hSmax : S ≤ B*x) (hR : 0 ≤ R) (hRmax : R ≤ A*x) :
    comparisonNativeScalarClock h0 b0 (laplaceComparisonStrength d lam R) R S/(T*x) ∈
      Icc (0:ℝ) ((H+A+Bclock*B)/T) := by
  let e := laplaceComparisonStrength d lam R
  have he0 : 0 ≤ e := by
    unfold e laplaceComparisonStrength comparisonStrength
    exact mul_nonneg hlam (laplaceComparisonShape_pos _).le
  have hel : e ≤ lam := laplaceComparisonStrength_le d hlam R
  have hek : e ≤ 1 := hel.trans hlam1
  have hbe : 0 ≤ b0-e := sub_nonneg.mpr (hel.trans hb0)
  have hclock : 0 ≤ comparisonNativeScalarClock h0 b0 e R S := by
    unfold comparisonNativeScalarClock
    exact add_nonneg (add_nonneg hh0 (mul_nonneg he0 hR)) (mul_nonneg hbe hS)
  have her : e*R ≤ R := by nlinarith
  have hbs : b0*S ≤ Bclock*(B*x) :=
    (mul_le_mul_of_nonneg_right hb0max hS).trans (mul_le_mul_of_nonneg_left hSmax hBclock)
  have hup : comparisonNativeScalarClock h0 b0 e R S ≤ (H+A+Bclock*B)*x := by
    unfold comparisonNativeScalarClock
    nlinarith [mul_nonneg he0 hS]
  refine ⟨div_nonneg hclock (mul_pos hT hx).le,?_⟩
  apply (div_le_iff₀ (mul_pos hT hx)).mpr
  calc
    _ ≤ (H+A+Bclock*B)*x := hup
    _ = ((H+A+Bclock*B)/T)*(T*x) := by field_simp [hT.ne']

section Mass
variable {Ω : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
theorem comparison_scalar_weighted_error_reconstruction_on
    (Gamma : ℕ → ℝ → ℝ) (h0 b0 e S R : ℕ → Ω → ℝ) (x : ℕ → ℝ)
    {T : ℝ} (hT : T ≠ 0) (hx : ∀n, x n ≠ 0) (n : ℕ) (w : Ω) :
    e n w*(S n w-R n w)/(x n)^3=
      T*comparisonRescaledScalarResponse (Gamma n) T (x n)
        (comparisonScalarMassClockOn h0 b0 e S R n w/(T*x n))+
      T*((S n w-Gamma n (comparisonScalarMassClockOn h0 b0 e S R n w))/(x n)^3)+
      ((b0 n w-T)*S n w+h0 n w)/(x n)^3 := by
  rw [comparison_scalar_mass_response_exact_on Gamma h0 b0 e S R x hT hx n w]
  field_simp [hT,hx n]
  ring

theorem comparison_scalar_floor_charge_le
    (μ : Measure Ω) [IsFiniteMeasure μ] (F : Set Ω) (hF : MeasurableSet F)
    (W C B clock : Ω → ℝ) (G : ℝ → ℝ) {T M : ℝ} (hT : 0 < T)
    (hW : Integrable W μ) (hC : Integrable C μ) (hB : Integrable B μ)
    (heq : ∀w, W w=T*G (clock w)+T*C w+B w)
    (hbound : ∀ᵐ w ∂μ, w ∈ F → |G (clock w)| ≤ M) :
    (∫w in F, |W w|∂μ) ≤ T*M*μ.real F+T*(∫w, |C w|∂μ)+(∫w, |B w|∂μ) := by
  have hpoint : ∀ᵐ w ∂μ.restrict F, |W w| ≤ T*M+T*|C w|+|B w| := by
    filter_upwards [ae_restrict_of_ae hbound,ae_restrict_mem hF] with w hw hwF
    rw [heq w]
    have h1 := abs_add_le (T*G (clock w)+T*C w) (B w)
    have h2 := abs_add_le (T*G (clock w)) (T*C w)
    rw [abs_mul,abs_mul,abs_of_pos hT] at h2
    have hh := mul_le_mul_of_nonneg_left (hw hwF) hT.le
    linarith
  have hi1 : Integrable (fun w => T*M+T*|C w|) (μ.restrict F) :=
    (integrable_const _).add (hC.abs.integrableOn.const_mul T)
  have hi2 := hi1.add hB.abs.integrableOn
  have hh := integral_mono_ae hW.abs.integrableOn hi2 hpoint
  have hiC : Integrable (fun w => T*|C w|) (μ.restrict F) := hC.abs.integrableOn.const_mul T
  have hiB : Integrable (fun w => |B w|) (μ.restrict F) := hB.abs.integrableOn
  have e1 := integral_add hi1 hiB
  have e2 := integral_add (integrable_const (T*M) : Integrable (fun _ : Ω => T*M) (μ.restrict F)) hiC
  simp only [Pi.add_apply] at hh
  rw [e1,e2,integral_const,integral_const_mul] at hh
  simp only [smul_eq_mul,measureReal_restrict_apply_univ] at hh
  have hc := setIntegral_le_integral (s:=F) hC.abs (Eventually.of_forall fun w => abs_nonneg _)
  have hb := setIntegral_le_integral (s:=F) hB.abs (Eventually.of_forall fun w => abs_nonneg _)
  nlinarith

theorem comparison_scalar_floor_weighted_L1_tendsto
    (μ : ℕ → Measure Ω) (hfinite : ∀n, IsFiniteMeasure (μ n))
    (F : ℕ → Set Ω) (hF : ∀n, MeasurableSet (F n))
    (W C B clock : ℕ → Ω → ℝ) (G : ℕ → ℝ → ℝ) (g : ℝ → ℝ) {T R : ℝ}
    (hT : 0 < T) (hW : ∀n, Integrable (W n) (μ n))
    (hC : ∀n, Integrable (C n) (μ n)) (hB : ∀n, Integrable (B n) (μ n))
    (heq : ∀n w, W n w=T*G n (clock n w)+T*C n w+B n w)
    (hclock : ∀ᶠ n in atTop, ∀ᵐ w ∂μ n, w ∈ F n → clock n w ∈ Icc (0:ℝ) R)
    (hG : TendstoUniformlyOn G g atTop (Icc (0:ℝ) R))
    (hg : ContinuousOn g (Icc (0:ℝ) R))
    (hfloor0 : Tendsto (fun n => (μ n).real (F n)) atTop (𝓝 0))
    (hC0 : Tendsto (fun n => ∫w, |C n w|∂μ n) atTop (𝓝 0))
    (hB0 : Tendsto (fun n => ∫w, |B n w|∂μ n) atTop (𝓝 0)) :
    Tendsto (fun n => ∫w in F n, |W n w|∂μ n) atTop (𝓝 0) := by
  obtain ⟨M,_,hM⟩ := comparison_scalar_compact_response_eventually_bounded G g hG hg
  have hb : ∀ᶠ n in atTop, (∫w in F n, |W n w|∂μ n) ≤
      T*M*(μ n).real (F n)+T*(∫w, |C n w|∂μ n)+(∫w, |B n w|∂μ n) := by
    filter_upwards [hclock,hM] with n hn hMn
    let _ := hfinite n
    apply comparison_scalar_floor_charge_le (μ n) (F n) (hF n) (W n) (C n) (B n) (clock n)
      (G n) hT (hW n) (hC n) (hB n) (heq n)
    exact hn.mono fun w hw hwF => hMn _ (hw hwF)
  exact squeeze_zero' (Eventually.of_forall fun n => integral_nonneg (fun w => abs_nonneg _)) hb
    (by simpa using ((hfloor0.const_mul (T*M)).add (hC0.const_mul T)).add hB0)

end Mass
end OAI.SKFluctuations.LaplaceWindowFormalization
