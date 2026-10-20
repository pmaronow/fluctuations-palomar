module

public import ComparisonScalarSupportZeros

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy
open scoped Topology
set_option maxHeartbeats 4000000
variable {Ω : Type*} [MeasurableSpace Ω]

def comparisonScalarMassClockOn (h0 b0 e S R : ℕ→Ω→ℝ) (n : ℕ) (v : Ω) : ℝ :=
  comparisonNativeScalarClock (h0 n v) (b0 n v) (e n v) (R n v) (S n v)

omit [MeasurableSpace Ω] in
theorem comparison_scalar_mass_response_exact_on (Gamma : ℕ→ℝ→ℝ)
    (h0 b0 e S R : ℕ→Ω→ℝ) (x : ℕ→ℝ) {T : ℝ}
    (hT : T≠0) (hx : ∀n,x n≠0) (n : ℕ) (v : Ω) :
    comparisonRescaledScalarResponse (Gamma n) T (x n)
      (comparisonScalarMassClockOn h0 b0 e S R n v/(T*x n)) =
      (e n v*(S n v-R n v)/(x n)^3)/T-
      (S n v-Gamma n (comparisonScalarMassClockOn h0 b0 e S R n v))/(x n)^3-
      (((b0 n v-T)*S n v+h0 n v)/(x n)^3)/T := by
  unfold comparisonRescaledScalarResponse comparisonScalarMassClockOn comparisonNativeScalarClock
  have harg : T*x n*((h0 n v+e n v*R n v+(b0 n v-e n v)*S n v)/(T*x n))=
      h0 n v+e n v*R n v+(b0 n v-e n v)*S n v := by field_simp [hT,hx n]
  rw [harg]
  field_simp [hT,hx n]
  ring

omit [MeasurableSpace Ω] in
theorem comparison_scalar_mass_clock_exact_on (h0 b0 e S R : ℕ→Ω→ℝ)
    (x : ℕ→ℝ) {T : ℝ} (hT : T≠0) (hx : ∀n,x n≠0) (n : ℕ) (v : Ω) :
    comparisonScalarMassClockOn h0 b0 e S R n v/(T*x n)-R n v/x n =
      (S n v/x n-R n v/x n)+(x n)^2/T*
        ((((b0 n v-T)*S n v+h0 n v)/(x n)^3)-e n v*(S n v-R n v)/(x n)^3) := by
  unfold comparisonScalarMassClockOn comparisonNativeScalarClock
  field_simp [hT,hx n]
  ring

theorem comparison_scalar_mass_response_L1_tendsto_on
    (mu : ℕ→Measure Ω) (Gamma : ℕ→ℝ→ℝ) (h0 b0 e S R : ℕ→Ω→ℝ) (x : ℕ→ℝ)
    {T : ℝ} (hT : 0<T) (hx : ∀n,x n≠0)
    (hmis : ∀n,Integrable (fun v=>e n v*(S n v-R n v)/(x n)^3) (mu n))
    (hcav : ∀n,Integrable (fun v=>(S n v-Gamma n (comparisonScalarMassClockOn h0 b0 e S R n v))/(x n)^3) (mu n))
    (hbare : ∀n,Integrable (fun v=>((b0 n v-T)*S n v+h0 n v)/(x n)^3) (mu n))
    (hmis0 : Tendsto (fun n=>∫v,|e n v*(S n v-R n v)/(x n)^3|∂mu n) atTop (𝓝 0))
    (hcav0 : Tendsto (fun n=>∫v,|(S n v-Gamma n (comparisonScalarMassClockOn h0 b0 e S R n v))/(x n)^3|∂mu n) atTop (𝓝 0))
    (hbare0 : Tendsto (fun n=>∫v,|((b0 n v-T)*S n v+h0 n v)/(x n)^3|∂mu n) atTop (𝓝 0)) :
    (∀n,Integrable (fun v=>comparisonRescaledScalarResponse (Gamma n) T (x n)
      (comparisonScalarMassClockOn h0 b0 e S R n v/(T*x n))) (mu n)) ∧
    Tendsto (fun n=>∫v,|comparisonRescaledScalarResponse (Gamma n) T (x n)
      (comparisonScalarMassClockOn h0 b0 e S R n v/(T*x n))|∂mu n) atTop (𝓝 0) := by
  let A := fun n v=>e n v*(S n v-R n v)/(x n)^3
  let B := fun n v=>(S n v-Gamma n (comparisonScalarMassClockOn h0 b0 e S R n v))/(x n)^3
  let C := fun n v=>((b0 n v-T)*S n v+h0 n v)/(x n)^3
  let F := fun n v=>comparisonRescaledScalarResponse (Gamma n) T (x n)
    (comparisonScalarMassClockOn h0 b0 e S R n v/(T*x n))
  have heq n : F n=(fun v=>A n v/T-B n v-C n v/T) := by
    funext v;exact comparison_scalar_mass_response_exact_on Gamma h0 b0 e S R x hT.ne' hx n v
  have hi n : Integrable (F n) (mu n) := heq n ▸ (((hmis n).div_const T).sub (hcav n)).sub ((hbare n).div_const T)
  refine ⟨hi,?_⟩
  have hbound n : (∫v,|F n v|∂mu n) ≤
      (∫v,|A n v|∂mu n)/T+(∫v,|B n v|∂mu n)+(∫v,|C n v|∂mu n)/T := by
    have hpoint v : |F n v| ≤ |A n v|/T+|B n v|+|C n v|/T := by
      rw [heq n]
      have h1 : |A n v/T-B n v-C n v/T| ≤ |A n v/T-B n v|+|C n v/T| := by
        simpa only [sub_eq_add_neg,abs_neg] using abs_add_le (A n v/T-B n v) (-(C n v/T))
      have h2 : |A n v/T-B n v| ≤ |A n v/T|+|B n v| := by
        simpa only [sub_eq_add_neg,abs_neg] using abs_add_le (A n v/T) (-(B n v))
      simp only [abs_div,abs_of_pos hT] at h1 h2
      linarith
    have hiA : Integrable (fun v=>|A n v|/T) (mu n) := (hmis n).abs.div_const T
    have hiB : Integrable (fun v=>|B n v|) (mu n) := (hcav n).abs
    have hiC : Integrable (fun v=>|C n v|/T) (mu n) := (hbare n).abs.div_const T
    have hiAB : Integrable (fun v=>|A n v|/T+|B n v|) (mu n) := hiA.add hiB
    have hR : Integrable (fun v=>|A n v|/T+|B n v|+|C n v|/T) (mu n) := hiAB.add hiC
    calc
      _ ≤ ∫v,(|A n v|/T+|B n v|+|C n v|/T)∂mu n :=
        integral_mono_ae (hi n).abs hR (Eventually.of_forall hpoint)
      _ = _ := by rw [integral_add hiAB hiC,integral_add hiA hiB,integral_div,integral_div]
  have hz := ((hmis0.div_const T).add hcav0).add (hbare0.div_const T)
  exact squeeze_zero (fun n=>integral_nonneg (fun _=>abs_nonneg _)) hbound (by simpa using hz)

theorem comparison_scalar_mass_clock_L1_tendsto_on
    (mu : ℕ→Measure Ω) (h0 b0 e S R : ℕ→Ω→ℝ) (x : ℕ→ℝ)
    {T : ℝ} (hT : 0<T) (hx : ∀n,x n≠0) (hx0 : Tendsto x atTop (𝓝 0))
    (hspin : ∀n,Integrable (fun v=>S n v/x n-R n v/x n) (mu n))
    (hmis : ∀n,Integrable (fun v=>e n v*(S n v-R n v)/(x n)^3) (mu n))
    (hbare : ∀n,Integrable (fun v=>((b0 n v-T)*S n v+h0 n v)/(x n)^3) (mu n))
    (hspin0 : Tendsto (fun n=>∫v,|S n v/x n-R n v/x n|∂mu n) atTop (𝓝 0))
    (hmis0 : Tendsto (fun n=>∫v,|e n v*(S n v-R n v)/(x n)^3|∂mu n) atTop (𝓝 0))
    (hbare0 : Tendsto (fun n=>∫v,|((b0 n v-T)*S n v+h0 n v)/(x n)^3|∂mu n) atTop (𝓝 0)) :
    (∀n,Integrable (fun v=>comparisonScalarMassClockOn h0 b0 e S R n v/(T*x n)-R n v/x n) (mu n)) ∧
    Tendsto (fun n=>∫v,|comparisonScalarMassClockOn h0 b0 e S R n v/(T*x n)-R n v/x n|∂mu n) atTop (𝓝 0) := by
  let A := fun n v=>S n v/x n-R n v/x n
  let B := fun n v=>e n v*(S n v-R n v)/(x n)^3
  let C := fun n v=>((b0 n v-T)*S n v+h0 n v)/(x n)^3
  let F := fun n v=>comparisonScalarMassClockOn h0 b0 e S R n v/(T*x n)-R n v/x n
  have heq n : F n=(fun v=>A n v+(x n)^2/T*(C n v-B n v)) := by
    funext v;exact comparison_scalar_mass_clock_exact_on h0 b0 e S R x hT.ne' hx n v
  have hi n : Integrable (F n) (mu n) := heq n ▸ (hspin n).add (((hbare n).sub (hmis n)).const_mul ((x n)^2/T))
  refine ⟨hi,?_⟩
  have hbound n : (∫v,|F n v|∂mu n) ≤ (∫v,|A n v|∂mu n)+
      (x n)^2/T*((∫v,|C n v|∂mu n)+(∫v,|B n v|∂mu n)) := by
    have hk : 0 ≤ (x n)^2/T := div_nonneg (sq_nonneg _) hT.le
    have hpoint v : |F n v| ≤ |A n v|+(x n)^2/T*(|C n v|+|B n v|) := by
      rw [heq n]
      have hh := abs_add_le (A n v) ((x n)^2/T*(C n v-B n v))
      rw [abs_mul,abs_of_nonneg hk] at hh
      have hsub : |C n v-B n v| ≤ |C n v|+|B n v| := by
        simpa only [sub_eq_add_neg,abs_neg] using abs_add_le (C n v) (-(B n v))
      exact hh.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hsub hk))
    have hiA : Integrable (fun v=>|A n v|) (mu n) := (hspin n).abs
    have hiB : Integrable (fun v=>|B n v|) (mu n) := (hmis n).abs
    have hiC : Integrable (fun v=>|C n v|) (mu n) := (hbare n).abs
    have hiBC : Integrable (fun v=>(x n)^2/T*(|C n v|+|B n v|)) (mu n) := (hiC.add hiB).const_mul _
    have hR : Integrable (fun v=>|A n v|+(x n)^2/T*(|C n v|+|B n v|)) (mu n) := hiA.add hiBC
    calc
      _ ≤ ∫v,(|A n v|+(x n)^2/T*(|C n v|+|B n v|))∂mu n :=
        integral_mono_ae (hi n).abs hR (Eventually.of_forall hpoint)
      _ = _ := by rw [integral_add hiA hiBC,integral_const_mul,integral_add hiC hiB]
  have hz := hspin0.add (((hx0.pow 2).div_const T).mul (hbare0.add hmis0))
  exact squeeze_zero (fun n=>integral_nonneg (fun _=>abs_nonneg _)) hbound (by simpa using hz)

theorem comparison_scalar_mass_support_zero_on
    (mu : ℕ→Measure Ω) (hfinite : ∀n,IsFiniteMeasure (mu n))
    (Gamma : ℕ→ℝ→ℝ) (h0 b0 e S R : ℕ→Ω→ℝ) (x : ℕ→ℝ) (g : ℝ→ℝ)
    {T t : ℝ} (hT : 0<T) (hx : ∀n,x n≠0) (hx0 : Tendsto x atTop (𝓝 0))
    (hR : ∀n,Measurable (R n))
    (hspin : ∀n,Integrable (fun v=>S n v/x n-R n v/x n) (mu n))
    (hmis : ∀n,Integrable (fun v=>e n v*(S n v-R n v)/(x n)^3) (mu n))
    (hcav : ∀n,Integrable (fun v=>(S n v-Gamma n (comparisonScalarMassClockOn h0 b0 e S R n v))/(x n)^3) (mu n))
    (hbare : ∀n,Integrable (fun v=>((b0 n v-T)*S n v+h0 n v)/(x n)^3) (mu n))
    (hspin0 : Tendsto (fun n=>∫v,|S n v/x n-R n v/x n|∂mu n) atTop (𝓝 0))
    (hmis0 : Tendsto (fun n=>∫v,|e n v*(S n v-R n v)/(x n)^3|∂mu n) atTop (𝓝 0))
    (hcav0 : Tendsto (fun n=>∫v,|(S n v-Gamma n (comparisonScalarMassClockOn h0 b0 e S R n v))/(x n)^3|∂mu n) atTop (𝓝 0))
    (hbare0 : Tendsto (fun n=>∫v,|((b0 n v-T)*S n v+h0 n v)/(x n)^3|∂mu n) atTop (𝓝 0))
    (hmass : ∀eps : ℝ,0<eps→∃c : ℝ,0<c ∧
      ∀ᶠ n in atTop,c ≤ (mu n).real {v | |R n v/x n-t|<eps})
    (hG : TendstoLocallyUniformly (fun n=>comparisonRescaledScalarResponse (Gamma n) T (x n)) g atTop)
    (hg : ContinuousAt g t) : g t=0 := by
  have hresponse := comparison_scalar_mass_response_L1_tendsto_on mu Gamma h0 b0 e S R x hT hx
    hmis hcav hbare hmis0 hcav0 hbare0
  have hclock := comparison_scalar_mass_clock_L1_tendsto_on mu h0 b0 e S R x hT hx hx0
    hspin hmis hbare hspin0 hmis0 hbare0
  exact comparison_scalar_zero_of_positive_normalized_mass mu hfinite
    (fun n v=>R n v/x n) (fun n v=>comparisonScalarMassClockOn h0 b0 e S R n v/(T*x n))
    (fun n=>comparisonRescaledScalarResponse (Gamma n) T (x n)) g (fun n=>(hR n).div_const _)
    (fun n=>(hresponse.1 n).abs) (fun n=>(hclock.1 n).abs) hresponse.2 hclock.2 hmass hG hg

end OAI.SKFluctuations.LaplaceWindowFormalization
