module

public import ComparisonNormalizedClockCoupling

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy ProbabilityTheory
open scoped Topology
set_option maxHeartbeats 3000000

section CDF
variable {Ω : Type*} [MeasurableSpace Ω]

theorem comparison_clock_cdf_support_mass_below_cut
    (μ : ℕ → Measure Ω) (hfinite : ∀n, IsFiniteMeasure (μ n))
    (q : ℕ → Ω → ℝ) (hq : ∀n, Measurable (q n)) (V : ℝ → ℝ) {R t : ℝ}
    (ht : t < R)
    (hV : ∀a ≤ R, Tendsto (fun n => comparisonClockCDF (μ n) (q n) a) atTop (𝓝 (V a)))
    (hsupport : ∀δ : ℝ, 0 < δ → t + δ < R → V (t-δ) < V (t+δ)) :
    ∀eps : ℝ, 0 < eps → ∃c : ℝ, 0 < c ∧
      ∀ᶠ n in atTop, c ≤ (μ n).real {w | |q n w-t| < eps} := by
  intro eps heps
  let δ := min (eps/2) ((R-t)/2)
  have hd : 0 < δ := lt_min (by positivity) (by linarith)
  have hde : δ ≤ eps/2 := min_le_left _ _
  have hdr : δ ≤ (R-t)/2 := min_le_right _ _
  have htr : t+δ < R := by linarith
  have hp := hsupport δ hd htr
  let c := (V (t+δ)-V (t-δ))/2
  have hc : 0 < c := by dsimp [c]; linarith
  have hlim := (hV (t+δ) htr.le).sub (hV (t-δ) (by linarith))
  have hev := hlim.eventually (lt_mem_nhds (show c < V (t+δ)-V (t-δ) by dsimp [c]; linarith))
  refine ⟨c,hc,?_⟩
  filter_upwards [hev] with n hn
  let _ := hfinite n
  have hid := comparison_clock_cdf_interval_mass (μ n) (q n) (hq n)
    (show t-δ ≤ t+δ by linarith)
  have hsub : {w | t-δ < q n w ∧ q n w ≤ t+δ} ⊆ {w | |q n w-t| < eps} := by
    intro w hw
    change t-δ < q n w ∧ q n w ≤ t+δ at hw
    change |q n w-t| < eps
    exact abs_lt.mpr ⟨by linarith [hw.1],by linarith [hw.2]⟩
  exact (hn.le.trans_eq hid.symm).trans (measureReal_mono hsub)

theorem comparison_scalar_zero_of_cdf_support_below_cut
    (μ : ℕ → Measure Ω) (hfinite : ∀n, IsFiniteMeasure (μ n))
    (radius clock : ℕ → Ω → ℝ) (G : ℕ → ℝ → ℝ) (g V : ℝ → ℝ) {R t : ℝ}
    (ht : t < R) (hr : ∀n, Measurable (radius n))
    (hV : ∀a ≤ R, Tendsto (fun n => comparisonClockCDF (μ n) (radius n) a) atTop (𝓝 (V a)))
    (hsupport : ∀δ : ℝ, 0 < δ → t+δ < R → V (t-δ) < V (t+δ))
    (hGint : ∀n, Integrable (fun w => |G n (clock n w)|) (μ n))
    (hKint : ∀n, Integrable (fun w => |clock n w-radius n w|) (μ n))
    (hGzero : Tendsto (fun n => ∫w, |G n (clock n w)|∂μ n) atTop (𝓝 0))
    (hKzero : Tendsto (fun n => ∫w, |clock n w-radius n w|∂μ n) atTop (𝓝 0))
    (hG : TendstoLocallyUniformly G g atTop) (hg : ContinuousAt g t) : g t=0 := by
  exact comparison_scalar_zero_of_positive_normalized_mass μ hfinite radius clock G g hr
    hGint hKint hGzero hKzero
    (comparison_clock_cdf_support_mass_below_cut μ hfinite radius hr V ht hV hsupport) hG hg
end CDF

theorem comparison_actual_radius_cdf_support_mass
    (r : ℕ → ℝ → ℝ) (x v : ℕ → ℝ) (V : ℝ → ℝ) {R t : ℝ}
    (hr : ∀n, MonotoneOn (r n) (Icc (0:ℝ) 1))
    (hrb : ∀n u, u ∈ Icc (0:ℝ) 1 → r n u ∈ Icc (0:ℝ) 1)
    (hx : ∀n, 0 < x n) (hv : ∀n, v n ∈ Icc (0:ℝ) 1)
    (hcut : ∀ᶠ n in atTop, x n*R < r n (v n))
    (hV : ∀a ≤ R, Tendsto (fun n => (quantileMassProfile (r n) (hrb n)).val (x n*a)/x n)
      atTop (𝓝 (V a))) (ht : t < R)
    (hsupport : ∀δ : ℝ, 0 < δ → t+δ < R → V (t-δ) < V (t+δ)) :
    ∀eps : ℝ, 0 < eps → ∃c : ℝ, 0 < c ∧
      ∀ᶠ n in atTop, c ≤ (comparisonNormalizedClockMass (x n) (v n)).real
        {w : ParisiFinite.OrderPoint | |r n (w:ℝ)/x n-t| < eps} := by
  have hrm n : Measurable (fun w : ParisiFinite.OrderPoint => r n (w:ℝ)/x n) := by
    have hm : Monotone (fun w : ParisiFinite.OrderPoint => r n (w:ℝ)) :=
      fun a b hab => hr n a.property b.property hab
    exact hm.measurable.div_const _
  have hVi : ∀a ≤ R, Tendsto (fun n => comparisonClockCDF
      (comparisonNormalizedClockMass (x n) (v n)) (fun w => r n (w:ℝ)/x n) a)
      atTop (𝓝 (V a)) := by
    intro a ha
    apply (hV a ha).congr'
    filter_upwards [hcut] with n hn
    exact (comparison_normalized_clock_cdf_exact (r n) (hr n) (hrb n) (hx n) (hv n) ha hn).symm
  exact comparison_clock_cdf_support_mass_below_cut
    (fun n => comparisonNormalizedClockMass (x n) (v n)) (fun _ => inferInstance)
    (fun n w => r n (w:ℝ)/x n) hrm V ht hVi hsupport

theorem comparison_actual_scalar_zero_of_radius_cdf_support
    (r : ℕ → ℝ → ℝ) (x v : ℕ → ℝ) (V : ℝ → ℝ)
    (clock : ℕ → ParisiFinite.OrderPoint → ℝ) (G : ℕ → ℝ → ℝ) (g : ℝ → ℝ) {R t : ℝ}
    (hr : ∀n, MonotoneOn (r n) (Icc (0:ℝ) 1))
    (hrb : ∀n u, u ∈ Icc (0:ℝ) 1 → r n u ∈ Icc (0:ℝ) 1)
    (hx : ∀n, 0 < x n) (hv : ∀n, v n ∈ Icc (0:ℝ) 1)
    (hcut : ∀ᶠ n in atTop, x n*R < r n (v n))
    (hV : ∀a ≤ R, Tendsto (fun n => (quantileMassProfile (r n) (hrb n)).val (x n*a)/x n)
      atTop (𝓝 (V a))) (ht : t < R)
    (hsupport : ∀δ : ℝ, 0 < δ → t+δ < R → V (t-δ) < V (t+δ))
    (hGint : ∀n, Integrable (fun w => |G n (clock n w)|) (comparisonNormalizedClockMass (x n) (v n)))
    (hKint : ∀n, Integrable (fun w => |clock n w-r n (w:ℝ)/x n|) (comparisonNormalizedClockMass (x n) (v n)))
    (hGzero : Tendsto (fun n => ∫w, |G n (clock n w)|∂comparisonNormalizedClockMass (x n) (v n)) atTop (𝓝 0))
    (hKzero : Tendsto (fun n => ∫w, |clock n w-r n (w:ℝ)/x n|∂comparisonNormalizedClockMass (x n) (v n)) atTop (𝓝 0))
    (hG : TendstoLocallyUniformly G g atTop) (hg : ContinuousAt g t) : g t=0 := by
  have hrm n : Measurable (fun w : ParisiFinite.OrderPoint => r n (w:ℝ)/x n) := by
    have hm : Monotone (fun w : ParisiFinite.OrderPoint => r n (w:ℝ)) :=
      fun a b hab => hr n a.property b.property hab
    exact hm.measurable.div_const _
  exact comparison_scalar_zero_of_positive_normalized_mass
    (fun n => comparisonNormalizedClockMass (x n) (v n)) (fun _ => inferInstance)
    (fun n w => r n (w:ℝ)/x n) clock G g hrm hGint hKint hGzero hKzero
    (comparison_actual_radius_cdf_support_mass r x v V hr hrb hx hv hcut hV ht hsupport) hG hg

end OAI.SKFluctuations.LaplaceWindowFormalization
