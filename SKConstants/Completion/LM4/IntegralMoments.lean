module

public import SKConstants.ConcentrationMoments
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.Mul

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory

namespace SKConstants.Completion.LM4

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem integrable_abs_add_pow {f g : Ω → ℝ} (hf : Measurable f) (hg : Measurable g)
    (p : ℕ) (hIf : Integrable (fun ω => |f ω| ^ p) μ)
    (hIg : Integrable (fun ω => |g ω| ^ p) μ) :
    Integrable (fun ω => |f ω + g ω| ^ p) μ := by
  apply ((hIf.add hIg).const_mul (2 ^ (p - 1))).mono' (by fun_prop)
  apply Filter.Eventually.of_forall
  intro ω
  simpa only [Real.norm_eq_abs, abs_pow, abs_abs, Pi.add_apply] using
    (pow_le_pow_left₀ (abs_nonneg _) (abs_add_le (f ω) (g ω)) p).trans
      (add_pow_le (abs_nonneg _) (abs_nonneg _) p)

theorem integral_abs_add_pow_le {f g : Ω → ℝ} {A B K : ℝ} {p : ℕ}
    (hf : Measurable f) (hg : Measurable g) (hA : 0 < A) (hB : 0 < B)
    (hIf : Integrable (fun ω => |f ω| ^ p) μ)
    (hIg : Integrable (fun ω => |g ω| ^ p) μ)
    (hMf : (∫ ω, |f ω| ^ p ∂μ) ≤ K * A ^ p)
    (hMg : (∫ ω, |g ω| ^ p ∂μ) ≤ K * B ^ p) :
    Integrable (fun ω => |f ω + g ω| ^ p) μ ∧
      (∫ ω, |f ω + g ω| ^ p ∂μ) ≤ K * (A + B) ^ p := by
  let D := A + B
  have hD : 0 < D := add_pos hA hB
  let R : Ω → ℝ := fun ω => D ^ p *
    ((A / D) * (|f ω| / A) ^ p + (B / D) * (|g ω| / B) ^ p)
  have hR : Integrable R μ := by
    dsimp [R]
    simpa only [div_pow, Pi.add_apply] using
      (((hIf.div_const (A ^ p)).const_mul (A / D)).add
        ((hIg.div_const (B ^ p)).const_mul (B / D))).const_mul (D ^ p)
  have hdom (ω : Ω) : |f ω + g ω| ^ p ≤ R ω := by
    have hc := (convexOn_pow (𝕜 := ℝ) p).2
      (div_nonneg (abs_nonneg (f ω)) hA.le) (div_nonneg (abs_nonneg (g ω)) hB.le)
      (show 0 ≤ A / D by positivity) (show 0 ≤ B / D by positivity)
      (show A / D + B / D = 1 by dsimp [D]; field_simp)
    simp only [smul_eq_mul] at hc
    have he : A / D * (|f ω| / A) + B / D * (|g ω| / B) =
        (|f ω| + |g ω|) / D := by field_simp
    rw [he, div_pow] at hc
    have hh := (div_le_iff₀ (pow_pos hD p)).mp hc
    exact (pow_le_pow_left₀ (abs_nonneg _) (abs_add_le _ _) p).trans (by
      simpa only [R, mul_comm] using hh)
  have hI : Integrable (fun ω => |f ω + g ω| ^ p) μ := by
    apply hR.mono' (by fun_prop)
    exact .of_forall (fun ω => by simpa only [Real.norm_eq_abs, abs_pow, abs_abs] using hdom ω)
  refine ⟨hI, (integral_mono hI hR hdom).trans ?_⟩
  calc
    (∫ ω, R ω ∂μ) = D ^ p *
        ((A / D) * ((∫ ω, |f ω| ^ p ∂μ) / A ^ p) +
          (B / D) * ((∫ ω, |g ω| ^ p ∂μ) / B ^ p)) := by
      dsimp [R]
      simp_rw [div_pow]
      rw [integral_const_mul, integral_add
        ((hIf.div_const (A ^ p)).const_mul (A / D))
        ((hIg.div_const (B ^ p)).const_mul (B / D))]
      simp_rw [integral_const_mul, integral_div]
    _ ≤ D ^ p * ((A / D) * K + (B / D) * K) := by
      gcongr
      · exact (div_le_iff₀ (pow_pos hA p)).mpr hMf
      · exact (div_le_iff₀ (pow_pos hB p)).mpr hMg
    _ = K * (A + B) ^ p := by
      dsimp [D]
      field_simp

theorem integral_abs_centered_pow_le [IsProbabilityMeasure μ]
    {Y : Ω → ℝ} (hY : Measurable Y) (hI : Integrable Y μ)
    {p : ℕ} (hp : 1 ≤ p) (hIp : Integrable (fun ω => |Y ω| ^ p) μ) :
    Integrable (fun ω => |Y ω - ∫ u, Y u ∂μ| ^ p) μ ∧
      (∫ ω, |Y ω - ∫ u, Y u ∂μ| ^ p ∂μ) ≤
        2 ^ p * (∫ ω, |Y ω| ^ p ∂μ) := by
  have hJ := (convexOn_pow (𝕜 := ℝ) p).map_integral_le
    (by fun_prop) isClosed_Ici (ae_of_all _ (fun ω => abs_nonneg (Y ω))) hI.abs hIp
  have hMean : |∫ ω, Y ω ∂μ| ^ p ≤ ∫ ω, |Y ω| ^ p ∂μ := by
    exact (pow_le_pow_left₀ (abs_nonneg _)
      (by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm Y) p).trans hJ
  let R : Ω → ℝ := fun ω =>
    2 ^ (p - 1) * (|Y ω| ^ p + |∫ u, Y u ∂μ| ^ p)
  have hR : Integrable R μ := (hIp.add (integrable_const _)).const_mul _
  have hdom (ω : Ω) : |Y ω - ∫ u, Y u ∂μ| ^ p ≤ R ω :=
    (pow_le_pow_left₀ (abs_nonneg _) (abs_sub _ _) p).trans
      (add_pow_le (abs_nonneg _) (abs_nonneg _) p)
  have hIc : Integrable (fun ω => |Y ω - ∫ u, Y u ∂μ| ^ p) μ := by
    apply hR.mono' (by fun_prop)
    exact .of_forall (fun ω => by simpa only [Real.norm_eq_abs, abs_pow, abs_abs] using hdom ω)
  refine ⟨hIc, (integral_mono hIc hR hdom).trans ?_⟩
  calc
    (∫ ω, R ω ∂μ) = 2 ^ (p - 1) *
        ((∫ ω, |Y ω| ^ p ∂μ) + |∫ u, Y u ∂μ| ^ p) := by
      dsimp [R]
      rw [integral_const_mul, integral_add hIp (integrable_const _)]
      simp
    _ ≤ 2 ^ (p - 1) * ((∫ ω, |Y ω| ^ p ∂μ) + (∫ ω, |Y ω| ^ p ∂μ)) := by
      gcongr
    _ = _ := by
      have he : (2 : ℝ) ^ (p - 1) * 2 = 2 ^ p := by
        rw [← pow_succ, Nat.sub_add_cancel hp]
      calc
        _ = (2 ^ (p - 1) * 2) * (∫ ω, |Y ω| ^ p ∂μ) := by ring
        _ = _ := by rw [he]

end SKConstants.Completion.LM4
