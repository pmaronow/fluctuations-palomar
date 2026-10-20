module

public import MacroQuantileCompetitors
public import JointScalarNearMinimum
public import ActualMacroEnvelope

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

theorem mass_strength_objective_l1_comparison (n : ℕ) (hn : 0 < n)
    (b h w q z : ℝ → ℝ) {W : ℝ} (hW : 0 ≤ W)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (hw : MonotoneOn w (Icc (0:ℝ) 1)) (hq : MonotoneOn q (Icc (0:ℝ) 1))
    (hz : MonotoneOn z (Icc (0:ℝ) 1))
    (hwb : ∀ u ∈ Icc (0:ℝ) 1, w u ∈ Icc (0:ℝ) W)
    (hqb : ∀ u ∈ Icc (0:ℝ) 1, q u ∈ Icc (0:ℝ) 1)
    (hzb : ∀ u ∈ Icc (0:ℝ) 1, z u ∈ Icc (0:ℝ) 1)
    (hb0 : 0 ≤ b 0) (hh0 : 0 ≤ h 0) :
    |massStrengthObjective n b h w q-massStrengthObjective n b h w z| ≤
      W*(∫u in (0:ℝ)..1,|q u-z u|) := by
  have hfield (f : ℝ → ℝ) (hf : MonotoneOn f (Icc (0:ℝ) 1))
      (hfb : ∀ u ∈ Icc (0:ℝ) 1, f u ∈ Icc (0:ℝ) 1) :
      MonotoneOn (fun u => h u+w u*f u) (Icc (0:ℝ) 1) := by
    intro u hu v hv huv
    exact add_le_add (hh hu hv huv)
      (mul_le_mul (hw hu hv huv) (hf hu hv huv) (hfb u hu).1 (hwb v hv).1)
  have h00 : (0:ℝ) ∈ Icc (0:ℝ) 1 := by norm_num
  have hp := realOrderedSKPathPressure_l1_comparison n hn b (fun u => h u+w u*q u)
    b (fun u => h u+w u*z u) hb (hfield q hq hqb) hb (hfield z hz hzb)
    hb0 (add_nonneg hh0 (mul_nonneg (hwb 0 h00).1 (hqb 0 h00).1))
    hb0 (add_nonneg hh0 (mul_nonneg (hwb 0 h00).1 (hzb 0 h00).1)) 0
  simp only [sub_self,abs_zero,intervalIntegral.integral_zero,mul_zero,zero_add] at hp
  have hiq : IntervalIntegrable q volume 0 1 :=
    (show MonotoneOn q (uIcc (0:ℝ) 1) by simpa using hq).intervalIntegrable
  have hiz : IntervalIntegrable z volume 0 1 :=
    (show MonotoneOn z (uIcc (0:ℝ) 1) by simpa using hz).intervalIntegrable
  have hiw : IntervalIntegrable w volume 0 1 :=
    (show MonotoneOn w (uIcc (0:ℝ) 1) by simpa using hw).intervalIntegrable
  have hqs := weighted_quantile_power_integrable w q hw hq (fun u hu => (hwb u hu).1)
    (fun u hu => (hqb u hu).1) 2
  have hzs := weighted_quantile_power_integrable w z hw hz (fun u hu => (hwb u hu).1)
    (fun u hu => (hzb u hu).1) 2
  have hfielddist : (∫u in (0:ℝ)..1,|h u+w u*q u-(h u+w u*z u)|) ≤
      W*(∫u in (0:ℝ)..1,|q u-z u|) := by
    have hifq : IntervalIntegrable (fun u => h u+w u*q u) volume 0 1 :=
      (show MonotoneOn (fun u => h u+w u*q u) (uIcc (0:ℝ) 1) by simpa using hfield q hq hqb).intervalIntegrable
    have hifz : IntervalIntegrable (fun u => h u+w u*z u) volume 0 1 :=
      (show MonotoneOn (fun u => h u+w u*z u) (uIcc (0:ℝ) 1) by simpa using hfield z hz hzb).intervalIntegrable
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on_of_le_Ioo zero_le_one (hifq.sub hifz).abs
      ((hiq.sub hiz).abs.const_mul W)
    intro u hu
    have hui : u ∈ Icc (0:ℝ) 1 := ⟨hu.1.le,hu.2.le⟩
    have he : h u+w u*q u-(h u+w u*z u)=w u*(q u-z u) := by ring
    rw [he,abs_mul,abs_of_nonneg (hwb u hui).1]
    exact mul_le_mul_of_nonneg_right (hwb u hui).2 (abs_nonneg _)
  have hpenalty : |(∫u in (0:ℝ)..1,w u*q u^2)-(∫u in (0:ℝ)..1,w u*z u^2)| ≤
      2*W*(∫u in (0:ℝ)..1,|q u-z u|) := by
    rw [← intervalIntegral.integral_sub hqs hzs]
    calc
      _ ≤ ∫u in (0:ℝ)..1,|w u*q u^2-w u*z u^2| := by
        simpa only [Real.norm_eq_abs] using intervalIntegral.norm_integral_le_integral_norm
          (f := fun u => w u*q u^2-w u*z u^2) zero_le_one
      _ ≤ ∫u in (0:ℝ)..1,2*W*|q u-z u| := by
        apply intervalIntegral.integral_mono_on_of_le_Ioo zero_le_one (hqs.sub hzs).abs
          ((hiq.sub hiz).abs.const_mul (2*W))
        intro u hu
        have hui : u ∈ Icc (0:ℝ) 1 := ⟨hu.1.le,hu.2.le⟩
        rw [← mul_sub,abs_mul,abs_of_nonneg (hwb u hui).1]
        have hs := unit_square_difference_le (hqb u hui) (hzb u hui)
        have h := mul_le_mul (hwb u hui).2 hs (abs_nonneg _) hW
        nlinarith
      _ = _ := intervalIntegral.integral_const_mul _ _
  have hpressure := hp.trans (mul_le_mul_of_nonneg_left hfielddist (by norm_num : (0:ℝ)≤1/2))
  have htri := abs_add_le
    (realOrderedSKPathPressure n b (fun u => h u+w u*q u) 0-
      realOrderedSKPathPressure n b (fun u => h u+w u*z u) 0)
    ((1/4:ℝ)*((∫u in (0:ℝ)..1,w u*q u^2)-(∫u in (0:ℝ)..1,w u*z u^2)))
  rw [abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤1/4)] at htri
  unfold massStrengthObjective
  have he : realOrderedSKPathPressure n b (fun u => h u+w u*q u) 0+(1/4:ℝ)*(∫u in (0:ℝ)..1,w u*q u^2)-
      (realOrderedSKPathPressure n b (fun u => h u+w u*z u) 0+(1/4:ℝ)*(∫u in (0:ℝ)..1,w u*z u^2))=
      (realOrderedSKPathPressure n b (fun u => h u+w u*q u) 0-
        realOrderedSKPathPressure n b (fun u => h u+w u*z u) 0)+
      (1/4:ℝ)*((∫u in (0:ℝ)..1,w u*q u^2)-(∫u in (0:ℝ)..1,w u*z u^2)) := by ring
  rw [he]
  linarith

theorem eventually_macro_objective_competitor (b h w q : ℝ → ℝ) {W ε : ℝ}
    (hW : 0 < W) (hε : 0 < ε)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (hw : MonotoneOn w (Icc (0:ℝ) 1)) (hq : MonotoneOn q (Icc (0:ℝ) 1))
    (hwb : ∀ u ∈ Icc (0:ℝ) 1, w u ∈ Icc (0:ℝ) W)
    (hqb : ∀ u ∈ Icc (0:ℝ) 1, q u ∈ Icc (0:ℝ) 1)
    (hb0 : 0 ≤ b 0) (hh0 : 0 ≤ h 0) :
    ∀ᶠ k : ℕ in atTop, ∀ (hη : 0 < macroDensityFloor k) (hQ : 1 < macroDensityCap k),
      ∃ γ : MacroInverseClass (macroDensityFloor k) (macroDensityCap k),
        ∀ (n : ℕ), 0 < n →
        |massStrengthObjective n b h w (macroInverseQuantile hη hQ γ)-massStrengthObjective n b h w q|<ε := by
  filter_upwards [eventually_macro_quantile_competitor q hq hqb (ε := ε/W) (by positivity)] with k hk
  intro hη hQ
  obtain ⟨γ,hγ⟩ := hk hη hQ
  refine ⟨γ,?_⟩
  intro n hn
  have hp := mass_strength_objective_l1_comparison n hn b h w (macroInverseQuantile hη hQ γ) q
    hW.le hb hh hw (macroInverseQuantile_monotone hη hQ γ) hq hwb
    (fun u _ => macroInverseQuantile_bounds hη hQ γ u) hqb hb0 hh0
  have hmul := mul_lt_mul_of_pos_left hγ hW
  rw [mul_div_cancel₀ _ hW.ne'] at hmul
  exact hp.trans_lt hmul

end OAI.SKFluctuations.LaplaceWindowFormalization
