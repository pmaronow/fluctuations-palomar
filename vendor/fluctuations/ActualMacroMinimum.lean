module

public import ActualMacroOptimizerDefect

@[expose] public section

noncomputable section

namespace OAI.SKFluctuations.LaplaceWindowFormalization

open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal

theorem mass_strength_objective_uniform_comparison (n : ℕ) (hn : 0 < n)
    (b h w q z : ℝ → ℝ) {W d : ℝ} (hW : 0 ≤ W)
    (hb : MonotoneOn b (Icc (0 : ℝ) 1))
    (hh : MonotoneOn h (Icc (0 : ℝ) 1))
    (hw : MonotoneOn w (Icc (0 : ℝ) 1))
    (hq : MonotoneOn q (Icc (0 : ℝ) 1))
    (hz : MonotoneOn z (Icc (0 : ℝ) 1))
    (hwb : ∀ u ∈ Icc (0 : ℝ) 1, w u ∈ Icc (0 : ℝ) W)
    (hqb : ∀ u ∈ Icc (0 : ℝ) 1, q u ∈ Icc (0 : ℝ) 1)
    (hzb : ∀ u ∈ Icc (0 : ℝ) 1, z u ∈ Icc (0 : ℝ) 1)
    (hb0 : 0 ≤ b 0) (hh0 : 0 ≤ h 0)
    (hd : ∀ u ∈ Icc (0 : ℝ) 1, |q u - z u| ≤ d) :
    |massStrengthObjective n b h w q - massStrengthObjective n b h w z| ≤ W * d := by
  have hfield (r : ℝ → ℝ) (hr : MonotoneOn r (Icc (0 : ℝ) 1))
      (hrb : ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ r u) :
      MonotoneOn (fun u => h u + w u * r u) (Icc (0 : ℝ) 1) := by
    intro u hu v hv huv
    exact add_le_add (hh hu hv huv)
      (mul_le_mul (hw hu hv huv) (hr hu hv huv) (hrb u hu) (hwb v hv).1)
  have h00 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have hp := realOrderedSKPathPressure_uniform_comparison n hn b
    (fun u => h u + w u * q u) b (fun u => h u + w u * z u)
    hb (hfield q hq (fun u hu => (hqb u hu).1))
    hb (hfield z hz (fun u hu => (hzb u hu).1)) hb0
    (add_nonneg hh0 (mul_nonneg (hwb 0 h00).1 (hqb 0 h00).1)) hb0
    (add_nonneg hh0 (mul_nonneg (hwb 0 h00).1 (hzb 0 h00).1))
    (B := 0) (H := W * d) (fun _ _ => by simp) (by
      intro u hu
      have he : h u + w u * q u - (h u + w u * z u) = w u * (q u - z u) := by ring
      rw [he, abs_mul, abs_of_nonneg (hwb u hu).1]
      exact mul_le_mul (hwb u hu).2 (hd u hu) (abs_nonneg _) hW) 0
  have hsq (r : ℝ → ℝ) (hr : MonotoneOn r (Icc (0 : ℝ) 1))
      (hrb : ∀ u ∈ Icc (0 : ℝ) 1, r u ∈ Icc (0 : ℝ) 1) :
      IntervalIntegrable (fun u => w u * r u ^ 2) volume 0 1 := by
    have hm : MonotoneOn (fun u => w u * r u ^ 2) (Icc (0 : ℝ) 1) := by
      intro u hu v hv huv
      exact mul_le_mul (hw hu hv huv) (sq_le_sq₀ (hrb u hu).1 (hrb v hv).1 |>.mpr (hr hu hv huv))
        (sq_nonneg _) (hwb v hv).1
    exact (show MonotoneOn (fun u => w u * r u ^ 2) (uIcc (0 : ℝ) 1) by simpa using hm).intervalIntegrable
  have hpi := intervalIntegral_abs_le_unit_bound (f := fun u => w u * q u^2 - w u*z u^2)
    (C := 2 * W * d) (by
      intro u hu
      rw [← mul_sub, abs_mul, abs_of_nonneg (hwb u hu).1]
      have hs := unit_square_difference_le (hqb u hu) (hzb u hu)
      calc
        _ ≤ W * (2 * d) := mul_le_mul (hwb u hu).2
          (hs.trans (mul_le_mul_of_nonneg_left (hd u hu) (by norm_num))) (abs_nonneg _) hW
        _ = _ := by ring)
  rw [intervalIntegral.integral_sub (hsq q hq hqb) (hsq z hz hzb)] at hpi
  have hid : massStrengthObjective n b h w q - massStrengthObjective n b h w z =
      (realOrderedSKPathPressure n b (fun u => h u+w u*q u) 0 -
        realOrderedSKPathPressure n b (fun u => h u+w u*z u) 0) +
      (1/4:ℝ)*((∫u in (0:ℝ)..1,w u*q u^2)-(∫u in (0:ℝ)..1,w u*z u^2)) := by
    unfold massStrengthObjective
    ring
  rw [hid]
  have ha := abs_add_le
    (realOrderedSKPathPressure n b (fun u => h u+w u*q u) 0 -
      realOrderedSKPathPressure n b (fun u => h u+w u*z u) 0)
    ((1/4:ℝ)*((∫u in (0:ℝ)..1,w u*q u^2)-(∫u in (0:ℝ)..1,w u*z u^2)))
  rw [abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (1/4:ℝ))] at ha
  linarith

section
variable {η Q W : ℝ} (hη : 0 < η) (hη1 : η < 1) (hQ : 1 < Q)

def macroQuantileMap (α : MacroInverseClass η Q) : C(Icc (0 : ℝ) 1, ℝ) :=
  constrainedQuantileMap zero_le_one hη continuousOn_const (fun _ _ => le_rfl)
    (fun _ _ _ _ _ => le_rfl) (zero_lt_one.trans hQ).le α

theorem macroQuantileMap_continuous : Continuous (macroQuantileMap hη hQ) :=
  constrainedQuantileMap_continuous zero_le_one hη continuousOn_const
    (fun _ _ => le_rfl) (fun _ _ _ _ _ => le_rfl) (zero_lt_one.trans hQ).le

theorem macroQuantileMap_eq (α : MacroInverseClass η Q) (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
    macroQuantileMap hη hQ α ⟨u, hu⟩ = macroInverseQuantile hη hQ α u := by
  unfold macroQuantileMap constrainedQuantileMap macroInverseQuantile inverseMassQuantile
  simp only [ContinuousMap.coe_mk, projIcc_of_mem zero_le_one hu]

theorem macroInverseObjective_continuous (n : ℕ) (hn : 0 < n)
    (b h w : ℝ → ℝ) (hW : 0 ≤ W)
    (hb : MonotoneOn b (Icc (0 : ℝ) 1))
    (hh : MonotoneOn h (Icc (0 : ℝ) 1))
    (hw : MonotoneOn w (Icc (0 : ℝ) 1))
    (hwb : ∀ u ∈ Icc (0 : ℝ) 1, w u ∈ Icc (0 : ℝ) W)
    (hb0 : 0 ≤ b 0) (hh0 : 0 ≤ h 0) :
    Continuous (macroInverseObjective hη hQ n b h w) := by
  rw [continuous_iff_continuousAt]
  intro α
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  have ht : Tendsto (fun β => W * dist (macroQuantileMap hη hQ β) (macroQuantileMap hη hQ α))
      (𝓝 α) (𝓝 0) := by
    simpa using (((macroQuantileMap_continuous hη hQ).dist
      (continuous_const : Continuous fun _ : MacroInverseClass η Q => macroQuantileMap hη hQ α)).tendsto α).const_mul W
  apply squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) _ ht
  apply Eventually.of_forall
  intro β
  rw [Real.dist_eq]
  apply mass_strength_objective_uniform_comparison n hn b h w _ _ hW hb hh hw
    (macroInverseQuantile_monotone hη hQ β) (macroInverseQuantile_monotone hη hQ α) hwb
    (fun u _ => macroInverseQuantile_bounds hη hQ β u)
    (fun u _ => macroInverseQuantile_bounds hη hQ α u) hb0 hh0
  intro u hu
  simpa only [Real.dist_eq, macroQuantileMap_eq hη hQ β u hu,
    macroQuantileMap_eq hη hQ α u hu] using
    ContinuousMap.dist_apply_le_dist (f := macroQuantileMap hη hQ β)
      (g := macroQuantileMap hη hQ α) ⟨u, hu⟩

include hη1 in
theorem macroInverseObjective_minimum (n : ℕ) (hn : 0 < n)
    (b h w : ℝ → ℝ) (hW : 0 ≤ W)
    (hb : MonotoneOn b (Icc (0 : ℝ) 1))
    (hh : MonotoneOn h (Icc (0 : ℝ) 1))
    (hw : MonotoneOn w (Icc (0 : ℝ) 1))
    (hwb : ∀ u ∈ Icc (0 : ℝ) 1, w u ∈ Icc (0 : ℝ) W)
    (hb0 : 0 ≤ b 0) (hh0 : 0 ≤ h 0) :
    ∃ α : MacroInverseClass η Q, ∀ β : MacroInverseClass η Q,
      macroInverseObjective hη hQ n b h w α ≤ macroInverseObjective hη hQ n b h w β := by
  let : CompactSpace (MacroInverseClass η Q) := isCompact_iff_compactSpace.mp
    (inverseIntegralConstraints_compact 0 0 (fun _ => η) (fun _ => Q)
      continuous_const (fun _ _ _ _ _ => le_rfl))
  obtain ⟨α, hα⟩ := macroInverseClass_nonempty hη1 hQ
  have hne : (univ : Set (MacroInverseClass η Q)).Nonempty := ⟨⟨α, hα⟩, mem_univ _⟩
  obtain ⟨α, _, hα⟩ := isCompact_univ.exists_isMinOn hne
    (macroInverseObjective_continuous hη hQ n hn b h w hW hb hh hw hwb hb0 hh0).continuousOn
  exact ⟨α, fun β => hα (mem_univ β)⟩

end

end OAI.SKFluctuations.LaplaceWindowFormalization
