module

public import ActualMacroEnvelope
public import ActualMacroOptimizer

@[expose] public section

noncomputable section

namespace OAI.SKFluctuations.LaplaceWindowFormalization

open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal

theorem orderedPathS_sq_intervalIntegrable (n : ℕ) (hn : 0 < n)
    (b h : ℝ → ℝ≥0) (hb : MonotoneOn b (Icc (0 : ℝ) 1))
    (hh : MonotoneOn h (Icc (0 : ℝ) 1)) :
    IntervalIntegrable (fun u => (orderedPathS n b h u)^2) volume 0 1 := by
  have hi : IntervalIntegrable (orderedPathS n b h) volume 0 1 := by
    simpa only [one_mul, orderedPathS] using orderedPathPair_mul_integrable n hn b h hb hh
      (orderedOverlap n) (fun _ => 1) intervalIntegrable_const
  have hm : AEStronglyMeasurable (fun u => (orderedPathS n b h u)^2)
      (volume.restrict (uIoc (0 : ℝ) 1)) := by
    convert hi.aestronglyMeasurable_restrict_uIoc.mul hi.aestronglyMeasurable_restrict_uIoc using 1
    ext u
    simp only [pow_two, Pi.mul_apply]
  apply (intervalIntegrable_const (c := (1:ℝ))).mono_fun hm
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with u hu
  have hu' : u ∈ Ioc (0 : ℝ) 1 := by simpa only [uIoc_of_le zero_le_one] using hu
  have hs := orderedPath_SK_bounds n hn b h hb hh hu'
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), abs_one]
  nlinarith

theorem actual_quadratic_integrable (n : ℕ) (hn : 0 < n)
    (b h : ℝ → ℝ≥0) (hb : MonotoneOn b (Icc (0 : ℝ) 1))
    (hh : MonotoneOn h (Icc (0 : ℝ) 1)) (q : ℝ → ℝ)
    (hq : MonotoneOn q (Icc (0 : ℝ) 1))
    (hqn : ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ q u) :
    IntervalIntegrable (fun u => orderedPathB n b h u-(orderedPathS n b h u)^2) volume 0 1 ∧
    IntervalIntegrable (fun u => (orderedPathS n b h u-q u)^2) volume 0 1 := by
  have hiB : IntervalIntegrable (orderedPathB n b h) volume 0 1 := by
    simpa only [one_mul, orderedPathB] using orderedPathPair_mul_integrable n hn b h hb hh
      (fun σ τ => (orderedOverlap n σ τ)^2) (fun _ => 1) intervalIntegrable_const
  have hiS2 := orderedPathS_sq_intervalIntegrable n hn b h hb hh
  have hiq : IntervalIntegrable q volume 0 1 :=
    (show MonotoneOn q (uIcc (0 : ℝ) 1) by simpa using hq).intervalIntegrable
  have hiSq : IntervalIntegrable (fun u => q u*orderedPathS n b h u) volume 0 1 :=
    orderedPathPair_mul_integrable n hn b h hb hh (orderedOverlap n) q hiq
  have hiq2 : IntervalIntegrable (fun u => q u^2) volume 0 1 := by
    simpa only [one_mul] using weighted_quantile_power_integrable (fun _ => 1) q
      (fun _ _ _ _ _ => le_rfl) hq (fun _ _ => zero_le_one) hqn 2
  refine ⟨hiB.sub hiS2, ?_⟩
  have hi := (hiS2.sub (hiSq.const_mul 2)).add hiq2
  convert hi using 1
  ext u
  ring

theorem actual_weighted_quadratic_le (n : ℕ) (hn : 0 < n)
    (b h : ℝ → ℝ≥0) (hb : MonotoneOn b (Icc (0 : ℝ) 1))
    (hh : MonotoneOn h (Icc (0 : ℝ) 1)) (w q : ℝ → ℝ) {W : ℝ}
    (hwb : ∀ u ∈ Icc (0 : ℝ) 1, w u ∈ Icc (0 : ℝ) W)
    (hq : MonotoneOn q (Icc (0 : ℝ) 1))
    (hqn : ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ q u) :
    (∫u in (0:ℝ)..1,w u*(orderedPathB n b h u-2*q u*orderedPathS n b h u+q u^2)) ≤
      W*((∫u in (0:ℝ)..1,orderedPathB n b h u-(orderedPathS n b h u)^2)+
        (∫u in (0:ℝ)..1,(orderedPathS n b h u-q u)^2)) := by
  obtain ⟨hiD, hiM⟩ := actual_quadratic_integrable n hn b h hb hh q hq hqn
  have hir : IntegrableOn (fun u => W*((orderedPathB n b h u-(orderedPathS n b h u)^2)+
      (orderedPathS n b h u-q u)^2)) (Icc (0:ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp ((hiD.add hiM).const_mul W)
  have hnon : 0 ≤ᵐ[volume.restrict (Icc (0:ℝ) 1)]
      (fun u => w u*(orderedPathB n b h u-2*q u*orderedPathS n b h u+q u^2)) := by
    apply (ae_restrict_iff' measurableSet_Icc).mpr
    filter_upwards [volume.ae_ne (0:ℝ)] with u hu0 hu
    have hs := orderedPath_SK_bounds n hn b h hb hh
      (⟨lt_of_le_of_ne hu.1 hu0.symm, hu.2⟩ : u ∈ Ioc (0:ℝ) 1)
    have hbr : 0 ≤ orderedPathB n b h u-2*q u*orderedPathS n b h u+q u^2 := by
      nlinarith [sq_nonneg (orderedPathS n b h u-q u)]
    exact mul_nonneg (hwb u hu).1 hbr
  have hle : (fun u => w u*(orderedPathB n b h u-2*q u*orderedPathS n b h u+q u^2)) ≤ᵐ[
      volume.restrict (Icc (0:ℝ) 1)] (fun u => W*((orderedPathB n b h u-(orderedPathS n b h u)^2)+
        (orderedPathS n b h u-q u)^2)) := by
    apply (ae_restrict_iff' measurableSet_Icc).mpr
    filter_upwards [volume.ae_ne (0:ℝ)] with u hu0 hu
    have hs := orderedPath_SK_bounds n hn b h hb hh
      (⟨lt_of_le_of_ne hu.1 hu0.symm, hu.2⟩ : u ∈ Ioc (0:ℝ) 1)
    have hsum : 0 ≤ (orderedPathB n b h u-(orderedPathS n b h u)^2)+
        (orderedPathS n b h u-q u)^2 := add_nonneg (sub_nonneg.mpr hs.2.2.1) (sq_nonneg _)
    have he : orderedPathB n b h u-2*q u*orderedPathS n b h u+q u^2 =
        (orderedPathB n b h u-(orderedPathS n b h u)^2)+(orderedPathS n b h u-q u)^2 := by ring
    rw [he]
    exact mul_le_mul_of_nonneg_right (hwb u hu).2 hsum
  have hi := integral_mono_of_nonneg hnon hir hle
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_add hiD hiM] at hi
  exact hi

def macroThermalDefect (n : ℕ) (b h q : ℝ → ℝ) (t : ℝ) : ℝ :=
  let bf := fun u => ((1-t)*b u).toNNReal
  let hf := fun u => (h u+t*b u*q u).toNNReal
  ∫u in (0:ℝ)..1,orderedPathB n bf hf u-(orderedPathS n bf hf u)^2

section
variable {η Q W bstar : ℝ} (hη : 0 < η) (hη1 : η < 1) (hQ : 1 < Q)

include hη1 in
theorem macro_minimizing_derivative_upper (n : ℕ) (hn : 0 < n)
    (b h : ℝ → ℝ) (hW : 0 ≤ W) (hbstar : 0 < bstar)
    (hb : MonotoneOn b (Icc (0 : ℝ) 1))
    (hh : MonotoneOn h (Icc (0 : ℝ) 1)) (hbm : Measurable b)
    (hbb : ∀ u ∈ Icc (0 : ℝ) 1, b u ∈ Icc (0 : ℝ) W)
    (hbl : ∀ u ∈ Icc (0 : ℝ) 1, bstar ≤ b u)
    (hhn : ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ h u)
    (α : MacroInverseClass η Q) {t E : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hmin : ∀ β : MacroInverseClass η Q,
      macroInterpolationObjective n b h (macroInverseQuantile hη hQ α) t ≤
        macroInterpolationObjective n b h (macroInverseQuantile hη hQ β) t)
    (hthermal : macroThermalDefect n b h (macroInverseQuantile hη hQ α) t ≤ E) :
    ∃ d, HasDerivAt (macroInterpolationObjective n b h (macroInverseQuantile hη hQ α)) d t ∧
      d ≤ (W/4)*(E+η+(1/Q)^2) := by
  let q := macroInverseQuantile hη hQ α
  let bf := fun u => ((1-t)*b u).toNNReal
  let hf := fun u => (h u+t*b u*q u).toNNReal
  have hmatrix : MonotoneOn (fun u => (1-t)*b u) (Icc (0 : ℝ) 1) := by
    intro u hu v hv huv
    exact mul_le_mul_of_nonneg_left (hb hu hv huv) (sub_nonneg.mpr ht.2.le)
  have hw : MonotoneOn (fun u => t*b u) (Icc (0 : ℝ) 1) := by
    intro u hu v hv huv
    exact mul_le_mul_of_nonneg_left (hb hu hv huv) ht.1.le
  have hfield : MonotoneOn (fun u => h u+t*b u*q u) (Icc (0 : ℝ) 1) := by
    intro u hu v hv huv
    exact add_le_add (hh hu hv huv)
      (mul_le_mul (hw hu hv huv) (macroInverseQuantile_monotone hη hQ α hu hv huv)
        (macroInverseQuantile_bounds hη hQ α u).1 (mul_nonneg ht.1.le (hbb v hv).1))
  have hmis := macro_inverse_minimum_mass_defect hη hη1 hQ n hn
    (fun u => (1-t)*b u) h (fun u => t*b u) (W := t*W) (mul_nonneg ht.1.le hW)
    hmatrix hh hw (measurable_const.mul hbm)
    (fun u hu => mul_pos ht.1 (hbstar.trans_le (hbl u hu)))
    (fun u hu => mul_le_mul_of_nonneg_left (hbb u hu).2 ht.1.le)
    (fun u hu => mul_nonneg (sub_nonneg.mpr ht.2.le) (hbb u hu).1) hhn α hmin
  dsimp only at hmis
  have hd := macro_interpolation_derivative n hn b h q hW hb hh
    (macroInverseQuantile_monotone hη hQ α) hbb
    (fun u _ => macroInverseQuantile_bounds hη hQ α u) hhn ht
  dsimp only at hd
  have hquad := actual_weighted_quadratic_le n hn bf hf
    (toNNReal_monotoneOn hmatrix) (toNNReal_monotoneOn hfield) b q hbb
    (macroInverseQuantile_monotone hη hQ α)
    (fun u _ => (macroInverseQuantile_bounds hη hQ α u).1)
  have hupper := mul_le_mul_of_nonneg_left hquad (by norm_num : 0 ≤ (1/4:ℝ))
  have hD : (∫u in (0:ℝ)..1,orderedPathB n bf hf u-(orderedPathS n bf hf u)^2) ≤ E := hthermal
  exact ⟨_, hd, by dsimp only [bf, hf, q] at *; nlinarith⟩

include hη1 in
theorem macro_minimum_cost_of_thermal_budget (n : ℕ) (hn : 0 < n)
    (b h E : ℝ → ℝ) (hW : 0 ≤ W) (hbstar : 0 < bstar)
    (hb : MonotoneOn b (Icc (0 : ℝ) 1))
    (hh : MonotoneOn h (Icc (0 : ℝ) 1)) (hbm : Measurable b)
    (hbb : ∀ u ∈ Icc (0 : ℝ) 1, b u ∈ Icc (0 : ℝ) W)
    (hbl : ∀ u ∈ Icc (0 : ℝ) 1, bstar ≤ b u)
    (hhn : ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ h u)
    (hE : IntervalIntegrable E volume 0 1)
    (hthermal : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ α : MacroInverseClass η Q,
      (∀ β : MacroInverseClass η Q,
        macroInterpolationObjective n b h (macroInverseQuantile hη hQ α) t ≤
          macroInterpolationObjective n b h (macroInverseQuantile hη hQ β) t) →
      macroThermalDefect n b h (macroInverseQuantile hη hQ α) t ≤ E t) :
    macroMinimumValue hη hQ n b h 1 - macroMinimumValue hη hQ n b h 0 ≤
      (W/4)*((∫t in (0:ℝ)..1,E t)+η+(1/Q)^2) := by
  let g := fun t => (W/4)*(E t+η+(1/Q)^2)
  have hg : IntervalIntegrable g volume 0 1 :=
    ((hE.add intervalIntegrable_const).add intervalIntegrable_const).const_mul (W/4)
  have hv : LipschitzOnWith (NNReal.mk W hW) (macroMinimumValue hη hQ n b h) (uIcc (0:ℝ) 1) := by
    simpa only [uIcc_of_le zero_le_one] using
      macroMinimumValue_lipschitz hη hη1 hQ n hn b h hW hb hh hbb hhn
  have hi := WallSweep.minimum_sub_le_integral zero_le_one
    (fun t α => macroInterpolationObjective n b h (macroInverseQuantile hη hQ α) t)
    (macroMinimumValue hη hQ n b h) g hv (by
      intro t ht
      obtain ⟨α, he, hbound⟩ := macroMinimumValue_attained hη hη1 hQ n hn b h hW hb hh hbb hhn
        ⟨ht.1.le, ht.2.le⟩
      have hmin : ∀ β : MacroInverseClass η Q,
          macroInterpolationObjective n b h (macroInverseQuantile hη hQ α) t ≤
            macroInterpolationObjective n b h (macroInverseQuantile hη hQ β) t :=
        fun β => he.trans_le (hbound β)
      obtain ⟨d, hd, hdu⟩ := macro_minimizing_derivative_upper hη hη1 hQ n hn b h hW hbstar
        hb hh hbm hbb hbl hhn α ht hmin (hthermal t ht α hmin)
      refine ⟨α, he, ?_, d, hd, hdu⟩
      have hev : ∀ᶠ s in 𝓝 t, s ∈ Icc (0:ℝ) 1 := Icc_mem_nhds ht.1 ht.2
      filter_upwards [hev] with s hs
      obtain ⟨β, _, hb'⟩ := macroMinimumValue_attained hη hη1 hQ n hn b h hW hb hh hbb hhn hs
      exact hb' α) hg
  have he : (∫t in (0:ℝ)..1,g t) = (W/4)*((∫t in (0:ℝ)..1,E t)+η+(1/Q)^2) := by
    unfold g
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add (hE.add intervalIntegrable_const) intervalIntegrable_const,
      intervalIntegral.integral_add hE intervalIntegrable_const]
    simp
  exact hi.trans_eq he

end

end OAI.SKFluctuations.LaplaceWindowFormalization
