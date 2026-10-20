module

public import ActualMacroEnvelope
public import SampledQuantileScalarBridge

@[expose] public section

noncomputable section

namespace OAI.SKFluctuations.LaplaceWindowFormalization

open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal

theorem macro_interpolation_derivative_nonneg (n : ℕ) (hn : 0 < n)
    (b h q : ℝ → ℝ) {t : ℝ}
    (hb : MonotoneOn b (Icc (0 : ℝ) 1))
    (hh : MonotoneOn h (Icc (0 : ℝ) 1))
    (hq : MonotoneOn q (Icc (0 : ℝ) 1))
    (hbn : ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ b u)
    (hqn : ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ q u)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    let bf := fun u => ((1-t)*b u).toNNReal
    let hf := fun u => (h u+t*b u*q u).toNNReal
    0 ≤ (1/4:ℝ)*(∫ u in (0:ℝ)..1,
      b u*(orderedPathB n bf hf u-2*q u*orderedPathS n bf hf u+q u^2)) := by
  dsimp only
  have hbm : MonotoneOn (fun u => ((1-t)*b u).toNNReal) (Icc (0 : ℝ) 1) :=
    toNNReal_monotoneOn (fun _ hu _ hv huv =>
      mul_le_mul_of_nonneg_left (hb hu hv huv) (sub_nonneg.mpr ht.2))
  have hfm : MonotoneOn (fun u => (h u+t*b u*q u).toNNReal) (Icc (0 : ℝ) 1) := by
    apply toNNReal_monotoneOn
    intro u hu v hv huv
    exact add_le_add (hh hu hv huv)
      (mul_le_mul (mul_le_mul_of_nonneg_left (hb hu hv huv) ht.1)
        (hq hu hv huv) (hqn u hu) (mul_nonneg ht.1 (hbn v hv)))
  apply mul_nonneg (by norm_num : 0 ≤ (1/4:ℝ))
  apply intervalIntegral.integral_nonneg_of_ae_restrict zero_le_one
  apply (ae_restrict_iff' measurableSet_Icc).mpr
  filter_upwards [volume.ae_ne (0:ℝ)] with u hu0 hu
  have hs := orderedPath_SK_bounds n hn
    (fun u => ((1-t)*b u).toNNReal) (fun u => (h u+t*b u*q u).toNNReal) hbm hfm
    (⟨lt_of_le_of_ne hu.1 hu0.symm, hu.2⟩ : u ∈ Ioc (0:ℝ) 1)
  apply mul_nonneg (hbn u hu)
  nlinarith [sq_nonneg (orderedPathS n (fun u => ((1-t)*b u).toNNReal)
    (fun u => (h u+t*b u*q u).toNNReal) u-q u)]

theorem macroInterpolationObjective_monotone (n : ℕ) (hn : 0 < n)
    (b h q : ℝ → ℝ) {W : ℝ} (hW : 0 ≤ W)
    (hb : MonotoneOn b (Icc (0 : ℝ) 1))
    (hh : MonotoneOn h (Icc (0 : ℝ) 1))
    (hq : MonotoneOn q (Icc (0 : ℝ) 1))
    (hbb : ∀ u ∈ Icc (0 : ℝ) 1, b u ∈ Icc (0 : ℝ) W)
    (hqb : ∀ u ∈ Icc (0 : ℝ) 1, q u ∈ Icc (0 : ℝ) 1)
    (hhn : ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ h u) :
    MonotoneOn (macroInterpolationObjective n b h q) (Icc (0 : ℝ) 1) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc (0:ℝ) 1)
    (macro_interpolation_lipschitz n hn b h q hW hb hh hq hbb hqb hhn).continuousOn
  · intro t ht
    rw [interior_Icc] at ht
    exact (macro_interpolation_derivative n hn b h q hW hb hh hq hbb hqb hhn ht).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    rw [(macro_interpolation_derivative n hn b h q hW hb hh hq hbb hqb hhn ht).deriv]
    exact macro_interpolation_derivative_nonneg n hn b h q hb hh hq
      (fun u hu => (hbb u hu).1) (fun u hu => (hqb u hu).1) ⟨ht.1.le, ht.2.le⟩

theorem macroInterpolationObjective_zero (n : ℕ) (b h q : ℝ → ℝ) :
    macroInterpolationObjective n b h q 0 = realOrderedSKPathPressure n b h 0 := by
  simp [macroInterpolationObjective, massStrengthObjective]

theorem macroInterpolationObjective_scalar_one (n : ℕ) (hn : 0 < n)
    {T : ℝ} (hT : 0 < T) (q : ℝ → ℝ)
    (hq : MonotoneOn q (Icc (0 : ℝ) 1))
    (hqb : ∀ u ∈ Icc (0 : ℝ) 1, q u ∈ Icc (0 : ℝ) 1) :
    macroInterpolationObjective n (fun _ => T) (fun _ => 0) q 1 =
      scalarParisiValue hT (quantileMassProfile q hqb) := by
  rw [scalar_physical_quantile_value n hn hT q hq hqb]
  simp only [macroInterpolationObjective, massStrengthObjective, physicalScalarQuantileValue,
    sub_self, zero_mul, one_mul, zero_add]
  rw [intervalIntegral.integral_const_mul]
  ring

section
variable {η Q W : ℝ} (hη : 0 < η) (hη1 : η < 1) (hQ : 1 < Q)

include hη1 in
theorem macroMinimumValue_monotone (n : ℕ) (hn : 0 < n)
    (b h : ℝ → ℝ) (hW : 0 ≤ W)
    (hb : MonotoneOn b (Icc (0 : ℝ) 1))
    (hh : MonotoneOn h (Icc (0 : ℝ) 1))
    (hbb : ∀ u ∈ Icc (0 : ℝ) 1, b u ∈ Icc (0 : ℝ) W)
    (hhn : ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ h u) :
    MonotoneOn (macroMinimumValue hη hQ n b h) (Icc (0 : ℝ) 1) := by
  intro s hs t ht hst
  obtain ⟨α, he, _⟩ := macroMinimumValue_attained hη hη1 hQ n hn b h hW hb hh hbb hhn ht
  obtain ⟨_, _, hmin⟩ := macroMinimumValue_attained hη hη1 hQ n hn b h hW hb hh hbb hhn hs
  exact (hmin α).trans ((macroInterpolationObjective_monotone n hn b h _ hW hb hh
    (macroInverseQuantile_monotone hη hQ α) hbb
    (fun u _ => macroInverseQuantile_bounds hη hQ α u) hhn hs ht hst).trans_eq he)

include hη1 in
theorem macroMinimumValue_zero (n : ℕ) (hn : 0 < n)
    (b h : ℝ → ℝ) (hW : 0 ≤ W)
    (hb : MonotoneOn b (Icc (0 : ℝ) 1))
    (hh : MonotoneOn h (Icc (0 : ℝ) 1))
    (hbb : ∀ u ∈ Icc (0 : ℝ) 1, b u ∈ Icc (0 : ℝ) W)
    (hhn : ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ h u) :
    macroMinimumValue hη hQ n b h 0 = realOrderedSKPathPressure n b h 0 := by
  obtain ⟨α, he, _⟩ := macroMinimumValue_attained hη hη1 hQ n hn b h hW hb hh hbb hhn
    (by norm_num : (0:ℝ) ∈ Icc (0:ℝ) 1)
  exact he.symm.trans (macroInterpolationObjective_zero n b h _)

end

end OAI.SKFluctuations.LaplaceWindowFormalization
