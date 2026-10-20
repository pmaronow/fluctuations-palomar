module

public import MassStrengthVariation
public import SKFluctuationsOAI.Probability.SKFluctuations.InverseConstraintNonempty

@[expose] public section

noncomputable section

namespace OAI.SKFluctuations.LaplaceWindowFormalization

open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal

abbrev MacroInverseClass (η Q : ℝ) :=
  inverseIntegralConstraints 0 0 (fun _ => η) (fun _ => Q)

section
variable {η Q W : ℝ} (hη : 0 < η) (hη1 : η < 1) (hQ : 1 < Q)

def macroInverseQuantile (α : MacroInverseClass η Q) : ℝ → ℝ :=
  inverseMassQuantile hη continuousOn_const (fun _ _ => le_rfl)
    (fun _ _ _ _ _ => le_rfl) (zero_lt_one.trans hQ).le α

def macroInverseObjective (n : ℕ) (b h w : ℝ → ℝ) (α : MacroInverseClass η Q) : ℝ :=
  massStrengthObjective n b h w (macroInverseQuantile hη hQ α)

theorem macroInverseQuantile_monotone (α : MacroInverseClass η Q) :
    MonotoneOn (macroInverseQuantile hη hQ α) (Icc (0 : ℝ) 1) := by
  intro u hu v hv huv
  unfold macroInverseQuantile inverseMassQuantile
  rw [projIcc_of_mem zero_le_one hu, projIcc_of_mem zero_le_one hv]
  exact (inverseConstraintOrderIso zero_le_one hη continuousOn_const
    (fun _ _ => le_rfl) (fun _ _ _ _ _ => le_rfl) (zero_lt_one.trans hQ).le α).symm.monotone huv

theorem macroInverseQuantile_bounds (α : MacroInverseClass η Q) (u : ℝ) :
    macroInverseQuantile hη hQ α u ∈ Icc (0 : ℝ) 1 :=
  (constrainedQuantile zero_le_one hη continuousOn_const (fun _ _ => le_rfl)
    (fun _ _ _ _ _ => le_rfl) (zero_lt_one.trans hQ).le α
    (projIcc 0 1 zero_le_one u)).property

include hη1 hQ in
theorem macroInverseClass_nonempty : (MacroInverseClass η Q).Nonempty := by
  apply inverseIntegralConstraints_nonempty_of_affine
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) ∈ Icc (0 : ℝ) 1)
    continuousOn_const continuous_const
  · intro r hr
    simpa using hη1.le
  · intro u hu
    simpa using hQ.le

include hη1 in
theorem macro_inverse_minimum_potential (n : ℕ) (hn : 0 < n)
    (b h w : ℝ → ℝ) (hW : 0 ≤ W)
    (hb : MonotoneOn b (Icc (0 : ℝ) 1))
    (hh : MonotoneOn h (Icc (0 : ℝ) 1))
    (hw : MonotoneOn w (Icc (0 : ℝ) 1)) (hwm : Measurable w)
    (hwp : ∀ u ∈ Icc (0 : ℝ) 1, 0 < w u)
    (hwb : ∀ u ∈ Icc (0 : ℝ) 1, w u ≤ W)
    (hbn : ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ b u)
    (hhn : ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ h u)
    (α : MacroInverseClass η Q)
    (hmin : ∀ β : MacroInverseClass η Q,
      macroInverseObjective hη hQ n b h w α ≤ macroInverseObjective hη hQ n b h w β) :
    let S := orderedPathS n (fun u => (b u).toNNReal)
      (fun u => (h u + w u * macroInverseQuantile hη hQ α u).toNNReal)
    ∃ H : ℝ → ℝ, AbsolutelyContinuousOnInterval H 0 1 ∧
      (∀ᵐ r, r ∈ Icc (0 : ℝ) 1 →
        HasDerivAt H (w (α.val.val r) * (r - S (α.val.val r))) r) ∧
      (∀ᵐ r, r ∈ Icc (0 : ℝ) 1 →
        (H r < 0 → deriv α.val.val r = Q) ∧
        (0 < H r → deriv α.val.val r = η)) ∧
      (∀ᵐ r, r ∈ Icc (0 : ℝ) 1 → H r = 0 → S (α.val.val r) = r) := by
  dsimp only
  let k : ℝ → ℝ := fun _ => η
  let M : ℝ → ℝ := fun _ => Q
  let q := macroInverseQuantile hη hQ α
  let bf : ℝ → ℝ≥0 := fun u => (b u).toNNReal
  let hf : ℝ → ℝ≥0 := fun u => (h u + w u * q u).toNNReal
  let S := orderedPathS n bf hf
  let G := fun r => w (α.val.val r) * (r - S (α.val.val r))
  have hwb' : ∀ u ∈ Icc (0 : ℝ) 1, w u ∈ Icc (0 : ℝ) W :=
    fun u hu => ⟨(hwp u hu).le, hwb u hu⟩
  have hbf : MonotoneOn bf (Icc (0 : ℝ) 1) := toNNReal_monotoneOn hb
  have hhfield : MonotoneOn (fun u => h u + w u * q u) (Icc (0 : ℝ) 1) := by
    intro u hu v hv huv
    apply add_le_add (hh hu hv huv)
    exact mul_le_mul (hw hu hv huv) (macroInverseQuantile_monotone hη hQ α hu hv huv)
      (macroInverseQuantile_bounds hη hQ α u).1 (hwp v hv).le
  have hhf : MonotoneOn hf (Icc (0 : ℝ) 1) := toNNReal_monotoneOn hhfield
  have hα := inverseIntegralConstraints_lipschitz (fun _ _ _ _ _ => le_rfl)
    (zero_lt_one.trans hQ).le α.property
  have hαstrict := inverseConstraint_strictMonoOn hη continuousOn_const
    (fun _ _ => le_rfl) α.property
  have hSi : IntervalIntegrable (fun r => S (α.val.val r)) volume 0 1 := by
    exact orderedPathPair_inverse_integrable zero_le_one
      (by norm_num : (0 : ℝ) ∈ Icc (0 : ℝ) 1) hη continuousOn_const
      (fun _ _ => le_rfl) (fun _ _ _ _ _ => le_rfl) (zero_lt_one.trans hQ).le α
      n hn bf hf hbf hhf (orderedOverlap n)
  have hGm : AEStronglyMeasurable G (volume.restrict (uIoc (0 : ℝ) 1)) := by
    exact (hwm.comp α.val.property.2.measurable).aestronglyMeasurable.mul
      ((measurable_id.aestronglyMeasurable).sub hSi.aestronglyMeasurable_restrict_uIoc)
  have hGi : IntervalIntegrable G volume 0 1 := by
    apply (intervalIntegrable_const (c := W)).mono_fun hGm
    filter_upwards [ae_restrict_mem (measurableSet_uIoc)] with r hr
    have hri : r ∈ Ioc (0 : ℝ) 1 := by simpa [uIoc_of_le zero_le_one] using hr
    have hur : α.val.val r ∈ Ioc (0 : ℝ) 1 := by
      have hp := hαstrict (by norm_num) ⟨hri.1.le, hri.2⟩ hri.1
      rw [α.property.1] at hp
      exact ⟨hp, (α.val.property.1 r).2⟩
    have hs := orderedPath_SK_bounds n hn bf hf hbf hhf hur
    change ‖w (α.val.val r) * (r - S (α.val.val r))‖ ≤ ‖W‖
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg hW,
      abs_of_nonneg (hwp _ ⟨hur.1.le, hur.2⟩).le]
    have hdiff : |r - S (α.val.val r)| ≤ 1 := by
      apply abs_le.mpr
      exact ⟨by linarith [hri.1, hs.2.1], by linarith [hri.2, hs.1]⟩
    exact (mul_le_mul_of_nonneg_left hdiff (hwp _ ⟨hur.1.le, hur.2⟩).le).trans
      (by simpa only [mul_one] using hwb _ ⟨hur.1.le, hur.2⟩)
  have hαd : sourceInverseConstraints 0 0 k M α.val.val := by
    have hd : α.val ∈ inverseDifferentialConstraints 0 0 k M := by
      rw [inverseDifferentialConstraints_eq 0 0 zero_le_one k M continuousOn_const
        continuous_const (fun _ _ _ _ _ => le_rfl) (zero_lt_one.trans hQ).le]
      exact α.property
    exact hd
  obtain ⟨H, hH, hHd, hbang, hzero⟩ := control_first_variation_to_potential
    (α := α.val.val) (k := k) (M := M) (M' := fun _ => 0)
    (w := inverseControlWeight α.val.val k M) (G := G)
    (gap := Q - η) (U := Q - η) (L := 0) (lo := η) (hi := Q)
    zero_le_one hα α.property.1 α.property.2.1 α.val.property.2.measurable
    measurable_const continuous_const measurable_const continuousOn_const
    (inverseControlWeight_measurable α.val.property.2.measurable measurable_const measurable_const)
    (fun _ _ => by simp [M]) (by linarith) (by linarith) le_rfl
    (inverseControlWeight_ae_equation hαd (fun _ _ => by dsimp [k, M]; linarith))
    (fun r hr => ⟨inverseControlWeight_mem _ _ _ _, by simp [k, M]⟩)
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) (by simpa using hη1) (by simpa using hQ)
    hGi (by
      intro ψ D B T hT hB hψ hψb hfeas
      exact inverse_mass_strength_minimum_first_variation hη continuousOn_const
        (fun _ _ => le_rfl) (fun _ _ _ _ _ => le_rfl) (zero_lt_one.trans hQ).le
        continuous_const α hfeas hT hB hψ hψb n hn b h w hW hb hh hw hwm hwb' hbn hhn hmin)
  refine ⟨H, hH, ?_, ?_, ?_⟩
  · simpa only [mul_zero, inverseControlFactor, intervalIntegral.integral_zero,
      Real.exp_zero, one_mul] using hHd
  · exact hbang
  · filter_upwards [hzero] with r hz hr hhr
    have he := hz hr hhr
    change w (α.val.val r) * (r - S (α.val.val r)) = 0 at he
    have hp := hwp _ (α.val.property.1 r)
    have he' := (mul_eq_zero.mp he).resolve_left hp.ne'
    exact (sub_eq_zero.mp he').symm

end

end OAI.SKFluctuations.LaplaceWindowFormalization
