module

public import MacroNegativeRegion
public import SKFluctuationsOAI.Probability.SKFluctuations.ClockRetainTwo

@[expose] public section

noncomputable section

namespace OAI.SKFluctuations.LaplaceWindowFormalization

open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal

section
variable {η Q W : ℝ} (hη : 0 < η) (hη1 : η < 1) (hQ : 1 < Q)

theorem macroInverseQuantile_inverse (α : MacroInverseClass η Q)
    (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) :
    macroInverseQuantile hη hQ α (α.val.val r) = r := by
  have hs := inverseConstraint_strictMonoOn hη continuousOn_const
    (fun _ _ => le_rfl) α.property
  have ha : α.val.val r ∈ Icc (0 : ℝ) 1 := α.val.property.1 r
  apply hs.injOn (macroInverseQuantile_bounds hη hQ α _) hr
  unfold macroInverseQuantile inverseMassQuantile
  rw [projIcc_of_mem zero_le_one ha]
  exact constrainedQuantile_spec zero_le_one hη continuousOn_const
    (fun _ _ => le_rfl) (fun _ _ _ _ _ => le_rfl) (zero_lt_one.trans hQ).le α
    ⟨α.val.val r, ha⟩

include hη1 in
theorem macro_inverse_minimum_mass_defect (n : ℕ) (hn : 0 < n)
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
    let q := macroInverseQuantile hη hQ α
    let S := orderedPathS n (fun u => (b u).toNNReal)
      (fun u => (h u + w u * q u).toNNReal)
    (∫ u in (0 : ℝ)..1, (S u - q u)^2) ≤ η + (1 / Q)^2 := by
  dsimp only
  let q := macroInverseQuantile hη hQ α
  let bf := fun u => (b u).toNNReal
  let hf := fun u => (h u + w u * q u).toNNReal
  let S := orderedPathS n bf hf
  let Sr := fun r => S (α.val.val r)
  have hbf : MonotoneOn bf (Icc (0 : ℝ) 1) := toNNReal_monotoneOn hb
  have hhfield : MonotoneOn (fun u => h u + w u * q u) (Icc (0 : ℝ) 1) := by
    intro u hu v hv huv
    exact add_le_add (hh hu hv huv)
      (mul_le_mul (hw hu hv huv) (macroInverseQuantile_monotone hη hQ α hu hv huv)
        (macroInverseQuantile_bounds hη hQ α u).1 (hwp v hv).le)
  have hhf : MonotoneOn hf (Icc (0 : ℝ) 1) := toNNReal_monotoneOn hhfield
  have hα := inverseIntegralConstraints_lipschitz (fun _ _ _ _ _ => le_rfl)
    (zero_lt_one.trans hQ).le α.property
  have hstrict := inverseConstraint_strictMonoOn hη continuousOn_const
    (fun _ _ => le_rfl) α.property
  have hαpos (r : ℝ) (hr : r ∈ Ioc (0 : ℝ) 1) :
      α.val.val r ∈ Ioc (0 : ℝ) 1 := by
    have hp := hstrict (by norm_num) ⟨hr.1.le, hr.2⟩ hr.1
    rw [α.property.1] at hp
    exact ⟨hp, (α.val.property.1 r).2⟩
  have hSr : MonotoneOn Sr (Ioc (0 : ℝ) 1) := by
    intro r hr t ht hrt
    exact (orderedPath_SK_monotone n hn bf hf hbf hhf).1
      (hαpos r hr) (hαpos t ht) (hstrict.monotoneOn ⟨hr.1.le, hr.2⟩ ⟨ht.1.le, ht.2⟩ hrt)
  have hSrb (r : ℝ) (hr : r ∈ Ioc (0 : ℝ) 1) : Sr r ∈ Icc (0 : ℝ) 1 := by
    have hs := orderedPath_SK_bounds n hn bf hf hbf hhf (hαpos r hr)
    exact ⟨hs.1, hs.2.1⟩
  have hden : ∀ᵐ r, r ∈ Icc (0 : ℝ) 1 → 0 ≤ deriv α.val.val r := by
    have hl := (lipschitz_ae_deriv_lower_iff zero_le_one hα continuousOn_const).mpr
      (fun r hr t ht hrt => (α.property.2.2 r hr t ht hrt).1)
    exact hl.mono (fun r hdr hr => hη.le.trans (hdr hr))
  obtain ⟨H, hH, hd, hbang, hzero⟩ :=
    macro_inverse_minimum_potential hη hη1 hQ n hn b h w hW hb hh hw hwm hwp hwb hbn hhn α hmin
  have hi := potential_macro_radius_defect hη.le (zero_lt_one.trans hQ) hH
    (fun r _ => hwp _ (α.val.property.1 r)) hd hbang hzero hSr hSrb hα hstrict
    (fun r _ => α.val.property.1 r) α.property.1 α.property.2.1 hden
  have he := macro_mass_defect_substitution (S := S) hα hstrict
    (inverseConstraint_image zero_le_one (fun _ _ _ _ _ => le_rfl) (zero_lt_one.trans hQ).le α)
    (macroInverseQuantile_inverse hη hQ α) hden
  exact he.trans_le hi

end

end OAI.SKFluctuations.LaplaceWindowFormalization
