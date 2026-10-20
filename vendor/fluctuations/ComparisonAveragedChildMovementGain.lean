module

public import OmittedPathMovementGain
public import StrengthParameterCalculus

@[expose] public section

noncomputable section
set_option maxHeartbeats 2000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory Filter Set Hierarchy
open scoped Topology

structure AveragedMovementClocks
    (b h e r D z eh rhat : ℝ → ℝ) : Prop where
  child_matrix : MonotoneOn (fun u => b u-e u-D u) (Icc (0 : ℝ) 1)
  child_field : MonotoneOn (fun u => h u+e u*r u+D u*z u) (Icc (0 : ℝ) 1)
  trial_matrix : MonotoneOn (fun u => b u-eh u) (Icc (0 : ℝ) 1)
  trial_field : MonotoneOn (fun u => h u+eh u*rhat u) (Icc (0 : ℝ) 1)
  child_matrix_zero : 0 ≤ b 0-e 0-D 0
  child_field_zero : 0 ≤ h 0+e 0*r 0+D 0*z 0
  trial_matrix_zero : 0 ≤ b 0-eh 0
  trial_field_zero : 0 ≤ h 0+eh 0*rhat 0

theorem comparison_movement_strength_upper
    (E : ℝ → ℝ) (hEn : ∀ q ∈ Icc (0 : ℝ) 1, 0 ≤ E q)
    (hEa : AntitoneOn E (Icc (0 : ℝ) 1))
    (hEm : MonotoneOn (fun q => q*E q) (Icc (0 : ℝ) 1))
    {r z rhat omega : ℝ} (hr : r ∈ Icc (0 : ℝ) 1)
    (hz : z ∈ Icc (0 : ℝ) 1) (hrhat : rhat ∈ Icc (0 : ℝ) 1)
    (hw : omega ∈ Ico (0 : ℝ) 1) (htrial : rhat=r+omega*(z-r)) :
    E rhat ≤ E r/(1-omega) := by
  have hden : 0 < 1-omega := by linarith [hw.2]
  apply (le_div_iff₀ hden).mpr
  by_cases hrr : r ≤ rhat
  · have hE := hEa hr hrhat hrr
    nlinarith [mul_nonneg (hEn rhat hrhat) hw.1]
  · have hrr' : rhat ≤ r := le_of_not_ge hrr
    have hprod := hEm hrhat hr hrr'
    have hlow : (1-omega)*r ≤ rhat := by
      rw [htrial]
      nlinarith [mul_nonneg hw.1 hz.1]
    have hrpos : 0 < r := by linarith [hrhat.1]
    have hmul := mul_le_mul_of_nonneg_left hlow (hEn rhat hrhat)
    nlinarith

theorem actual_averaged_path_chord_of_ae_continuous_cost
    (n : ℕ) (hn : 0 < n) (b h b' h' : ℝ → ℝ)
    (hb : MonotoneOn b (Icc (0 : ℝ) 1)) (hh : MonotoneOn h (Icc (0 : ℝ) 1))
    (hb' : MonotoneOn b' (Icc (0 : ℝ) 1)) (hh' : MonotoneOn h' (Icc (0 : ℝ) 1))
    (hb0 : 0 ≤ b 0) (hh0 : 0 ≤ h 0) (hb0' : 0 ≤ b' 0) (hh0' : 0 ≤ h' 0)
    (hba : ∀ u ∈ Icc (0 : ℝ) 1, b u ≤ b' u)
    (hzero : ∀ u ∈ Icc (0 : ℝ) 1, b u=b' u → h u=h' u)
    {C : ℝ} (hbound : ∀ u ∈ Icc (0 : ℝ) 1, ‖(h u-h' u)^2/(b' u-b u)‖ ≤ C)
    (hc : ∀ᵐ u ∂volume, u ∈ Icc (0 : ℝ) 1 →
      ContinuousWithinAt (fun v => (h v-h' v)^2/(b' v-b v)) (Icc (0 : ℝ) 1) u) :
    realOrderedSKPathPressure n b' h' 0 ≤ realOrderedSKPathPressure n b h 0+
      (1/4 : ℝ)*(∫ u in (0 : ℝ)..1, (h u-h' u)^2/(b' u-b u)) := by
  have hlim := bounded_ae_continuous_partitionSum_tendsto hbound hc
  apply le_of_tendsto_of_tendsto
    (orderedSKPressure_samples_tendsto n hn b' h' hb' hh' hb0' hh0' 0)
    ((orderedSKPressure_samples_tendsto n hn b h hb hh hb0 hh0 0).add
      (hlim.const_mul (1/4 : ℝ)))
  apply Eventually.of_forall
  intro k
  let as := uniformMasses k
  have ha : MassOrdered 0 as := uniformMasses_ordered k
  exact orderedSK_cumulative_chord n hn as ha.pairwise ha.members_le_one
    (fun j => b (partitionPoint 0 as j)) (fun j => h (partitionPoint 0 as j))
    (fun j => b' (partitionPoint 0 as j)) (fun j => h' (partitionPoint 0 as j))
    (comp_partitionPoint_monotone hb as ha) (comp_partitionPoint_monotone hh as ha)
    (comp_partitionPoint_monotone hb' as ha) (comp_partitionPoint_monotone hh' as ha)
    (by simpa [partitionPoint] using hb0) (by simpa [partitionPoint] using hh0)
    (by simpa [partitionPoint] using hb0') (by simpa [partitionPoint] using hh0')
    (fun j _ => hba _ (partitionPoint_mem as ha j))
    (fun j _ he => hzero _ (partitionPoint_mem as ha j) he) 0

theorem actual_averaged_extended_child_movement_gain
    (n : ℕ) (hn : 0 < n) (b h e r D z eh rhat omega : ℝ → ℝ)
    (he : ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ e u)
    (hD : ∀ u ∈ Icc (0 : ℝ) 1, 0 < D u)
    (heh : ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ eh u)
    (hr : ∀ u ∈ Icc (0 : ℝ) 1, r u ∈ Icc (0 : ℝ) 1)
    (hz : ∀ u ∈ Icc (0 : ℝ) 1, z u ∈ Icc (0 : ℝ) 1)
    (hw0 : ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ omega u)
    (hw : ∀ u ∈ Icc (0 : ℝ) 1, omega u < D u/(e u+D u))
    (hehat : ∀ u ∈ Icc (0 : ℝ) 1, eh u ≤ e u/(1-omega u))
    (hrhat : ∀ u ∈ Icc (0 : ℝ) 1, rhat u=r u+omega u*(z u-r u))
    {C : ℝ} (hbudget : ∀ u ∈ Icc (0 : ℝ) 1, e u+D u ≤ C)
    (hc : ∀ᵐ u ∂volume, u ∈ Icc (0 : ℝ) 1 → ContinuousWithinAt
      (fun v => (e v*r v+D v*z v-eh v*rhat v)^2/(e v+D v-eh v)) (Icc (0 : ℝ) 1) u)
    (hiE : IntervalIntegrable (fun u => e u*(r u)^2) volume 0 1)
    (hiD : IntervalIntegrable (fun u => D u*(z u)^2) volume 0 1)
    (hiH : IntervalIntegrable (fun u => eh u*(rhat u)^2) volume 0 1)
    (hiC : IntervalIntegrable
      (fun u => (e u*r u+D u*z u-eh u*rhat u)^2/(e u+D u-eh u)) volume 0 1)
    (hiG : IntervalIntegrable (fun u => e u*(rhat u-r u)*(z u-r u)) volume 0 1)
    (hclocks : AveragedMovementClocks b h e r D z eh rhat) {err : ℝ}
    (hminimum : pathCompensatedPressure n b h e r 0 ≤
      pathCompensatedPressure n b h eh rhat 0)
    (hchild : pathCompensatedPressure n (fun u => b u-e u)
      (fun u => h u+e u*r u) D z 0 ≤
      realOrderedSKPathPressure n (fun u => b u-e u)
        (fun u => h u+e u*r u) 0+err) :
    (∫ u in (0 : ℝ)..1, e u*(rhat u-r u)*(z u-r u)) ≤ 4*err := by
  let cost := fun u => (e u*r u+D u*z u-eh u*rhat u)^2/(e u+D u-eh u)
  have hpos (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) : 0 < e u+D u-eh u :=
    (movement_strength_positive (he u hu) (hD u hu) (hw0 u hu) (hw u hu) (hehat u hu)).2
  have hid (u : ℝ) : (h u+e u*r u+D u*z u-(h u+eh u*rhat u))^2/
      (b u-eh u-(b u-e u-D u))=cost u := by
    dsimp [cost]
    congr 1 <;> ring
  have hbound : ∀ u ∈ Icc (0 : ℝ) 1, ‖cost u‖ ≤ C := by
    intro u hu
    have hrange := movement_chord_cost_bound (he u hu) (hD u hu) (heh u hu)
      (hw0 u hu) (hw u hu) (hehat u hu) (hr u hu) (hz u hu)
    rw [← hrhat u hu] at hrange
    change ‖cost u‖ ≤ C
    rw [Real.norm_eq_abs, abs_of_nonneg hrange.1]
    exact hrange.2.trans (hbudget u hu)
  have hchord := actual_averaged_path_chord_of_ae_continuous_cost n hn
    (fun u => b u-e u-D u) (fun u => h u+e u*r u+D u*z u)
    (fun u => b u-eh u) (fun u => h u+eh u*rhat u)
    hclocks.child_matrix hclocks.child_field hclocks.trial_matrix hclocks.trial_field
    hclocks.child_matrix_zero hclocks.child_field_zero
    hclocks.trial_matrix_zero hclocks.trial_field_zero
    (fun u hu => by linarith [hpos u hu])
    (fun u hu heq => by exfalso; linarith [hpos u hu])
    (by simpa only [hid] using hbound) (by simpa only [hid] using hc)
  simp_rw [hid] at hchord
  have hsum : (∫ u in (0 : ℝ)..1, e u*(rhat u-r u)*(z u-r u)) ≤
      ∫ u in (0 : ℝ)..1, e u*(r u)^2+D u*(z u)^2-eh u*(rhat u)^2-cost u := by
    apply intervalIntegral.integral_mono_on zero_le_one hiG (((hiE.add hiD).sub hiH).sub hiC)
    intro u hu
    have hgain := movement_pointwise_gain (r := r u) (z := z u)
      (he u hu) (hD u hu) (hw0 u hu) (hw u hu) (hehat u hu)
    rw [← hrhat u hu] at hgain
    have heq : e u*(rhat u-r u)*(z u-r u)=e u*omega u*(z u-r u)^2 := by
      rw [hrhat u hu]
      ring
    rw [heq]
    exact hgain
  rw [intervalIntegral.integral_sub ((hiE.add hiD).sub hiH) hiC,
    intervalIntegral.integral_sub (hiE.add hiD) hiH,
    intervalIntegral.integral_add hiE hiD] at hsum
  unfold pathCompensatedPressure at hminimum hchild
  dsimp only at hminimum hchild
  linarith

theorem actual_averaged_child_movement_gain
    (n : ℕ) (hn : 0 < n) (b h e r D z eh rhat omega : ℝ → ℝ)
    (he : ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ e u)
    (hD : ∀ u ∈ Icc (0 : ℝ) 1, 0 < D u)
    (hw0 : ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ omega u)
    (hw : ∀ u ∈ Icc (0 : ℝ) 1, omega u < D u/(e u+D u))
    (hehat : ∀ u ∈ Icc (0 : ℝ) 1, eh u ≤ e u/(1-omega u))
    (hrhat : ∀ u ∈ Icc (0 : ℝ) 1, rhat u=r u+omega u*(z u-r u))
    (hec : ContinuousOn e (Icc (0 : ℝ) 1))
    (hDc : ContinuousOn D (Icc (0 : ℝ) 1))
    (hehc : ContinuousOn eh (Icc (0 : ℝ) 1))
    (hrc : ContinuousOn r (Icc (0 : ℝ) 1))
    (hzc : ContinuousOn z (Icc (0 : ℝ) 1))
    (hrhc : ContinuousOn rhat (Icc (0 : ℝ) 1))
    (hclocks : AveragedMovementClocks b h e r D z eh rhat) {err : ℝ}
    (hminimum : pathCompensatedPressure n b h e r 0 ≤
      pathCompensatedPressure n b h eh rhat 0)
    (hchild : pathCompensatedPressure n (fun u => b u-e u)
      (fun u => h u+e u*r u) D z 0 ≤
      realOrderedSKPathPressure n (fun u => b u-e u)
        (fun u => h u+e u*r u) 0+err) :
    (∫ u in (0 : ℝ)..1, e u*omega u*(z u-r u)^2) ≤ 4*err := by
  have hgain := actual_path_movement_gain n hn b h e r D z eh rhat omega
    he hD hw0 hw hehat hrhat hec hDc hehc hrc hzc hrhc
    hclocks.child_matrix hclocks.child_field hclocks.trial_matrix hclocks.trial_field
    hclocks.child_matrix_zero hclocks.child_field_zero
    hclocks.trial_matrix_zero hclocks.trial_field_zero 0
  have hid : (∫ u in (0 : ℝ)..1, e u*(rhat u-r u)*(z u-r u)) =
      ∫ u in (0 : ℝ)..1, e u*omega u*(z u-r u)^2 := by
    apply intervalIntegral.integral_congr
    intro u hu
    have hu' : u ∈ Icc (0 : ℝ) 1 := by simpa using hu
    dsimp only
    rw [hrhat u hu']
    ring
  rw [hid] at hgain
  linarith

theorem actual_averaged_omitted_child_movement_gain
    (n : ℕ) (hn : 0 < n) {u0 : ℝ} (hu0 : u0 ∈ Icc (0 : ℝ) 1)
    (b h e r D z eh rhat omega : ℝ → ℝ)
    (he : ∀ u ∈ Icc u0 1, 0 ≤ e u) (hD : ∀ u ∈ Icc u0 1, 0 < D u)
    (hw0 : ∀ u ∈ Icc u0 1, 0 ≤ omega u)
    (hw : ∀ u ∈ Icc u0 1, omega u < D u/(e u+D u))
    (hehat : ∀ u ∈ Icc u0 1, eh u ≤ e u/(1-omega u))
    (hrhat : ∀ u ∈ Icc u0 1, rhat u=r u+omega u*(z u-r u))
    (hec : ContinuousOn e (Icc u0 1)) (hDc : ContinuousOn D (Icc u0 1))
    (hehc : ContinuousOn eh (Icc u0 1)) (hrc : ContinuousOn r (Icc u0 1))
    (hzc : ContinuousOn z (Icc u0 1)) (hrhc : ContinuousOn rhat (Icc u0 1))
    (hbefore : ∀ u ∈ Ico (0 : ℝ) u0, e u=0 ∧ D u=0 ∧ eh u=0)
    (hclocks : AveragedMovementClocks b h e r D z eh rhat) {err : ℝ}
    (hminimum : pathCompensatedPressure n b h e r 0 ≤
      pathCompensatedPressure n b h eh rhat 0)
    (hchild : pathCompensatedPressure n (fun u => b u-e u)
      (fun u => h u+e u*r u) D z 0 ≤
      realOrderedSKPathPressure n (fun u => b u-e u)
        (fun u => h u+e u*r u) 0+err) :
    (∫ u in (0 : ℝ)..1, e u*(rhat u-r u)*(z u-r u)) ≤ 4*err := by
  have hgain := actual_omitted_path_movement_gain n hn hu0 b h e r D z eh rhat omega
    he hD hw0 hw hehat hrhat hec hDc hehc hrc hzc hrhc hbefore
    hclocks.child_matrix hclocks.child_field hclocks.trial_matrix hclocks.trial_field
    hclocks.child_matrix_zero hclocks.child_field_zero
    hclocks.trial_matrix_zero hclocks.trial_field_zero 0
  linarith

def actualAveragedParentObjective (n : ℕ) (b h : ℝ → ℝ) (d lam : ℝ)
    (r : ℝ → ℝ) : ℝ :=
  pathCompensatedPressure n b h (fun u => laplaceComparisonStrength d lam (r u)) r 0

theorem actual_averaged_child_gain_of_feasible_minimum
    (n : ℕ) (hn : 0 < n) (b h r D z rhat omega : ℝ → ℝ)
    {d lam err : ℝ} (hd : d ≠ 0) (hlam : 0 ≤ lam)
    (feasible : Set (ℝ → ℝ)) (_hparent : r ∈ feasible) (htrial : rhat ∈ feasible)
    (hminimum : ∀ R ∈ feasible,
      actualAveragedParentObjective n b h d lam r ≤
        actualAveragedParentObjective n b h d lam R)
    (hr : ∀ u ∈ Icc (0 : ℝ) 1, r u ∈ Icc (0 : ℝ) 1)
    (hz : ∀ u ∈ Icc (0 : ℝ) 1, z u ∈ Icc (0 : ℝ) 1)
    (hrhat : ∀ u ∈ Icc (0 : ℝ) 1, rhat u ∈ Icc (0 : ℝ) 1)
    (hD : ∀ u ∈ Icc (0 : ℝ) 1, 0 < D u)
    (hw0 : ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ omega u)
    (hw : ∀ u ∈ Icc (0 : ℝ) 1,
      omega u < D u/(laplaceComparisonStrength d lam (r u)+D u))
    (hmove : ∀ u ∈ Icc (0 : ℝ) 1, rhat u=r u+omega u*(z u-r u))
    (hrc : ContinuousOn r (Icc (0 : ℝ) 1))
    (hzc : ContinuousOn z (Icc (0 : ℝ) 1))
    (hrhc : ContinuousOn rhat (Icc (0 : ℝ) 1))
    (hDc : ContinuousOn D (Icc (0 : ℝ) 1))
    (hclocks : AveragedMovementClocks b h
      (fun u => laplaceComparisonStrength d lam (r u)) r D z
      (fun u => laplaceComparisonStrength d lam (rhat u)) rhat)
    (hchild : pathCompensatedPressure n
      (fun u => b u-laplaceComparisonStrength d lam (r u))
      (fun u => h u+laplaceComparisonStrength d lam (r u)*r u) D z 0 ≤
      realOrderedSKPathPressure n
        (fun u => b u-laplaceComparisonStrength d lam (r u))
        (fun u => h u+laplaceComparisonStrength d lam (r u)*r u) 0+err) :
    (∫ u in (0 : ℝ)..1,
      laplaceComparisonStrength d lam (r u)*omega u*(z u-r u)^2) ≤ 4*err := by
  have he : ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ laplaceComparisonStrength d lam (r u) :=
    fun u _ => laplaceComparisonStrength_nonneg d (r u) hlam
  have hehat : ∀ u ∈ Icc (0 : ℝ) 1,
      laplaceComparisonStrength d lam (rhat u) ≤
        laplaceComparisonStrength d lam (r u)/(1-omega u) := by
    intro u hu
    have hden : 0 < laplaceComparisonStrength d lam (r u)+D u :=
      add_pos_of_nonneg_of_pos (he u hu) (hD u hu)
    have hratio : D u/(laplaceComparisonStrength d lam (r u)+D u) ≤ 1 :=
      (div_le_one₀ hden).mpr (by linarith [he u hu])
    exact comparison_movement_strength_upper (laplaceComparisonStrength d lam)
      (fun q _ => laplaceComparisonStrength_nonneg d q hlam)
      (laplaceComparisonStrength_monotonicities_nonneg hd hlam).1
      (by simpa only [mul_comm] using (laplaceComparisonStrength_monotonicities_nonneg hd hlam).2)
      (hr u hu) (hz u hu) (hrhat u hu)
      ⟨hw0 u hu, (hw u hu).trans_le hratio⟩ (hmove u hu)
  exact actual_averaged_child_movement_gain n hn b h
    (fun u => laplaceComparisonStrength d lam (r u)) r D z
    (fun u => laplaceComparisonStrength d lam (rhat u)) rhat omega
    he hD hw0 hw hehat hmove
    ((laplaceComparisonStrength_contDiff d lam).continuous.comp_continuousOn hrc)
    hDc ((laplaceComparisonStrength_contDiff d lam).continuous.comp_continuousOn hrhc)
    hrc hzc hrhc hclocks (hminimum rhat htrial) hchild

end OAI.SKFluctuations.LaplaceWindowFormalization
