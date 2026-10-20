module

public import PhysicalWholeCapBudget
public import ComparisonContactSideTrace

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 1800000

theorem cap_bounded_density_trace_le
    (μ : Measure ℝ) [IsFiniteMeasure μ] (hdom : μ ≤ volume)
    (f w : ℝ → ℝ)
    (hm : Monotone f) (hw : Measurable w)
    (A : Set ℝ) (hA : MeasurableSet A) {D W : ℝ}
    (hD : 0 ≤ D) (_hW : 0 ≤ W)
    (hden : ∀ᵐ r, r∈A → deriv f r ≤ D)
    (hwb : ∀r∈A, 0 ≤ w r ∧ w r ≤ W) :
    (∫r in A, deriv f r*w r∂μ) ≤ D*W*μ.real A := by
  have hmeas : AEStronglyMeasurable (fun r => deriv f r*w r) μ :=
    ((stronglyMeasurable_deriv f).mul hw.stronglyMeasurable).aestronglyMeasurable
  have haeden : ∀ᵐ r∂μ, r∈A → deriv f r ≤ D := ae_mono hdom hden
  have hbd : ∀ᵐ r∂μ.restrict A, ‖deriv f r*w r‖ ≤ D*W := by
    filter_upwards [ae_restrict_mem hA, ae_restrict_of_ae haeden] with r hr hdr
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hm.deriv_nonneg (hwb r hr).1)]
    exact mul_le_mul (hdr hr) (hwb r hr).2 (hwb r hr).1 hD
  have hi : IntegrableOn (fun r => deriv f r*w r) A μ := by
    apply Integrable.of_bound hmeas.restrict (D*W)
    exact hbd
  have hh := setIntegral_mono_on_ae hi (integrableOn_const (μ:=μ) (C:=D*W)) hA
    (haeden.mono (fun r hr hri => mul_le_mul (hr hri) (hwb r hri).2
      (hwb r hri).1 hD))
  simpa only [setIntegral_const, smul_eq_mul, mul_comm (μ.real A)] using hh

section
variable {c : ℝ} {k M : ℝ→ℝ}
variable (hc : 0 < c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r∈Icc (0:ℝ) 1,c ≤ k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)

include hm hM in
theorem comparison_cap_mass_lower
    (α : inverseIntegralConstraints 0 0 k M) (H : ℝ→ℝ)
    (hbang : ∀ᵐ r, r∈Icc (0:ℝ) 1 → H r<0 → deriv α.val.val r=M (α.val.val r))
    {a z : ℝ} (ha : 0 ≤ a) (haz : a ≤ z) (hz : z ≤ 1)
    (hneg : ∀r∈Ioo a z,H r<0) :
    M (α.val.val a)*(z-a) ≤ α.val.val z-α.val.val a := by
  have hsub : Icc a z⊆Icc (0:ℝ) 1 := Icc_subset_Icc ha hz
  have hLip : LipschitzOnWith ⟨M 1,hM⟩ α.val.val (uIcc a z) := by
    simpa only [uIcc_of_le haz] using (inverseIntegralConstraints_lipschitz hm hM α.property).mono hsub
  have hac : AbsolutelyContinuousOnInterval α.val.val a z := hLip.absolutelyContinuousOnInterval
  have hden := potential_cap_density_on_interval ha hz hbang hneg
  have hbound : ∀ᵐ r∂volume.restrict (Icc a z), M (α.val.val a) ≤ deriv α.val.val r := by
    filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hden] with r hr hd
    rw [hd hr]
    exact hm (α.val.property.1 a) (α.val.property.1 r) (α.val.property.2 hr.1)
  have hh := intervalIntegral.integral_mono_ae_restrict haz
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ=>M (α.val.val a)) volume a z)
    hac.intervalIntegrable_deriv hbound
  simpa only [intervalIntegral.integral_const, smul_eq_mul, hac.integral_deriv_eq_sub,
    mul_comm (z-a)] using hh

theorem comparisonPhysicalWeightedCapTrace_eventually
    {N d lam : ℝ} (hN : 1≤N) (hlog : 1≤Real.log N) (hd : 0<d)
    (hnd : 1/N≤d) (hlam : 0<lam) (hld : lam≤d^2)
    (n dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1)) (b h : ℝ → ℝ) (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hlb : lam≤b 0) (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0≤h 0) (α : inverseIntegralConstraints 0 0 k M)
    (H J : ℝ → ℝ) (hH : AbsolutelyContinuousOnInterval H 0 1)
    (hJ : ∀r∈Icc (0:ℝ) 1,0<J r)
    (hD : ∀ᵐ r,r∈Icc (0:ℝ) 1→HasDerivAt H
      (J r*radiusComparisonGradient (laplaceComparisonStrength d lam) α.val.val
        (orderedPathS (n+1)
          (fun u=>(b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)).toNNReal)
          (fun u=>(h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)*comparisonSweepQuantile hc hk hkc hm hM α u).toNNReal))
        (orderedPathB (n+1)
          (fun u=>(b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)).toNNReal)
          (fun u=>(h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)*comparisonSweepQuantile hc hk hkc hm hM α u).toNNReal)) r) r)
    (hbang : ∀ᵐ r, r∈Icc (0:ℝ) 1 → H r<0 → deriv α.val.val r=M (α.val.val r))
    {a z : ℝ} (ha : 0 ≤ a) (haz : a < z) (hz : z ≤ 1)
    (haH : H a=0) (hzH : H z=0) (hneg : ∀r∈Ioo a z,H r<0)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hend : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hmesh0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0))
    (hMz : 0 ≤ M (α.val.val z))
    (A : Set ℝ) (hA : MeasurableSet A) (hAcap : A⊆Ioo a z)
    (w : ℝ→ℝ) (hw : Measurable w) {W : ℝ} (hW : 0 ≤ W)
    (hwb : ∀r∈A, 0 ≤ w r ∧ w r ≤ W)
    {ε : ℝ} (hε : 0 < ε) :
    let F := (n+1:ℝ)*(((1/3)/Real.log N)*laplaceComparisonStrength d lam z)
    ∀ᶠ j in atTop,
      (∫r in A,deriv α.val.val r*w r∂comparisonPhysicalRadiusMeasure hc hk hkc hm hM
        n dphys e d lam b h α (as j) (ho j)) ≤
      M (α.val.val z)*W*((9*Real.log N)*(z-a)/F)+ε := by
  dsimp only
  let F := (n+1:ℝ)*(((1/3)/Real.log N)*laplaceComparisonStrength d lam z)
  let D := M (α.val.val z)
  let B := (9*Real.log N)*(z-a)/F
  have hαz : α.val.val z∈Icc (0:ℝ) 1 := α.val.property.1 z
  have hden : ∀ᵐ r, r∈A → deriv α.val.val r ≤ D := by
    filter_upwards [hbang] with r hr hri
    have hrz := hAcap hri
    have hr01 : r∈Icc (0:ℝ) 1 := ⟨ha.trans hrz.1.le,hrz.2.le.trans hz⟩
    rw [hr hr01 (hneg r hrz)]
    exact hm (α.val.property.1 r) hαz (α.val.property.2 hrz.2.le)
  have hF : 0 < F := mul_pos (by positivity) (mul_pos
    (div_pos (by norm_num) (by linarith)) (laplaceComparisonStrength_pos d hlam z))
  have hB : 0 ≤ B := div_nonneg (by positivity) hF.le
  have hD0 : 0 ≤ D := hMz
  have hDW : 0 ≤ D*W := mul_nonneg hD0 hW
  have hsmall : 0 < ε/(D*W+1) := div_pos hε (by linarith)
  have ht := comparisonPhysicalWholeCapTrace_eventually hc hk hkc hm hM
    hN hlog hd hnd hlam hld n dphys e b h hb hlb hh hh0 α H J hH hJ hD
    ha haz hz haH hzH hneg as mesh ho hend hmesh hmesh0 hlim hsmall
  filter_upwards [ht] with j hj
  let μ := comparisonPhysicalRadiusMeasure hc hk hkc hm hM n dphys e d lam b h α (as j) (ho j)
  have hdom : μ ≤ volume := (comparisonPhysicalRadiusMeasure_le_compact_volume hc hk hkc hm hM
    n dphys e d lam b h α (as j) (ho j)).trans Measure.restrict_le_self
  have hμcap : μ.real (Ioo a z) ≤ B+ε/(D*W+1) := by
    have hb0 : 0 ≤ B+ε/(D*W+1) := add_nonneg hB hsmall.le
    exact (ENNReal.le_ofReal_iff_toReal_le (by finiteness) hb0).mp hj
  have hi := cap_bounded_density_trace_le μ hdom α.val.val w
    α.val.property.2 hw A hA hD0 hW hden hwb
  have hμA := measureReal_mono (μ:=μ) hAcap
  have hmul := mul_le_mul_of_nonneg_left (hμA.trans hμcap) hDW
  have herr : D*W*(ε/(D*W+1)) ≤ ε := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by linarith : 0 < D*W+1)).mpr
    nlinarith
  dsimp only [D,B,F] at *
  nlinarith

theorem comparisonPhysicalSelectedCapTrace_eventually
    {N d lam : ℝ} (hN : 1≤N) (hlog : 1≤Real.log N) (hd : 0<d)
    (hnd : 1/N≤d) (hlam : 0<lam) (hld : lam≤d^2)
    (n dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1)) (b h : ℝ → ℝ) (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hlb : lam≤b 0) (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0≤h 0) (α : inverseIntegralConstraints 0 0 k M)
    (H J : ℝ → ℝ) (hH : AbsolutelyContinuousOnInterval H 0 1)
    (hJ : ∀r∈Icc (0:ℝ) 1,0<J r)
    (hD : ∀ᵐ r,r∈Icc (0:ℝ) 1→HasDerivAt H
      (J r*radiusComparisonGradient (laplaceComparisonStrength d lam) α.val.val
        (orderedPathS (n+1)
          (fun u=>(b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)).toNNReal)
          (fun u=>(h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)*comparisonSweepQuantile hc hk hkc hm hM α u).toNNReal))
        (orderedPathB (n+1)
          (fun u=>(b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)).toNNReal)
          (fun u=>(h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)*comparisonSweepQuantile hc hk hkc hm hM α u).toNNReal)) r) r)
    (hbang : ∀ᵐ r, r∈Icc (0:ℝ) 1 → H r<0 → deriv α.val.val r=M (α.val.val r))
    {a z : ℝ} (ha : 0 ≤ a) (haz : a < z) (hz : z ≤ 1)
    (haH : H a=0) (hzH : H z=0) (hneg : ∀r∈Ioo a z,H r<0)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hend : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hmesh0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0))
    (V : ℝ) (hV : V∈Icc (0:ℝ) 1) (hMV : 0 ≤ M V)
    (A : Set ℝ) (hA : MeasurableSet A) (hAcap : A⊆Ioo a z)
    (hAV : ∀r∈A, α.val.val r ≤ V)
    (w : ℝ→ℝ) (hw : Measurable w) {W : ℝ} (hW : 0 ≤ W)
    (hwb : ∀r∈A, 0 ≤ w r ∧ w r ≤ W)
    {ε : ℝ} (hε : 0 < ε) :
    let F := (n+1:ℝ)*(((1/3)/Real.log N)*laplaceComparisonStrength d lam z)
    ∀ᶠ j in atTop,
      (∫r in A,deriv α.val.val r*w r∂comparisonPhysicalRadiusMeasure hc hk hkc hm hM
        n dphys e d lam b h α (as j) (ho j)) ≤
      M V*W*((9*Real.log N)*(z-a)/F)+ε := by
  dsimp only
  let F := (n+1:ℝ)*(((1/3)/Real.log N)*laplaceComparisonStrength d lam z)
  let D := M V
  let B := (9*Real.log N)*(z-a)/F
  have hden : ∀ᵐ r, r∈A → deriv α.val.val r ≤ D := by
    filter_upwards [hbang] with r hr hri
    have hrz := hAcap hri
    have hr01 : r∈Icc (0:ℝ) 1 := ⟨ha.trans hrz.1.le,hrz.2.le.trans hz⟩
    rw [hr hr01 (hneg r hrz)]
    exact hm (α.val.property.1 r) hV (hAV r hri)
  have hF : 0 < F := mul_pos (by positivity) (mul_pos
    (div_pos (by norm_num) (by linarith)) (laplaceComparisonStrength_pos d hlam z))
  have hB : 0 ≤ B := div_nonneg (by positivity) hF.le
  have hD0 : 0 ≤ D := hMV
  have hDW : 0 ≤ D*W := mul_nonneg hD0 hW
  have hsmall : 0 < ε/(D*W+1) := div_pos hε (by linarith)
  have ht := comparisonPhysicalWholeCapTrace_eventually hc hk hkc hm hM
    hN hlog hd hnd hlam hld n dphys e b h hb hlb hh hh0 α H J hH hJ hD
    ha haz hz haH hzH hneg as mesh ho hend hmesh hmesh0 hlim hsmall
  filter_upwards [ht] with j hj
  let μ := comparisonPhysicalRadiusMeasure hc hk hkc hm hM n dphys e d lam b h α (as j) (ho j)
  have hdom : μ ≤ volume := (comparisonPhysicalRadiusMeasure_le_compact_volume hc hk hkc hm hM
    n dphys e d lam b h α (as j) (ho j)).trans Measure.restrict_le_self
  have hμcap : μ.real (Ioo a z) ≤ B+ε/(D*W+1) := by
    have hb0 : 0 ≤ B+ε/(D*W+1) := add_nonneg hB hsmall.le
    exact (ENNReal.le_ofReal_iff_toReal_le (by finiteness) hb0).mp hj
  have hi := cap_bounded_density_trace_le μ hdom α.val.val w
    α.val.property.2 hw A hA hD0 hW hden hwb
  have hμA := measureReal_mono (μ:=μ) hAcap
  have hmul := mul_le_mul_of_nonneg_left (hμA.trans hμcap) hDW
  have herr : D*W*(ε/(D*W+1)) ≤ ε := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by linarith : 0 < D*W+1)).mpr
    nlinarith
  dsimp only [D,B,F] at *
  nlinarith

end
end OAI.SKFluctuations.LaplaceWindowFormalization
