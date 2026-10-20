module

public import ComparisonActualHighOnlyConditionalCapDensityLength
public import ComparisonActualHighOnlyBroadMovingTrace

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 38000000
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false
attribute [local instance] Classical.propDecidable
namespace ActualHighOnlyOverlapMinimum.ShiftedCapInterval
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable {a : ActualHighOnlyOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}
    {P : a.Potential} (cap : ShiftedCapInterval a P)
theorem cropped_moving_trace_eventually_from_density_length_high_only
    (hN : 1≤a.data.N) (hlog : 1≤Real.log a.data.N) (hnd : 1/a.data.N≤a.data.d)
    (dphys : ℕ) (e : Fin (dphys+1)≃FeatureIndex (n+1))
    {ag zg l z V loss beta B : ℝ} (hag : 0<ag) (hzg : zg≤1)
    (hl : cap.left≤l) (hz : z≤cap.right) (hlz : l<z)
    (hagL : ag≤l) (hzG : z≤zg)
    (hboundary : (P.H cap.left=0 ∨ cap.left=0) ∧ (P.H cap.right=0 ∨ cap.right=1))
    (hV : V∈Icc (0:ℝ) 1)
    (hAV : ∀r∈Ioo l z,a.alpha.val.val r≤V)
    (hloss : 0≤loss)
    (hDensity : a.data.M V*(cap.right-cap.left)≤loss*(∫r in Ioo l z,deriv a.alpha.val.val r))
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hend : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hmesh0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0))
    (moving : ℕ→ℝ→ℝ) (hmeas : ∀j,Measurable (moving j))
    (hbeta : 0≤beta) (hbetaB : beta≤B) (hmoveB : ∀j r,‖moving j r‖≤B)
    (hsupport : ∀j,∀ᵐr,r∉Ioo ag zg→moving j r=0)
    (hcolumns : Tendsto (fun j=>∫r in Ioo ag zg,
      |moving j r-(Ioo l z).indicator (fun _=>beta) r|) atTop (𝓝 0))
    {epsilon : ℝ} (hepsilon : 0<epsilon) :
    let C:=27*(Real.log a.data.N)^2/((n+1:ℝ)*laplaceComparisonStrength a.data.d a.lam zg)
    ∀ᶠj in atTop,(∫r,deriv a.alpha.val.val r*moving j r
      ∂a.shiftedNativeModel.radiusMeasure dphys e (as j) (ho j))≤
      C*loss*
        (beta*(∫r in Ioo l z,deriv a.alpha.val.val r))+epsilon := by
  let m:=a.shiftedNativeModel
  let fixed:=(Ioo l z).indicator (fun _ : ℝ=>beta)
  let C:=27*(Real.log a.data.N)^2/((n+1:ℝ)*laplaceComparisonStrength a.data.d a.lam zg)
  let coef:=C*loss
  have hfixedM : Measurable fixed:=measurable_const.indicator measurableSet_Ioo
  have hfixedB r : ‖fixed r‖≤B:=by
    by_cases hr:r∈Ioo l z
    · rw [show fixed r=beta from indicator_of_mem hr _,Real.norm_eq_abs,abs_of_nonneg hbeta]
      exact hbetaB
    · rw [show fixed r=0 from indicator_of_notMem hr _,norm_zero]
      exact hbeta.trans hbetaB
  have herror:=m.inverse_weight_L1_tendsto hag hzg fixed hfixedM moving hmeas
    hfixedB hmoveB hcolumns
  have hfixedI:=m.radiusWeight_integrableOn hag hzg (Ioo ag zg) measurableSet_Ioo
    (Subset.refl _) fixed hfixedM hfixedB
  have hmoveI j:=m.radiusWeight_integrableOn hag hzg (Ioo ag zg) measurableSet_Ioo
    (Subset.refl _) (moving j) (hmeas j) (hmoveB j)
  have hsA : Ioo l z⊆Ioo ag zg:=Ioo_subset_Ioo hagL hzG
  have hcapA : Ioo l z⊆Ioo cap.left cap.right:=Ioo_subset_Ioo hl hz
  have hoverlap : max cap.left ag < min cap.right zg:=by
    have HH:=max_le hl hagL
    have HR:=le_min hz hzG
    exact HH.trans_lt (hlz.trans_le HR)
  have hfixed:=cap.cropped_unit_trace_from_density_length_high_only hN hlog hnd dphys e hag hzg hoverlap hboundary
    hV (Ioo l z) measurableSet_Ioo hcapA hsA hAV hloss hDensity
    as mesh ho hend hmesh hmesh0 hlim
    (div_pos (show 0<epsilon/2 by positivity) (by linarith : 0<beta+1))
  filter_upwards [hfixed,(tendsto_order.mp herror).2 (epsilon/2) (by positivity)] with j hj he
  let mu:=m.radiusMeasure dphys e (as j) (ho j)
  have hdom : mu≤volume:=m.radiusMeasure_le_volume dphys e (as j) (ho j)
  have hfixedGlobal : (∫r in Ioo ag zg,deriv a.alpha.val.val r*fixed r∂mu)=
      ∫r,deriv a.alpha.val.val r*fixed r∂mu:=by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro r hr
    rw [show fixed r=0 from indicator_of_notMem (fun HH=>hr (hsA HH)) _,mul_zero]
  have hmoveGlobal : (∫r in Ioo ag zg,deriv a.alpha.val.val r*moving j r∂mu)=
      ∫r,deriv a.alpha.val.val r*moving j r∂mu:=by
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    filter_upwards [ae_mono hdom (hsupport j)] with r hr hrd
    rw [hr hrd,mul_zero]
  have H:=dominated_setIntegral_difference_le (Ioo ag zg) (Ioo ag zg) (Subset.refl _) mu hdom
    (fun r=>deriv a.alpha.val.val r*fixed r) (fun r=>deriv a.alpha.val.val r*moving j r)
    hfixedI (hmoveI j)
  rw [hfixedGlobal,hmoveGlobal] at H
  have hfixedEq : (∫r,deriv a.alpha.val.val r*fixed r∂mu)=
      beta*(∫r in Ioo l z,deriv a.alpha.val.val r∂mu):=by
    have heq : (fun r=>deriv a.alpha.val.val r*fixed r)=
        (Ioo l z).indicator (fun r=>beta*deriv a.alpha.val.val r):=by
      funext r
      by_cases hr:r∈Ioo l z <;> simp [fixed,hr,mul_comm]
    rw [heq,integral_indicator measurableSet_Ioo,integral_const_mul]
  have Hj:=mul_le_mul_of_nonneg_left hj hbeta
  have herr : beta*((epsilon/2)/(beta+1))≤epsilon/2:=by
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (by linarith : 0<beta+1)).mpr
    nlinarith
  rw [hfixedEq] at H
  have HA:=le_abs_self ((∫r,deriv a.alpha.val.val r*moving j r∂mu)-
    beta*(∫r in Ioo l z,deriv a.alpha.val.val r∂mu))
  nlinarith

end ActualHighOnlyOverlapMinimum.ShiftedCapInterval
end OAI.SKFluctuations.LaplaceWindowFormalization
