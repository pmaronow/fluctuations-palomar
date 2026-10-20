module

public import ComparisonActualHighOnlyCapTrace
public import ComparisonCapSideTraceLocalizedBroad

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 4000000
namespace ActualHighOnlyOverlapMinimum.ShiftedCapInterval
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable {a : ActualHighOnlyOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}
    {P : a.Potential} (c : ShiftedCapInterval a P)

theorem mass_lower : a.data.M (a.alpha.val.val c.left)*(c.right-c.left)≤
    a.alpha.val.val c.right-a.alpha.val.val c.left := by
  have hsub : Icc c.left c.right⊆Icc (0:ℝ) 1:=Icc_subset_Icc c.hleft c.hright
  have hLip : LipschitzOnWith ⟨a.data.M 1,a.data.hM⟩ a.alpha.val.val (uIcc c.left c.right):=by
    simpa only [uIcc_of_le c.hlt.le] using
      (inverseIntegralConstraints_lipschitz a.data.hm a.data.hM a.alpha.property).mono hsub
  have hac:=hLip.absolutelyContinuousOnInterval
  have hden:=P.cap_density_on_interval c.hleft c.hright c.negative
  have hbound : ∀ᵐr∂volume.restrict (Icc c.left c.right),
      a.data.M (a.alpha.val.val c.left)≤ deriv a.alpha.val.val r:=by
    filter_upwards [ae_restrict_mem measurableSet_Icc,ae_restrict_of_ae hden] with r hr hd
    rw [hd hr]
    exact a.data.hm (a.alpha.val.property.1 c.left) (a.alpha.val.property.1 r)
      (a.alpha.val.property.2 hr.1)
  have HH:=intervalIntegral.integral_mono_ae_restrict c.hlt.le intervalIntegrable_const
    hac.intervalIntegrable_deriv hbound
  simpa only [intervalIntegral.integral_const,smul_eq_mul,hac.integral_deriv_eq_sub,
    mul_comm (c.right-c.left)] using HH

theorem unit_trace_eventually
    (hN : 1≤a.data.N) (hlog : 1≤Real.log a.data.N) (hnd : 1/a.data.N≤a.data.d)
    (dphys : ℕ) (e : Fin (dphys+1)≃FeatureIndex (n+1))
    (hl : 0<c.left) (hleft : P.H c.left=0) (hright : P.H c.right=0 ∨ c.right=1)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hend : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hmesh0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0)) {ε : ℝ} (hε : 0<ε) :
    let F:=(n+1:ℝ)*(((1/3)/Real.log a.data.N)*laplaceComparisonStrength a.data.d a.lam c.right)
    ∀ᶠj in atTop,(∫r in Ioo c.left c.right,deriv a.alpha.val.val r
      ∂a.shiftedNativeModel.radiusMeasure dphys e (as j) (ho j))≤
      (a.data.M (a.alpha.val.val c.right)/a.data.M (a.alpha.val.val c.left))*
        ((9*Real.log a.data.N)/F)*(a.alpha.val.val c.right-a.alpha.val.val c.left)+ε := by
  dsimp only
  let m:=a.shiftedNativeModel
  let F:=(n+1:ℝ)*(((1/3)/Real.log a.data.N)*laplaceComparisonStrength a.data.d a.lam c.right)
  let Mz:=a.data.M (a.alpha.val.val c.right)
  let Ma:=a.data.M (a.alpha.val.val c.left)
  have hF : 0<F:=mul_pos (by positivity) (mul_pos (div_pos (by norm_num) (by linarith))
    (laplaceComparisonStrength_pos a.data.d a.hlam c.right))
  have hMa : 0<Ma:=(comparisonCap_first_term (δ:=delta) a.data.hN a.data.hU a.data.hL
    a.data.hE a.data.hd.le (a.alpha.val.property.1 c.left).1).1
  have hMz : 0≤Mz:=hMa.le.trans (a.data.hm (a.alpha.val.property.1 c.left)
    (a.alpha.val.property.1 c.right) (a.alpha.val.property.2 c.hlt.le))
  have hden : ∀ᵐr,r∈Ioo c.left c.right→deriv a.alpha.val.val r≤Mz:=by
    filter_upwards [P.cap_density_on_interval c.hleft c.hright c.negative] with r hdr hr
    rw [hdr (Ioo_subset_Icc_self hr)]
    exact a.data.hm (a.alpha.val.property.1 r) (a.alpha.val.property.1 c.right)
      (a.alpha.val.property.2 hr.2.le)
  have hlength : c.right-c.left≤(a.alpha.val.val c.right-a.alpha.val.val c.left)/Ma:=
    (le_div_iff₀ hMa).mpr (by simpa only [mul_comm] using c.mass_lower)
  have hnormal : Mz*((9*Real.log a.data.N)*(c.right-c.left)/F)≤
      (Mz/Ma)*((9*Real.log a.data.N)/F)*(a.alpha.val.val c.right-a.alpha.val.val c.left):=by
    have H:=mul_le_mul_of_nonneg_left hlength
      (mul_nonneg hMz (div_nonneg (show 0≤9*Real.log a.data.N by linarith) hF.le))
    convert H using 1 <;> ring
  have ht:=c.localized_measure_eventually hN hlog hnd dphys e hl c.hright
    (by simpa only [max_self,min_self] using c.hlt) ⟨Or.inl hleft,hright⟩
    (Ioo c.left c.right) (Subset.refl _) (Subset.refl _) as mesh ho hend hmesh hmesh0 hlim
    (div_pos hε (by linarith : 0<Mz+1))
  filter_upwards [ht] with j hj
  let mu:=m.radiusMeasure dphys e (as j) (ho j)
  have hb:=cap_bounded_density_trace_le mu (m.radiusMeasure_le_volume dphys e (as j) (ho j))
    a.alpha.val.val (fun _=>1) a.alpha.val.property.2 measurable_const
    (Ioo c.left c.right) measurableSet_Ioo hMz (by norm_num : (0:ℝ)≤1) hden
    (fun _ _=>by norm_num)
  simp only [mul_one] at hb
  have hh:=mul_le_mul_of_nonneg_left hj hMz
  have herr : Mz*(ε/(Mz+1))≤ε:=by
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (by linarith : 0<Mz+1)).mpr
    nlinarith
  dsimp only [F,Ma,Mz] at hb hh hnormal herr ⊢
  nlinarith

end ActualHighOnlyOverlapMinimum.ShiftedCapInterval
end OAI.SKFluctuations.LaplaceWindowFormalization
