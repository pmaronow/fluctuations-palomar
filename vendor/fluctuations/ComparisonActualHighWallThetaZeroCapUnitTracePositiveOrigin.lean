module

public import ComparisonActualHighWallThetaZeroCapOscillation
public import ComparisonActualHighWallThetaZeroTraceLimit
public import ComparisonCapSideTrace

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 12000000
namespace ActualThetaZeroOverlapMinimum.ShiftedCapInterval
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable {Q : ActualThetaZeroOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}
    {P : Q.Potential} (c : ShiftedCapInterval Q P)

theorem endpoint_radiusS_increment_strict
    (hN : 1≤ Q.data.N) (hlog : 1≤ Real.log Q.data.N) (hnd : 1/Q.data.N≤ Q.data.d)
    (dphys : ℕ) (e : Fin (dphys+1)≃FeatureIndex (n+1))
    (hl : Q.data.rmin< c.left) (hleft : P.H c.left=0) (hright : P.H c.right=0 ∨ c.right=1) :
    Q.radiusS c.right-Q.radiusS c.left≤9*Real.log Q.data.N*(c.right-c.left) := by
  let D:=9*Real.log Q.data.N*(c.right-c.left)
  have hD : 0≤ D:=mul_nonneg (by linarith) (sub_nonneg.mpr c.hlt.le)
  have hc : ContinuousOn Q.radiusS (Icc c.left c.right):=by
    simpa only [uIcc_of_le c.hlt.le] using
      (Q.radiusS_absolutelyContinuous dphys e hl c.hlt.le c.hright).continuousOn
  let Se:=fun r=>Q.radiusS (projIcc c.left c.right c.hlt.le r)
  have hSe : Continuous Se:=(continuousOn_iff_continuous_domRestrict.mp hc).comp continuous_projIcc
  have hEq r (hr : r∈Icc c.left c.right) : Se r=Q.radiusS r:=by
    dsimp only [Se]
    rw [projIcc_of_mem c.hlt.le hr]
  have hi (s t : ℝ) (hs : s∈Ioo c.left c.right) (ht : t∈Ioo c.left c.right) : Se t-Se s≤ D:=by
    rw [hEq s (Ioo_subset_Icc_self hs),hEq t (Ioo_subset_Icc_self ht)]
    by_cases hst:s≤ t
    · exact c.interior_radiusS_increment hN hlog hnd hleft hright hs ht hst
    · have H:=Q.radius_moments.1
        ⟨c.hleft.trans ht.1.le,ht.2.le.trans c.hright⟩
        ⟨c.hleft.trans hs.1.le,hs.2.le.trans c.hright⟩ (le_of_not_ge hst)
      linarith
  have ht (s : ℝ) (hs : s∈Ioo c.left c.right) : Se c.right-Se s≤ D:=by
    have hclosed : IsClosed {t : ℝ | Se t-Se s≤ D}:=
      isClosed_le (hSe.sub continuous_const) continuous_const
    have hsub : Ioo c.left c.right⊆{t : ℝ | Se t-Se s≤ D}:=fun t ht=>hi s t hs ht
    have H:=hclosed.closure_subset_iff.mpr hsub
    rw [closure_Ioo c.hlt.ne] at H
    exact H ⟨c.hlt.le,le_rfl⟩
  have hclosed : IsClosed {s : ℝ | Se c.right-Se s≤ D}:=
    isClosed_le (continuous_const.sub hSe) continuous_const
  have H:=hclosed.closure_subset_iff.mpr ht
  rw [closure_Ioo c.hlt.ne] at H
  have HH:=H (show c.left∈Icc c.left c.right from ⟨le_rfl,c.hlt.le⟩)
  simpa only [mem_ofPred_eq,hEq c.left ⟨le_rfl,c.hlt.le⟩,hEq c.right ⟨c.hlt.le,le_rfl⟩] using HH

theorem mass_lower_strict : Q.data.M (Q.alpha.val.val c.left)*(c.right-c.left)≤
    Q.alpha.val.val c.right-Q.alpha.val.val c.left := by
  have hsub : Icc c.left c.right⊆Icc Q.data.rmin 1:=Icc_subset_Icc c.hleft c.hright
  have hLip : LipschitzOnWith ⟨Q.data.M 1,Q.data.hM⟩ Q.alpha.val.val (uIcc c.left c.right):=by
    simpa only [uIcc_of_le c.hlt.le] using
      (inverseIntegralConstraints_lipschitz Q.data.hm Q.data.hM Q.alpha.property).mono hsub
  have hac:=hLip.absolutelyContinuousOnInterval
  have hden:=P.cap_density_on_interval Q c.hleft c.hright c.negative
  have hbound : ∀ᵐr∂volume.restrict (Icc c.left c.right),
      Q.data.M (Q.alpha.val.val c.left)≤ deriv Q.alpha.val.val r:=by
    filter_upwards [ae_restrict_mem measurableSet_Icc,ae_restrict_of_ae hden] with r hr hd
    rw [hd hr]
    exact Q.data.hm (Q.alpha.val.property.1 c.left) (Q.alpha.val.property.1 r)
      (Q.alpha.val.property.2 hr.1)
  have HH:=intervalIntegral.integral_mono_ae_restrict c.hlt.le intervalIntegrable_const
    hac.intervalIntegrable_deriv hbound
  simpa only [intervalIntegral.integral_const,smul_eq_mul,hac.integral_deriv_eq_sub,
    mul_comm (c.right-c.left)] using HH

theorem unit_trace_eventually_strict
    (hN : 1≤ Q.data.N) (hlog : 1≤ Real.log Q.data.N) (hnd : 1/Q.data.N≤ Q.data.d)
    (dphys : ℕ) (e : Fin (dphys+1)≃FeatureIndex (n+1))
    (hl : Q.data.rmin< c.left) (hleft : P.H c.left=0) (hright : P.H c.right=0 ∨ c.right=1)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hend : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hmesh0 : ∀j,0≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0)) {epsilon : ℝ} (hepsilon : 0< epsilon) :
    let m:=Q.shiftedNativeModel
    let F:=(n+1:ℝ)*(((1/3)/Real.log Q.data.N)*laplaceComparisonStrength Q.data.d Q.lam c.right)
    ∀ᶠj : ℕ in atTop,
      (∫r in Ioo c.left c.right,deriv Q.alpha.val.val r∂m.radiusMeasure dphys e (as j) (ho j))≤
        (Q.data.M (Q.alpha.val.val c.right)/Q.data.M (Q.alpha.val.val c.left))*
          ((9*Real.log Q.data.N)/F)*(Q.alpha.val.val c.right-Q.alpha.val.val c.left)+epsilon := by
  dsimp only
  let m:=Q.shiftedNativeModel
  let F:=(n+1:ℝ)*(((1/3)/Real.log Q.data.N)*laplaceComparisonStrength Q.data.d Q.lam c.right)
  let Mz:=Q.data.M (Q.alpha.val.val c.right)
  let Ma:=Q.data.M (Q.alpha.val.val c.left)
  let Cnode:=2*ClockTree.errorJetVariation 2 0 0*
    clockVariationBound (physicalFeatureCoordinateBound n) m.q
  have hF : 0< F:=mul_pos (by positivity) (mul_pos
    (div_pos (by norm_num) (by linarith))
    (laplaceComparisonStrength_pos Q.data.d Q.hlam c.right))
  have hMa : 0< Ma:=(comparisonCap_first_term (δ:=delta) Q.data.hN Q.data.hU Q.data.hL
    Q.data.hE Q.data.hd.le (Q.alpha.val.property.1 c.left).1).1
  have hMz : 0≤ Mz:=hMa.le.trans (Q.data.hm (Q.alpha.val.property.1 c.left)
    (Q.alpha.val.property.1 c.right) (Q.alpha.val.property.2 c.hlt.le))
  have hCn : 0≤ Cnode:=mul_nonneg (mul_nonneg (by norm_num) (ClockTree.errorJetVariation_nonneg _ _ _))
    (clockVariationBound_nonneg _ _ (completedPathClock_monotone _ m.hbf m.hhf))
  have hder : ∀ᵐr,r∈Ioo c.left c.right→deriv Q.alpha.val.val r≤ Mz:=by
    filter_upwards [P.cap_density_on_interval Q c.hleft c.hright c.negative] with r hdr hr
    rw [hdr (Ioo_subset_Icc_self hr)]
    exact Q.data.hm (Q.alpha.val.property.1 r) (Q.alpha.val.property.1 c.right)
      (Q.alpha.val.property.2 hr.2.le)
  have hSi:=c.endpoint_radiusS_increment_strict hN hlog hnd dphys e hl hleft hright
  have hlength : c.right-c.left≤(Q.alpha.val.val c.right-Q.alpha.val.val c.left)/Ma:=
    (le_div_iff₀ hMa).mpr (by simpa only [mul_comm] using c.mass_lower_strict)
  have hnormal : Mz*(9*Real.log Q.data.N*(c.right-c.left)/F)≤
      (Mz/Ma)*((9*Real.log Q.data.N)/F)*(Q.alpha.val.val c.right-Q.alpha.val.val c.left):=by
    have H:=mul_le_mul_of_nonneg_left hlength
      (mul_nonneg hMz (div_nonneg (show 0≤9*Real.log Q.data.N from by linarith) hF.le))
    convert H using 1 <;> ring
  have hErr : Tendsto (fun j=>Mz*(2*(mesh j*Cnode)/F+2*(mesh j/m.c))) atTop (𝓝 0):=by
    simpa only [zero_mul,mul_zero,zero_div,zero_add] using
      ((((hlim.mul_const Cnode).const_mul 2).div_const F).add ((hlim.div_const m.c).const_mul 2)).const_mul Mz
  filter_upwards [(tendsto_order.mp hErr).2 epsilon hepsilon] with j hj
  let mu:=m.radiusMeasure dphys e (as j) (ho j)
  have hmuDom : mu≤ volume:=m.radiusMeasure_le_volume dphys e (as j) (ho j)
  have HB:=cap_bounded_density_trace_le mu hmuDom Q.alpha.val.val (fun _=>1)
    Q.alpha.val.property.2 measurable_const (Ioo c.left c.right) measurableSet_Ioo hMz
    (show (0:ℝ)≤1 by norm_num) hder (fun _ _=>by norm_num)
  simp only [mul_one] at HB
  have HI:=Q.radiusMeasure_interval_le_fixedStrength hN hlog hnd dphys e (as j) (ho j) (hend j)
    (hmesh j) (hmesh0 j) hl c.hlt.le le_rfl c.hright
  have he0 : 0≤2*(mesh j*Cnode)/F+2*(mesh j/m.c):=
    add_nonneg (div_nonneg (mul_nonneg (by norm_num) (mul_nonneg (hmesh0 j) hCn)) hF.le)
      (mul_nonneg (by norm_num) (div_nonneg (hmesh0 j) m.hc.le))
  have hinc0 : 0≤ Q.radiusS c.right-Q.radiusS c.left:=sub_nonneg.mpr
    (Q.radius_moments.1 ⟨c.hleft,c.hlt.le.trans c.hright⟩
      ⟨c.hleft.trans c.hlt.le,c.hright⟩ c.hlt.le)
  have Hreal : mu.real (Ioo c.left c.right)≤
      (Q.radiusS c.right-Q.radiusS c.left)/F+(2*(mesh j*Cnode)/F+2*(mesh j/m.c)):=by
    change mu (Ioo c.left c.right)≤ENNReal.ofReal ((Q.radiusS c.right-Q.radiusS c.left)/F)+
      ENNReal.ofReal (2*(mesh j*Cnode)/F+2*(mesh j/m.c)) at HI
    have HH:=ENNReal.toReal_mono (by finiteness) HI
    rw [ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (div_nonneg hinc0 hF.le),ENNReal.toReal_ofReal he0] at HH
    exact HH
  have HM:=mul_le_mul_of_nonneg_left Hreal hMz
  have HS:=mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hSi hF.le) hMz
  change (∫r in Ioo c.left c.right,deriv Q.alpha.val.val r∂mu)≤_
  dsimp only [Mz,Ma,F,Cnode] at hnormal HM HS hj HB ⊢
  nlinarith

end ActualThetaZeroOverlapMinimum.ShiftedCapInterval
end OAI.SKFluctuations.LaplaceWindowFormalization
