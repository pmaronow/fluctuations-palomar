module

public import ComparisonActualHighWallThetaZeroFixedTracePositiveOrigin
public import ComparisonShiftedNativePositiveOriginFixedWeights

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 12000000
attribute [local instance] Classical.propDecidable
namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}

structure PositiveOriginFixedCapWeights
    (W : ActualThetaZeroOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock)
    (P : W.Potential) where
  ag : ℝ
  zg : ℝ
  lo : ℝ
  hi : ℝ
  K : ℝ
  hag : W.data.rmin≤ ag
  hagz : ag≤ zg
  hzg : zg≤1
  hlo : 0≤ lo
  hK : 1≤ K
  hband : hi+comparisonSmallMass W.data.N W.data.E≤ K*(lo+comparisonSmallMass W.data.N W.data.E)
  count : ℕ
  caps : Fin count→ShiftedCapInterval W P
  hga : ∀i,ag≤(caps i).left
  hgz : ∀i,(caps i).right≤ zg
  haH : ∀i,P.H (caps i).left=0 ∨ (caps i).left=W.data.rmin
  hinitialU : ∀i,(caps i).left=W.data.rmin → comparisonSmallMass W.data.N W.data.E≤
    W.alpha.val.val (caps i).right-W.alpha.val.val (caps i).left
  hzH : ∀i,P.H (caps i).right=0 ∨ (caps i).right=1
  hamass : ∀i,lo≤ W.alpha.val.val (caps i).left
  hzmass : ∀i,W.alpha.val.val (caps i).right≤ hi
  weight : Fin count→ℝ
  hweight : ∀i,0≤ weight i
  contact : ℝ→ℝ
  hmeas : Measurable contact
  W : ℝ
  hW : 0≤ W
  hbound : ∀r,‖contact r‖≤ W
  hnonneg : ∀r,0≤ contact r

namespace PositiveOriginFixedCapWeights
variable {W : ActualThetaZeroOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}
    {P : W.Potential} (f : PositiveOriginFixedCapWeights W P)

abbrev domain:=Ioo f.ag f.zg
abbrev contactSet:=f.domain∩P.contactSet
abbrev fixed:=fixedCapContactWeight (fun i=>(f.caps i).left) (fun i=>(f.caps i).right)
  f.weight f.contactSet f.contact
def mass : ℝ:=∫r,deriv W.alpha.val.val r*f.fixed r
def coefficient : ℝ:=27*(Real.log W.data.N)^2/((n+1:ℝ)*laplaceComparisonStrength W.data.d W.lam f.zg)

theorem contactSet_measurable : MeasurableSet f.contactSet:=
  measurableSet_Ioo.inter P.contactSet_measurable

theorem fixed_measurable : Measurable f.fixed:=
  fixedCapContactWeight_measurable _ _ _ _ f.contactSet_measurable _ f.hmeas

theorem fixed_nonneg (r : ℝ) : 0≤ f.fixed r:=
  fixedCapContactWeight_nonneg _ _ _ f.hweight _ _ f.hnonneg r

theorem fixed_bound (r : ℝ) : ‖f.fixed r‖≤(∑i,f.weight i)+f.W:=
  fixedCapContactWeight_bound _ _ _ f.hweight _ _ f.hnonneg f.hW f.hbound r

theorem fixed_zero_outside {r : ℝ} (hr : r∉f.domain) : f.fixed r=0:=by
  have hcap i : r∉Ioo (f.caps i).left (f.caps i).right:=fun hc=>hr
    ⟨(f.hga i).trans_lt hc.1,hc.2.trans_le (f.hgz i)⟩
  have hcontact : r∉f.contactSet:=fun hc=>hr hc.1
  dsimp only [fixed,fixedCapContactWeight]
  rw [indicator_of_notMem hcontact,add_zero]
  exact Finset.sum_eq_zero (fun i _=>indicator_of_notMem (hcap i) _)

theorem fixed_integral_domain (mu : Measure ℝ) :
    (∫r in f.domain,deriv W.alpha.val.val r*f.fixed r∂mu)=
      ∫r,deriv W.alpha.val.val r*f.fixed r∂mu:=
  setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun r hr=>by rw [f.fixed_zero_outside hr,mul_zero])

theorem integral_decomp (mu : Measure ℝ) (hmu : mu≤ volume) :
    (∫r,deriv W.alpha.val.val r*f.fixed r∂mu)=
      (∑i,f.weight i*(∫r in Ioo (f.caps i).left (f.caps i).right,deriv W.alpha.val.val r∂mu))+
      (∫r in f.contactSet,deriv W.alpha.val.val r*f.contact r∂mu):=
  (W.shiftedNativeModel.fixedCapContactWeight_integral_positive_origin f.hag f.hzg _ _ _ f.hga f.hgz
    f.contactSet f.contactSet_measurable inter_subset_left f.contact f.hmeas f.hbound mu hmu).2

theorem mass_decomp : f.mass=
    (∑i,f.weight i*(W.alpha.val.val (f.caps i).right-W.alpha.val.val (f.caps i).left))+
      (∫r in f.contactSet,deriv W.alpha.val.val r*f.contact r):=by
  rw [mass,f.integral_decomp volume le_rfl]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  have hsub : Icc (f.caps i).left (f.caps i).right⊆Icc W.data.rmin 1:=
    Icc_subset_Icc (f.caps i).hleft (f.caps i).hright
  have hac : AbsolutelyContinuousOnInterval W.alpha.val.val (f.caps i).left (f.caps i).right:=by
    apply LipschitzOnWith.absolutelyContinuousOnInterval
    simpa only [uIcc_of_le (f.caps i).hlt.le] using
      (inverseIntegralConstraints_lipschitz W.data.hm W.data.hM W.alpha.property).mono hsub
  rw [←integral_Ioc_eq_integral_Ioo,←intervalIntegral.integral_of_le (f.caps i).hlt.le]
  exact hac.integral_deriv_eq_sub

theorem coefficient_nonneg : 0≤ f.coefficient:=div_nonneg
  (mul_nonneg (by norm_num) (sq_nonneg _))
  (mul_nonneg (by positivity) (laplaceComparisonStrength_pos W.data.d W.hlam _).le)

theorem trace_eventually
    (hN : 1≤ W.data.N) (hlog : 1≤ Real.log W.data.N) (hnd : 1/W.data.N≤ W.data.d)
    (dphys : ℕ) (e : Fin (dphys+1)≃FeatureIndex (n+1))
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hend : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hmesh0 : ∀j,0≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0)) {epsilon : ℝ} (hepsilon : 0< epsilon) :
    ∀ᶠj : ℕ in atTop,
      (∫r,deriv W.alpha.val.val r*f.fixed r∂W.shiftedNativeModel.radiusMeasure dphys e (as j) (ho j))≤
        2*f.coefficient*f.K^2*f.mass+epsilon:=by
  have ht:=P.cap_contact_weight_trace_eventually_positive_origin hN hlog hnd dphys e f.caps f.hag f.hagz f.hzg
    f.hlo f.hK f.hband f.hga f.hgz f.haH f.hzH f.hinitialU f.hamass f.hzmass f.weight f.hweight
    as mesh ho hend hmesh hmesh0 hlim f.contact f.hmeas f.hbound f.hnonneg hepsilon
  have hcontact0 : 0≤∫r in f.contactSet,deriv W.alpha.val.val r*f.contact r:=
    integral_nonneg (fun r=>mul_nonneg W.alpha.val.property.2.deriv_nonneg (f.hnonneg r))
  have hKsq : 1≤ 2*f.K^2:=by nlinarith [f.hK]
  filter_upwards [ht] with j hj
  rw [f.integral_decomp _ (W.shiftedNativeModel.radiusMeasure_le_volume dphys e (as j) (ho j))]
  have HH:=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hKsq hcontact0) f.coefficient_nonneg
  rw [f.mass_decomp]
  dsimp only [coefficient] at HH ⊢
  nlinarith

theorem moving_trace_eventually
    (hN : 1≤ W.data.N) (hlog : 1≤ Real.log W.data.N) (hnd : 1/W.data.N≤ W.data.d)
    (dphys : ℕ) (e : Fin (dphys+1)≃FeatureIndex (n+1))
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hend : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hmesh0 : ∀j,0≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0))
    (moving : ℕ→ℝ→ℝ) (hmeas : ∀j,Measurable (moving j)) {B : ℝ}
    (hfixedB : ∀r,‖f.fixed r‖≤ B) (hmoveB : ∀j r,‖moving j r‖≤ B)
    (hsupport : ∀j,∀ᵐr,r∉f.domain→moving j r=0)
    (hcolumns : Tendsto (fun j=>∫r in f.domain,|moving j r-f.fixed r|) atTop (𝓝 0))
    {epsilon : ℝ} (hepsilon : 0< epsilon) :
    ∀ᶠj : ℕ in atTop,
      (∫r,deriv W.alpha.val.val r*moving j r∂W.shiftedNativeModel.radiusMeasure dphys e (as j) (ho j))≤
        2*f.coefficient*f.K^2*f.mass+epsilon:=by
  let m:=W.shiftedNativeModel
  have herror:=m.inverse_weight_L1_tendsto_positive_origin f.hag f.hzg f.fixed f.fixed_measurable moving hmeas
    hfixedB hmoveB hcolumns
  have hfixedI:=m.radiusWeight_integrableOn_positive_origin f.hag f.hzg f.domain measurableSet_Ioo
    (Subset.refl _) f.fixed f.fixed_measurable hfixedB
  have hmoveI j:=m.radiusWeight_integrableOn_positive_origin f.hag f.hzg f.domain measurableSet_Ioo
    (Subset.refl _) (moving j) (hmeas j) (hmoveB j)
  have hfixed:=f.trace_eventually hN hlog hnd dphys e as mesh ho hend hmesh hmesh0 hlim
    (show 0< epsilon/2 by positivity)
  filter_upwards [hfixed,(tendsto_order.mp herror).2 (epsilon/2) (by positivity)] with j hj he
  let mu:=m.radiusMeasure dphys e (as j) (ho j)
  have hdom : mu≤ volume:=m.radiusMeasure_le_volume dphys e (as j) (ho j)
  have hmoveGlobal : (∫r in f.domain,deriv W.alpha.val.val r*moving j r∂mu)=
      ∫r,deriv W.alpha.val.val r*moving j r∂mu:=by
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    filter_upwards [ae_mono hdom (hsupport j)] with r hr hrd
    rw [hr hrd,mul_zero]
  have H:=dominated_setIntegral_difference_le f.domain f.domain (Subset.refl _) mu hdom
    (fun r=>deriv W.alpha.val.val r*f.fixed r) (fun r=>deriv W.alpha.val.val r*moving j r)
    hfixedI (hmoveI j)
  rw [f.fixed_integral_domain mu,hmoveGlobal] at H
  nlinarith [le_abs_self ((∫r,deriv W.alpha.val.val r*moving j r∂mu)-
    (∫r,deriv W.alpha.val.val r*f.fixed r∂mu))]

theorem moving_mass_tendsto
    (moving : ℕ→ℝ→ℝ) (hmeas : ∀j,Measurable (moving j)) {B : ℝ}
    (hfixedB : ∀r,‖f.fixed r‖≤B) (hmoveB : ∀j r,‖moving j r‖≤B)
    (hsupport : ∀j,∀ᵐr,r∉f.domain→moving j r=0)
    (hcolumns : Tendsto (fun j=>∫r in f.domain,|moving j r-f.fixed r|) atTop (𝓝 0)) :
    Tendsto (fun j=>∫r,deriv W.alpha.val.val r*moving j r) atTop (𝓝 f.mass):=by
  let m:=W.shiftedNativeModel
  have herror:=m.inverse_weight_L1_tendsto_positive_origin f.hag f.hzg f.fixed f.fixed_measurable moving hmeas
    hfixedB hmoveB hcolumns
  have hfixedI:=m.radiusWeight_integrableOn_positive_origin f.hag f.hzg f.domain measurableSet_Ioo
    (Subset.refl _) f.fixed f.fixed_measurable hfixedB
  have hmoveI j:=m.radiusWeight_integrableOn_positive_origin f.hag f.hzg f.domain measurableSet_Ioo
    (Subset.refl _) (moving j) (hmeas j) (hmoveB j)
  have hmoveGlobal j : (∫r in f.domain,deriv W.alpha.val.val r*moving j r)=
      ∫r,deriv W.alpha.val.val r*moving j r:=by
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    filter_upwards [hsupport j] with r hr hrd
    rw [hr hrd,mul_zero]
  apply (tendsto_iff_dist_tendsto_zero).mpr
  change Tendsto (fun j=>|(∫r,deriv W.alpha.val.val r*moving j r)-f.mass|) atTop (𝓝 0)
  apply squeeze_zero (fun j=>abs_nonneg _) _ herror
  intro j
  have H:=dominated_setIntegral_difference_le f.domain f.domain (Subset.refl _) volume le_rfl
    (fun r=>deriv W.alpha.val.val r*f.fixed r) (fun r=>deriv W.alpha.val.val r*moving j r)
    hfixedI (hmoveI j)
  have Hback:=dominated_setIntegral_difference_le f.domain f.domain (Subset.refl _) volume le_rfl
    (fun r=>deriv W.alpha.val.val r*moving j r) (fun r=>deriv W.alpha.val.val r*f.fixed r)
    (hmoveI j) hfixedI
  rw [f.fixed_integral_domain volume,hmoveGlobal j] at H Hback
  simp only [abs_sub_comm] at Hback
  apply abs_le.mpr
  constructor <;> dsimp only [mass] <;> linarith

end PositiveOriginFixedCapWeights
end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
