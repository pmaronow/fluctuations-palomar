module

public import ComparisonActualHighWallThetaZeroBarePullback
public import ComparisonActualHighWallThetaZeroSelectedRadius
public import PhysicalOverlapPathRegularity

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 12000000

namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
  (Q : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)

theorem sweep_matrix_pullback {r : ℝ} (hr : r∈Icc Q.data.rmin 1) :
    Q.data.thetaZeroHighOnlyData.b (Q.alpha.val.val r)-
      Q.sweepCoefficient (Q.alpha.val.val r)=
      Q.data.T-laplaceComparisonStrength Q.data.d Q.lam r := by
  have hm : Q.data.s≤Q.alpha.val.val r :=
    (inverseConstraint_mass_mem Q.data.hr Q.data.hc Q.data.hk
      Q.data.hkc Q.alpha hr).1
  have hR:Q.sweepRadius (Q.alpha.val.val r)=r:=Q.shiftedNativeModel.R_inverse hr
  rw [Q.bare_matrix_pullback_constant hr]
  simp only [sweepCoefficient,omittedStrengthCoefficient,ite_eq_left hm] at ⊢
  rw [hR]

theorem sweep_field_pullback {r : ℝ} (hr : r∈Icc Q.data.rmin 1) :
    Q.data.thetaZeroHighOnlyData.h (Q.alpha.val.val r)+
      Q.sweepCoefficient (Q.alpha.val.val r)*Q.sweepRadius (Q.alpha.val.val r)=
      laplaceComparisonStrength Q.data.d Q.lam r*r := by
  have hm : Q.data.s≤Q.alpha.val.val r :=
    (inverseConstraint_mass_mem Q.data.hr Q.data.hc Q.data.hk
      Q.data.hkc Q.alpha hr).1
  have hR:Q.sweepRadius (Q.alpha.val.val r)=r:=Q.shiftedNativeModel.R_inverse hr
  rw [Q.bare_field_pullback_zero]
  simp only [sweepCoefficient,omittedStrengthCoefficient,ite_eq_left hm,zero_add] at ⊢
  rw [hR]

theorem radiusS_absolutelyContinuous
    (dphys : ℕ) (e : Fin (dphys+1)≃FeatureIndex (n+1))
    {lo z : ℝ} (hlo : Q.data.rmin<lo) (hloz : lo≤z) (hz : z≤1) :
    AbsolutelyContinuousOnInterval Q.radiusS lo z := by
  let g:=laplaceComparisonStrength Q.data.d Q.lam
  let bf:=Q.sweepBf
  let hf:=Q.sweepHf
  have hsub:Icc lo z⊆Icc Q.data.rmin 1:=Icc_subset_Icc hlo.le hz
  have hα:MapsTo Q.alpha.val.val (Icc lo z) (Ioc (0:ℝ) 1):=
    fun r hr=>Q.radius_mass_mem (hsub hr)
  obtain ⟨Kg,hgLip⟩:=(laplaceComparisonStrength_contDiff Q.data.d Q.lam).contDiffOn.exists_lipschitzOnWith
    (by norm_num) (convex_Icc Q.data.rmin 1) isCompact_Icc
  obtain ⟨Kf,hfLip⟩:=((laplaceComparisonStrength_contDiff Q.data.d Q.lam).mul contDiff_id).contDiffOn.exists_lipschitzOnWith
    (by norm_num) (convex_Icc Q.data.rmin 1) isCompact_Icc
  have hclock (j:FeatureIndex (n+1)) : LipschitzOnWith (Kg+Kf)
      (fun r=>(completedPathClock (n+1) bf hf (Q.alpha.val.val r) j:ℝ)) (Icc lo z) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hbx:=(Q.data.thetaZeroShiftedParentData Q.lam Q.hlam Q.hld).clockAdmissible Q.alpha
    cases j with
    | inl j=>
      change dist (hf (Q.alpha.val.val x):ℝ) (hf (Q.alpha.val.val y):ℝ)≤_
      dsimp only [hf,sweepHf]
      have hxNon : 0 ≤ Q.data.thetaZeroHighOnlyData.h (Q.alpha.val.val x)+
          Q.sweepCoefficient (Q.alpha.val.val x)*Q.sweepRadius (Q.alpha.val.val x) :=
        hbx.2.2.2 _ (Q.alpha.val.property.1 x)
      have hyNon : 0 ≤ Q.data.thetaZeroHighOnlyData.h (Q.alpha.val.val y)+
          Q.sweepCoefficient (Q.alpha.val.val y)*Q.sweepRadius (Q.alpha.val.val y) :=
        hbx.2.2.2 _ (Q.alpha.val.property.1 y)
      rw [Real.coe_toNNReal _ hxNon,Real.coe_toNNReal _ hyNon,
        Q.sweep_field_pullback (hsub hx),Q.sweep_field_pullback (hsub hy)]
      have HH:=hfLip.dist_le_mul x (hsub hx) y (hsub hy)
      change dist (g x*x) (g y*y)≤(Kf:ℝ)*dist x y at HH
      exact HH.trans (by simp only [NNReal.coe_add];nlinarith [Kg.coe_nonneg,dist_nonneg (x:=x) (y:=y)])
    | inr j=>
      change dist (bf (Q.alpha.val.val x):ℝ) (bf (Q.alpha.val.val y):ℝ)≤_
      dsimp only [bf,sweepBf]
      have hxNon : 0 ≤ Q.data.thetaZeroHighOnlyData.b (Q.alpha.val.val x)-
          Q.sweepCoefficient (Q.alpha.val.val x) :=
        hbx.2.2.1 _ (Q.alpha.val.property.1 x)
      have hyNon : 0 ≤ Q.data.thetaZeroHighOnlyData.b (Q.alpha.val.val y)-
          Q.sweepCoefficient (Q.alpha.val.val y) :=
        hbx.2.2.1 _ (Q.alpha.val.property.1 y)
      rw [Real.coe_toNNReal _ hxNon,Real.coe_toNNReal _ hyNon,
        Q.sweep_matrix_pullback (hsub hx),Q.sweep_matrix_pullback (hsub hy)]
      have HH:=hgLip.dist_le_mul x (hsub hx) y (hsub hy)
      have HE:dist (Q.data.T-g x) (Q.data.T-g y)=dist (g x) (g y):=by
        simp only [Real.dist_eq]
        rw [show Q.data.T-g x-(Q.data.T-g y)=-(g x-g y) by ring,abs_neg]
      rw [HE]
      exact HH.trans (by simp only [NNReal.coe_add];nlinarith [Kf.coe_nonneg,dist_nonneg (x:=x) (y:=y)])
  have HL:=physicalOrderedPathS_comp_lipschitzOn n dphys e bf hf
    Q.sweep_bf_monotone Q.sweep_hf_monotone Q.alpha.val.val _ (Kg+Kf) hα hclock
  rw [←uIcc_of_le hloz] at HL
  exact HL.absolutelyContinuousOnInterval

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
