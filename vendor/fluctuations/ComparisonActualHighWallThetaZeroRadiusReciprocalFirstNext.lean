module

public import ComparisonActualHighWallThetaZeroTraceLimitPositiveOrigin
public import ComparisonNativeRadiusTraceVariance

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 24000000
set_option linter.unnecessarySeqFocus false
attribute [local instance] Classical.propDecidable
namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable (a : ActualThetaZeroOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock)

theorem reciprocal_radius_trace_eventually_first
    (hN : 1  ≤  a.data.N) (hlog : 1  ≤  Real.log a.data.N) (hnd : 1/a.data.N  ≤  a.data.d)
    (dphys : ℕ) (e : Fin (dphys+1)≃FeatureIndex (n+1))
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hend : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hmesh0 : ∀j,0  ≤  mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0))
    {lo z x kmin : ℝ} (hlo : a.data.rmin < lo) (hloz : lo  ≤  z) (hz : z  ≤  1)
    (hx : 0 < x) (hkmin : 0 < kmin) {A : Set ℝ} (hA : MeasurableSet A) (hAD : A⊆Ioo lo z)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    let m:=a.shiftedNativeModel
    let F:=(n+1:ℝ)*(((1/3)/Real.log a.data.N)*laplaceComparisonStrength a.data.d a.lam z)
    ∀ᶠj : ℕ in atTop,
      (∫r in A,comparisonReciprocalDensityWeight a.alpha.val.val x kmin r
        ∂m.radiusMeasure dphys e (as j) (ho j))  ≤ 
          (a.radiusS z-a.radiusS lo)/(x^2*kmin*F)+epsilon := by
  dsimp only
  let F:=(n+1:ℝ)*(((1/3)/Real.log a.data.N)*laplaceComparisonStrength a.data.d a.lam z)
  let weight:=comparisonReciprocalDensityWeight a.alpha.val.val x kmin
  have hF : 0 < F:=mul_pos (by positivity) (mul_pos
    (div_pos (by norm_num) (by linarith))
    (laplaceComparisonStrength_pos a.data.d (a.hlam) z))
  have hSm : MonotoneOn a.radiusS (Icc lo z):=
    a.radius_moments.1.mono (Icc_subset_Icc hlo.le hz)
  have hAC:=a.radiusS_absolutelyContinuous_positive_origin dphys e hlo.le hloz hz
  have hw r:=comparisonReciprocalDensityWeight_bounds a.alpha.val.val hx hkmin r
  have hwm : AEStronglyMeasurable weight volume:=
    (comparisonReciprocalDensityWeight_measurable a.alpha.val.val x kmin).aestronglyMeasurable
  have HFTC:=reciprocal_density_derivative_budget hloz hSm hAC hA
    (hAD.trans Ioo_subset_Icc_self) hwm (by positivity : 0  ≤  1/(x^2*kmin))
    (fun r _=>by simpa only [weight,Real.norm_eq_abs,abs_of_nonneg (hw r).1] using (hw r).2)
    (fun r _=>(hw r).1)
  have Htrace:=a.radius_trace_boundedWeight_positive_origin hN hlog hnd dphys e as ho hend mesh hmesh hmesh0
    hlim hlo.le hloz hz hA hAD weight hwm (1/(x^2*kmin))
    (fun r _=>by simpa only [weight,Real.norm_eq_abs,abs_of_nonneg (hw r).1] using (hw r).2)
    (fun r _=>(hw r).1) hepsilon
  filter_upwards [Htrace] with j hj
  apply hj.trans
  have HB:=div_le_div_of_nonneg_right HFTC hF.le
  have HB' : (∫r in A,weight r*deriv a.radiusS r)/F  ≤ 
      (a.radiusS z-a.radiusS lo)/(x^2*kmin*F):=by
    have hden : x^2*kmin ≠ 0 := ne_of_gt (mul_pos (sq_pos_of_pos hx) hkmin)
    have hscalar (D : ℝ) : ((1/(x^2*kmin))*D)/F = D/(x^2*kmin*F) := by
      field_simp [hden, hF.ne']
    exact HB.trans_eq (hscalar (a.radiusS z-a.radiusS lo))
  exact add_le_add HB' le_rfl

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
