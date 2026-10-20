module

public import ComparisonActualHighWallThetaZeroCapUnitTracePositiveOrigin
public import ComparisonActualHighWallThetaZeroBroadTracePositiveOrigin

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 16000000
namespace ActualThetaZeroOverlapMinimum.ShiftedCapInterval
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable {Q : ActualThetaZeroOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}
    {P : Q.Potential} (c : ShiftedCapInterval Q P)

theorem unit_trace_eventually_with_origin
    (hN : 1≤Q.data.N) (hlog : 1≤Real.log Q.data.N) (hnd : 1/Q.data.N≤Q.data.d)
    (dphys : ℕ) (e : Fin (dphys+1)≃FeatureIndex (n+1))
    (hboundary : (P.H c.left=0 ∨ c.left=Q.data.rmin) ∧ (P.H c.right=0 ∨ c.right=1))
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hend : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hmesh0 : ∀j,0≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0)) {epsilon : ℝ} (hepsilon : 0<epsilon) :
    let m:=Q.shiftedNativeModel
    let F:=(n+1:ℝ)*(((1/3)/Real.log Q.data.N)*laplaceComparisonStrength Q.data.d Q.lam c.right)
    let Mz:=Q.data.M (Q.alpha.val.val c.right)
    let Ma:=Q.data.M (Q.alpha.val.val c.left)
    ∀ᶠj in atTop,
      (∫r in Ioo c.left c.right,deriv Q.alpha.val.val r∂m.radiusMeasure dphys e (as j) (ho j))≤
      (Mz/Ma)*((9*Real.log Q.data.N)/F)*
        (Q.alpha.val.val c.right-Q.alpha.val.val c.left)+
      ((9*Real.log Q.data.N)/F)*Mz*Q.data.rmin+epsilon := by
  dsimp only
  let m:=Q.shiftedNativeModel
  let F:=(n+1:ℝ)*(((1/3)/Real.log Q.data.N)*laplaceComparisonStrength Q.data.d Q.lam c.right)
  let Mz:=Q.data.M (Q.alpha.val.val c.right)
  let Ma:=Q.data.M (Q.alpha.val.val c.left)
  have hF : 0<F:=mul_pos (by positivity) (mul_pos
    (div_pos (by norm_num) (by linarith)) (laplaceComparisonStrength_pos Q.data.d Q.hlam c.right))
  have hMa : 0<Ma:=(comparisonCap_first_term (δ:=delta) Q.data.hN Q.data.hU Q.data.hL
    Q.data.hE Q.data.hd.le (Q.alpha.val.property.1 c.left).1).1
  have hMz : 0≤Mz:=hMa.le.trans (Q.data.hm (Q.alpha.val.property.1 c.left)
    (Q.alpha.val.property.1 c.right) (Q.alpha.val.property.2 c.hlt.le))
  have hder : ∀ᵐr,r∈Ioo c.left c.right→deriv Q.alpha.val.val r≤Mz:=by
    filter_upwards [P.cap_density_on_interval Q c.hleft c.hright c.negative] with r hdr hr
    rw [hdr (Ioo_subset_Icc_self hr)]
    exact Q.data.hm (Q.alpha.val.property.1 r) (Q.alpha.val.property.1 c.right)
      (Q.alpha.val.property.2 hr.2.le)
  have hlength : c.right-c.left≤(Q.alpha.val.val c.right-Q.alpha.val.val c.left)/Ma:=
    (le_div_iff₀ hMa).mpr (by simpa only [mul_comm] using c.mass_lower_strict)
  have hnormal : Mz*(9*Real.log Q.data.N*(c.right-c.left)/F)≤
      (Mz/Ma)*((9*Real.log Q.data.N)/F)*
        (Q.alpha.val.val c.right-Q.alpha.val.val c.left):=by
    have H:=mul_le_mul_of_nonneg_left hlength
      (mul_nonneg hMz (div_nonneg (show 0≤9*Real.log Q.data.N from by linarith) hF.le))
    convert H using 1 <;> ring
  have herr : 0<epsilon/(Mz+1):=div_pos hepsilon (by linarith)
  have hmeas:=c.localized_measure_eventually_positive_origin hN hlog hnd dphys e
    c.hleft c.hright (by simpa only [max_self,min_self] using c.hlt) hboundary
    (Ioo c.left c.right) (Subset.refl _) (Subset.refl _)
    as mesh ho hend hmesh hmesh0 hlim herr
  filter_upwards [hmeas] with j hj
  let μ:=m.radiusMeasure dphys e (as j) (ho j)
  have hdom : μ≤volume:=m.radiusMeasure_le_volume dphys e (as j) (ho j)
  have htrace:=cap_bounded_density_trace_le μ hdom Q.alpha.val.val (fun _=>1)
    Q.alpha.val.property.2 measurable_const (Ioo c.left c.right) measurableSet_Ioo hMz
    (show (0:ℝ)≤1 by norm_num) hder (fun _ _=>by norm_num)
  simp only [mul_one] at htrace
  have hμ:=mul_le_mul_of_nonneg_left hj hMz
  have heps : Mz*(epsilon/(Mz+1))≤epsilon:=by
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (by linarith : 0<Mz+1)).mpr
    nlinarith
  have hsplit : Mz*(9*Real.log Q.data.N*(c.right-c.left+Q.data.rmin)/F)=
      Mz*(9*Real.log Q.data.N*(c.right-c.left)/F)+
      ((9*Real.log Q.data.N)/F)*Mz*Q.data.rmin:=by ring
  rw [mul_add,hsplit] at hμ
  dsimp only [F,Mz,Ma] at hj hnormal hμ htrace ⊢
  nlinarith only [htrace,hμ,hnormal,heps]

end ActualThetaZeroOverlapMinimum.ShiftedCapInterval
end OAI.SKFluctuations.LaplaceWindowFormalization
