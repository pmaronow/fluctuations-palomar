module

public import ComparisonActualHighWallThetaZeroBroadTracePositiveOrigin
public import ComparisonActualHighWallThetaZeroBroadBudgets
public import ComparisonActualHighWallCriticalBroadPhysicalTrace

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 26000000
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
namespace ActualThetaZeroOverlapMinimum.ShiftedCapInterval
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable {Q : ActualThetaZeroOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}
    {P : Q.Potential} (cap : ShiftedCapInterval Q P)

theorem broad_unit_trace_eventually_positive_origin
    (hN : 1≤Q.data.N) (hlog : 1≤Real.log Q.data.N) (hnd : 1/Q.data.N≤Q.data.d)
    (dphys : ℕ) (e : Fin (dphys+1)≃FeatureIndex (n+1))
    {ag zg v V K : ℝ} (hag : Q.data.rmin≤ag) (hzg : zg≤1)
    (hoverlap : max cap.left ag < min cap.right zg)
    (hboundary : (P.H cap.left=0 ∨ cap.left=Q.data.rmin) ∧ (P.H cap.right=0 ∨ cap.right=1))
    (hK : 1≤K) (hUv : (comparisonSmallMass Q.data.N Q.data.E)≤v) (hV : V∈Icc (0:ℝ) 1) (hVv : V≤K*v)
    (hcal : Q.data.d^3*(comparisonConstraintLength Q.data.N Q.data.E Q.data.d)*(comparisonSmallMass Q.data.N Q.data.E)≤Q.data.E)
    (A : Set ℝ) (hA : MeasurableSet A) (hAcap : A⊆Ioo cap.left cap.right)
    (hAgroup : A⊆Ioo ag zg) (hAV : ∀r∈A,Q.alpha.val.val r≤V)
    (hslice : v≤∫r in A,deriv Q.alpha.val.val r)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hend : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hmesh0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0)) {ε : ℝ} (hε : 0<ε) :
    let C:=27*(Real.log Q.data.N)^2/((n+1:ℝ)*laplaceComparisonStrength Q.data.d Q.lam zg)
    ∀ᶠj in atTop,(∫r in A,deriv Q.alpha.val.val r
      ∂Q.shiftedNativeModel.radiusMeasure dphys e (as j) (ho j))≤
      C*Q.criticalBroadTraceLoss K v V*
        (∫r in A,deriv Q.alpha.val.val r)+ε := by
  let N:=Q.data.N
  let d:=Q.data.d
  let lam:=Q.lam
  let U:=(comparisonSmallMass Q.data.N Q.data.E)
  let L:=(comparisonConstraintLength Q.data.N Q.data.E Q.data.d)
  let E:=Q.data.E
  let δcap:=delta
  let M:=Q.data.M
  let α:=Q.alpha
  let hm:=Q.data.hm
  have hMdef : M=comparisonCap N δcap U L E d:=rfl
  have hU:=Q.data.hU
  have hL:=Q.data.hL
  have hE:=Q.data.hE
  have hd:=Q.data.hd
  have hlam:=Q.hlam
  let left:=cap.left
  let z:=cap.right
  have ha : Q.data.rmin≤left:=cap.hleft
  have haz : left<z:=cap.hlt
  have hz : z≤1:=cap.hright
  have hneg:=cap.negative

  dsimp only
  let F := (n+1:ℝ)*(((1/3)/Real.log N)*laplaceComparisonStrength d lam zg)
  let C := 27*(Real.log N)^2/((n+1:ℝ)*laplaceComparisonStrength d lam zg)
  let T := Real.log ((1+U)/U)
  let Qfac := (K+1)^2*(1+v/U)
  have hNp : 0<N := by linarith
  have hv : 0<v := hU.trans_le hUv
  have hlogpos : 0<Real.log N := by linarith
  have hgpos := laplaceComparisonStrength_pos d hlam zg
  have hF : 0<F := mul_pos (by positivity)
    (mul_pos (div_pos (by norm_num) hlogpos) hgpos)
  have hC : 0≤C := by dsimp [C]; positivity
  have hT : 0≤T := by
    apply Real.log_nonneg
    apply (le_div_iff₀ hU).mpr
    linarith
  have hQfac : 0≤Qfac := by dsimp [Qfac]; positivity
  have hMV : 0≤M V := by
    rw [congrFun hMdef V]
    exact (comparisonCap_first_term (δ:=δcap) hNp hU hL hE hd.le hV.1).1.le
  have htravel:=P.cap_interval_travel Q cap.hleft cap.hlt.le cap.hright cap.negative
  have hlength : z-left≤(L/N^δcap)*T := htravel.2.1
  have hprofile : M V*(L/N^δcap)≤Qfac*v := by
    have ht := comparisonCap_broad_length_multiplier_le (δ:=δcap)
      hNp hU hL hE hd.le hV.1 hK hUv hVv hcal
    have ht' := (div_le_iff₀ hv).mp
      (show (comparisonCap N δcap U L E d V*(L/N^δcap))/v≤Qfac by
        convert ht using 1 <;> ring)
    simpa only [congrFun hMdef V] using ht'
  have hnormal0 : M V*C*(z-left)≤C*Qfac*T*(∫r in A,deriv α.val.val r) := by
    have h1 := mul_le_mul_of_nonneg_left hlength (mul_nonneg hMV hC)
    have h2 := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hprofile hT) hC
    have h3 := mul_le_mul_of_nonneg_left hslice (mul_nonneg (mul_nonneg hC hQfac) hT)
    nlinarith
  have hnormal : M V*C*(z-left+Q.data.rmin)≤C*Q.criticalBroadTraceLoss K v V*(∫r in A,deriv α.val.val r) := by
    have horigin := mul_le_mul_of_nonneg_left hslice (div_nonneg (mul_nonneg hMV Q.data.hrbounds.1.le) hv.le)
    rw [div_mul_cancel₀ _ hv.ne'] at horigin
    have H := mul_le_mul_of_nonneg_left horigin hC
    dsimp only [criticalBroadTraceLoss,M,U,Qfac,T] at H hnormal0 ⊢
    nlinarith only [H,hnormal0]
  have hcommon : (9*Real.log N)/F=C := by
    dsimp [F,C]
    field_simp [hlogpos.ne',hgpos.ne']
    <;> ring
  have hden : ∀ᵐ r,r∈A→deriv α.val.val r≤M V := by
    filter_upwards [P.hbang] with r hr hrA
    have hrc := hAcap hrA
    rw [hr ⟨ha.trans hrc.1.le,hrc.2.le.trans hz⟩ (hneg r hrc)]
    exact hm (α.val.property.1 r) hV (hAV r hrA)
  have hsmall : 0<ε/(M V+1) := div_pos hε (by linarith)
  have ht:=cap.localized_measure_eventually_positive_origin hN hlog hnd dphys e hag hzg hoverlap hboundary
    A hAcap hAgroup as mesh ho hend hmesh hmesh0 hlim hsmall
  filter_upwards [ht] with j hj
  let μ := Q.shiftedNativeModel.radiusMeasure dphys e (as j) (ho j)
  have hdom : μ≤volume:=Q.shiftedNativeModel.radiusMeasure_le_volume dphys e (as j) (ho j)
  have hdens := cap_bounded_density_trace_le μ hdom α.val.val (fun _=>1)
    α.val.property.2 measurable_const A hA hMV (show (0:ℝ)≤1 by norm_num) hden
    (fun _ _=>by norm_num)
  simp only [mul_one] at hdens
  have hμ := mul_le_mul_of_nonneg_left hj hMV
  have hcommon' : (9*Real.log N)*(z-left+Q.data.rmin)/F=C*(z-left+Q.data.rmin) := by
    calc (9*Real.log N)*(z-left+Q.data.rmin)/F=((9*Real.log N)/F)*(z-left+Q.data.rmin) := by ring
         _=C*(z-left+Q.data.rmin) := by rw [hcommon]
  rw [hcommon'] at hμ
  have herr : M V*(ε/(M V+1))≤ε := by
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (by linarith : 0<M V+1)).mpr
    nlinarith
  dsimp only [C] at hnormal ⊢
  nlinarith

end ActualThetaZeroOverlapMinimum.ShiftedCapInterval
end OAI.SKFluctuations.LaplaceWindowFormalization
