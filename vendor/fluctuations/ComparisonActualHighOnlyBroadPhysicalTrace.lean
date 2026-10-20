module

public import ComparisonActualHighOnlyBroadSliceSampler
public import ComparisonActualHighOnlyCapTraceNormalized

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 24000000
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
namespace ActualHighOnlyOverlapMinimum.ShiftedCapInterval
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable {a : ActualHighOnlyOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}
    {P : a.Potential} (cap : ShiftedCapInterval a P)

theorem broad_unit_trace_eventually
    (hN : 1≤a.data.N) (hlog : 1≤Real.log a.data.N) (hnd : 1/a.data.N≤a.data.d)
    (dphys : ℕ) (e : Fin (dphys+1)≃FeatureIndex (n+1))
    {ag zg v V K : ℝ} (hag : 0<ag) (hzg : zg≤1)
    (hoverlap : max cap.left ag < min cap.right zg)
    (hboundary : (P.H cap.left=0 ∨ cap.left=0) ∧ (P.H cap.right=0 ∨ cap.right=1))
    (hK : 1≤K) (hUv : a.data.U≤v) (hV : V∈Icc (0:ℝ) 1) (hVv : V≤K*v)
    (hcal : a.data.d^3*a.data.L*a.data.U≤a.data.E)
    (A : Set ℝ) (hA : MeasurableSet A) (hAcap : A⊆Ioo cap.left cap.right)
    (hAgroup : A⊆Ioo ag zg) (hAV : ∀r∈A,a.alpha.val.val r≤V)
    (hslice : v≤∫r in A,deriv a.alpha.val.val r)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hend : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hmesh0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0)) {ε : ℝ} (hε : 0<ε) :
    let C:=27*(Real.log a.data.N)^2/((n+1:ℝ)*laplaceComparisonStrength a.data.d a.lam zg)
    ∀ᶠj in atTop,(∫r in A,deriv a.alpha.val.val r
      ∂a.shiftedNativeModel.radiusMeasure dphys e (as j) (ho j))≤
      C*(K+1)^2*(1+v/a.data.U)*Real.log ((1+a.data.U)/a.data.U)*
        (∫r in A,deriv a.alpha.val.val r)+ε := by
  let N:=a.data.N
  let d:=a.data.d
  let lam:=a.lam
  let U:=a.data.U
  let L:=a.data.L
  let E:=a.data.E
  let δcap:=delta
  let M:=a.data.M
  let α:=a.alpha
  let hm:=a.data.hm
  have hMdef : M=comparisonCap N δcap U L E d:=rfl
  have hU:=a.data.hU
  have hL:=a.data.hL
  have hE:=a.data.hE
  have hd:=a.data.hd
  have hlam:=a.hlam
  let left:=cap.left
  let z:=cap.right
  have ha : 0≤left:=cap.hleft
  have haz : left<z:=cap.hlt
  have hz : z≤1:=cap.hright
  have hneg:=cap.negative

  dsimp only
  let F := (n+1:ℝ)*(((1/3)/Real.log N)*laplaceComparisonStrength d lam zg)
  let C := 27*(Real.log N)^2/((n+1:ℝ)*laplaceComparisonStrength d lam zg)
  let T := Real.log ((1+U)/U)
  let Q := (K+1)^2*(1+v/U)
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
  have hQ : 0≤Q := by dsimp [Q]; positivity
  have hMV : 0≤M V := by
    rw [congrFun hMdef V]
    exact (comparisonCap_first_term (δ:=δcap) hNp hU hL hE hd.le hV.1).1.le
  have htravel:=P.cap_interval_travel cap.hleft cap.hlt.le cap.hright cap.negative
  have hlength : z-left≤(L/N^δcap)*T := htravel.2.1
  have hprofile : M V*(L/N^δcap)≤Q*v := by
    have ht := comparisonCap_broad_length_multiplier_le (δ:=δcap)
      hNp hU hL hE hd.le hV.1 hK hUv hVv hcal
    have ht' := (div_le_iff₀ hv).mp
      (show (comparisonCap N δcap U L E d V*(L/N^δcap))/v≤Q by
        convert ht using 1 <;> ring)
    simpa only [congrFun hMdef V] using ht'
  have hnormal : M V*C*(z-left)≤C*Q*T*(∫r in A,deriv α.val.val r) := by
    have h1 := mul_le_mul_of_nonneg_left hlength (mul_nonneg hMV hC)
    have h2 := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hprofile hT) hC
    have h3 := mul_le_mul_of_nonneg_left hslice (mul_nonneg (mul_nonneg hC hQ) hT)
    nlinarith
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
  have ht:=cap.localized_measure_eventually hN hlog hnd dphys e hag hzg hoverlap hboundary
    A hAcap hAgroup as mesh ho hend hmesh hmesh0 hlim hsmall
  filter_upwards [ht] with j hj
  let μ := a.shiftedNativeModel.radiusMeasure dphys e (as j) (ho j)
  have hdom : μ≤volume:=a.shiftedNativeModel.radiusMeasure_le_volume dphys e (as j) (ho j)
  have hdens := cap_bounded_density_trace_le μ hdom α.val.val (fun _=>1)
    α.val.property.2 measurable_const A hA hMV (show (0:ℝ)≤1 by norm_num) hden
    (fun _ _=>by norm_num)
  simp only [mul_one] at hdens
  have hμ := mul_le_mul_of_nonneg_left hj hMV
  have hcommon' : (9*Real.log N)*(z-left)/F=C*(z-left) := by
    calc (9*Real.log N)*(z-left)/F=((9*Real.log N)/F)*(z-left) := by ring
         _=C*(z-left) := by rw [hcommon]
  rw [hcommon'] at hμ
  have herr : M V*(ε/(M V+1))≤ε := by
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (by linarith : 0<M V+1)).mpr
    nlinarith
  dsimp only [C,Q,T] at hnormal ⊢
  nlinarith

end ActualHighOnlyOverlapMinimum.ShiftedCapInterval
end OAI.SKFluctuations.LaplaceWindowFormalization
