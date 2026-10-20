module

public import ComparisonActualHighOnlyBroadDensityLengthTrace
public import ComparisonActualHighOnlyOuterComparableDensity

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 14000000
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false
namespace ActualHighOnlyOverlapMinimum.ShiftedCapInterval
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable {a : ActualHighOnlyOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}
    {P : a.Potential} (cap : ShiftedCapInterval a P)

theorem complete_density_length_le_of_mass_band_high_only
    {V K : ℝ} (hV : V∈Icc (0:ℝ) 1) (hK : 1≤K)
    (hband : V+a.data.U≤K*(a.alpha.val.val cap.left+a.data.U)) :
    a.data.M V*(cap.right-cap.left)≤K^2*(∫r in Ioo cap.left cap.right,deriv a.alpha.val.val r) := by
  have hα:(a.alpha.val.val cap.left)∈Icc (0:ℝ) 1:=a.alpha.val.property.1 cap.left
  have HM:=comparisonCap_common_mass_band_ratio (δ:=delta) a.data.hN a.data.hU a.data.hL
    a.data.hE a.data.hd.le hα.1 hK hband (u:=a.alpha.val.val cap.left) (v:=V) le_rfl le_rfl hV.1
  have hMpos:0<a.data.M (a.alpha.val.val cap.left):=
    (comparisonCap_first_term (δ:=delta) a.data.hN a.data.hU a.data.hL a.data.hE a.data.hd.le hα.1).1
  have HM':a.data.M V≤K^2*a.data.M (a.alpha.val.val cap.left):=by
    change a.data.M V/a.data.M (a.alpha.val.val cap.left)≤K^2 at HM
    simpa only [mul_comm] using (div_le_iff₀ hMpos).mp HM
  have H1:=mul_le_mul_of_nonneg_right HM' (sub_nonneg.mpr cap.hlt.le)
  have H2:=mul_le_mul_of_nonneg_left cap.mass_lower (sq_nonneg K)
  have heq:=a.inverse_slice_mass cap.hleft cap.hlt.le cap.hright
  rw [heq]
  nlinarith only [H1,H2]

theorem cropped_unit_trace_from_density_length_high_only
    (hN : 1≤a.data.N) (hlog : 1≤Real.log a.data.N) (hnd : 1/a.data.N≤a.data.d)
    (dphys : ℕ) (e : Fin (dphys+1)≃FeatureIndex (n+1))
    {ag zg V loss : ℝ} (hag : 0<ag) (hzg : zg≤1)
    (hoverlap : max cap.left ag < min cap.right zg)
    (hboundary : (P.H cap.left=0 ∨ cap.left=0) ∧ (P.H cap.right=0 ∨ cap.right=1))
    (hV : V∈Icc (0:ℝ) 1)
    (A : Set ℝ) (hA : MeasurableSet A) (hAcap : A⊆Ioo cap.left cap.right)
    (hAgroup : A⊆Ioo ag zg) (hAV : ∀r∈A,a.alpha.val.val r≤V)
    (hloss : 0≤loss)
    (hdensity : a.data.M V*(cap.right-cap.left)≤loss*(∫r in A,deriv a.alpha.val.val r))
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hend : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hmesh0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0)) {ε : ℝ} (hε : 0<ε) :
    let C:=27*(Real.log a.data.N)^2/((n+1:ℝ)*laplaceComparisonStrength a.data.d a.lam zg)
    ∀ᶠj in atTop,(∫r in A,deriv a.alpha.val.val r
      ∂a.shiftedNativeModel.radiusMeasure dphys e (as j) (ho j))≤
      C*loss*
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
  have hNp : 0<N := by linarith
  have hlogpos : 0<Real.log N := by linarith
  have hgpos := laplaceComparisonStrength_pos d hlam zg
  have hF : 0<F := mul_pos (by positivity)
    (mul_pos (div_pos (by norm_num) hlogpos) hgpos)
  have hC : 0≤C := by dsimp [C]; positivity
  have hT : 0≤T := by
    apply Real.log_nonneg
    apply (le_div_iff₀ hU).mpr
    linarith
  have hMV : 0≤M V := by
    rw [congrFun hMdef V]
    exact (comparisonCap_first_term (δ:=δcap) hNp hU hL hE hd.le hV.1).1.le
  have hnormal : M V*C*(z-left)≤C*loss*(∫r in A,deriv α.val.val r) := by
    have H:=mul_le_mul_of_nonneg_left hdensity hC
    convert H using 1 <;> dsimp only [M,z,left,α] <;> ring
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
  dsimp only [C] at hnormal ⊢
  nlinarith

end ActualHighOnlyOverlapMinimum.ShiftedCapInterval
end OAI.SKFluctuations.LaplaceWindowFormalization
