module

public import ComparisonActualHighOnlyMovingTrace
public import ComparisonShiftedNativeSideColumns

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 12000000
namespace ActualHighOnlyOverlapMinimum.FixedCapWeights
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable {a : ActualHighOnlyOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}
    {P : a.Potential} (f : FixedCapWeights a P)

theorem side_filled_eventually
    (hN : 1≤ a.data.N) (hlog : 1≤ Real.log a.data.N) (hnd : 1/a.data.N≤ a.data.d)
    (dphys : ℕ) (e : Fin (dphys+1)≃FeatureIndex (n+1))
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hend : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hmesh0 : ∀j,0≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0))
    (Ks : ℕ→ℕ)
    (selected : (j : ℕ)→Finset (Fin ((sampleClockSteps a.shiftedNativeModel.q 0 (as j)).length+1)))
    (unit : (j : ℕ)→Fin ((sampleClockSteps a.shiftedNativeModel.q 0 (as j)).length+1)→Fin (Ks j))
    (x : ℕ→ℕ→ℝ) (widths : ℕ→ℝ) {cut width : ℝ}
    (hcut : 0< cut) (hwidth : 2*cut≤ width) (hwidths : ∀j,2*cut≤ widths j)
    (hwidthlim : Tendsto widths atTop (𝓝 width))
    (hstart : ∀j,x j 0=0) (hendx : ∀j,x j (Ks j)=widths j)
    (hx : ∀j,∀u : Fin (Ks j),x j u.val< x j (u.val+1))
    (hmass : ∀j,∀u : Fin (Ks j),physicalSelectedUnitMass
      (sampleClockSteps a.shiftedNativeModel.q 0 (as j)) (selected j) (unit j) u=x j (u.val+1)-x j u.val)
    (hhigh : ∀j,∀i∈selected j,a.data.s≤ partitionPoint 0 (as j) i.val)
    {cutRadius : ℝ} (hrcut : (0:ℝ)< cutRadius) (hrcut1 : cutRadius≤1)
    (hleft : ∀j,∀i∈selected j,cutRadius≤ a.shiftedNativeModel.R (partitionPoint 0 (as j) i.val))
    (hsupport : ∀j,∀ᵐr,r∉f.domain→a.shiftedNativeModel.unitColumn (as j) (selected j) (unit j)
      (fun u=>sideSquareColumn (x j) cut (widths j) u.val) r=0)
    (hcolumns : Tendsto (fun j=>∫r in f.domain,
      |a.shiftedNativeModel.unitColumn (as j) (selected j) (unit j)
        (fun u=>sideSquareColumn (x j) cut (widths j) u.val) r-f.fixed r|) atTop (𝓝 0))
    {epsilon : ℝ} (hepsilon : 0< epsilon) :
    let m:=a.shiftedNativeModel
    ∀ᶠj : ℕ in atTop,
      (2*(∫r,deriv a.alpha.val.val r*m.unitColumn (as j) (selected j) (unit j)
        (fun u=>sideSquareColumn (x j) cut (widths j) u.val) r
          ∂m.radiusMeasure dphys e (as j) (ho j))+4*mesh j/cut)/a.alpha.val.val cutRadius≤
        (108*f.K^2*(Real.log a.data.N)^2/((n+1:ℝ)*(laplaceComparisonStrength a.data.d a.lam) f.zg*a.alpha.val.val cutRadius))*
          Real.log (width/cut)+epsilon ∧
      actualBinSideVariance (n+1) (Ks j) (sampleClockSteps m.q 0 (as j)) (m.q 0)
        (selected j) (unit j) (x j) cut (widths j)≤
        (108*f.K^2*(Real.log a.data.N)^2/((n+1:ℝ)*(laplaceComparisonStrength a.data.d a.lam) f.zg*a.alpha.val.val cutRadius))*
          Real.log (width/cut)+epsilon := by
  dsimp only
  let m:=a.shiftedNativeModel
  let moving:=fun j=>m.unitColumn (as j) (selected j) (unit j)
    (fun u=>sideSquareColumn (x j) cut (widths j) u.val)
  let B:=(∑i,f.weight i)+f.W+2/cut
  have hsWeight : 0≤∑i,f.weight i:=Finset.sum_nonneg (fun i _=>f.hweight i)
  have hfixedB r : ‖f.fixed r‖≤ B:=(f.fixed_bound r).trans
    (le_add_of_nonneg_right (div_nonneg (by norm_num) hcut.le))
  have hmoveB j r : ‖moving j r‖≤ B:=by
    have H:=m.unitColumn_side_bound (as j) (ho j) (selected j) (unit j) (x j)
      (hstart j) (hendx j) hcut (hwidths j) (hx j) r
    rw [Real.norm_eq_abs,abs_of_nonneg H.1]
    exact H.2.trans (by dsimp only [B];linarith [f.hW])
  have hmoveMeas j : Measurable (moving j):=m.unitColumn_measurable _ _ _ _
  have hmassT:=f.moving_mass_tendsto moving hmoveMeas hfixedB hmoveB hsupport hcolumns
  have hlogT : Tendsto (fun j=>2*Real.log (widths j/cut)) atTop (𝓝 (2*Real.log (width/cut))):=
    ((Real.continuousAt_log (div_pos (by linarith) hcut).ne').tendsto.comp (hwidthlim.div_const cut)).const_mul 2
  have hfixedMass : f.mass≤2*Real.log (width/cut):=le_of_tendsto_of_tendsto hmassT hlogT
    (Eventually.of_forall (fun j=>m.unitColumn_side_mass_le_log (as j) (ho j) (hend j)
      (selected j) (unit j) (hhigh j) (x j) (hstart j) (hendx j) hcut (hwidths j) (hx j) (hmass j)))
  have hcutMass : 0<a.alpha.val.val cutRadius:=m.profile_pos hrcut hrcut1
  let err:=epsilon*a.alpha.val.val cutRadius/8
  have herr : 0< err:=div_pos (mul_pos hepsilon hcutMass) (by norm_num)
  have ht:=f.moving_trace_eventually hN hlog hnd dphys e as mesh ho hend hmesh hmesh0 hlim
    moving hmoveMeas hfixedB hmoveB hsupport hcolumns herr
  have hmeshSmall:=(tendsto_order.mp hlim).2 (epsilon*a.alpha.val.val cutRadius*cut/8) (by positivity)
  filter_upwards [ht,hmeshSmall] with j hj hmj
  have Htrace : (∫r,deriv a.alpha.val.val r*moving j r∂m.radiusMeasure dphys e (as j) (ho j))≤
      f.coefficient*f.K^2*(2*Real.log (width/cut))+err:=
    hj.trans (add_le_add (mul_le_mul_of_nonneg_left hfixedMass
      (mul_nonneg f.coefficient_nonneg (sq_nonneg _))) le_rfl)
  have Hfinal : (2*(∫r,deriv a.alpha.val.val r*moving j r∂m.radiusMeasure dphys e (as j) (ho j))+
      4*mesh j/cut)/a.alpha.val.val cutRadius≤
      (4*f.coefficient*f.K^2/a.alpha.val.val cutRadius)*Real.log (width/cut)+epsilon:=by
    apply (div_le_iff₀ hcutMass).mpr
    have HM : 4*mesh j/cut≤ epsilon*a.alpha.val.val cutRadius/2:=by
      apply (div_le_iff₀ hcut).mpr
      nlinarith
    dsimp only [err] at Htrace
    have HE : ((4*f.coefficient*f.K^2/a.alpha.val.val cutRadius)*Real.log (width/cut)+epsilon)*
        a.alpha.val.val cutRadius=4*f.coefficient*f.K^2*Real.log (width/cut)+epsilon*a.alpha.val.val cutRadius:=by
      field_simp
    rw [HE]
    nlinarith
  have HE : (4*f.coefficient*f.K^2/a.alpha.val.val cutRadius)*Real.log (width/cut)=
      (108*f.K^2*(Real.log a.data.N)^2/((n+1:ℝ)*(laplaceComparisonStrength a.data.d a.lam) f.zg*a.alpha.val.val cutRadius))*
        Real.log (width/cut):=by
    dsimp only [coefficient]
    field_simp [hcutMass.ne',(laplaceComparisonStrength_pos a.data.d a.hlam f.zg).ne']
    ring
  have HV:=m.actual_bin_sideVariance_le_integral dphys e (as j) (ho j) (hend j) (hmesh j) (hmesh0 j)
    (selected j) (unit j) (hhigh j) (x j) (hstart j) (hendx j) hcut (hwidths j) (hx j)
    hrcut hrcut1 (hleft j)
  constructor
  · simpa only [HE] using Hfinal
  · exact HV.trans (by simpa only [HE] using Hfinal)

theorem union_filled_eventually
    (hN : 1≤ a.data.N) (hlog : 1≤ Real.log a.data.N) (hnd : 1/a.data.N≤ a.data.d)
    (dphys : ℕ) (e : Fin (dphys+1)≃FeatureIndex (n+1))
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hend : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hmesh0 : ∀j,0≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0))
    (selected : (j : ℕ)→Finset (Fin ((sampleClockSteps a.shiftedNativeModel.q 0 (as j)).length+1)))
    (hhigh : ∀j,∀i∈selected j,a.data.s≤ partitionPoint 0 (as j) i.val)
    {cutRadius v : ℝ} (hrcut : (0:ℝ)< cutRadius) (hrcut1 : cutRadius≤1)
    (hleft : ∀j,∀i∈selected j,cutRadius≤ a.shiftedNativeModel.R (partitionPoint 0 (as j) i.val))
    (hmasslim : Tendsto (fun j=>∑i,physicalSelectedCellMass
      (sampleClockSteps a.shiftedNativeModel.q 0 (as j)) (selected j) i) atTop (𝓝 v))
    (hsupport : ∀j,∀ᵐr,r∉f.domain→a.shiftedNativeModel.unitColumn (as j) (selected j)
      (fun _=>(0:Fin 1)) (fun _=>1) r=0)
    (hcolumns : Tendsto (fun j=>∫r in f.domain,
      |a.shiftedNativeModel.unitColumn (as j) (selected j) (fun _=>(0:Fin 1)) (fun _=>1) r-f.fixed r|)
      atTop (𝓝 0)) {epsilon : ℝ} (hepsilon : 0< epsilon) :
    let m:=a.shiftedNativeModel
    ∀ᶠj : ℕ in atTop,
      (2*(∫r,deriv a.alpha.val.val r*m.unitColumn (as j) (selected j) (fun _=>(0:Fin 1)) (fun _=>1) r
        ∂m.radiusMeasure dphys e (as j) (ho j))+2*mesh j)/(a.alpha.val.val cutRadius)^2≤
        (54*f.K^2*(Real.log a.data.N)^2/((n+1:ℝ)*(laplaceComparisonStrength a.data.d a.lam) f.zg*(a.alpha.val.val cutRadius)^2))*v+epsilon ∧
      (∑i,physicalSelectedCellMass (sampleClockSteps m.q 0 (as j)) (selected j) i*
        actualCutCovarianceEnergy (n+1) (sampleClockSteps m.q 0 (as j)) (m.q 0) i.val)≤
        (54*f.K^2*(Real.log a.data.N)^2/((n+1:ℝ)*(laplaceComparisonStrength a.data.d a.lam) f.zg*(a.alpha.val.val cutRadius)^2))*v+epsilon := by
  dsimp only
  let m:=a.shiftedNativeModel
  let moving:=fun j=>m.unitColumn (as j) (selected j) (fun _=>(0:Fin 1)) (fun _=>1)
  let B:=(∑i,f.weight i)+f.W+1
  have hsWeight : 0≤∑i,f.weight i:=Finset.sum_nonneg (fun i _=>f.hweight i)
  have hfixedB r : ‖f.fixed r‖≤ B:=(f.fixed_bound r).trans (by dsimp only [B];linarith)
  have hmoveB j r : ‖moving j r‖≤ B:=by
    have hcol : ∀i,nativeSelectedColumn (selected j) (fun _=>(0:Fin 1)) (fun _=>1) i∈Icc (0:ℝ) 1:=by
      intro i
      unfold nativeSelectedColumn
      split_ifs <;> norm_num
    have H:=radiusCellEnergyDensity_mem_Icc_bound m.R m.R_monotone (as j) (ho j) _ zero_le_one hcol r
    change moving j r∈Icc (0:ℝ) 1 at H
    rw [Real.norm_eq_abs,abs_of_nonneg H.1]
    exact H.2.trans (by dsimp only [B];linarith [f.hW])
  have hmoveMeas j : Measurable (moving j):=m.unitColumn_measurable _ _ _ _
  have hmassT:=f.moving_mass_tendsto moving hmoveMeas hfixedB hmoveB hsupport hcolumns
  have hmassEq j : (∫r,deriv a.alpha.val.val r*moving j r)=
      ∑i,physicalSelectedCellMass (sampleClockSteps m.q 0 (as j)) (selected j) i:=by
    rw [m.unitColumn_mass (as j) (ho j) (hend j) (selected j) (fun _=>(0:Fin 1)) (fun _=>1) (hhigh j)]
    rw [Fin.sum_univ_one]
    simp only [physicalSelectedUnitMass,physicalSelectedCellMass,and_true,mul_one]
  have hmass : f.mass=v:=tendsto_nhds_unique hmassT (hmasslim.congr (fun j=>(hmassEq j).symm))
  have hcutMass : 0<a.alpha.val.val cutRadius:=m.profile_pos hrcut hrcut1
  let err:=epsilon*(a.alpha.val.val cutRadius)^2/8
  have herr : 0< err:=div_pos (mul_pos hepsilon (sq_pos_of_pos hcutMass)) (by norm_num)
  have ht:=f.moving_trace_eventually hN hlog hnd dphys e as mesh ho hend hmesh hmesh0 hlim
    moving hmoveMeas hfixedB hmoveB hsupport hcolumns herr
  have hmeshSmall:=(tendsto_order.mp hlim).2 (epsilon*(a.alpha.val.val cutRadius)^2/8) (by positivity)
  filter_upwards [ht,hmeshSmall] with j hj hmj
  rw [hmass] at hj
  have Hfinal : (2*(∫r,deriv a.alpha.val.val r*moving j r∂m.radiusMeasure dphys e (as j) (ho j))+
      2*mesh j)/(a.alpha.val.val cutRadius)^2≤(2*f.coefficient*f.K^2/(a.alpha.val.val cutRadius)^2)*v+epsilon:=by
    apply (div_le_iff₀ (sq_pos_of_pos hcutMass)).mpr
    dsimp only [err] at hj
    have HE : ((2*f.coefficient*f.K^2/(a.alpha.val.val cutRadius)^2)*v+epsilon)*
        (a.alpha.val.val cutRadius)^2=2*f.coefficient*f.K^2*v+epsilon*(a.alpha.val.val cutRadius)^2:=by
      field_simp
    rw [HE]
    nlinarith
  have HE : (2*f.coefficient*f.K^2/(a.alpha.val.val cutRadius)^2)*v=
      (54*f.K^2*(Real.log a.data.N)^2/((n+1:ℝ)*(laplaceComparisonStrength a.data.d a.lam) f.zg*(a.alpha.val.val cutRadius)^2))*v:=by
    dsimp only [coefficient]
    field_simp [hcutMass.ne',(laplaceComparisonStrength_pos a.data.d a.hlam f.zg).ne']
    ring
  have HC:=m.weightedCovarianceEnergy_le_integral dphys e (as j) (ho j) (hend j) (hmesh j) (hmesh0 j)
    (selected j) (fun _=>(0:Fin 1)) (fun _=>1) (fun _=>by norm_num)
    zero_le_one (fun _=>le_rfl) (hhigh j) hrcut hrcut1 (hleft j)
  rw [nativeWeightedCovarianceEnergy_one] at HC
  simp only [mul_one] at HC
  constructor
  · simpa only [HE] using Hfinal
  · exact HC.trans (by simpa only [HE] using Hfinal)

end ActualHighOnlyOverlapMinimum.FixedCapWeights
end OAI.SKFluctuations.LaplaceWindowFormalization
