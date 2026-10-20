module

public import ComparisonCapSideTrace

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 1800000
section
variable {c : ℝ} {k M : ℝ→ℝ}
variable (hc : 0 < c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r∈Icc (0:ℝ) 1,c ≤ k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)

theorem actual_variableEndpoint_comparison_cap_right_bound
    {N d lam : ℝ} (hN : 1≤N) (hlog : 1≤Real.log N) (hd : 0<d)
    (hnd : 1/N≤d) (hlam : 0<lam) (hld : lam≤d^2)
    (n : ℕ) (hn : 0<n) (b h : ℝ → ℝ) (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hlb : lam≤b 0) (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0≤h 0) (α : inverseIntegralConstraints 0 0 k M)
    (H J : ℝ → ℝ) (hH : AbsolutelyContinuousOnInterval H 0 1)
    (hJ : ∀r∈Icc (0:ℝ) 1,0<J r)
    (hD : ∀ᵐ r,r∈Icc (0:ℝ) 1→HasDerivAt H
      (J r*radiusComparisonGradient (laplaceComparisonStrength d lam) α.val.val
        (orderedPathS n
          (fun u=>(b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)).toNNReal)
          (fun u=>(h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)*comparisonSweepQuantile hc hk hkc hm hM α u).toNNReal))
        (orderedPathB n
          (fun u=>(b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)).toNNReal)
          (fun u=>(h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)*comparisonSweepQuantile hc hk hkc hm hM α u).toNNReal)) r) r)
    {a z t : ℝ} (ha : 0≤a) (hz : z≤1)
    (ht : t∈Ioo a z)
    (hzH : H z=0) (htH : H t<0) :
    let R := comparisonSweepQuantile hc hk hkc hm hM α
    let bf := fun u=>(b u-laplaceComparisonStrength d lam (R u)).toNNReal
    let hf := fun u=>(h u+laplaceComparisonStrength d lam (R u)*R u).toNNReal
    let S := fun r=>orderedPathS n bf hf (α.val.val r)
    S t≤z := by
  dsimp only
  let g := laplaceComparisonStrength d lam
  let R := comparisonSweepQuantile hc hk hkc hm hM α
  let bf := fun u=>(b u-g (R u)).toNNReal
  let hf := fun u=>(h u+g (R u)*R u).toNNReal
  let S := orderedPathS n bf hf
  let B := orderedPathB n bf hf
  let Sr := fun r=>S (α.val.val r)
  let Br := fun r=>B (α.val.val r)
  let p := comparisonLogSlope g
  let κ := (1/3)/Real.log N
  have hlogp : 0<Real.log N := by linarith
  have hκ : 0<κ := div_pos (by norm_num) hlogp
  have haz : a<z := ht.1.trans ht.2
  have hsub : Icc a z⊆Icc (0:ℝ) 1 := Icc_subset_Icc ha hz
  have hsubo : Ioo a z⊆Ioc (0:ℝ) 1 := fun r hr=>⟨ha.trans_lt hr.1,hr.2.le.trans hz⟩
  have hJg (r : ℝ) (hr : r∈Icc a z) : 0<J r*g r :=
    mul_pos (hJ r (hsub hr)) (laplaceComparisonStrength_pos d hlam r)
  have hDp : ∀ᵐ r,r∈Icc a z→HasDerivAt H
      ((J r*g r)*comparisonBracket (p r) r (Sr r) (Br r)) r := by
    filter_upwards [hD,volume.ae_ne (0:ℝ)] with r hdr hr0 hr
    have hrpos : 0<r := lt_of_le_of_ne (hsub hr).1 hr0.symm
    have hh := hdr (hsub hr)
    rw [comparison_gradient_slope hrpos.ne' (laplaceComparisonStrength_pos d hlam r).ne'] at hh
    convert hh using 1
    dsimp only [Sr,Br,S,B,bf,hf,g,R,p,comparisonBracket]
    ring
  have hpm : MonotoneOn p (Ioo a z) := by
    intro r hr t ht hrt
    dsimp only [p,g]
    rw [laplaceComparisonStrength_logSlope hd.ne' hlam.ne',laplaceComparisonStrength_logSlope hd.ne' hlam.ne']
    exact laplaceComparisonSlope_monotone (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hrt hlam.le) (pow_nonneg hd.le _))
  have hpb (r : ℝ) (hr : r∈Ioo a z) : p r∈Icc (0:ℝ) (1-κ) :=
    ⟨(laplaceComparisonStrength_logSlope_mem hd.ne' hlam.ne' r).1,by
      have hh := laplaceComparisonStrength_uniform_slope hN hlog hd hnd hlam hld (hsub (Ioo_subset_Icc_self hr))
      dsimp only [κ,p,g]
      linarith⟩
  have hpb' (r : ℝ) (hr : r∈Ioo a z) : p r∈Icc (0:ℝ) 1 :=
    ⟨(hpb r hr).1,by linarith [(hpb r hr).2]⟩
  have hmom := comparisonVariableEndpoint_radius_moments hc hk hkc hm hM n hn b h hd.ne' hlam.le hlb hb hh hh0 α
  have hS := hmom.1.mono (Ioo_subset_Icc_self.trans hsub)
  have hB := hmom.2.1.mono (Ioo_subset_Icc_self.trans hsub)
  have hSb (r : ℝ) (hr : r∈Ioo a z) : 0≤Sr r :=
    (hmom.2.2 r (hsub (Ioo_subset_Icc_self hr))).1.1
  have hBb (r : ℝ) (hr : r∈Ioo a z) : (Sr r)^2≤Br r :=
    (hmom.2.2 r (hsub (Ioo_subset_Icc_self hr))).2.1
  have hac : AbsolutelyContinuousOnInterval H a z := hH.mono (by simpa only [uIcc_of_le zero_le_one,uIcc_of_le haz.le] using hsub)
  exact cap_S_le_right (S:=Sr) (B:=Br) (r:=t) ha ht hac hJg hDp hzH htH hpb' hS hSb hBb

theorem comparisonPhysicalRightContactCapTrace_eventually
    {N d lam : ℝ} (hN : 1≤N) (hlog : 1≤Real.log N) (hd : 0<d)
    (hnd : 1/N≤d) (hlam : 0<lam) (hld : lam≤d^2)
    (n dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1)) (b h : ℝ → ℝ) (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hlb : lam≤b 0) (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0≤h 0) (α : inverseIntegralConstraints 0 0 k M)
    (H J : ℝ → ℝ) (hH : AbsolutelyContinuousOnInterval H 0 1)
    (hJ : ∀r∈Icc (0:ℝ) 1,0<J r)
    (hD : ∀ᵐ r,r∈Icc (0:ℝ) 1→HasDerivAt H
      (J r*radiusComparisonGradient (laplaceComparisonStrength d lam) α.val.val
        (orderedPathS (n+1)
          (fun u=>(b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)).toNNReal)
          (fun u=>(h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)*comparisonSweepQuantile hc hk hkc hm hM α u).toNNReal))
        (orderedPathB (n+1)
          (fun u=>(b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)).toNNReal)
          (fun u=>(h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)*comparisonSweepQuantile hc hk hkc hm hM α u).toNNReal)) r) r)
    {a z : ℝ} (ha : 0 ≤ a) (haz : a < z) (hz : z ≤ 1)
    (hzH : H z=0) (hneg : ∀r∈Ioo a z,H r<0)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hend : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hmesh0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    let F := (n+1:ℝ)*(((1/3)/Real.log N)*laplaceComparisonStrength d lam z)
    ∀ᶠ j in atTop,
      comparisonPhysicalRadiusMeasure hc hk hkc hm hM n dphys e d lam b h α
        (as j) (ho j) (Ioo a z) ≤ ENNReal.ofReal (z/F+ε) := by
  dsimp only
  let R := comparisonSweepQuantile hc hk hkc hm hM α
  let bf := fun u=>(b u-laplaceComparisonStrength d lam (R u)).toNNReal
  let hf := fun u=>(h u+laplaceComparisonStrength d lam (R u)*R u).toNNReal
  let clock := completedPathClock (n+1) bf hf
  let S := fun r=>orderedPathS (n+1) bf hf (α.val.val r)
  let F := (n+1:ℝ)*(((1/3)/Real.log N)*laplaceComparisonStrength d lam z)
  let Cnode := 2*ClockTree.errorJetVariation 2 0 0*
    clockVariationBound (physicalFeatureCoordinateBound n) clock
  let bound := z/F
  let η := min ((z-a)/4) (ε/8)
  let p := a+η
  let q := z-η
  have hη : 0 < η := lt_min (by linarith) (by positivity)
  have hηLen : η ≤ (z-a)/4 := min_le_left _ _
  have hηε : η ≤ ε/8 := min_le_right _ _
  have hp : p∈Ioo a z := by dsimp only [p];constructor <;> linarith
  have hq : q∈Ioo a z := by dsimp only [q];constructor <;> linarith
  have hpq : p ≤ q := by dsimp only [p,q];linarith
  have hF : 0 < F := mul_pos (by positivity) (mul_pos
    (div_pos (by norm_num) (by linarith)) (laplaceComparisonStrength_pos d hlam z))
  have hlog0 : 0 ≤ Real.log N := by linarith
  have hbound : 0 ≤ bound := div_nonneg (ha.trans haz.le) hF.le
  have had := comparisonVariableEndpoint_clocks_admissible hc hk hkc hm hM b h
    hd.ne' hlam.le hlb hb hh hh0 α
  have hCn : 0 ≤ Cnode := mul_nonneg
    (mul_nonneg (by norm_num) (ClockTree.errorJetVariation_nonneg _ _ _))
    (clockVariationBound_nonneg (physicalFeatureCoordinateBound n) clock
      (completedPathClock_monotone (n+1) (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1)))
  have hright : S q ≤ z := actual_variableEndpoint_comparison_cap_right_bound hc hk hkc hm hM
    hN hlog hd hnd hlam hld (n+1) (by omega) b h hb hlb hh hh0 α H J hH hJ hD
    ha hz hq hzH (hneg q hq)
  have hmom := comparisonVariableEndpoint_radius_moments hc hk hkc hm hM
    (n+1) (by omega) b h hd.ne' hlam.le hlb hb hh hh0 α
  have hSp : 0 ≤ S p := ((hmom.2.2 p ⟨ha.trans hp.1.le,hp.2.le.trans hz⟩).1).1
  have hinc : S q-S p ≤ z := by linarith
  have herror : Tendsto (fun j=>2*(mesh j*Cnode)/F+2*(mesh j/c)) atTop (𝓝 0) := by
    convert (((hlim.mul_const Cnode).const_mul 2).div_const F).add
      ((hlim.div_const c).const_mul 2) using 1 <;> simp
  have herr := herror.eventually (gt_mem_nhds (by positivity : (0:ℝ)<ε/2))
  filter_upwards [herr] with j hj
  let μ := comparisonPhysicalRadiusMeasure hc hk hkc hm hM n dphys e d lam b h α (as j) (ho j)
  let error := 2*(mesh j*Cnode)/F+2*(mesh j/c)
  have hmeshj : 0 ≤ mesh j := hmesh0 j
  have herror0 : 0 ≤ error := by dsimp only [error];positivity
  have hinterval := comparisonPhysicalRadiusMeasure_interval_le_fixedStrength hc hk hkc hm hM
    hN hlog hd hnd hlam hld n dphys e b h hb hh hh0 hlb α (as j) (ho j) (hend j)
    (hmesh j) (hmesh0 j) (ha.trans_lt hp.1) hpq hq.2.le hz
  have hinner : μ (Ioo p q) ≤ ENNReal.ofReal bound+ENNReal.ofReal error := by
    apply hinterval.trans
    apply add_le_add
    · exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hinc hF.le)
    · exact le_rfl
  have hinnerReal : μ.real (Ioo p q) ≤ bound+error := by
    have ht := ENNReal.toReal_mono (by finiteness) hinner
    rw [ENNReal.toReal_add (by finiteness) (by finiteness),
      ENNReal.toReal_ofReal hbound,ENNReal.toReal_ofReal herror0] at ht
    exact ht
  have hdom : μ ≤ volume :=
    (comparisonPhysicalRadiusMeasure_le_compact_volume hc hk hkc hm hM n dphys e d lam b h α
      (as j) (ho j)).trans Measure.restrict_le_self
  have hwhole := radius_measure_open_le_inner hdom hp.1.le hpq hq.2.le
  have hreal : μ.real (Ioo a z) ≤ bound+ε := by
    dsimp only [error] at hinnerReal
    dsimp only [p,q] at hwhole
    linarith
  exact (ENNReal.le_ofReal_iff_toReal_le (by finiteness) (by positivity : 0 ≤ bound+ε)).mpr hreal

theorem comparisonPhysicalWeightedRightContactCapTrace_eventually
    {N d lam : ℝ} (hN : 1≤N) (hlog : 1≤Real.log N) (hd : 0<d)
    (hnd : 1/N≤d) (hlam : 0<lam) (hld : lam≤d^2)
    (n dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1)) (b h : ℝ → ℝ) (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hlb : lam≤b 0) (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0≤h 0) (α : inverseIntegralConstraints 0 0 k M)
    (H J : ℝ → ℝ) (hH : AbsolutelyContinuousOnInterval H 0 1)
    (hJ : ∀r∈Icc (0:ℝ) 1,0<J r)
    (hD : ∀ᵐ r,r∈Icc (0:ℝ) 1→HasDerivAt H
      (J r*radiusComparisonGradient (laplaceComparisonStrength d lam) α.val.val
        (orderedPathS (n+1)
          (fun u=>(b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)).toNNReal)
          (fun u=>(h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)*comparisonSweepQuantile hc hk hkc hm hM α u).toNNReal))
        (orderedPathB (n+1)
          (fun u=>(b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)).toNNReal)
          (fun u=>(h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)*comparisonSweepQuantile hc hk hkc hm hM α u).toNNReal)) r) r)
    (hbang : ∀ᵐ r, r∈Icc (0:ℝ) 1 → H r<0 → deriv α.val.val r=M (α.val.val r))
    {a z : ℝ} (ha : 0 ≤ a) (haz : a < z) (hz : z ≤ 1)
    (hzH : H z=0) (hneg : ∀r∈Ioo a z,H r<0)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hend : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hmesh0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0))
    (hMz : 0 ≤ M (α.val.val z))
    (A : Set ℝ) (hA : MeasurableSet A) (hAcap : A⊆Ioo a z)
    (w : ℝ→ℝ) (hw : Measurable w) {W : ℝ} (hW : 0 ≤ W)
    (hwb : ∀r∈A, 0 ≤ w r ∧ w r ≤ W)
    {ε : ℝ} (hε : 0 < ε) :
    let F := (n+1:ℝ)*(((1/3)/Real.log N)*laplaceComparisonStrength d lam z)
    ∀ᶠ j in atTop,
      (∫r in A,deriv α.val.val r*w r∂comparisonPhysicalRadiusMeasure hc hk hkc hm hM
        n dphys e d lam b h α (as j) (ho j)) ≤
      M (α.val.val z)*W*(z/F)+ε := by
  dsimp only
  let F := (n+1:ℝ)*(((1/3)/Real.log N)*laplaceComparisonStrength d lam z)
  let D := M (α.val.val z)
  let B := z/F
  have hαz : α.val.val z∈Icc (0:ℝ) 1 := α.val.property.1 z
  have hden : ∀ᵐ r, r∈A → deriv α.val.val r ≤ D := by
    filter_upwards [hbang] with r hr hri
    have hrz := hAcap hri
    have hr01 : r∈Icc (0:ℝ) 1 := ⟨ha.trans hrz.1.le,hrz.2.le.trans hz⟩
    rw [hr hr01 (hneg r hrz)]
    exact hm (α.val.property.1 r) hαz (α.val.property.2 hrz.2.le)
  have hF : 0 < F := mul_pos (by positivity) (mul_pos
    (div_pos (by norm_num) (by linarith)) (laplaceComparisonStrength_pos d hlam z))
  have hB : 0 ≤ B := div_nonneg (ha.trans haz.le) hF.le
  have hD0 : 0 ≤ D := hMz
  have hDW : 0 ≤ D*W := mul_nonneg hD0 hW
  have hsmall : 0 < ε/(D*W+1) := div_pos hε (by linarith)
  have ht := comparisonPhysicalRightContactCapTrace_eventually hc hk hkc hm hM
    hN hlog hd hnd hlam hld n dphys e b h hb hlb hh hh0 α H J hH hJ hD
    ha haz hz hzH hneg as mesh ho hend hmesh hmesh0 hlim hsmall
  filter_upwards [ht] with j hj
  let μ := comparisonPhysicalRadiusMeasure hc hk hkc hm hM n dphys e d lam b h α (as j) (ho j)
  have hdom : μ ≤ volume := (comparisonPhysicalRadiusMeasure_le_compact_volume hc hk hkc hm hM
    n dphys e d lam b h α (as j) (ho j)).trans Measure.restrict_le_self
  have hμcap : μ.real (Ioo a z) ≤ B+ε/(D*W+1) := by
    have hb0 : 0 ≤ B+ε/(D*W+1) := add_nonneg hB hsmall.le
    exact (ENNReal.le_ofReal_iff_toReal_le (by finiteness) hb0).mp hj
  have hi := cap_bounded_density_trace_le μ hdom α.val.val w
    α.val.property.2 hw A hA hD0 hW hden hwb
  have hμA := measureReal_mono (μ:=μ) hAcap
  have hmul := mul_le_mul_of_nonneg_left (hμA.trans hμcap) hDW
  have herr : D*W*(ε/(D*W+1)) ≤ ε := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by linarith : 0 < D*W+1)).mpr
    nlinarith
  dsimp only [D,B,F] at *
  nlinarith

theorem comparisonPhysicalSelectedRightContactCapTrace_eventually
    {N d lam : ℝ} (hN : 1≤N) (hlog : 1≤Real.log N) (hd : 0<d)
    (hnd : 1/N≤d) (hlam : 0<lam) (hld : lam≤d^2)
    (n dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1)) (b h : ℝ → ℝ) (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hlb : lam≤b 0) (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0≤h 0) (α : inverseIntegralConstraints 0 0 k M)
    (H J : ℝ → ℝ) (hH : AbsolutelyContinuousOnInterval H 0 1)
    (hJ : ∀r∈Icc (0:ℝ) 1,0<J r)
    (hD : ∀ᵐ r,r∈Icc (0:ℝ) 1→HasDerivAt H
      (J r*radiusComparisonGradient (laplaceComparisonStrength d lam) α.val.val
        (orderedPathS (n+1)
          (fun u=>(b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)).toNNReal)
          (fun u=>(h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)*comparisonSweepQuantile hc hk hkc hm hM α u).toNNReal))
        (orderedPathB (n+1)
          (fun u=>(b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)).toNNReal)
          (fun u=>(h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)*comparisonSweepQuantile hc hk hkc hm hM α u).toNNReal)) r) r)
    (hbang : ∀ᵐ r, r∈Icc (0:ℝ) 1 → H r<0 → deriv α.val.val r=M (α.val.val r))
    {a z : ℝ} (ha : 0 ≤ a) (haz : a < z) (hz : z ≤ 1)
    (hzH : H z=0) (hneg : ∀r∈Ioo a z,H r<0)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hend : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hmesh0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0))
    (V : ℝ) (hV : V∈Icc (0:ℝ) 1) (hMV : 0 ≤ M V)
    (A : Set ℝ) (hA : MeasurableSet A) (hAcap : A⊆Ioo a z)
    (hAV : ∀r∈A, α.val.val r ≤ V)
    (w : ℝ→ℝ) (hw : Measurable w) {W : ℝ} (hW : 0 ≤ W)
    (hwb : ∀r∈A, 0 ≤ w r ∧ w r ≤ W)
    {ε : ℝ} (hε : 0 < ε) :
    let F := (n+1:ℝ)*(((1/3)/Real.log N)*laplaceComparisonStrength d lam z)
    ∀ᶠ j in atTop,
      (∫r in A,deriv α.val.val r*w r∂comparisonPhysicalRadiusMeasure hc hk hkc hm hM
        n dphys e d lam b h α (as j) (ho j)) ≤
      M V*W*(z/F)+ε := by
  dsimp only
  let F := (n+1:ℝ)*(((1/3)/Real.log N)*laplaceComparisonStrength d lam z)
  let D := M V
  let B := z/F
  have hden : ∀ᵐ r, r∈A → deriv α.val.val r ≤ D := by
    filter_upwards [hbang] with r hr hri
    have hrz := hAcap hri
    have hr01 : r∈Icc (0:ℝ) 1 := ⟨ha.trans hrz.1.le,hrz.2.le.trans hz⟩
    rw [hr hr01 (hneg r hrz)]
    exact hm (α.val.property.1 r) hV (hAV r hri)
  have hF : 0 < F := mul_pos (by positivity) (mul_pos
    (div_pos (by norm_num) (by linarith)) (laplaceComparisonStrength_pos d hlam z))
  have hB : 0 ≤ B := div_nonneg (ha.trans haz.le) hF.le
  have hD0 : 0 ≤ D := hMV
  have hDW : 0 ≤ D*W := mul_nonneg hD0 hW
  have hsmall : 0 < ε/(D*W+1) := div_pos hε (by linarith)
  have ht := comparisonPhysicalRightContactCapTrace_eventually hc hk hkc hm hM
    hN hlog hd hnd hlam hld n dphys e b h hb hlb hh hh0 α H J hH hJ hD
    ha haz hz hzH hneg as mesh ho hend hmesh hmesh0 hlim hsmall
  filter_upwards [ht] with j hj
  let μ := comparisonPhysicalRadiusMeasure hc hk hkc hm hM n dphys e d lam b h α (as j) (ho j)
  have hdom : μ ≤ volume := (comparisonPhysicalRadiusMeasure_le_compact_volume hc hk hkc hm hM
    n dphys e d lam b h α (as j) (ho j)).trans Measure.restrict_le_self
  have hμcap : μ.real (Ioo a z) ≤ B+ε/(D*W+1) := by
    have hb0 : 0 ≤ B+ε/(D*W+1) := add_nonneg hB hsmall.le
    exact (ENNReal.le_ofReal_iff_toReal_le (by finiteness) hb0).mp hj
  have hi := cap_bounded_density_trace_le μ hdom α.val.val w
    α.val.property.2 hw A hA hD0 hW hden hwb
  have hμA := measureReal_mono (μ:=μ) hAcap
  have hmul := mul_le_mul_of_nonneg_left (hμA.trans hμcap) hDW
  have herr : D*W*(ε/(D*W+1)) ≤ ε := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by linarith : 0 < D*W+1)).mpr
    nlinarith
  dsimp only [D,B,F] at *
  nlinarith

end
end OAI.SKFluctuations.LaplaceWindowFormalization
