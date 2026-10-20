module

public import ComparisonCapSideTraceBroad

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 2200000
section
variable {c : ℝ} {k M : ℝ→ℝ}
variable (hc : 0<c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r∈Icc (0:ℝ) 1,c≤k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0≤M 1)

theorem comparisonPhysicalLocalizedCapMeasure_eventually
    {N d lam : ℝ} (hN : 1≤N) (hlog : 1≤Real.log N)
    (hd : 0<d)
    (hnd : 1/N≤d) (hlam : 0<lam) (hld : lam≤d^2)
    (n dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1))
    (b h : ℝ→ℝ) (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hlb : lam≤b 0) (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0≤h 0)
    (α : inverseIntegralConstraints 0 0 k M)
    (H J : ℝ→ℝ) (hH : AbsolutelyContinuousOnInterval H 0 1)
    (hJ : ∀r∈Icc (0:ℝ) 1,0<J r)
    (hD : ∀ᵐ r,r∈Icc (0:ℝ) 1→HasDerivAt H
      (J r*radiusComparisonGradient (laplaceComparisonStrength d lam) α.val.val
        (orderedPathS (n+1)
          (fun u=>(b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)).toNNReal)
          (fun u=>(h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)*comparisonSweepQuantile hc hk hkc hm hM α u).toNNReal))
        (orderedPathB (n+1)
          (fun u=>(b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)).toNNReal)
          (fun u=>(h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)*comparisonSweepQuantile hc hk hkc hm hM α u).toNNReal)) r) r)
    {a z ag zg : ℝ} (ha : 0≤a) (haz : a<z) (hz : z≤1)
    (hag : 0<ag) (hzg : zg≤1) (hoverlap : max a ag < min z zg)
    (hboundary : (H a=0 ∧ H z=0) ∨ (a=0 ∧ H z=0) ∨ (H a=0 ∧ z=1))
    (hneg : ∀r∈Ioo a z,H r<0)
    (A : Set ℝ) (hAcap : A⊆Ioo a z) (hAgroup : A⊆Ioo ag zg)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hend : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hmesh0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0)) {ε : ℝ} (hε : 0<ε) :
    let F := (n+1:ℝ)*(((1/3)/Real.log N)*laplaceComparisonStrength d lam zg)
    ∀ᶠ j in atTop,
      (comparisonPhysicalRadiusMeasure hc hk hkc hm hM n dphys e d lam b h α
        (as j) (ho j)).real A≤(9*Real.log N)*(z-a)/F+ε := by
  dsimp only
  let R := comparisonSweepQuantile hc hk hkc hm hM α
  let bf := fun u=>(b u-laplaceComparisonStrength d lam (R u)).toNNReal
  let hf := fun u=>(h u+laplaceComparisonStrength d lam (R u)*R u).toNNReal
  let clock := completedPathClock (n+1) bf hf
  let S := fun r=>orderedPathS (n+1) bf hf (α.val.val r)
  let F := (n+1:ℝ)*(((1/3)/Real.log N)*laplaceComparisonStrength d lam zg)
  let Cnode := 2*ClockTree.errorJetVariation 2 0 0*
    clockVariationBound (physicalFeatureCoordinateBound n) clock
  let bound := (9*Real.log N)*(z-a)/F
  let lo := max a ag
  let hi := min z zg
  let η := min ((hi-lo)/4) (ε/8)
  let p := lo+η
  let q := hi-η
  have hη : 0<η := lt_min (by dsimp [hi,lo]; linarith) (by positivity)
  have hηLen : η≤(hi-lo)/4 := min_le_left _ _
  have hηε : η≤ε/8 := min_le_right _ _
  have hloA : a≤lo := le_max_left _ _
  have hloG : ag≤lo := le_max_right _ _
  have hhiZ : hi≤z := min_le_left _ _
  have hhiG : hi≤zg := min_le_right _ _
  have hp : p∈Ioo a z := by dsimp only [p]; constructor <;> linarith
  have hq : q∈Ioo a z := by dsimp only [q]; constructor <;> linarith
  have hpq : p≤q := by dsimp only [p,q]; linarith
  have hF : 0<F := mul_pos (by positivity) (mul_pos
    (div_pos (by norm_num) (by linarith)) (laplaceComparisonStrength_pos d hlam zg))
  have hbound : 0≤bound := by dsimp [bound]; positivity
  have hinc : S q-S p≤(9*Real.log N)*(z-a) := by
    rcases hboundary with ho | hi | ht
    · exact (actual_variableEndpoint_comparison_cap_interior_geometry hc hk hkc hm hM
        hN hlog hd hnd hlam hld (n+1) (by omega) b h hb hlb hh hh0 α H J hH hJ hD
        ha hz hp hq hpq ho.1 ho.2 (hneg p hp) (hneg q hq)).1
    · have hright := actual_variableEndpoint_comparison_cap_right_bound hc hk hkc hm hM
        hN hlog hd hnd hlam hld (n+1) (by omega) b h hb hlb hh hh0 α H J hH hJ hD
        ha hz hq hi.2 (hneg q hq)
      have hp0 : 0≤S p :=
        ((comparisonVariableEndpoint_radius_moments hc hk hkc hm hM (n+1) (by omega)
          b h hd.ne' hlam.le hlb hb hh hh0 α).2.2 p ⟨ha.trans hp.1.le,hp.2.le.trans hz⟩).1.1
      have hz0 : 0≤z := ha.trans haz.le
      have hscale := mul_le_mul_of_nonneg_right (show (1:ℝ)≤9*Real.log N by linarith) hz0
      dsimp only at hright
      rw [hi.1,sub_zero]
      nlinarith
    · have ht' := actual_variableEndpoint_comparison_terminal_cap_increment hc hk hkc hm hM
        hN hlog hd hnd hlam hld (n+1) (by omega) b h hb hlb hh hh0 α H J hH hJ hD ha
        (by simpa only [ht.2] using hp) (by simpa only [ht.2] using hq) hpq ht.1
        (hneg p hp) (hneg q hq)
      simpa only [ht.2] using ht'
  have herror : Tendsto (fun j=>2*(mesh j*Cnode)/F+2*(mesh j/c)) atTop (𝓝 0) := by
    convert (((hlim.mul_const Cnode).const_mul 2).div_const F).add
      ((hlim.div_const c).const_mul 2) using 1 <;> simp
  have herr := herror.eventually (gt_mem_nhds (by positivity : (0:ℝ)<ε/2))
  have had := comparisonVariableEndpoint_clocks_admissible hc hk hkc hm hM b h
    hd.ne' hlam.le hlb hb hh hh0 α
  have hCn : 0≤Cnode := mul_nonneg
    (mul_nonneg (by norm_num) (ClockTree.errorJetVariation_nonneg _ _ _))
    (clockVariationBound_nonneg (physicalFeatureCoordinateBound n) clock
      (completedPathClock_monotone (n+1) (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1)))
  filter_upwards [herr] with j hj
  let μ := comparisonPhysicalRadiusMeasure hc hk hkc hm hM n dphys e d lam b h α (as j) (ho j)
  let error := 2*(mesh j*Cnode)/F+2*(mesh j/c)
  have hmeshj := hmesh0 j
  have herror0 : 0≤error := by dsimp [error]; positivity
  have hinterval := comparisonPhysicalRadiusMeasure_interval_le_fixedStrength hc hk hkc hm hM
    hN hlog hd hnd hlam hld n dphys e b h hb hh hh0 hlb α (as j) (ho j) (hend j)
    (hmesh j) (hmesh0 j) (by dsimp [p]; linarith) hpq
    (by dsimp [q]; linarith) hzg
  have hinner : μ (Ioo p q)≤ENNReal.ofReal bound+ENNReal.ofReal error := by
    exact hinterval.trans (add_le_add (ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_right hinc hF.le)) le_rfl)
  have hinnerReal : μ.real (Ioo p q)≤bound+error := by
    have ht := ENNReal.toReal_mono (by finiteness) hinner
    rw [ENNReal.toReal_add (by finiteness) (by finiteness),
      ENNReal.toReal_ofReal hbound,ENNReal.toReal_ofReal herror0] at ht
    exact ht
  have hdom : μ≤volume :=
    (comparisonPhysicalRadiusMeasure_le_compact_volume hc hk hkc hm hM n dphys e d lam b h α
      (as j) (ho j)).trans Measure.restrict_le_self
  have hwhole := radius_measure_open_le_inner hdom
    (by dsimp [p]; linarith : lo≤p) hpq (by dsimp [q]; linarith : q≤hi)
  have hAsub : A⊆Ioo lo hi := by
    intro r hr
    exact ⟨max_lt ((hAcap hr).1) ((hAgroup hr).1),lt_min ((hAcap hr).2) ((hAgroup hr).2)⟩
  have hreal : μ.real (Ioo lo hi)≤bound+ε := by
    dsimp only [p,q] at hwhole
    dsimp only [error] at hinnerReal
    linarith
  exact (measureReal_mono hAsub).trans hreal

theorem comparisonPhysicalLocalizedBroadCapUnitTrace_eventually
    {N δcap U L E d lam : ℝ} (hN : 1≤N) (hlog : 1≤Real.log N)
    (hU : 0<U) (hL : 0<L) (hE : 0<E) (hd : 0<d)
    (hnd : 1/N≤d) (hlam : 0<lam) (hld : lam≤d^2)
    (hMdef : M=comparisonCap N δcap U L E d)
    (n dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1))
    (b h : ℝ→ℝ) (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hlb : lam≤b 0) (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0≤h 0)
    (α : inverseIntegralConstraints 0 0 k M)
    (H J : ℝ→ℝ) (hH : AbsolutelyContinuousOnInterval H 0 1)
    (hJ : ∀r∈Icc (0:ℝ) 1,0<J r)
    (hD : ∀ᵐ r,r∈Icc (0:ℝ) 1→HasDerivAt H
      (J r*radiusComparisonGradient (laplaceComparisonStrength d lam) α.val.val
        (orderedPathS (n+1)
          (fun u=>(b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)).toNNReal)
          (fun u=>(h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)*comparisonSweepQuantile hc hk hkc hm hM α u).toNNReal))
        (orderedPathB (n+1)
          (fun u=>(b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)).toNNReal)
          (fun u=>(h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)*comparisonSweepQuantile hc hk hkc hm hM α u).toNNReal)) r) r)
    (hbang : ∀ᵐ r,r∈Icc (0:ℝ) 1→H r<0→deriv α.val.val r=M (α.val.val r))
    {a z ag zg v V K : ℝ} (ha : 0≤a) (haz : a<z) (hz : z≤1)
    (hag : 0<ag) (hzg : zg≤1) (hoverlap : max a ag < min z zg)
    (hboundary : (H a=0 ∧ H z=0) ∨ (a=0 ∧ H z=0) ∨ (H a=0 ∧ z=1))
    (hneg : ∀r∈Ioo a z,H r<0)
    (hK : 1≤K) (hUv : U≤v) (hV : V∈Icc (0:ℝ) 1) (hVv : V≤K*v)
    (hcal : d^3*L*U≤E)
    (A : Set ℝ) (hA : MeasurableSet A) (hAcap : A⊆Ioo a z)
    (hAgroup : A⊆Ioo ag zg)
    (hAV : ∀r∈A,α.val.val r≤V)
    (hslice : v≤∫r in A,deriv α.val.val r)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hend : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hmesh0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0))
    {ε : ℝ} (hε : 0<ε) :
    let C := 27*(Real.log N)^2/((n+1:ℝ)*laplaceComparisonStrength d lam zg)
    ∀ᶠ j in atTop,
      (∫r in A,deriv α.val.val r∂comparisonPhysicalRadiusMeasure hc hk hkc hm hM
        n dphys e d lam b h α (as j) (ho j)) ≤
      C*(K+1)^2*(1+v/U)*Real.log ((1+U)/U)*(∫r in A,deriv α.val.val r)+ε := by
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
  have hcap : ∀ᵐ r,r∈Icc (0:ℝ) 1→H r<0→
      deriv α.val.val r=comparisonCap N δcap U L E d (α.val.val r) := by
    filter_upwards [hbang] with r hr hr01 hrH
    simpa only [congrFun hMdef (α.val.val r)] using hr hr01 hrH
  have htravel := potential_comparison_cap_interval_travel (δ:=δcap)
    hNp hU hL hE hd
    (inverseIntegralConstraints_lipschitz hm hM α.property)
    (inverseConstraint_strictMonoOn hc hk hkc α.property)
    (fun r _=>α.val.property.1 r) hcap ha hz haz.le hneg
  have hlength : z-a≤(L/N^δcap)*T := htravel.2.1
  have hprofile : M V*(L/N^δcap)≤Q*v := by
    have ht := comparisonCap_broad_length_multiplier_le (δ:=δcap)
      hNp hU hL hE hd.le hV.1 hK hUv hVv hcal
    have ht' := (div_le_iff₀ hv).mp
      (show (comparisonCap N δcap U L E d V*(L/N^δcap))/v≤Q by
        convert ht using 1 <;> ring)
    simpa only [congrFun hMdef V] using ht'
  have hnormal : M V*C*(z-a)≤C*Q*T*(∫r in A,deriv α.val.val r) := by
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
    filter_upwards [hbang] with r hr hrA
    have hrc := hAcap hrA
    rw [hr ⟨ha.trans hrc.1.le,hrc.2.le.trans hz⟩ (hneg r hrc)]
    exact hm (α.val.property.1 r) hV (hAV r hrA)
  have hsmall : 0<ε/(M V+1) := div_pos hε (by linarith)
  have ht := comparisonPhysicalLocalizedCapMeasure_eventually hc hk hkc hm hM
    hN hlog hd hnd hlam hld n dphys e b h hb hlb hh hh0 α H J hH hJ hD
    ha haz hz hag hzg hoverlap hboundary hneg A hAcap hAgroup
    as mesh ho hend hmesh hmesh0 hlim hsmall
  filter_upwards [ht] with j hj
  let μ := comparisonPhysicalRadiusMeasure hc hk hkc hm hM n dphys e d lam b h α (as j) (ho j)
  have hdom : μ≤volume :=
    (comparisonPhysicalRadiusMeasure_le_compact_volume hc hk hkc hm hM n dphys e d lam b h α
      (as j) (ho j)).trans Measure.restrict_le_self
  have hdens := cap_bounded_density_trace_le μ hdom α.val.val (fun _=>1)
    α.val.property.2 measurable_const A hA hMV (show (0:ℝ)≤1 by norm_num) hden
    (fun _ _=>by norm_num)
  simp only [mul_one] at hdens
  have hμ := mul_le_mul_of_nonneg_left hj hMV
  have hcommon' : (9*Real.log N)*(z-a)/F=C*(z-a) := by
    calc (9*Real.log N)*(z-a)/F=((9*Real.log N)/F)*(z-a) := by ring
         _=C*(z-a) := by rw [hcommon]
  rw [hcommon'] at hμ
  have herr : M V*(ε/(M V+1))≤ε := by
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (by linarith : 0<M V+1)).mpr
    nlinarith
  dsimp only [C,Q,T] at hnormal ⊢
  nlinarith

end
end OAI.SKFluctuations.LaplaceWindowFormalization
