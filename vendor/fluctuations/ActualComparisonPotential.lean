module

public import ActualStrengthMinimum
public import OrderedPairClockCongruence
public import NegativeComparisonGeometry

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal

section
variable {c : ℝ} {k M : ℝ → ℝ}
variable (hc : 0<c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀ r∈Icc (0:ℝ) 1,c≤k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0≤M 1)

theorem comparisonSweep_inverse_clocks_admissible (b : ℝ → ℝ)
    {d lam : ℝ} (hd : d≠0) (hlam : 0≤lam) (hlb : lam≤b 0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (α : inverseIntegralConstraints 0 0 k M) :
    let g := laplaceComparisonStrength d lam
    let hg := (laplaceComparisonStrength_contDiff d lam).continuous
    let e := omittedExtension zero_le_one
      (constrainedCoefficient zero_le_one hc hk hkc hm hM g hg α)
    let q := omittedExtension zero_le_one
      (constrainedCoefficient zero_le_one hc hk hkc hm hM (fun r=>g r*r) (hg.mul continuous_id) α)
    MonotoneOn (fun u=>b u-e u) (Icc (0:ℝ) 1) ∧
      MonotoneOn (fun u=>0+q u) (Icc (0:ℝ) 1) ∧
      0≤b 0-e 0 ∧ 0≤0+q 0 := by
  dsimp only
  have hmstrength := laplaceComparisonStrength_monotonicities_nonneg hd hlam
  have heanti := fullMassCoefficient_antitone zero_le_one hc hk hkc hm hM _
    (laplaceComparisonStrength_contDiff d lam).continuous hmstrength.1 α
  have hqmono := fullMassCoefficient_monotone zero_le_one hc hk hkc hm hM
    (fun r=>laplaceComparisonStrength d lam r*r)
    ((laplaceComparisonStrength_contDiff d lam).continuous.mul continuous_id) hmstrength.2 α
  refine ⟨?_,by simpa only [zero_add] using hqmono,?_,?_⟩
  · intro u hu v hv huv
    exact sub_le_sub (hb hu hv huv) (heanti hu hv huv)
  · rw [fullMassCoefficient_eq zero_le_one hc hk hkc hm hM _ _ α (by norm_num)]
    exact sub_nonneg.mpr ((laplaceComparisonStrength_le d hlam _).trans hlb)
  · simp only [zero_add]
    rw [fullMassCoefficient_eq zero_le_one hc hk hkc hm hM _ _ α (by norm_num)]
    exact mul_nonneg (laplaceComparisonStrength_nonneg d _ hlam)
      (constrainedQuantile zero_le_one hc hk hkc hm hM α ⟨0,by norm_num⟩).property.1

theorem comparisonSweep_inverse_pair_eq (n : ℕ) (hn : 0<n) (b : ℝ → ℝ)
    {d lam : ℝ} (hd : d≠0) (hlam : 0≤lam) (hlb : lam≤b 0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (α : inverseIntegralConstraints 0 0 k M)
    (P : Spin n → Spin n → ℝ) {u : ℝ} (hu : u∈Ioc (0:ℝ) 1) :
    let g := laplaceComparisonStrength d lam
    let hg := (laplaceComparisonStrength_contDiff d lam).continuous
    let e := omittedExtension zero_le_one
      (constrainedCoefficient zero_le_one hc hk hkc hm hM g hg α)
    let q := omittedExtension zero_le_one
      (constrainedCoefficient zero_le_one hc hk hkc hm hM (fun r=>g r*r) (hg.mul continuous_id) α)
    let R := comparisonSweepQuantile hc hk hkc hm hM α
    orderedPathPair n (fun v=>(b v-e v).toNNReal) (fun v=>(0+q v).toNNReal) P u=
      orderedPathPair n (fun v=>(b v-g (R v)).toNNReal) (fun v=>(g (R v)*R v).toNNReal) P u := by
  dsimp only
  have ha := comparisonSweep_inverse_clocks_admissible hc hk hkc hm hM b hd hlam hlb hb α
  have ha' := strengthSweep_clocks_admissible b _ hd hlam hlb hb
    ((comparisonSweepQuantile_monotone hc hk hkc hm hM α).monotoneOn _)
    (fun v _=>comparisonSweepQuantile_bounds hc hk hkc hm hM α v)
  apply orderedPathPair_clock_congr n hn _ _ _ _
    (toNNReal_monotoneOn ha.1) (toNNReal_monotoneOn ha.2.1)
    (toNNReal_monotoneOn ha'.1) (toNNReal_monotoneOn ha'.2.1) _ P hu
  intro v hv
  rw [fullMassCoefficient_eq_sweepQuantile hc hk hkc hm hM _ _ α hv,
    fullMassCoefficient_eq_sweepQuantile hc hk hkc hm hM _ _ α hv]
  simp only [zero_add]
  constructor <;> trivial
end

theorem exists_concrete_comparison_optimizer_potential
    {N δ U L E d lam : ℝ} (hN : 0<N) (hU : 0<U) (hL : 0<L)
    (hLU : L≤U) (hE : 0<E) (hd : 0<d) (hq : 2≤N^δ) (hlam : 0<lam)
    (b : ℝ → ℝ) (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hlb : lam≤b 0)
    (n : ℕ) (hn : 0<n) :
    let k := comparisonFloor N δ U
    let M := comparisonCap N δ U L E d
    let c := k 1
    let hc : 0<c := comparisonFloor_pos hN hU (by norm_num)
    let hk := comparisonFloor_continuousOn (δ:=δ) hN hU (r₀:=0) le_rfl
    let hkc := fun r (hr : r∈Icc (0:ℝ) 1)=>comparisonFloor_lower_on (δ:=δ) hN hU le_rfl hr
    let hm := comparisonCap_monotoneOn (δ:=δ) hN hU.le hL hE hd.le
    let hM := comparisonCap_nonneg (δ:=δ) hN hU.le hL hE hd.le zero_le_one
    let g := laplaceComparisonStrength d lam
    ∃ (α : inverseIntegralConstraints 0 0 k M) (H : ℝ → ℝ),
      comparisonSweepObjective hc hk hkc hm hM n b d lam α=
        comparisonSweepMinimum hc hk hkc hm hM n b d lam ∧
      let R := comparisonSweepQuantile hc hk hkc hm hM α
      let bf := fun u=>(b u-g (R u)).toNNReal
      let hf := fun u=>(g (R u)*R u).toNNReal
      let S := orderedPathS n bf hf
      let B := orderedPathB n bf hf
      let J := inverseControlFactor 0 (fun r=>inverseControlWeight α.val.val k M r*
        comparisonCapSlope N δ U L E d (α.val.val r))
      AbsolutelyContinuousOnInterval H 0 1 ∧
      (∀ᵐ r,r∈Icc (0:ℝ) 1→HasDerivAt H
        (J r*radiusComparisonGradient g α.val.val S B r) r) ∧
      (∀ᵐ r,r∈Icc (0:ℝ) 1→
        (H r<0→deriv α.val.val r=M (α.val.val r)) ∧
        (0<H r→deriv α.val.val r=k r)) ∧
      (∀ᵐ r,r∈Icc (0:ℝ) 1→H r=0→
        radiusComparisonGradient g α.val.val S B r=0 ∧
        S (α.val.val r)≤r ∧
        (S (α.val.val r)-r)^2≤B (α.val.val r)-(S (α.val.val r))^2) := by
  dsimp only
  let k := comparisonFloor N δ U
  let M := comparisonCap N δ U L E d
  have hc : 0<k 1 := comparisonFloor_pos hN hU (by norm_num)
  have hk : ContinuousOn k (Icc (0:ℝ) 1) := comparisonFloor_continuousOn (δ:=δ) hN hU le_rfl
  have hkc : ∀ r∈Icc (0:ℝ) 1,k 1≤k r := fun r hr=>comparisonFloor_lower_on (δ:=δ) hN hU le_rfl hr
  have hm : MonotoneOn M (Icc (0:ℝ) 1) := comparisonCap_monotoneOn (δ:=δ) hN hU.le hL hE hd.le
  have hM : 0≤M 1 := comparisonCap_nonneg (δ:=δ) hN hU.le hL hE hd.le zero_le_one
  have hMc : Continuous M := comparisonCap_continuous N δ U L E d
  have hne : (inverseDifferentialConstraints 0 0 k M).Nonempty :=
    comparisonConstraints_nonempty hN hU hL hLU hE hd.le hq (by norm_num) (by norm_num)
  rw [inverseDifferentialConstraints_eq 0 0 zero_le_one k M hk hMc hm hM] at hne
  obtain ⟨α,hα,hmin⟩ := comparisonSweepMinimum_attained hc hk hkc hm hM n hn b hd.ne'
    hlam.le hlb hb hMc hne
  have hfeas (β) := comparisonSweep_inverse_clocks_admissible hc hk hkc hm hM b hd.ne' hlam.le hlb hb β
  have hmini (β) : inverseCompensatedPressure zero_le_one zero_le_one hc hk hkc hm hM
      (laplaceComparisonStrength d lam) (laplaceComparisonStrength_contDiff d lam).continuous
      n b (fun _=>0) 0 α ≤ inverseCompensatedPressure zero_le_one zero_le_one hc hk hkc hm hM
      (laplaceComparisonStrength d lam) (laplaceComparisonStrength_contDiff d lam).continuous
      n b (fun _=>0) 0 β := by
    rw [← comparisonSweepObjective_eq_inverse hc hk hkc hm hM n hn b hd.ne' hlam.le hlb hb α,
      ← comparisonSweepObjective_eq_inverse hc hk hkc hm hM n hn b hd.ne' hlam.le hlb hb β,hα]
    exact hmin β
  obtain ⟨H,hH,hD,hbang,hzero⟩ := comparison_minimum_contact_potential hN hU hL hLU hE hd.le
    hq (by norm_num : (0:ℝ)∈Icc (0:ℝ) (1/4)) (by norm_num : (0:ℝ)∈Icc (0:ℝ) (1/4))
    n hn (laplaceComparisonStrength d lam) α (laplaceComparisonStrength_contDiff d lam)
    (fun r _=>laplaceComparisonStrength_pos d hlam r)
    (fun r _=>⟨(laplaceComparisonStrength_logSlope_mem hd.ne' hlam.ne' r).1,
      (laplaceComparisonStrength_logSlope_mem hd.ne' hlam.ne' r).2.le⟩)
    b (fun _=>0) (fun β=>(hfeas β).1) (fun β=>(hfeas β).2.1)
    (fun β=>(hfeas β).2.2.1) (fun β=>(hfeas β).2.2.2) hmini
  have hstrict := inverseConstraint_strictMonoOn hc hk hkc α.property
  have hαpos (r : ℝ) (hr : r∈Ioc (0:ℝ) 1) : α.val.val r∈Ioc (0:ℝ) 1 := by
    have hh := hstrict (by norm_num) ⟨hr.1.le,hr.2⟩ hr.1
    rw [α.property.1] at hh
    exact ⟨hh,(α.val.property.1 r).2⟩
  have hpair (P) (r : ℝ) (hr : r∈Ioc (0:ℝ) 1) :=
    comparisonSweep_inverse_pair_eq hc hk hkc hm hM n hn b hd.ne' hlam.le hlb hb α P (hαpos r hr)
  refine ⟨α,H,hα,hH,?_,hbang,?_⟩
  · filter_upwards [hD,volume.ae_ne (0:ℝ)] with r hdr hr0 hr
    have hr' : r∈Ioc (0:ℝ) 1 := ⟨lt_of_le_of_ne hr.1 hr0.symm,hr.2⟩
    have hs := hpair (orderedOverlap n) r hr'
    have hb2 := hpair (fun σ τ=>(orderedOverlap n σ τ)^2) r hr'
    have hh := hdr hr
    simpa only [radiusComparisonGradient,orderedPathS,orderedPathB,hs,hb2] using hh
  · filter_upwards [hzero,volume.ae_ne (0:ℝ)] with r hz hr0 hr hHr
    have hr' : r∈Ioc (0:ℝ) 1 := ⟨lt_of_le_of_ne hr.1 hr0.symm,hr.2⟩
    have hs := hpair (orderedOverlap n) r hr'
    have hb2 := hpair (fun σ τ=>(orderedOverlap n σ τ)^2) r hr'
    have hh := hz hr hHr
    simpa only [radiusComparisonGradient,orderedPathS,orderedPathB,hs,hb2] using hh

end OAI.SKFluctuations.LaplaceWindowFormalization
