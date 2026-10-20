module

public import ComparisonPerturbedEndpointBand
public import ComparisonPhysicalGeometry

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal

section
variable {c : ℝ} {k M : ℝ → ℝ}
variable (hc : 0<c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r∈Icc (0:ℝ) 1,c≤k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0≤M 1)

theorem comparisonVariableEndpoint_clocks_admissible (b h : ℝ→ℝ)
    {d lam : ℝ} (hd : d≠0) (hlam : 0≤lam) (hlb : lam≤b 0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (hh0 : 0≤h 0) (α : inverseIntegralConstraints 0 0 k M) :
    let R := comparisonSweepQuantile hc hk hkc hm hM α
    comparisonClockAdmissible b h (fun u=>laplaceComparisonStrength d lam (R u)) R := by
  dsimp only
  have ha := strengthSweep_clocks_admissible b (comparisonSweepQuantile hc hk hkc hm hM α)
    hd hlam hlb hb ((comparisonSweepQuantile_monotone hc hk hkc hm hM α).monotoneOn _)
    (fun u _=>comparisonSweepQuantile_bounds hc hk hkc hm hM α u)
  exact ⟨ha.1,hh.add ha.2.1,ha.2.2.1 0 (by norm_num),
    add_nonneg hh0 (ha.2.2.2 0 (by norm_num))⟩

theorem comparisonVariableEndpoint_inverse_clocks_admissible (b h : ℝ→ℝ)
    {d lam : ℝ} (hd : d≠0) (hlam : 0≤lam) (hlb : lam≤b 0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (hh0 : 0≤h 0) (α : inverseIntegralConstraints 0 0 k M) :
    let g := laplaceComparisonStrength d lam
    let hg := (laplaceComparisonStrength_contDiff d lam).continuous
    let e := omittedExtension zero_le_one
      (constrainedCoefficient zero_le_one hc hk hkc hm hM g hg α)
    let q := omittedExtension zero_le_one
      (constrainedCoefficient zero_le_one hc hk hkc hm hM (fun r=>g r*r) (hg.mul continuous_id) α)
    MonotoneOn (fun u=>b u-e u) (Icc (0:ℝ) 1) ∧
      MonotoneOn (fun u=>h u+q u) (Icc (0:ℝ) 1) ∧
      0≤b 0-e 0 ∧ 0≤h 0+q 0 := by
  dsimp only
  have ha := comparisonSweep_inverse_clocks_admissible hc hk hkc hm hM b hd hlam hlb hb α
  have hq := ha.2.1
  have hq0 := ha.2.2.2
  simp only [zero_add] at hq hq0
  exact ⟨ha.1,hh.add hq,ha.2.2.1,add_nonneg hh0 hq0⟩

theorem comparisonVariableEndpoint_inverse_pair_eq (n : ℕ) (hn : 0<n) (b h : ℝ→ℝ)
    {d lam : ℝ} (hd : d≠0) (hlam : 0≤lam) (hlb : lam≤b 0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (hh0 : 0≤h 0) (α : inverseIntegralConstraints 0 0 k M)
    (P : Spin n→Spin n→ℝ) {u : ℝ} (hu : u∈Ioc (0:ℝ) 1) :
    let g := laplaceComparisonStrength d lam
    let hg := (laplaceComparisonStrength_contDiff d lam).continuous
    let e := omittedExtension zero_le_one
      (constrainedCoefficient zero_le_one hc hk hkc hm hM g hg α)
    let q := omittedExtension zero_le_one
      (constrainedCoefficient zero_le_one hc hk hkc hm hM (fun r=>g r*r) (hg.mul continuous_id) α)
    let R := comparisonSweepQuantile hc hk hkc hm hM α
    orderedPathPair n (fun v=>(b v-e v).toNNReal) (fun v=>(h v+q v).toNNReal) P u=
      orderedPathPair n (fun v=>(b v-g (R v)).toNNReal) (fun v=>(h v+g (R v)*R v).toNNReal) P u := by
  dsimp only
  have ha := comparisonVariableEndpoint_inverse_clocks_admissible hc hk hkc hm hM
    b h hd hlam hlb hb hh hh0 α
  have ha' := comparisonVariableEndpoint_clocks_admissible hc hk hkc hm hM
    b h hd hlam hlb hb hh hh0 α
  apply orderedPathPair_clock_congr n hn _ _ _ _
    (toNNReal_monotoneOn ha.1) (toNNReal_monotoneOn ha.2.1)
    (toNNReal_monotoneOn ha'.1) (toNNReal_monotoneOn ha'.2.1) _ P hu
  intro v hv
  rw [fullMassCoefficient_eq_sweepQuantile hc hk hkc hm hM _ _ α hv,
    fullMassCoefficient_eq_sweepQuantile hc hk hkc hm hM _ _ α hv]
  constructor <;> trivial

theorem comparisonVariableEndpointObjective_eq_inverse (n : ℕ) (hn : 0<n) (b h : ℝ→ℝ)
    {d lam : ℝ} (hd : d≠0) (hlam : 0≤lam) (hlb : lam≤b 0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (hh0 : 0≤h 0) (α : inverseIntegralConstraints 0 0 k M) :
    comparisonVariableEndpointObjective hc hk hkc hm hM n b h d lam α=
      inverseCompensatedPressure zero_le_one zero_le_one hc hk hkc hm hM
        (laplaceComparisonStrength d lam) (laplaceComparisonStrength_contDiff d lam).continuous
        n b h 0 α := by
  let R := comparisonSweepQuantile hc hk hkc hm hM α
  let g := laplaceComparisonStrength d lam
  let hg := (laplaceComparisonStrength_contDiff d lam).continuous
  let e := omittedExtension zero_le_one
    (constrainedCoefficient zero_le_one hc hk hkc hm hM g hg α)
  let q := omittedExtension zero_le_one
    (constrainedCoefficient zero_le_one hc hk hkc hm hM (fun r=>g r*r) (hg.mul continuous_id) α)
  let p := omittedExtension zero_le_one
    (constrainedCoefficient zero_le_one hc hk hkc hm hM (fun r=>g r*r^2) (hg.mul (continuous_id.pow 2)) α)
  have he (u : ℝ) (hu : u∈Icc (0:ℝ) 1) : e u=g (R u) :=
    fullMassCoefficient_eq_sweepQuantile hc hk hkc hm hM g hg α hu
  have hq (u : ℝ) (hu : u∈Icc (0:ℝ) 1) : q u=g (R u)*R u :=
    fullMassCoefficient_eq_sweepQuantile hc hk hkc hm hM _ (hg.mul continuous_id) α hu
  have hp (u : ℝ) (hu : u∈Icc (0:ℝ) 1) : p u=g (R u)*(R u)^2 :=
    fullMassCoefficient_eq_sweepQuantile hc hk hkc hm hM _ (hg.mul (continuous_id.pow 2)) α hu
  have ha := comparisonVariableEndpoint_clocks_admissible hc hk hkc hm hM b h hd hlam hlb hb hh hh0 α
  have hai := comparisonVariableEndpoint_inverse_clocks_admissible hc hk hkc hm hM b h hd hlam hlb hb hh hh0 α
  have hpeq := realOrderedSKPathPressure_uniform_comparison n hn
    (fun u=>b u-g (R u)) (fun u=>h u+g (R u)*R u) (fun u=>b u-e u) (fun u=>h u+q u)
    ha.1 ha.2.1 hai.1 hai.2.1 ha.2.2.1 ha.2.2.2 hai.2.2.1 hai.2.2.2 (B:=0) (H:=0)
    (by intro u hu;rw [he u hu];simp) (by intro u hu;rw [hq u hu];simp) 0
  have hP : realOrderedSKPathPressure n (fun u=>b u-g (R u)) (fun u=>h u+g (R u)*R u) 0=
      realOrderedSKPathPressure n (fun u=>b u-e u) (fun u=>h u+q u) 0 := by
    apply sub_eq_zero.mp
    exact abs_eq_zero.mp (le_antisymm (by simpa using hpeq) (abs_nonneg _))
  change realOrderedSKPathPressure n (fun u=>b u-g (R u)) (fun u=>h u+g (R u)*R u) 0+
      (1/4:ℝ)*(∫u in (0:ℝ)..1,g (R u)*(R u)^2)=
    realOrderedSKPathPressure n (fun u=>b u-e u) (fun u=>h u+q u) 0+
      (1/4:ℝ)*(∫u in (0:ℝ)..1,p u)
  rw [hP]
  congr 2
  apply intervalIntegral.integral_congr
  intro u hu
  exact (hp u (by simpa only [uIcc_of_le zero_le_one] using hu)).symm

theorem comparisonVariableEndpointMinimum_attained (n : ℕ) (hn : 0<n) (b h : ℝ→ℝ)
    {d lam : ℝ} (hd : d≠0) (hlam : 0≤lam) (hlb : lam≤b 0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (hh0 : 0≤h 0) (hMc : Continuous M) (hne : (inverseIntegralConstraints 0 0 k M).Nonempty) :
    ∃α:inverseIntegralConstraints 0 0 k M,∀γ:inverseIntegralConstraints 0 0 k M,
      comparisonVariableEndpointObjective hc hk hkc hm hM n b h d lam α≤
        comparisonVariableEndpointObjective hc hk hkc hm hM n b h d lam γ := by
  have hfeas γ := comparisonVariableEndpoint_inverse_clocks_admissible hc hk hkc hm hM
    b h hd hlam hlb hb hh hh0 γ
  obtain ⟨α,hα⟩ := inverseCompensatedPressure_minimum zero_le_one zero_le_one hc hk hkc hm hM
    (laplaceComparisonStrength d lam) (laplaceComparisonStrength_contDiff d lam).continuous
    hMc hne n hn b h (fun γ=>(hfeas γ).1) (fun γ=>(hfeas γ).2.1)
    (fun γ=>(hfeas γ).2.2.1) (fun γ=>(hfeas γ).2.2.2) 0
  refine ⟨α,fun γ=>?_⟩
  rw [comparisonVariableEndpointObjective_eq_inverse hc hk hkc hm hM n hn b h hd hlam hlb hb hh hh0 α,
    comparisonVariableEndpointObjective_eq_inverse hc hk hkc hm hM n hn b h hd hlam hlb hb hh hh0 γ]
  exact hα γ

theorem comparisonVariableEndpoint_radius_moments (n : ℕ) (hn : 0<n) (b h : ℝ → ℝ)
    {d lam : ℝ} (hd : d≠0) (hlam : 0≤lam) (hlb : lam≤b 0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (hh0 : 0≤h 0) (α : inverseIntegralConstraints 0 0 k M) :
    let R := comparisonSweepQuantile hc hk hkc hm hM α
    let bf := fun u=>(b u-laplaceComparisonStrength d lam (R u)).toNNReal
    let hf := fun u=>(h u+laplaceComparisonStrength d lam (R u)*R u).toNNReal
    let S := fun r=>orderedPathS n bf hf (α.val.val r)
    let B := fun r=>orderedPathB n bf hf (α.val.val r)
    MonotoneOn S (Icc (0:ℝ) 1) ∧ MonotoneOn B (Icc (0:ℝ) 1) ∧
      (∀ r∈Icc (0:ℝ) 1,S r∈Icc (0:ℝ) 1 ∧ B r∈Icc ((S r)^2) 1) := by
  dsimp only
  let R := comparisonSweepQuantile hc hk hkc hm hM α
  let bf := fun u=>(b u-laplaceComparisonStrength d lam (R u)).toNNReal
  let hf := fun u=>(h u+laplaceComparisonStrength d lam (R u)*R u).toNNReal
  have ha := comparisonVariableEndpoint_clocks_admissible hc hk hkc hm hM
    b h hd hlam hlb hb hh hh0 α
  have hbf := toNNReal_monotoneOn ha.1
  have hhf := toNNReal_monotoneOn ha.2.1
  have hstrict := inverseConstraint_strictMonoOn hc hk hkc α.property
  have hpos (r : ℝ) (hr : r∈Ioc (0:ℝ) 1) : α.val.val r∈Ioc (0:ℝ) 1 := by
    have hs := hstrict (by norm_num) ⟨hr.1.le,hr.2⟩ hr.1
    rw [α.property.1] at hs
    exact ⟨hs,(α.val.property.1 r).2⟩
  have hbounds (r : ℝ) (hr : r∈Icc (0:ℝ) 1) :
      orderedPathS n bf hf (α.val.val r)∈Icc (0:ℝ) 1 ∧
      orderedPathB n bf hf (α.val.val r)∈Icc ((orderedPathS n bf hf (α.val.val r))^2) 1 := by
    by_cases hr0 : r=0
    · subst r
      rw [α.property.1]
      simp only [orderedPathS,orderedPathB,orderedPathPair_zero]
      norm_num
    · have hs := orderedPath_SK_bounds n hn bf hf hbf hhf
        (hpos r ⟨lt_of_le_of_ne hr.1 (Ne.symm hr0),hr.2⟩)
      exact ⟨⟨hs.1,hs.2.1⟩,⟨hs.2.2.1,hs.2.2.2⟩⟩
  refine ⟨?_,?_,hbounds⟩
  · intro r hr t ht hrt
    by_cases hr0 : r=0
    · subst r
      change orderedPathS n bf hf (α.val.val 0)≤orderedPathS n bf hf (α.val.val t)
      rw [α.property.1]
      simp only [orderedPathS,orderedPathPair_zero]
      exact (hbounds t ht).1.1
    · exact (orderedPath_SK_monotone n hn bf hf hbf hhf).1
        (hpos r ⟨lt_of_le_of_ne hr.1 (Ne.symm hr0),hr.2⟩)
        (hpos t ⟨lt_of_lt_of_le (lt_of_le_of_ne hr.1 (Ne.symm hr0)) hrt,ht.2⟩)
        (α.val.property.2 hrt)
  · intro r hr t ht hrt
    by_cases hr0 : r=0
    · subst r
      change orderedPathB n bf hf (α.val.val 0)≤orderedPathB n bf hf (α.val.val t)
      rw [α.property.1]
      simp only [orderedPathB,orderedPathPair_zero]
      exact (sq_nonneg _).trans (hbounds t ht).2.1
    · exact (orderedPath_SK_monotone n hn bf hf hbf hhf).2
        (hpos r ⟨lt_of_le_of_ne hr.1 (Ne.symm hr0),hr.2⟩)
        (hpos t ⟨lt_of_lt_of_le (lt_of_le_of_ne hr.1 (Ne.symm hr0)) hrt,ht.2⟩)
        (α.val.property.2 hrt)
end

theorem exists_concrete_variableEndpoint_optimizer_potential
    {N δ U L E d lam : ℝ} (hN : 0<N) (hU : 0<U) (hL : 0<L)
    (hLU : L≤U) (hE : 0<E) (hd : 0<d) (hq : 2≤N^δ) (hlam : 0<lam)
    (b h : ℝ → ℝ) (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hlb : lam≤b 0)
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0≤h 0)
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
      (∀γ:inverseIntegralConstraints 0 0 k M,
        comparisonVariableEndpointObjective hc hk hkc hm hM n b h d lam α≤
          comparisonVariableEndpointObjective hc hk hkc hm hM n b h d lam γ) ∧
      let R := comparisonSweepQuantile hc hk hkc hm hM α
      let bf := fun u=>(b u-g (R u)).toNNReal
      let hf := fun u=>(h u+g (R u)*R u).toNNReal
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
  obtain ⟨α,hmin⟩ := comparisonVariableEndpointMinimum_attained hc hk hkc hm hM n hn b h hd.ne'
    hlam.le hlb hb hh hh0 hMc hne
  have hfeas (β) := comparisonVariableEndpoint_inverse_clocks_admissible hc hk hkc hm hM
    b h hd.ne' hlam.le hlb hb hh hh0 β
  have hmini (β) : inverseCompensatedPressure zero_le_one zero_le_one hc hk hkc hm hM
      (laplaceComparisonStrength d lam) (laplaceComparisonStrength_contDiff d lam).continuous
      n b h 0 α ≤ inverseCompensatedPressure zero_le_one zero_le_one hc hk hkc hm hM
      (laplaceComparisonStrength d lam) (laplaceComparisonStrength_contDiff d lam).continuous
      n b h 0 β := by
    rw [← comparisonVariableEndpointObjective_eq_inverse hc hk hkc hm hM n hn b h hd.ne' hlam.le hlb hb hh hh0 α,
      ← comparisonVariableEndpointObjective_eq_inverse hc hk hkc hm hM n hn b h hd.ne' hlam.le hlb hb hh hh0 β]
    exact hmin β
  obtain ⟨H,hH,hD,hbang,hzero⟩ := comparison_minimum_contact_potential hN hU hL hLU hE hd.le
    hq (by norm_num : (0:ℝ)∈Icc (0:ℝ) (1/4)) (by norm_num : (0:ℝ)∈Icc (0:ℝ) (1/4))
    n hn (laplaceComparisonStrength d lam) α (laplaceComparisonStrength_contDiff d lam)
    (fun r _=>laplaceComparisonStrength_pos d hlam r)
    (fun r _=>⟨(laplaceComparisonStrength_logSlope_mem hd.ne' hlam.ne' r).1,
      (laplaceComparisonStrength_logSlope_mem hd.ne' hlam.ne' r).2.le⟩)
    b h (fun β=>(hfeas β).1) (fun β=>(hfeas β).2.1)
    (fun β=>(hfeas β).2.2.1) (fun β=>(hfeas β).2.2.2) hmini
  have hstrict := inverseConstraint_strictMonoOn hc hk hkc α.property
  have hαpos (r : ℝ) (hr : r∈Ioc (0:ℝ) 1) : α.val.val r∈Ioc (0:ℝ) 1 := by
    have hh := hstrict (by norm_num) ⟨hr.1.le,hr.2⟩ hr.1
    rw [α.property.1] at hh
    exact ⟨hh,(α.val.property.1 r).2⟩
  have hpair (P) (r : ℝ) (hr : r∈Ioc (0:ℝ) 1) :=
    comparisonVariableEndpoint_inverse_pair_eq hc hk hkc hm hM n hn b h hd.ne' hlam.le hlb hb hh hh0 α P (hαpos r hr)
  refine ⟨α,H,hmin,hH,?_,hbang,?_⟩
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
