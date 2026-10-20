module

public import ComparisonNativeOverlapRawAmplitude
public import CavityActualLowRawMoments
public import SKFluctuationsOAI.Probability.SKFluctuations.ComparisonMinimumRealOverlapConclusion

@[expose] public section

noncomputable section
set_option maxHeartbeats 5000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

theorem eventually_actual_minimum_overlap_natural_moment
    (ell : ℕ) (Bclock : ℝ) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0 ≤ Az) (hC0 : 0<C0) (hCt : 0 ≤ Ct) :
    ∃ K : ℝ,0<K ∧ ∀ᶠ n : ℕ in atTop,
      ∀ a : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock,
      ∀ u∈Ioc (0:ℝ) 1,
        pathPairMoment (uniformWeight n) (finiteFeature n) (completedPathClock n a.bf a.hf)
          (fun σ τ=>|orderedOverlap n σ τ|^(2*(ell+1))) u ≤ K*(a.xs+u)^(2*(ell+1)) := by
  obtain ⟨K,hK,hamp⟩ := comparison_minimum_retained_overlap_moment_normalized
    (D:=D) ell Bclock hm hdelta hroom hcl hcu hAz (by norm_num : (0:ℝ)<1/3) hC0 hCt
  have hlog : ∀ᶠ n : ℕ in atTop,1 ≤ Real.log (n:ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)
  refine ⟨K,hK,?_⟩
  filter_upwards [hamp,eventually_comparisonLowerScale_depth hC0 hm,hlog,eventually_ge_atTop (1:ℕ)]
    with n hnamp hndepth hnlog hn1
  intro a u hu
  let c := a.context
  have hN1 : (1:ℝ) ≤ c.N := by exact_mod_cast hn1
  have hnd : 1/c.N ≤ c.d := by
    have H := hndepth c.E c.d c.hE c.hd a.hlower
    have hscale : comparisonLowerScale n c.E c.d ≤ c.d := by
      unfold comparisonLowerScale
      exact (div_le_iff₀ c.hd).mpr (by simpa only [pow_two] using a.hupper)
    exact H.trans hscale
  let g := laplaceComparisonStrength c.d a.lam
  let hg := (laplaceComparisonStrength_contDiff c.d a.lam).continuous
  let ie := omittedExtension zero_le_one
    (constrainedCoefficient zero_le_one c.hc c.hk c.hkc c.hm c.hM g hg a.alpha)
  let iq := omittedExtension zero_le_one
    (constrainedCoefficient zero_le_one c.hc c.hk c.hkc c.hm c.hM (fun r=>g r*r)
      (hg.mul continuous_id) a.alpha)
  let bi := fun v=>(a.b v-ie v).toNNReal
  let hi := fun v=>(a.h v+iq v).toNNReal
  have had β := comparisonVariableEndpoint_inverse_clocks_admissible c.hc c.hk c.hkc c.hm c.hM
    a.b a.h c.hd.ne' a.hlam.le a.hlb a.hb a.hh a.hh0 β
  have hmin : ∀ β:c.Profile,
      inverseCompensatedPressure zero_le_one zero_le_one c.hc c.hk c.hkc c.hm c.hM
        g hg n a.b a.h 0 a.alpha ≤
      inverseCompensatedPressure zero_le_one zero_le_one c.hc c.hk c.hkc c.hm c.hM
        g hg n a.b a.h 0 β := by
    intro β
    have H := a.minimum β
    rw [comparisonVariableEndpointObjective_eq_inverse c.hc c.hk c.hkc c.hm c.hM n c.hn
        a.b a.h c.hd.ne' a.hlam.le a.hlb a.hb a.hh a.hh0 a.alpha,
      comparisonVariableEndpointObjective_eq_inverse c.hc c.hk c.hkc c.hm c.hM n c.hn
        a.b a.h c.hd.ne' a.hlam.le a.hlb a.hb a.hh a.hh0 β] at H
    exact H
  have hslow : ∀ r∈Icc a.z 1,(1/3)/Real.log (n:ℝ) ≤ 1-comparisonLogSlope g r := by
    intro r hr
    exact laplaceComparisonStrength_uniform_slope hN1 hnlog c.hd hnd a.hlam a.hld
      (Icc_subset_Icc a.hz.1 le_rfl hr)
  have hclock : (hi 1:ℝ)-(hi 0:ℝ) ≤ Bclock := by
    dsimp [hi,iq]
    rw [fullMassCoefficient_eq_sweepQuantile c.hc c.hk c.hkc c.hm c.hM _ _ a.alpha
        (show (1:ℝ)∈Icc (0:ℝ) 1 by simp),
      fullMassCoefficient_eq_sweepQuantile c.hc c.hk c.hkc c.hm c.hM _ _ a.alpha
        (show (0:ℝ)∈Icc (0:ℝ) 1 by simp)]
    exact a.clockBudget
  let up : PositiveMass := ⟨u,hu.1⟩
  have hbMono : MonotoneOn bi (Icc (0:ℝ) 1) := toNNReal_monotoneOn (had a.alpha).1
  have hhMono : MonotoneOn hi (Icc (0:ℝ) 1) := toNNReal_monotoneOn (had a.alpha).2.1
  have hpoint := hnamp c.hn c.hE c.hd (by norm_num : (0:ℝ)∈Icc (0:ℝ) (1/4))
    (by norm_num : (0:ℝ)∈Icc (0:ℝ) (1/4)) g a.alpha
    (laplaceComparisonStrength_contDiff _ _) (fun r _=>laplaceComparisonStrength_pos c.d a.hlam r)
    (fun r _=>by
      have hp := laplaceComparisonStrength_logSlope_mem c.hd.ne' a.hlam.ne' r
      exact ⟨hp.1,hp.2.le⟩)
    a.b a.h (fun β=>(had β).1) (fun β=>(had β).2.1)
    (fun β=>(had β).2.2.1) (fun β=>(had β).2.2.2) hmin up hu.2 a.xs a.z
    a.hxs a.hscale a.hxs.le c.hU.le a.hz a.hzxs a.hdD a.hupper a.hlower a.htest
    a.regular hslow a.hh hclock
  let P := fun σ τ:Spin n=>|orderedOverlap n σ τ|^(2*(ell+1))
  have hpInv := orderedPathPair_eq_completed n c.hn bi hi hbMono hhMono P hu
  rw [←hpInv,comparisonVariableEndpoint_inverse_pair_eq c.hc c.hk c.hkc c.hm c.hM
    n c.hn a.b a.h c.hd.ne' a.hlam.le a.hlb a.hb a.hh a.hh0 a.alpha P hu] at hpoint
  have ha := comparisonVariableEndpoint_clocks_admissible c.hc c.hk c.hkc c.hm c.hM
    a.b a.h c.hd.ne' a.hlam.le a.hlb a.hb a.hh a.hh0 a.alpha
  have hpActual := orderedPathPair_eq_completed n c.hn a.bf a.hf
    (toNNReal_monotoneOn ha.1) (toNNReal_monotoneOn ha.2.1) P hu
  rw [hpActual] at hpoint
  exact hpoint

theorem actual_mass_net_upper_cover {a mesh u : ℝ} (as : List PositiveMass)
    (ho : MassOrdered a as) (hm : PartitionMesh mesh a as)
    (hend : partitionEnd a as=1) (ha : a<1) (hu : u∈Icc a 1) :
    ∃ v : PositiveMass,v∈as ∧ u ≤ v.val ∧ v.val ≤ u+mesh := by
  induction as generalizing a with
  | nil => change a=1 at hend; linarith
  | cons v as ih =>
    by_cases huv : u ≤ v.val
    · refine ⟨v,List.mem_cons_self,huv,?_⟩
      have H := hm.1
      linarith [hu.1]
    · have hvu : v.val<u := lt_of_not_ge huv
      obtain ⟨w,hw,huv',hwu⟩ := ih ho.2.2 hm.2 hend
        (hvu.trans_le hu.2) ⟨hvu.le,hu.2⟩
      exact ⟨w,List.mem_cons_of_mem v hw,huv',hwu⟩

theorem actual_index_le_retained_split {ι : Type} [Fintype ι]
    (steps : List (GaussianStep ι)) {a : ℝ} (ho : OrderedSteps a steps)
    {j : ℕ} (hj : j ≤ steps.length) {u : ℝ}
    (hmass : physicalCutMass a steps j ≤ u) :
    j ≤ (splitClockSteps u steps).1.length := by
  induction steps generalizing a j with
  | nil => simp only [List.length_nil] at hj; omega
  | cons st steps ih =>
    cases j with
    | zero => exact Nat.zero_le _
    | succ j =>
      have H := (physicalCutMass_monotone steps ho.2.2.2 (Nat.zero_le j)).trans hmass
      simp only [physicalCutMass] at H
      rw [splitClockSteps,ite_eq_left H,List.length_cons]
      exact Nat.succ_le_succ (ih ho.2.2.2 (by simpa using hj) hmass)

theorem actual_retained_overlap_net_eventually (n l : ℕ) (hn : 0<n)
    (b h : ℝ→ℝ≥0) (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (us net : List PositiveMass) (hu : ∀ u∈us,u.val ≤ 1)
    (hnet : ∀ u∈net,u∈us) (bound : PositiveMass→ℝ)
    (hbound : ∀ u∈net,
      pathPairMoment (uniformWeight n) (finiteFeature n) (completedPathClock n b h)
        (fun σ τ=>|orderedOverlap n σ τ|^(2*l)) u.val<bound u) :
    ∀ᶠ k : ℕ in atTop,∀ u∈net,
      let q := completedPathClock n b h
      let steps := sampleClockSteps q 0 (finiteCutMasses us k)
      physicalOverlapMoment n l steps (Measure.pi fun i=>gaussianReal 0 (q 0 i))
        id measurable_id (splitClockSteps u.val steps).1.length ≤ bound u := by
  classical
  have hp (u : PositiveMass) (hui : u∈net) :=
    (physicalRetainedOverlapMoment_tendsto n l hn b h hb hh
      (finiteCutMasses us) (fun k=>(((k+1:ℕ):ℝ)⁻¹))
      (finiteCutMasses_ordered us hu) (finiteCutMasses_mesh us hu)
      (finiteCutMasses_end us hu) uniformMasses_mesh_tendsto
      u (hu u (hnet u hui)) (fun k=>finiteCutMasses_nodes us k (hnet u hui))).eventually
      (gt_mem_nhds (hbound u hui))
  have H : ∀ᶠ k : ℕ in atTop,∀ u∈(net.toFinset : Set PositiveMass),
      let q := completedPathClock n b h
      let steps := sampleClockSteps q 0 (finiteCutMasses us k)
      physicalOverlapMoment n l steps (Measure.pi fun i=>gaussianReal 0 (q 0 i))
        id measurable_id (splitClockSteps u.val steps).1.length<bound u :=
    (eventually_all_finite net.toFinset.finite_toSet).mpr (by
      intro u hui
      exact hp u (List.mem_toFinset.mp hui))
  filter_upwards [H] with k hk
  intro u hui
  exact (hk u (List.mem_toFinset.mpr hui)).le

theorem actual_finite_overlap_natural_calibration_on_retained_net
    (n l : ℕ) (hn : 0<n) (b h : ℝ→ℝ≥0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (L : ℕ) (us : List PositiveMass) (hus : ∀ u∈us,u.val ≤ 1)
    (hretained : ∀ u∈uniformMasses L,u∈us)
    {xs K : ℝ} (hxs : 0<xs) (hK : 0<K) (hstep : ((L+1:ℕ):ℝ)⁻¹ ≤ xs)
    (hamp : ∀ u∈Ioc (0:ℝ) 1,
      pathPairMoment (uniformWeight n) (finiteFeature n) (completedPathClock n b h)
        (fun σ τ=>|orderedOverlap n σ τ|^(2*l)) u ≤ K*(xs+u)^(2*l)) :
    ∀ᶠ k : ℕ in atTop,
      let q := completedPathClock n b h
      let as := finiteCutMasses us k
      let steps := sampleClockSteps q 0 as
      ∀ j ≤ as.length,
        physicalOverlapMoment n l steps (Measure.pi fun i=>gaussianReal 0 (q 0 i))
          id measurable_id j ≤ (2*K*(2:ℝ)^(2*l))*(xs+physicalCutMass 0 steps j)^(2*l) := by
  let net := uniformMasses L
  have hnet : ∀ u∈net,u.val ≤ 1 := (uniformMasses_ordered L).members_le_one
  have hnetbound (u : PositiveMass) (hui : u∈net) :
      pathPairMoment (uniformWeight n) (finiteFeature n) (completedPathClock n b h)
        (fun σ τ=>|orderedOverlap n σ τ|^(2*l)) u.val<2*K*(xs+u.val)^(2*l) := by
    apply lt_of_le_of_lt (hamp u.val ⟨u.property,hnet u hui⟩)
    have hpow : 0<(xs+u.val)^(2*l) := pow_pos (add_pos hxs u.property) _
    nlinarith
  have H := actual_retained_overlap_net_eventually n l hn b h hb hh us net hus
    hretained (fun u=>2*K*(xs+u.val)^(2*l)) hnetbound
  filter_upwards [H] with k hk
  dsimp only
  intro j hj
  let q := completedPathClock n b h
  let as := finiteCutMasses us k
  let steps := sampleClockSteps q 0 as
  have ho : MassOrdered 0 as := finiteCutMasses_ordered us hus k
  have hs : OrderedSteps 0 steps := sampleClockSteps_ordered q as ho
  have hu := physicalCutMass_mem steps hs j
  obtain ⟨v,hv,hjv,hvupper⟩ := actual_mass_net_upper_cover net
    (uniformMasses_ordered L) (uniformMasses_mesh L) (uniformMasses_end L)
    (by norm_num : (0:ℝ)<1) hu
  have hjs : j ≤ steps.length := by simpa only [steps,sampleClockSteps_length] using hj
  have hidx := actual_index_le_retained_split steps hs hjs hjv
  have hmono := physicalOverlapMoment_mono n l steps hs (q 0) hidx
    (splitClockSteps_length_le steps v.val)
  apply hmono.trans
  have hbnd := hk v hv
  have hscale : xs+v.val ≤ 2*(xs+physicalCutMass 0 steps j) := by
    have hu0 := hu.1
    linarith
  have hsc := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (add_nonneg hxs.le v.property.le) hscale (2*l)) (by positivity : 0 ≤ 2*K)
  have hsc' : 2*K*(xs+v.val)^(2*l) ≤
      (2*K*(2:ℝ)^(2*l))*(xs+physicalCutMass 0 steps j)^(2*l) := by
    simpa only [mul_pow,mul_assoc] using hsc
  exact hbnd.trans hsc'

theorem exists_actual_finite_overlap_natural_calibration
    (n l : ℕ) (hn : 0<n) (b h : ℝ→ℝ≥0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (old : List PositiveMass) (hold : ∀ u∈old,u.val ≤ 1)
    {xs K : ℝ} (hxs : 0<xs) (hK : 0<K)
    (hamp : ∀ u∈Ioc (0:ℝ) 1,
      pathPairMoment (uniformWeight n) (finiteFeature n) (completedPathClock n b h)
        (fun σ τ=>|orderedOverlap n σ τ|^(2*l)) u ≤ K*(xs+u)^(2*l)) :
    ∃ us : List PositiveMass,(∀ u∈us,u.val ≤ 1) ∧ (∀ u∈old,u∈us) ∧
      ∀ᶠ k : ℕ in atTop,
        let q := completedPathClock n b h
        let as := finiteCutMasses us k
        let steps := sampleClockSteps q 0 as
        ∀ j ≤ as.length,
          physicalOverlapMoment n l steps (Measure.pi fun i=>gaussianReal 0 (q 0 i))
            id measurable_id j ≤ (2*K*(2:ℝ)^(2*l))*(xs+physicalCutMass 0 steps j)^(2*l) := by
  obtain ⟨L,hL⟩ := exists_nat_one_div_lt hxs
  let net := uniformMasses L
  let us := old++net
  have hnet : ∀ u∈net,u.val ≤ 1 := (uniformMasses_ordered L).members_le_one
  have hus : ∀ u∈us,u.val ≤ 1 := by
    intro u hui
    rcases List.mem_append.mp hui with hui|hui
    · exact hold u hui
    · exact hnet u hui
  have hstep : ((L+1:ℕ):ℝ)⁻¹ ≤ xs := by
    simpa only [Nat.cast_add,Nat.cast_one,one_div] using hL.le
  exact ⟨us,hus,(fun u hui=>List.mem_append_left net hui),
    actual_finite_overlap_natural_calibration_on_retained_net n l hn b h hb hh L us hus
      (fun u hui=>List.mem_append_right old hui) hxs hK hstep hamp⟩

theorem eventually_actual_minimum_finite_overlap_natural_calibration
    (ell : ℕ) (Bclock : ℝ) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0 ≤ Az) (hC0 : 0<C0) (hCt : 0 ≤ Ct) :
    ∃ K : ℝ,0<K ∧ ∀ᶠ n : ℕ in atTop,
      ∀ a : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock,
      ∀ old : List PositiveMass,(∀ u∈old,u.val ≤ 1) →
      ∃ us : List PositiveMass,(∀ u∈us,u.val ≤ 1) ∧ (∀ u∈old,u∈us) ∧
        ∀ᶠ k : ℕ in atTop,
          let q := completedPathClock n a.bf a.hf
          let as := finiteCutMasses us k
          let steps := sampleClockSteps q 0 as
          ∀ j ≤ as.length,
            physicalOverlapMoment n (ell+1) steps (Measure.pi fun i=>gaussianReal 0 (q 0 i))
              id measurable_id j ≤ K*(a.xs+physicalCutMass 0 steps j)^(2*(ell+1)) := by
  obtain ⟨K,hK,H⟩ := eventually_actual_minimum_overlap_natural_moment ell Bclock hm hdelta hroom
    hcl hcu hAz hC0 hCt
  refine ⟨2*K*(2:ℝ)^(2*(ell+1)),by positivity,?_⟩
  filter_upwards [H] with n hn
  intro a old hold
  have had := comparisonVariableEndpoint_clocks_admissible a.context.hc a.context.hk
    a.context.hkc a.context.hm a.context.hM a.b a.h a.context.hd.ne' a.hlam.le
    a.hlb a.hb a.hh a.hh0 a.alpha
  exact exists_actual_finite_overlap_natural_calibration n (ell+1) a.context.hn a.bf a.hf
    (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1) old hold a.hxs hK (hn a)

theorem eventually_actual_minimum_inverse_size_le_scale
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D : ℝ} (hm : 0 < m) (hC0 : 0<C0) :
    ∀ᶠ n : ℕ in atTop,
      ∀ a : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock,
      1/(n:ℝ) ≤ a.xs := by
  filter_upwards [eventually_comparisonLowerScale_depth hC0 hm] with n hn
  intro a
  exact (hn a.context.E a.context.d a.context.hE a.context.hd a.hlower).trans a.hscale

theorem eventually_actual_minimum_finite_overlap_on_retained_net
    (ell : ℕ) (Bclock : ℝ) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0 ≤ Az) (hC0 : 0<C0) (hCt : 0 ≤ Ct) :
    ∃ K : ℝ,0<K ∧ ∀ᶠ n : ℕ in atTop,
      ∀ a : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock,
      ∀ (L : ℕ) (us : List PositiveMass),
        (∀ u∈us,u.val ≤ 1) → (∀ u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ a.xs →
        ∀ᶠ k : ℕ in atTop,
          let q := completedPathClock n a.bf a.hf
          let as := finiteCutMasses us k
          let steps := sampleClockSteps q 0 as
          ∀ j ≤ as.length,
            physicalOverlapMoment n (ell+1) steps (Measure.pi fun i=>gaussianReal 0 (q 0 i))
              id measurable_id j ≤ K*(a.xs+physicalCutMass 0 steps j)^(2*(ell+1)) := by
  obtain ⟨K,hK,H⟩ := eventually_actual_minimum_overlap_natural_moment ell Bclock hm hdelta hroom
    hcl hcu hAz hC0 hCt
  refine ⟨2*K*(2:ℝ)^(2*(ell+1)),by positivity,?_⟩
  filter_upwards [H] with n hn
  intro a L us hus hret hmesh
  have had := comparisonVariableEndpoint_clocks_admissible a.context.hc a.context.hk
    a.context.hkc a.context.hm a.context.hM a.b a.h a.context.hd.ne' a.hlam.le
    a.hlb a.hb a.hh a.hh0 a.alpha
  exact actual_finite_overlap_natural_calibration_on_retained_net n (ell+1) a.context.hn a.bf a.hf
    (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1) L us hus hret a.hxs hK hmesh (hn a)

end OAI.SKFluctuations.Cavity
