module

public import ComparisonActualHighOnlyClocks
public import ComparisonActualHighOnlyOverlapAmplitude
public import ComparisonSignedCavityInheritedCanonicalSourceMoments

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set MeasureTheory ProbabilityTheory Filter Hierarchy LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 16000000

theorem eventually_actual_high_only_finite_overlap_on_retained_net
    (ell : ℕ) (Bclock : ℝ) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0 ≤ Az) (hC0 : 0<C0) (hCt : 0 ≤ Ct) :
    ∃ K : ℝ,0<K ∧ ∀ᶠ n : ℕ in atTop,
      ∀ a : ActualHighOnlyOverlapMinimum n m delta cl cu Az C0 Ct D Bclock,
      a.data.s ≤ 1/4 → a.data.s ≤ a.xs →
      ∀ (L : ℕ) (us : List PositiveMass),
        (∀ u∈us,u.val ≤ 1) → (∀ u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ a.xs →
        ∀ᶠ k : ℕ in atTop,
          let q := completedPathClock n a.bf a.hf
          let as := finiteCutMasses us k
          let steps := sampleClockSteps q 0 as
          ∀ j ≤ as.length,
            physicalOverlapMoment n (ell+1) steps (Measure.pi fun i=>gaussianReal 0 (q 0 i))
              id measurable_id j ≤ K*(a.xs+physicalCutMass 0 steps j)^(2*(ell+1)) := by
  obtain ⟨K,hK,H⟩ := eventually_actual_high_only_overlap_moment_normalized ell Bclock hm hdelta hroom
    hcl hcu hAz hC0 hCt
  refine ⟨2*K*(2:ℝ)^(2*(ell+1)),by positivity,?_⟩
  filter_upwards [H] with n hn
  intro a hs hsxs L us hus hret hmesh
  exact actual_finite_overlap_natural_calibration_on_retained_net n (ell+1) a.data.hn a.bf a.hf
    a.bf_monotone a.hf_monotone L us hus hret a.hxs hK hmesh (hn a hs hsxs)

theorem eventually_actual_high_only_inverse_size_le_scale
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (hm : 0 < m) (hC0 : 0 < C0) :
    ∀ᶠ n : ℕ in atTop,∀a : ActualHighOnlyOverlapMinimum n m delta cl cu Az C0 Ct D Bclock,
      1/(n:ℝ)≤a.xs := by
  filter_upwards [eventually_comparisonLowerScale_depth hC0 hm] with n hn
  intro a
  exact (hn a.data.E a.data.d a.data.hE a.data.hd a.hlower).trans a.hscale

theorem eventually_actual_high_only_deleted_raw_on_retained_net
    (a : ℕ) (ha : 0<a) (Bclock Btotal Bbond : ℝ)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) :
    ∃ Cd : ℝ,0 < Cd ∧ ∀ᶠ n : ℕ in atTop,
      ∀ M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      M.data.s ≤ 1/4 → M.data.s ≤ M.xs →
      ∀ (L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
        ∀ᶠ k : ℕ in atTop,
          let as:=finiteCutMasses us k
          let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
          let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
          ∀ low≤as.length,
            finitePhysicalMixedClock (n+1) as b h as.length+b as.length+h as.length≤Btotal →
            b as.length≤Bbond →
            finitePhysicalDeletedRawBudget n a as b h low≤
              (Cd*(M.xs+partitionPoint 0 as low))^(2*a) := by
  obtain ⟨K,hK,hraw⟩ := eventually_actual_high_only_finite_overlap_on_retained_net
    (D:=D) (a-1) Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  have HE := (tendsto_add_atTop_nat 1).eventually hraw
  have HS := (tendsto_add_atTop_nat 1).eventually
    (eventually_actual_high_only_inverse_size_le_scale (D:=D) (delta:=delta)
      (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (Bclock:=Bclock) hm hC0)
  refine ⟨actualNaturalDeletedConstant K Btotal Bbond,
    actualNaturalDeletedConstant_pos hK.le,?_⟩
  filter_upwards [HE,HS] with n hn hsite
  intro M hs hsxs L us hus hret hmesh
  have hb := M.bf_monotone
  have hh := M.hf_monotone
  filter_upwards [hn M hs hsxs L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro low hlow hclock hbond
  let as:=finiteCutMasses us k
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus k
  have hpoint : 0≤partitionPoint 0 as low:=(partitionPoint_mem as ho low).1
  have hnat : 0 < M.xs+partitionPoint 0 as low:=add_pos_of_pos_of_nonneg M.hxs hpoint
  have hsize : 1/(n+1:ℕ)≤M.xs+partitionPoint 0 as low:=
    (hsite M).trans (le_add_of_nonneg_right hpoint)
  have hdiag:=actual_sampled_completed_diagonal_steps_eq (n+1) M.bf M.hf hb hh as ho
  have hq:=actual_sampled_completed_clock_eq (n+1) M.bf M.hf hb hh as ho
  have hz (i : FeatureIndex (n+1)) : physicalCompletedClock (n+1) b h 0 i=
      (completedPathClock (n+1) M.bf M.hf 0 i:ℝ) := by
    have H:=congrFun (congrFun hq.symm 0) i
    simpa only [stepClockValues_zero] using H
  have hroot : (Measure.pi fun i=>gaussianReal 0
      (Real.toNNReal (physicalCompletedClock (n+1) b h 0 i)))=
      Measure.pi fun i=>gaussianReal 0 (completedPathClock (n+1) M.bf M.hf 0 i) := by
    congr 1
    funext i
    rw [hz,Real.toNNReal_coe]
  have Hmom:=hk low hlow
  have ha' : a-1+1=a := by omega
  rw [ha'] at Hmom
  have Hmom' : physicalOverlapMoment (n+1) a
      (diagonalBoundarySteps as (physicalCompletedClock (n+1) b h 0)
        (fun j=>physicalCompletedClock (n+1) b h (j+1)))
      (Measure.pi fun i=>gaussianReal 0 (Real.toNNReal (physicalCompletedClock (n+1) b h 0 i)))
      id measurable_id low≤K*(M.xs+partitionPoint 0 as low)^(2*a) := by
    rw [hdiag,hroot]
    simpa only [physicalCutMass_sampleClockSteps _ _ _ low hlow] using Hmom
  exact actual_deleted_raw_budget_from_overlap n a ha as b h low hK.le hnat hclock hbond hsize Hmom'

theorem eventually_actual_high_only_continuum_center_bound
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Cs : ℝ,0<Cs ∧ ∀ᶠ n : ℕ in atTop,
      ∀M : ActualHighOnlyOverlapMinimum n m delta cl cu Az C0 Ct D Bclock,
      M.data.s ≤ 1/4 → M.data.s ≤ M.xs →
      ∀u∈Icc (0:ℝ) 1,
        |pathPairMoment (uniformWeight n) (finiteFeature n)
          (completedPathClock n M.bf M.hf) (orderedOverlap n) u|≤Cs*(M.xs+u) := by
  obtain ⟨K,hK,H⟩ := eventually_actual_high_only_overlap_moment_normalized
    (D:=D) 0 Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨1+K,by positivity,?_⟩
  filter_upwards [H] with n hn
  intro M hs hsxs
  apply continuum_center_bound_closed_interval n M.bf M.hf M.hxs.le (by positivity)
  intro u hu
  exact actual_continuum_center_le_of_second_moment n M.bf M.hf
    (M.bf_monotone) (M.hf_monotone) hu M.hxs (by
      simpa only [Nat.zero_add,Nat.mul_one] using hn M hs hsxs u hu)

end OAI.SKFluctuations.Cavity
