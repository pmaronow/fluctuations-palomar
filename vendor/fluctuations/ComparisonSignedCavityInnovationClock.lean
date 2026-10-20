module

public import ComparisonSignedCavityPrimitiveRates
public import ComparisonPhysicalGeometry
public import ConcreteComparisonStrength
public import SKFluctuationsOAI.Probability.SKFluctuations.PhysicalOverlapClockSchedule

@[expose] public section

noncomputable section
set_option maxHeartbeats 2500000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

theorem actual_comparison_radius_field_increment_lower {N d lam r₀ r₁ : ℝ}
    (hN : 1 ≤ N) (hlog : 1 ≤ Real.log N) (hd : 0<d) (hnd : 1/N ≤ d)
    (hlam : 0<lam) (hld : lam ≤ d^2) (hr₀ : 0 ≤ r₀) (hr₁ : r₁ ≤ 1)
    (hrr : r₀ ≤ r₁) :
    ((1/3)/Real.log N)*laplaceComparisonStrength d lam r₁*(r₁-r₀) ≤
      laplaceComparisonStrength d lam r₁*r₁-laplaceComparisonStrength d lam r₀*r₀ := by
  have hsub : Icc r₀ r₁⊆Icc (0:ℝ) 1 := Icc_subset_Icc hr₀ hr₁
  apply radius_strength_growth hrr
    (fun r _=>(laplaceComparisonStrength_contDiff d lam).differentiable (by norm_num) r)
    (fun r _=>laplaceComparisonStrength_pos d hlam r)
    ((laplaceComparisonStrength_monotonicities hd.ne' hlam (r₀:=0) le_rfl).1.mono hsub)
    (by positivity)
  intro r hr
  exact laplaceComparisonStrength_uniform_slope hN hlog hd hnd hlam hld (hsub hr)

theorem actual_comparison_quantile_field_increment_lower
    {c N d lam : ℝ} {k M : ℝ→ℝ}
    (hc : 0<c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
    (hkc : ∀ r∈Icc (0:ℝ) 1,c ≤ k r)
    (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)
    (α : inverseIntegralConstraints 0 0 k M)
    (hN : 1 ≤ N) (hlog : 1 ≤ Real.log N) (hd : 0<d) (hnd : 1/N ≤ d)
    (hlam : 0<lam) (hld : lam ≤ d^2) {u₀ u₁ : ℝ} (hu : u₀ ≤ u₁) :
    let R := comparisonSweepQuantile hc hk hkc hm hM α
    ((1/3)/Real.log N)*laplaceComparisonStrength d lam (R u₁)*(R u₁-R u₀) ≤
      laplaceComparisonStrength d lam (R u₁)*R u₁-
        laplaceComparisonStrength d lam (R u₀)*R u₀ := by
  dsimp only
  exact actual_comparison_radius_field_increment_lower hN hlog hd hnd hlam hld
    (comparisonSweepQuantile_bounds hc hk hkc hm hM α u₀).1
    (comparisonSweepQuantile_bounds hc hk hkc hm hM α u₁).2
    (comparisonSweepQuantile_monotone hc hk hkc hm hM α hu)

theorem actual_comparison_quantile_field_duration_lower
    {c N d lam W cw ce : ℝ} {k M : ℝ→ℝ}
    (hc : 0<c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
    (hkc : ∀ r∈Icc (0:ℝ) 1,c ≤ k r)
    (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)
    (α : inverseIntegralConstraints 0 0 k M)
    (hN : 1 ≤ N) (hlog : 1 ≤ Real.log N) (hd : 0<d) (hnd : 1/N ≤ d)
    (hlam : 0<lam) (hld : lam ≤ d^2) (hW : 0 ≤ W) (hcw : 0 ≤ cw) (hce : 0 ≤ ce)
    {u₀ u₁ : ℝ} (hu : u₀ ≤ u₁)
    (hwidth : cw*W ≤ comparisonSweepQuantile hc hk hkc hm hM α u₁-
      comparisonSweepQuantile hc hk hkc hm hM α u₀)
    (hstrength : ce*W^2 ≤ laplaceComparisonStrength d lam
      (comparisonSweepQuantile hc hk hkc hm hM α u₁)) :
    let R := comparisonSweepQuantile hc hk hkc hm hM α
    (ce*cw/3)*W^3/Real.log N ≤
      laplaceComparisonStrength d lam (R u₁)*R u₁-
        laplaceComparisonStrength d lam (R u₀)*R u₀ := by
  dsimp only
  have hl := actual_comparison_quantile_field_increment_lower hc hk hkc hm hM α
    hN hlog hd hnd hlam hld hu
  have hlog0 : 0<Real.log N := lt_of_lt_of_le zero_lt_one hlog
  have hr := (comparisonSweepQuantile_monotone hc hk hkc hm hM α hu)
  have hb := mul_le_mul hstrength hwidth (mul_nonneg hcw hW)
    (laplaceComparisonStrength_pos d hlam _).le
  have hh := mul_le_mul_of_nonneg_left hb (show 0 ≤ ((1:ℝ)/3)/Real.log N by positivity)
  apply le_trans _ hl
  convert hh using 1 <;> ring

def nativeSampledRestClock (n : ℕ) (b h : ℝ→ℝ≥0) (u : ℝ) : RestCoordinate n→ℝ≥0 :=
  Sum.elim (fun _=>b u) (fun _=>h u)

def nativeSampledPhysicalSteps (n : ℕ) (b h : ℝ→ℝ≥0) (as : List PositiveMass) :
    List (GaussianStep (FeatureIndex n)) :=
  sampleClockSteps (fun u=>restFiniteVariance n (nativeSampledRestClock n b h u)) 0 as

private theorem native_sampled_clock_monotone (n : ℕ) {b h : ℝ→ℝ≥0}
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1)) :
    ∀ i,MonotoneOn (fun u=>restFiniteVariance n (nativeSampledRestClock n b h u) i)
      (Icc (0:ℝ) 1) := by
  intro i u hu v hv huv
  cases i with
  | inl i => exact hh hu hv huv
  | inr i => cases i with
    | none => exact le_rfl
    | some i => exact mul_le_mul_of_nonneg_left (hb hu hv huv) (show (0:ℝ≥0) ≤ restFiniteEdgeScale n from zero_le)

theorem native_sampled_field_homogeneous (n : ℕ) (b h : ℝ→ℝ≥0)
    (as : List PositiveMass) (i₀ : Fin n) :
    ∀ st∈nativeSampledPhysicalSteps n b h as,∀ i : Fin n,
      st.2 (Sum.inl i)=st.2 (Sum.inl i₀) := by
  have hg (xs : List PositiveMass) (a : ℝ) :
      ∀ st∈sampleClockSteps (fun u=>restFiniteVariance n (nativeSampledRestClock n b h u)) a xs,
        ∀ i : Fin n,st.2 (Sum.inl i)=st.2 (Sum.inl i₀) := by
    induction xs generalizing a with
    | nil => simp [sampleClockSteps]
    | cons m xs ih =>
      intro st hst i
      rcases List.mem_cons.mp hst with rfl|hst
      · rfl
      · exact ih m.val _ hst i
  exact hg as 0

theorem native_sampled_field_duration_index (n : ℕ) (b h : ℝ→ℝ≥0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (as : List PositiveMass) (ho : MassOrdered 0 as) (i₀ : Fin n)
    (j : ℕ) (hj : j ≤ as.length) :
    physicalFieldDuration (fun st=>st.2 (Sum.inl i₀))
      ((nativeSampledPhysicalSteps n b h as).take j)=
      (h (partitionPoint 0 as j):ℝ)-(h 0:ℝ) := by
  unfold nativeSampledPhysicalSteps
  rw [physicalFieldDuration_take_coordinate (Sum.inl i₀)
    (fun i=>(restFiniteVariance n (nativeSampledRestClock n b h 0) i:ℝ))]
  rw [sampleClockSteps_values _ (native_sampled_clock_monotone n hb hh) as ho,partitionValues_point]
  rfl

theorem native_sampled_field_duration_slice (n : ℕ) (b h : ℝ→ℝ≥0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (as : List PositiveMass) (ho : MassOrdered 0 as) (i₀ : Fin n)
    {j₀ j₁ : ℕ} (hjj : j₀ ≤ j₁) (hj : j₁ ≤ as.length) :
    physicalFieldDuration (fun st=>st.2 (Sum.inl i₀))
      (cutSlice (nativeSampledPhysicalSteps n b h as) j₀ j₁)=
      (h (partitionPoint 0 as j₁):ℝ)-(h (partitionPoint 0 as j₀):ℝ) := by
  rw [physicalFieldDuration_slice_eq _ _ hjj,
    native_sampled_field_duration_index n b h hb hh as ho i₀ j₁ hj,
    native_sampled_field_duration_index n b h hb hh as ho i₀ j₀ (hjj.trans hj)]
  ring

theorem native_sampled_terminal_projection_clock (n : ℕ) (b h : ℝ→ℝ≥0)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (i₀ : Fin n)
    {a : ℝ} (ha : 0 ≤ a) {j₀ j₁ : ℕ} (hjj : j₀ ≤ j₁) (hj : j₁ ≤ as.length)
    (ham : a ≤ partitionPoint 0 as j₀) :
    PhysicalProjectionClock n (nativeSampledPhysicalSteps n b h as) 0 j₁ (as.length+1) a
      (physicalFieldDuration (fun st=>st.2 (Sum.inl i₀))
        (cutSlice (nativeSampledPhysicalSteps n b h as) j₀ j₁)) := by
  have hs : OrderedSteps 0 (nativeSampledPhysicalSteps n b h as) := sampleClockSteps_ordered _ _ ho
  have hmass : a ≤ physicalCutMass 0 (nativeSampledPhysicalSteps n b h as) j₀ := by
    simpa only [nativeSampledPhysicalSteps,physicalCutMass_sampleClockSteps _ _ _ j₀ (hjj.trans hj)] using ham
  have hc := alignedFieldClock_slice n (nativeSampledPhysicalSteps n b h as)
    (fun st=>st.2 (Sum.inl i₀)) (native_sampled_field_homogeneous n b h as i₀) j₀ j₁
  have hp := physicalProjectionClock_of_terminal_cuts n _ hs ha (Nat.zero_le _) hjj
    (by simpa only [nativeSampledPhysicalSteps,sampleClockSteps_length] using hj) hmass hc
  simpa only [nativeSampledPhysicalSteps,sampleClockSteps_length] using hp

theorem actual_comparison_native_innovation_clock
    (n : ℕ) (i₀ : Fin n) {c N d lam W cw ce a : ℝ} {k M : ℝ→ℝ}
    (hc : 0<c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
    (hkc : ∀ r∈Icc (0:ℝ) 1,c ≤ k r)
    (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)
    (α : inverseIntegralConstraints 0 0 k M) (b : ℝ→ℝ)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hlb : lam ≤ b 0)
    (hN : 1 ≤ N) (hlog : 1 ≤ Real.log N) (hd : 0<d) (hnd : 1/N ≤ d)
    (hlam : 0<lam) (hld : lam ≤ d^2) (hW : 0 ≤ W) (hcw : 0 ≤ cw) (hce : 0 ≤ ce)
    (as : List PositiveMass) (ho : MassOrdered 0 as)
    {j₀ j₁ : ℕ} (hjj : j₀ ≤ j₁) (hj : j₁ ≤ as.length) (ha : 0 ≤ a)
    (ham : a ≤ partitionPoint 0 as j₀)
    (hwidth : cw*W ≤
      comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as j₁)-
        comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as j₀))
    (hstrength : ce*W^2 ≤ laplaceComparisonStrength d lam
      (comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as j₁))) :
    let R := comparisonSweepQuantile hc hk hkc hm hM α
    let bf := fun u=>(b u-laplaceComparisonStrength d lam (R u)).toNNReal
    let hf := fun u=>(laplaceComparisonStrength d lam (R u)*R u).toNNReal
    let steps := nativeSampledPhysicalSteps n bf hf as
    let D := physicalFieldDuration (fun st=>st.2 (Sum.inl i₀)) (cutSlice steps j₀ j₁)
    (ce*cw/3)*W^3/Real.log N ≤ D ∧
      PhysicalProjectionClock n steps 0 j₁ (as.length+1) a D := by
  let R := comparisonSweepQuantile hc hk hkc hm hM α
  let bf := fun u=>(b u-laplaceComparisonStrength d lam (R u)).toNNReal
  let hf := fun u=>(laplaceComparisonStrength d lam (R u)*R u).toNNReal
  have had := strengthSweep_clocks_admissible b R hd.ne' hlam.le hlb hb
    ((comparisonSweepQuantile_monotone hc hk hkc hm hM α).monotoneOn _)
    (fun u _=>comparisonSweepQuantile_bounds hc hk hkc hm hM α u)
  have hbf : MonotoneOn bf (Icc (0:ℝ) 1) := toNNReal_monotoneOn had.1
  have hhf : MonotoneOn hf (Icc (0:ℝ) 1) := toNNReal_monotoneOn had.2.1
  constructor
  · rw [native_sampled_field_duration_slice n bf hf hbf hhf as ho i₀ hjj hj]
    have hnon (u : ℝ) : 0 ≤ laplaceComparisonStrength d lam (R u)*R u :=
      mul_nonneg (laplaceComparisonStrength_pos d hlam _).le
        (comparisonSweepQuantile_bounds hc hk hkc hm hM α u).1
    change _ ≤ (hf (partitionPoint 0 as j₁):ℝ)-(hf (partitionPoint 0 as j₀):ℝ)
    dsimp only [hf]
    rw [Real.coe_toNNReal _ (hnon _),Real.coe_toNNReal _ (hnon _)]
    exact actual_comparison_quantile_field_duration_lower hc hk hkc hm hM α
      hN hlog hd hnd hlam hld hW hcw hce (partitionPoint_mono as ho hjj) hwidth hstrength
  · exact native_sampled_terminal_projection_clock n bf hf as ho i₀ ha hjj hj ham

end OAI.SKFluctuations.Cavity
