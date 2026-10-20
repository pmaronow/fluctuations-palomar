module

public import ComparisonSignedCavityLocalInnovation

@[expose] public section

noncomputable section
set_option maxHeartbeats 3500000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

theorem actual_comparison_native_mass_innovation_clock
    (n : ℕ) (i₀ : Fin n) {c N d lam gap M₀ g₀ a : ℝ} {k M : ℝ→ℝ}
    (hc : 0<c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
    (hkc : ∀ r∈Icc (0:ℝ) 1,c ≤ k r)
    (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)
    (α : inverseIntegralConstraints 0 0 k M) (b : ℝ→ℝ)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hlb : lam ≤ b 0)
    (hN : 1 ≤ N) (hlog : 1 ≤ Real.log N) (hd : 0<d) (hnd : 1/N ≤ d)
    (hlam : 0<lam) (hld : lam ≤ d^2)
    (hgap0 : 0 ≤ gap) (hM₀ : 0<M₀) (hg₀ : 0 ≤ g₀)
    (as : List PositiveMass) (ho : MassOrdered 0 as)
    {fork pre v w : ℕ} (hfork : fork ≤ pre) (hpv : pre ≤ v) (hvw : v ≤ w)
    (hv : v ≤ as.length) (hw : w ≤ as.length+1) (ha : 0 ≤ a)
    (ham : a ≤ partitionPoint 0 as pre)
    (hcap : M (partitionPoint 0 as v) ≤ M₀)
    (hgap : gap ≤ partitionPoint 0 as v-partitionPoint 0 as pre)
    (hstrength : g₀ ≤ laplaceComparisonStrength d lam
      (comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as v))) :
    let R := comparisonSweepQuantile hc hk hkc hm hM α
    let bf := fun u=>(b u-laplaceComparisonStrength d lam (R u)).toNNReal
    let hf := fun u=>(laplaceComparisonStrength d lam (R u)*R u).toNNReal
    let steps := nativeSampledPhysicalSteps n bf hf as
    let D := physicalFieldDuration (fun st=>st.2 (Sum.inl i₀)) (cutSlice steps pre v)
    g₀*gap/(3*M₀*Real.log N) ≤ D ∧ PhysicalProjectionClock n steps fork v w a D := by
  let R := comparisonSweepQuantile hc hk hkc hm hM α
  let bf := fun u=>(b u-laplaceComparisonStrength d lam (R u)).toNNReal
  let hf := fun u=>(laplaceComparisonStrength d lam (R u)*R u).toNNReal
  have had := strengthSweep_clocks_admissible b R hd.ne' hlam.le hlb hb
    ((comparisonSweepQuantile_monotone hc hk hkc hm hM α).monotoneOn _)
    (fun u _=>comparisonSweepQuantile_bounds hc hk hkc hm hM α u)
  have hbf : MonotoneOn bf (Icc (0:ℝ) 1) := toNNReal_monotoneOn had.1
  have hhf : MonotoneOn hf (Icc (0:ℝ) 1) := toNNReal_monotoneOn had.2.1
  constructor
  · rw [native_sampled_field_duration_slice n bf hf hbf hhf as ho i₀ hpv hv]
    have hnon (u : ℝ) : 0 ≤ laplaceComparisonStrength d lam (R u)*R u :=
      mul_nonneg (laplaceComparisonStrength_pos d hlam _).le
        (comparisonSweepQuantile_bounds hc hk hkc hm hM α u).1
    change _ ≤ (hf (partitionPoint 0 as v):ℝ)-(hf (partitionPoint 0 as pre):ℝ)
    dsimp only [hf]
    rw [Real.coe_toNNReal _ (hnon _),Real.coe_toNNReal _ (hnon _)]
    exact actual_comparison_mass_field_duration_lower hc hk hkc hm hM α
      hN hlog hd hnd hlam hld
      (partitionPoint_mem as ho pre) (partitionPoint_mem as ho v)
      (partitionPoint_mono as ho hpv) hgap0 hM₀ hg₀ hcap hgap hstrength
  · exact native_sampled_field_layer_projection_clock n bf hf as ho i₀ ha hfork hpv hvw hv hw ham

end OAI.SKFluctuations.Cavity
