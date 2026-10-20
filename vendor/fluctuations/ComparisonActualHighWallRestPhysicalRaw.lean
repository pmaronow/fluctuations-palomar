module

public import ComparisonActualHighWallRestRawMoments
public import ComparisonSignedCavityActualRestPhysicalRaw

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem eventually_actual_high_wall_rest_physical_raw_ratio
    (ell : ℕ) (Bclock : ℝ) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        (physicalRawRatio n (ell+1) (nativeSampledPhysicalSteps n M.bf M.hf (finiteCutMasses us k))
          0 M.xs (Measure.pi (fun i => gaussianReal 0
            (restFiniteVariance n (nativeSampledRestClock n M.bf M.hf 0) i)))
          id measurable_id)^2 ≤ C := by
  obtain ⟨C,hC,HR⟩ := eventually_actual_high_wall_rest_even_bound
    (D:=D) (ell+1) (by omega) Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨2*max 1 C,by positivity,?_⟩
  filter_upwards [HR,eventually_gt_atTop (0:ℕ)] with n hn hn0
  intro M L us hus hret hmesh
  filter_upwards [hn M L us hus hret hmesh] with k hk
  let as := finiteCutMasses us k
  let q₀ := restFiniteVariance n (nativeSampledRestClock n M.bf M.hf 0)
  let steps := nativeSampledPhysicalSteps n M.bf M.hf as
  have ho : MassOrdered 0 as := finiteCutMasses_ordered us hus k
  have hs : OrderedSteps 0 steps := sampleClockSteps_ordered _ as ho
  have hb : MonotoneOn M.bf (Icc (0:ℝ) 1):=M.data.bf_monotone M.alpha
  have hh : MonotoneOn M.hf (Icc (0:ℝ) 1):=M.data.hf_monotone M.alpha
  apply physical_raw_ratio_sq_le_of_pair_moments n (ell+1) (by omega) steps hs q₀ M.hxs hC.le
  intro j hj
  have hj' : j ≤ as.length := by simpa only [steps,nativeSampledPhysicalSteps,sampleClockSteps_length] using hj
  rw [show steps=nativeSampledPhysicalSteps n M.bf M.hf as from rfl,
    native_sampled_rest_physical_raw_eq n (ell+1) hn0 M.bf M.hf hb hh as ho j hj']
  simpa only [nativeSampledPhysicalSteps,physicalCutMass_sampleClockSteps _ _ _ j hj'] using hk j hj'

end OAI.SKFluctuations.Cavity
