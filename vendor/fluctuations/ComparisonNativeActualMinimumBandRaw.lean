module

public import ComparisonNativeActualMinimumCapGeometry
public import ComparisonSignedCavityActualMinimumResampling

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 5000000

theorem eventually_actual_minimum_canonical_band_raw
    (ell : ℕ) (hell : 2 < ell+1) (Bclock : ℝ)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃(Q : ℝ) (hQ : 1 ≤ Q), ∀ᶠn : ℕ in atTop,
      ∀a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      ∀p : a.Potential, ∀g : a.CommonBandGeometry p,
      ∀(v : ℝ) (hv : 0 < v) (hv1 : v ≤ 1),
      ∀(Lside : ℝ) (hLside : 0 ≤ Lside),
      ∀(dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1)),
      ∀(hlog : 1 ≤ Real.log a.context.N) (hnd : 1/a.context.N ≤ a.context.d),
      NativeBandRawMaster
        ((g.canonical v hv hv1 (ell+1) hell Q Lside hQ hLside).toModel
          dphys e hlog hnd) := by
  obtain ⟨C,hC,hraw⟩ := eventually_native_minimum_original_boundary_raw
    ell Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  have hQ : 1 ≤ 1+2*C := by linarith
  have hshift : Tendsto (fun n : ℕ => n+1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro k
    filter_upwards [eventually_ge_atTop k] with n hn
    omega
  refine ⟨1+2*C, hQ, ?_⟩
  filter_upwards [hshift.eventually hraw] with n hnraw
  intro a p g v hv hv1 Lside hLside dphys e hlog hnd extra hextra
  let u : PositiveMass := ⟨1, zero_lt_one⟩
  obtain ⟨nodes,hbound,_,hretain,hR⟩ := hnraw a u le_rfl extra hextra
  refine ⟨nodes, hbound, hretain, ?_⟩
  filter_upwards [hR] with j hj
  let r := physicalRawRatio (n+1) (ell+1)
    (sampleClockSteps (completedPathClock (n+1) a.bf a.hf) 0 (finiteCutMasses nodes j))
    0 a.xs (Measure.pi fun i => gaussianReal 0 (completedPathClock (n+1) a.bf a.hf 0 i))
    id measurable_id
  have hr : 1 ≤ r := physicalRawRatio_one_le _ _ _ _ _ _ _ _
  have hs : r^2 ≤ 2*C := hj.1
  have hfinal : r ≤ 1+2*C := by nlinarith
  exact hfinal

end OAI.SKFluctuations.LaplaceWindowFormalization
