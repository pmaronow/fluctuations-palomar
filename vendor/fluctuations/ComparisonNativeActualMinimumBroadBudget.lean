module

public import ComparisonNativeActualMergedBroadGeometry

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 5000000

theorem eventually_actual_minimum_constant_clock_broad_budget
    (ell : ℕ) (hell : 2 < ell+1) (Bclock : ℝ)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃(Q : ℝ) (hQ : 1 ≤ Q), ∀ᶠn : ℕ in atTop,
      ∀a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      ∀(T H : ℝ) (hb : ∀u, a.b u = T) (hh : ∀u, a.h u = H),
      ∀p : a.Potential,
        ∀(v : ℝ) (hv : 0 < v) (hv1 : v ≤ 1),
        ∀(Lside : ℝ) (hLside : 0 ≤ Lside),
        ∀(dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1)),
        ∀(hlog : 1 ≤ Real.log a.context.N) (hnd : 1/a.context.N ≤ a.context.d),
        let b := ((p.constantClockGeometry hb hh).canonical v hv hv1
          (ell+1) hell Q Lside hQ hLside).toModel dphys e hlog hnd
        ∀(c : NativeActualCapInterval b) (f : NativeWholeCapBroadSampler b c)
          (i : Fin f.count), f.scale i=v →
          ((p.H c.a=0 ∧ p.H c.z=0) ∨ (c.a=0 ∧ p.H c.z=0) ∨ (p.H c.a=0 ∧ c.z=1)) →
          ∀cut : ℝ, 0 < cut → 2*cut < a.context.U → Real.log (1/cut) ≤ Lside →
          let width := ∫r in f.slice i, deriv a.alpha.val.val r
          let loss := (32:ℝ)^2+25*(1+v/a.context.U)*Real.log ((1+a.context.U)/a.context.U)+1
          (∫u in 0..1, (f.slice i).indicator (fun _ => 1) (a.R u)*
            (orderedPathB (n+1) a.bf a.hf u-(orderedPathS (n+1) a.bf a.hf u)^2)) ≤
            nativeConditionalLedgerBudget 1 width cut b.D0
              (108*loss*(Real.log a.context.N)^2/(b.P*b.rho)*Real.log (width/cut))
              (54*loss*(Real.log a.context.N)^2*width/(b.P*b.rho^2)) (b.reverse b.D0) Lside := by
  obtain ⟨Q,hQ,hraw⟩ := eventually_actual_minimum_canonical_band_raw (D:=D) ell hell
    Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Q,hQ,?_⟩
  filter_upwards [hraw] with n hnraw
  intro a T H hb hh p v hv hv1 Lside hLside dphys e hlog hnd
  dsimp only
  let g := p.constantClockGeometry hb hh
  let b := (g.canonical v hv hv1 (ell+1) hell Q Lside hQ hLside).toModel
    dphys e hlog hnd
  have hR : NativeBandRawMaster b := hnraw a p g v hv hv1 Lside hLside dphys e hlog hnd
  intro c f i hscale hboundary cut hcut hsmall hlogcut
  have hag : b.ag=b.R (f.scale i/2) := by rw [hscale]; rfl
  have hzg : b.zg=b.R (min (16*f.scale i) 1) := by rw [hscale]; rfl
  let broad := f.toSliceGeometry i hboundary hag hzg a.constraint_length_calibration
  obtain ⟨s,hs⟩ := exists_nativeRawMasterRefinement b hR
  have hf := g.canonical_model_facts v hv hv1 (ell+1) hell Q Lside hQ hLside
    dphys e hlog hnd
  have hbroad := actual_native_calibrated_positive_broad_slice_comparison_of_eventual_raw
    b s broad hcut hsmall hf.1 hf.2.1 hlogcut hs
  have hslice : Ioo broad.a broad.b = f.slice i := rfl
  have hscale' : broad.scale = v := hscale
  dsimp only at hbroad
  rw [hslice,hscale'] at hbroad
  change (∫u in 0..1,(f.slice i).indicator (fun _=>1) (b.R u)*b.thermal u) ≤ _
  exact hbroad

end OAI.SKFluctuations.LaplaceWindowFormalization
