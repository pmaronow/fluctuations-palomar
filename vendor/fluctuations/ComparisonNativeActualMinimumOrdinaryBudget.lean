module

public import ComparisonNativeActualMinimumBandRaw

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 5000000

theorem eventually_actual_minimum_constant_clock_ordinary_budget
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
        NativeBandRawMaster b ∧
        ∀cut : ℝ, 0 < cut → Real.log (1/cut) ≤ Lside →
          (∫u in 0..1, b.ordinaryMask (a.R u)*
            (orderedPathB (n+1) a.bf a.hf u-(orderedPathS (n+1) a.bf a.hf u)^2)) ≤
            nativeBinScaleLoss Lside b.AS b.AC b.bandMass b.rho*b.bandMass*
              (2*((Q^2*b.y)/(b.P*b.bandMass^2))^((2:ℝ)/3)+
                3/(b.P*b.bandMass^2)+(b.localDiameter (v/2+b.U) 32)^2+
                  b.reverse (b.localDiameter (v/2+b.U) 32))+
              18*(((Q^2*b.y)^2*b.P*b.bandMass^2)^((1:ℝ)/3)+2)*cut := by
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
  refine ⟨hR,?_⟩
  intro cut hcut hlogcut
  have hf := g.canonical_model_facts v hv hv1 (ell+1) hell Q Lside hQ hLside
    dphys e hlog hnd
  have hU := a.context.hU
  have hpos : 0 < v/2+b.U := by change 0 < v/2+a.context.U; positivity
  have hspan : b.hi-b.lo ≤ 32*(v/2+b.U) := by
    change min (16*v) 1-v/2 ≤ 32*(v/2+a.context.U)
    linarith [min_le_left (16*v) 1]
  exact actual_master_full_ordinary_local_band_explicit b hcut hf.1 hf.2.1 hf.2.2.1
    hlogcut hR hpos (by norm_num) le_rfl hspan

end OAI.SKFluctuations.LaplaceWindowFormalization
