module

public import ComparisonNativeGeneralMinimumMassGeometry

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 12000000
namespace NativeOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}

theorem general_actual_canonical_ordinary_mass_budget
    (a : NativeOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock)
    (p : a.Potential) (Kb Kh : ℝ≥0)
    (hparent : LipschitzOnWith Kb (fun r=>a.b (a.alpha.val.val r)) (Icc 0 1))
    (hfield : LipschitzOnWith Kh (fun r=>a.h (a.alpha.val.val r)) (Icc 0 1))
    (ell : ℕ) (hell : 2 < ell) (Q Lside : ℝ) (hQ : 1 ≤ Q) (hLside : 0 ≤ Lside)
    (dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1))
    (hlog : 1 ≤ Real.log a.context.N) (hnd : 1/a.context.N ≤ a.context.d)
    (v : ℝ) (hv : 0 < v) (hv1 : v ≤ 1)
    (hraw : NativeBandRawMaster (((p.commonGeometry Kb Kh hparent hfield).canonical
      v hv hv1 ell hell Q Lside hQ hLside).toModel dphys e hlog hnd))
    {cut : ℝ} (hcut : 0 < cut) (hlogcut : Real.log (1/cut) ≤ Lside) :
    let b := ((p.commonGeometry Kb Kh hparent hfield).canonical
      v hv hv1 ell hell Q Lside hQ hLside).toModel dphys e hlog hnd
    (∫u in 0..1,b.ordinaryMask (a.R u)*
      (orderedPathB (n+1) a.bf a.hf u-(orderedPathS (n+1) a.bf a.hf u)^2)) ≤
        a.canonicalOrdinaryMassBudget ell Q Lside cut v := by
  dsimp only
  let g := p.commonGeometry Kb Kh hparent hfield
  let b := (g.canonical v hv hv1 ell hell Q Lside hQ hLside).toModel dphys e hlog hnd
  have hf := g.canonical_model_facts v hv hv1 ell hell Q Lside hQ hLside dphys e hlog hnd
  have hb := actual_master_full_ordinary_band_explicit b hcut hf.1 hf.2.1 hf.2.2.1 hlogcut hraw
  have hpower : b.P=a.canonicalMassPower v := by
    change (n+1 : ℝ)*laplaceComparisonStrength a.context.d a.lam (a.R (min (16*v) 1)) = _
    simp only [canonicalMassPower,NativeOverlapContext.N,Nat.cast_add,Nat.cast_one]
  have hdiam : b.D0=a.canonicalMassDiameter := rfl
  have hrev : b.reverse b.D0=a.canonicalMassReverse ell Q v := rfl
  have hrho : b.rho=v/4 := hf.2.2.2.1
  rw [hrev,hpower,hdiam,hrho] at hb
  exact hb

theorem general_actual_canonical_broad_mass_budget
    (a : NativeOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock)
    (p : a.Potential) (Kb Kh : ℝ≥0)
    (hparent : LipschitzOnWith Kb (fun r=>a.b (a.alpha.val.val r)) (Icc 0 1))
    (hfield : LipschitzOnWith Kh (fun r=>a.h (a.alpha.val.val r)) (Icc 0 1))
    (ell : ℕ) (hell : 2 < ell) (Q Lside : ℝ) (hQ : 1 ≤ Q) (hLside : 0 ≤ Lside)
    (dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1))
    (hlog : 1 ≤ Real.log a.context.N) (hnd : 1/a.context.N ≤ a.context.d)
    (c : NativeActualCapInterval (p.generalCanonicalModel Kb Kh hparent hfield ell hell Q Lside hQ hLside
      dphys e hlog hnd 1 zero_lt_one le_rfl))
    (f : NativeWholeCapBroadSampler _ c) (i : Fin f.count)
    (hcase : (p.H c.a=0 ∧ p.H c.z=0) ∨ (c.a=0 ∧ p.H c.z=0) ∨ (p.H c.a=0 ∧ c.z=1))
    (hraw : NativeBandRawMaster (p.generalCanonicalModel Kb Kh hparent hfield ell hell Q Lside hQ hLside
      dphys e hlog hnd (f.scale i)
      (a.context.hU.trans_le (f.actual_dyadic_group i).1) (f.actual_dyadic_group i).2.1))
    {cut : ℝ} (hcut : 0 < cut) (hsmall : 2*cut < a.context.U)
    (hlogcut : Real.log (1/cut) ≤ Lside) :
    (∫u in 0..1,(f.slice i).indicator (fun _=>1) (a.R u)*
      (orderedPathB (n+1) a.bf a.hf u-(orderedPathS (n+1) a.bf a.hf u)^2)) ≤
      a.canonicalBroadMassBudget ell Q Lside cut (f.scale i)
        (∫r in f.slice i,deriv a.alpha.val.val r) := by
  let base := p.generalCanonicalModel Kb Kh hparent hfield ell hell Q Lside hQ hLside dphys e hlog hnd
    1 zero_lt_one le_rfl
  let v := f.scale i
  have hv : 0 < v := a.context.hU.trans_le (f.actual_dyadic_group i).1
  have hv1 : v ≤ 1 := (f.actual_dyadic_group i).2.1
  let b := p.generalCanonicalModel Kb Kh hparent hfield ell hell Q Lside hQ hLside dphys e hlog hnd v hv hv1
  have hH : b.H=base.H := rfl
  have hU : b.U=base.U := rfl
  have ha : b.alpha.val.val=base.alpha.val.val := rfl
  have hR : b.R=base.R := rfl
  have hT : b.thermal=base.thermal := rfl
  let f' := f.reassign b hH hU ha
  have hcase' := c.reassign_boundary b hH hcase
  have hscl : f'.scale i=v := f.reassign_scale b hH hU ha i
  have hag : b.ag=b.R (f'.scale i/2) := by rw [hscl]; rfl
  have hzg : b.zg=b.R (min (16*f'.scale i) 1) := by rw [hscl]; rfl
  let broad := f'.toSliceGeometry i hcase' hag hzg a.constraint_length_calibration
  obtain ⟨s,hs⟩ := exists_nativeRawMasterRefinement b hraw
  have hf := (p.commonGeometry Kb Kh hparent hfield).canonical_model_facts v hv hv1 ell hell Q Lside hQ hLside
    dphys e hlog hnd
  have hbudget := actual_native_calibrated_positive_broad_slice_comparison_of_eventual_raw
    b s broad hcut hsmall hf.1 hf.2.1 hlogcut hs
  have hslice : Ioo broad.a broad.b=f'.slice i := rfl
  have hscale : broad.scale=v := hscl
  dsimp only at hbudget
  rw [hslice,hscale] at hbudget
  have hsame := f.reassign_original_thermal_integral b hH hU ha hR hT i
  rw [hsame] at hbudget
  have hslice' := f.reassign_slice b hH hU ha hR i
  rw [hslice'] at hbudget
  have hpower : b.P=a.canonicalMassPower v := by
    change (n+1 : ℝ)*laplaceComparisonStrength a.context.d a.lam (a.R (min (16*v) 1)) = _
    simp only [canonicalMassPower,NativeOverlapContext.N,Nat.cast_add,Nat.cast_one]
  have hdiam : b.D0=a.canonicalMassDiameter := rfl
  have hrev : b.reverse b.D0=a.canonicalMassReverse ell Q v := rfl
  have hrho : b.rho=v/4 := hf.2.2.2.1
  rw [hrev,hpower,hdiam,hrho] at hbudget
  exact hbudget

end NativeOverlapMinimum

theorem eventually_general_minimum_ordinary_mass_budget
    (ell : ℕ) (hell : 2 < ell+1) (Bclock : ℝ)
    {margin delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < margin) (hdelta : 0 < delta) (hroom : delta < 3*margin)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃(Q : ℝ) (hQ : 1 ≤ Q), ∀ᶠn : ℕ in atTop,
      ∀(a : NativeOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock)
        (p : a.Potential) (Kb Kh : ℝ≥0)
        (hparent : LipschitzOnWith Kb (fun r=>a.b (a.alpha.val.val r)) (Icc 0 1))
        (hfield : LipschitzOnWith Kh (fun r=>a.h (a.alpha.val.val r)) (Icc 0 1))
        (dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1))
        (hlog : 1 ≤ Real.log a.context.N) (hnd : 1/a.context.N ≤ a.context.d)
        (Lside : ℝ) (hLside : 0 ≤ Lside) (v : ℝ) (hv : 0 < v) (hv1 : v ≤ 1)
        (cut : ℝ), 0 < cut → Real.log (1/cut) ≤ Lside →
        let b := p.generalCanonicalModel Kb Kh hparent hfield (ell+1) hell Q Lside hQ hLside
          dphys e hlog hnd v hv hv1
        (∫u in 0..1,b.ordinaryMask (a.R u)*
          (orderedPathB (n+1) a.bf a.hf u-(orderedPathS (n+1) a.bf a.hf u)^2)) ≤
            a.canonicalOrdinaryMassBudget (ell+1) Q Lside cut v := by
  obtain ⟨Q,hQ,hraw⟩ := eventually_actual_minimum_canonical_band_raw (D:=D) ell hell
    Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Q,hQ,?_⟩
  filter_upwards [hraw] with n hn
  intro a p Kb Kh hparent hfield dphys e hlog hnd Lside hLside v hv hv1 cut hcut hlogcut
  exact a.general_actual_canonical_ordinary_mass_budget p Kb Kh hparent hfield (ell+1) hell Q Lside hQ hLside
    dphys e hlog hnd v hv hv1
    (hn a p (p.commonGeometry Kb Kh hparent hfield) v hv hv1 Lside hLside dphys e hlog hnd) hcut hlogcut

theorem eventually_general_minimum_broad_mass_budget
    (ell : ℕ) (hell : 2 < ell+1) (Bclock : ℝ)
    {margin delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < margin) (hdelta : 0 < delta) (hroom : delta < 3*margin)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃(Q : ℝ) (hQ : 1 ≤ Q), ∀ᶠn : ℕ in atTop,
      ∀(a : NativeOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock)
        (p : a.Potential) (Kb Kh : ℝ≥0)
        (hparent : LipschitzOnWith Kb (fun r=>a.b (a.alpha.val.val r)) (Icc 0 1))
        (hfield : LipschitzOnWith Kh (fun r=>a.h (a.alpha.val.val r)) (Icc 0 1))
        (dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1))
        (hlog : 1 ≤ Real.log a.context.N) (hnd : 1/a.context.N ≤ a.context.d)
        (Lside : ℝ) (hLside : 0 ≤ Lside)
        (c : NativeActualCapInterval (p.generalCanonicalModel Kb Kh hparent hfield (ell+1) hell Q Lside hQ hLside
          dphys e hlog hnd 1 zero_lt_one le_rfl))
        (f : NativeWholeCapBroadSampler _ c) (i : Fin f.count),
        ((p.H c.a=0 ∧ p.H c.z=0) ∨ (c.a=0 ∧ p.H c.z=0) ∨ (p.H c.a=0 ∧ c.z=1)) →
        ∀cut : ℝ, 0 < cut → 2*cut < a.context.U → Real.log (1/cut) ≤ Lside →
        (∫u in 0..1,(f.slice i).indicator (fun _=>1) (a.R u)*
          (orderedPathB (n+1) a.bf a.hf u-(orderedPathS (n+1) a.bf a.hf u)^2)) ≤
          a.canonicalBroadMassBudget (ell+1) Q Lside cut (f.scale i)
            (∫r in f.slice i,deriv a.alpha.val.val r) := by
  obtain ⟨Q,hQ,hraw⟩ := eventually_actual_minimum_canonical_band_raw (D:=D) ell hell
    Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Q,hQ,?_⟩
  filter_upwards [hraw] with n hn
  intro a p Kb Kh hparent hfield dphys e hlog hnd Lside hLside c f i hcase cut hcut hsmall hlogcut
  exact a.general_actual_canonical_broad_mass_budget p Kb Kh hparent hfield (ell+1) hell Q Lside hQ hLside
    dphys e hlog hnd c f i hcase
    (hn a p (p.commonGeometry Kb Kh hparent hfield) (f.scale i)
      (a.context.hU.trans_le (f.actual_dyadic_group i).1) (f.actual_dyadic_group i).2.1
      Lside hLside dphys e hlog hnd) hcut hsmall hlogcut

end OAI.SKFluctuations.LaplaceWindowFormalization
