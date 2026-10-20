module

public import ComparisonNativeActualCanonicalBroadRates
public import ComparisonNativeFinitePhysicalConsumers

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 12000000
namespace NativeOverlapMinimum

theorem eventually_actual_sampler_broad_error
    (ell : ℕ) (hell : 2 < ell+1)
    {margin delta cl cu Az C0 Ct D Bclock Cv : ℝ}
    (hm : 0 < margin) (hdelta : 0 < delta) (hroom : delta < 3*margin)
    (hcl : 0 < cl) (hcu : 0 < cu) (hclcu : cl ≤ cu)
    (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCv1 : 1 ≤ Cv) (hCvOuter : 4*cu*Az ≤ Cv) (hCvCap : 2*cu*(Az+1) ≤ Cv)
    (horder : (delta+2)/(ell:ℝ) ≤ delta) :
    ∃(Q : ℝ) (hQ : 1 ≤ Q), ∀ᶠn : ℕ in atTop,
      ∀a : NativeOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock,
      a.context.d ≤ 1 →
      a.xs=comparisonConditionalScale a.context.N delta a.context.E a.lam →
      a.xs+1 ≤ a.context.N →
      ∀p : a.Potential, ∀g : a.CommonBandGeometry p,
      ∀(dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1)),
      ∀(hlog : 1 ≤ Real.log a.context.N) (hnd : 1/a.context.N ≤ a.context.d),
      let base := (g.canonical 1 zero_lt_one le_rfl (ell+1) hell Q
        (10*Real.log a.context.N) hQ (by positivity)).toModel dphys e hlog hnd
      ∀(c : NativeActualCapInterval base) (f : NativeWholeCapBroadSampler base c) (i : Fin f.count),
      ((base.H c.a=0 ∧ base.H c.z=0) ∨ (c.a=0 ∧ base.H c.z=0) ∨ (base.H c.a=0 ∧ c.z=1)) →
      (∫u in 0..1,(f.slice i).indicator (fun _=>1) (base.R u)*base.comparisonErrorDensity u) ≤
        a.context.N^(6*delta)*a.context.E := by
  obtain ⟨Q,hQ,hevent⟩ := eventually_actual_canonical_broad_error ell hell hm hdelta hroom
    hcl hcu hclcu hAz hC0 hCt hCv1 hCvOuter hCvCap horder
  refine ⟨Q,hQ,?_⟩
  filter_upwards [hevent] with n hn
  intro a hd1 hxs hy p g dphys e hlog hnd
  dsimp only
  intro c f i hcase
  let Lside := 10*Real.log a.context.N
  have hLside : 0 ≤ Lside := by dsimp [Lside]; positivity
  let base := (g.canonical 1 zero_lt_one le_rfl (ell+1) hell Q Lside hQ hLside).toModel dphys e hlog hnd
  let v := f.scale i
  have hv : 0 < v := a.context.hU.trans_le (f.actual_dyadic_group i).1
  have hv1 : v ≤ 1 := (f.actual_dyadic_group i).2.1
  let b := (g.canonical v hv hv1 (ell+1) hell Q Lside hQ hLside).toModel dphys e hlog hnd
  have hH : b.H=base.H := rfl
  have hU : b.U=base.U := rfl
  have ha : b.alpha.val.val=base.alpha.val.val := rfl
  have hR : b.R=base.R := rfl
  let f' := f.reassign b hH hU ha
  have hcase' := c.reassign_boundary b hH hcase
  have hscl : f'.scale i=v := f.reassign_scale b hH hU ha i
  have hag : b.ag=b.R (f'.scale i/2) := by rw [hscl]; rfl
  have hzg : b.zg=b.R (min (16*f'.scale i) 1) := by rw [hscl]; rfl
  let broad := f'.toSliceGeometry i hcase' hag hzg a.constraint_length_calibration
  have hb := hn a hd1 hxs hy p g v hv hv1 (f.actual_dyadic_group i).1 dphys e hlog hnd broad hscl
  have hslice : Ioo broad.a broad.b=f'.slice i := rfl
  rw [hslice,f.reassign_slice b hH hU ha hR i] at hb
  exact hb

theorem eventually_actual_finite_physical_consumers
    (ell : ℕ) (hell : 2 < ell+1)
    {margin delta cl cu Az C0 Ct D Bclock : ℝ}
    (hm : 0 < margin) (hdelta : 0 < delta) (hroom : delta < 3*margin)
    (hcl : 0 < cl) (hcu : 0 < cu) (hclcu : cl ≤ cu)
    (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (horder : (delta+2)/(ell:ℝ) ≤ delta) :
    ∃(Q : ℝ) (hQ : 1 ≤ Q), ∀ᶠn : ℕ in atTop,
      ∀a : NativeOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock,
      a.context.d ≤ 1 →
      a.xs=comparisonConditionalScale a.context.N delta a.context.E a.lam →
      a.xs+1 ≤ a.context.N →
      ∀(p : a.Potential) (Kb Kh : ℝ≥0)
        (hparent : LipschitzOnWith Kb (fun r=>a.b (a.alpha.val.val r)) (Icc 0 1))
        (hfield : LipschitzOnWith Kh (fun r=>a.h (a.alpha.val.val r)) (Icc 0 1))
        (dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1))
        (hlog : 1 ≤ Real.log a.context.N) (hnd : 1/a.context.N ≤ a.context.d),
      let base := p.generalCanonicalModel Kb Kh hparent hfield (ell+1) hell Q
        (10*Real.log a.context.N) hQ (by positivity) dphys e hlog hnd 1 zero_lt_one le_rfl
      ∃bands : NativeFiniteBandConsumers base,
        bands.budget=48*Real.log a.context.N*a.context.N^(7*delta)*a.context.E+
          (∫u in 0..min (8*a.context.U) 1,base.comparisonErrorDensity u) := by
  let Cv := max 1 (max (4*cu*Az) (2*cu*(Az+1)))
  have hCv1 : 1 ≤ Cv := le_max_left _ _
  have hCvO : 4*cu*Az ≤ Cv := (le_max_left _ _).trans (le_max_right _ _)
  have hCvC : 2*cu*(Az+1) ≤ Cv := (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨Qo,hQo,ho⟩ := eventually_actual_canonical_ordinary_error ell hell hm hdelta hroom
    hcl hcu hAz hC0 hCt horder
  obtain ⟨Q,hQ,hb⟩ := eventually_actual_sampler_broad_error ell hell hm hdelta hroom
    hcl hcu hclcu hAz hC0 hCt hCv1 hCvO hCvC horder
  refine ⟨Q,hQ,?_⟩
  filter_upwards [ho,hb,eventually_actual_minimum_physical_scalar_data hm hC0] with n hno hnb hns
  intro a hd1 hxs hy p Kb Kh hparent hfield dphys e hlog hnd
  dsimp only
  let g := p.commonGeometry Kb Kh hparent hfield
  let Lside := 10*Real.log a.context.N
  have hLside : 0 ≤ Lside := by dsimp [Lside]; positivity
  let base := p.generalCanonicalModel Kb Kh hparent hfield (ell+1) hell Q Lside hQ hLside dphys e hlog hnd
    1 zero_lt_one le_rfl
  let family := p.generalContactDyadicFamily Kb Kh hparent hfield ell hell Q Lside hQ hLside dphys e hlog hnd
  have hordinary : ∀j : comparisonMassDyadicIndices base.U,
      (∫u in 0..1,(family.model j).ordinaryMask ((family.model j).R u)*(family.model j).comparisonErrorDensity u) ≤
        base.N^(7*delta)*base.E := by
    intro j
    have hs := comparison_mass_dyadic_scale a.context.hU j
    exact hno a hd1 hxs hy p g (a.context.U*(2:ℝ)^(j:ℕ)) hs.1 hs.2.2 hs.2.1 dphys e hlog hnd
  have hbroad : ∀(c : NativeActualCapInterval base) (f : NativeWholeCapBroadSampler base c) (i : Fin f.count),
      ((base.H c.a=0 ∧ base.H c.z=0) ∨ (c.a=0 ∧ base.H c.z=0) ∨ (base.H c.a=0 ∧ c.z=1)) →
      (∫u in 0..1,(f.slice i).indicator (fun _=>1) (base.R u)*base.comparisonErrorDensity u) ≤
        base.N^(7*delta)*base.E := by
    intro c f i hcase
    have hh := hnb a hd1 hxs hy p g dphys e hlog hnd c f i hcase
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ a.context.hE.le
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Nat.succ_pos n) (by linarith)
  exact ⟨family.finitePhysicalConsumers (hns a hd1).2.2.2.1 hordinary hbroad,rfl⟩

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
