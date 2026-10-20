module

public import ComparisonNativeActualMinimumLocalDiameterBudgets
public import ComparisonNativeRegularBandGeometry
public import ComparisonNativeActualMinimumMassBudgets
public import ComparisonNativeMasterLocalFullBand

@[expose] public section

noncomputable section
set_option maxHeartbeats 8000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
namespace NativeOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}

theorem actual_regular_local_ordinary_mass_budget
    (a : NativeOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock)
    (p : a.Potential) (hclock : NativePullbackClockRegularity a.alpha.val.val a.b a.h 0 1)
    (ell : ℕ) (hell : 2 < ell) (Q Lside : ℝ) (hQ : 1 ≤ Q) (hLside : 0 ≤ Lside)
    (dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1))
    (hlog : 1 ≤ Real.log a.context.N) (hnd : 1/a.context.N ≤ a.context.d)
    (v : ℝ) (hv : 0 < v) (hv1 : v ≤ 1)
    (hraw : NativeBandRawMaster (p.regularCanonicalModel hclock ell hell Q Lside hQ hLside
      dphys e hlog hnd v hv hv1))
    {cut : ℝ} (hcut : 0 < cut) (hlogcut : Real.log (1/cut) ≤ Lside) :
    let b := p.regularCanonicalModel hclock ell hell Q Lside hQ hLside dphys e hlog hnd v hv hv1
    (∫u in 0..1,b.ordinaryMask (a.R u)*
      (orderedPathB (n+1) a.bf a.hf u-(orderedPathS (n+1) a.bf a.hf u)^2)) ≤
        a.canonicalOrdinaryMassBudgetAtDiameter ell Q Lside cut v (a.canonicalLocalMassDiameter v) := by
  dsimp only
  let g := p.regularCommonGeometry hclock
  let b := p.regularCanonicalModel hclock ell hell Q Lside hQ hLside dphys e hlog hnd v hv hv1
  have hf := g.canonical_model_facts v hv hv1 ell hell Q Lside hQ hLside dphys e hlog hnd
  have hU := a.context.hU
  have hpos : 0 < v/2+b.U := by change 0 < v/2+a.context.U; positivity
  have hspan : b.hi-b.lo ≤ 32*(v/2+b.U) := by
    change min (16*v) 1-v/2 ≤ 32*(v/2+a.context.U)
    linarith [min_le_left (16*v) 1]
  have hbudget := actual_master_full_ordinary_local_band_explicit b hcut hf.1 hf.2.1 hf.2.2.1
    hlogcut hraw hpos (by norm_num) le_rfl hspan
  have hpower : b.P=a.canonicalMassPower v := by
    change (n+1 : ℝ)*laplaceComparisonStrength a.context.d a.lam (a.R (min (16*v) 1)) = _
    simp only [canonicalMassPower,NativeOverlapContext.N,Nat.cast_add,Nat.cast_one]
  have hdiam : b.localDiameter (v/2+b.U) 32=a.canonicalLocalMassDiameter v := rfl
  have hrev : b.reverse (b.localDiameter (v/2+b.U) 32)=
      a.canonicalMassReverseAtDiameter ell Q v (a.canonicalLocalMassDiameter v) := rfl
  have hrho : b.rho=v/4 := hf.2.2.2.1
  rw [hrev,hpower,hdiam,hrho] at hbudget
  exact hbudget

theorem actual_regular_outer_broad_mass_budget
    (a : NativeOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock)
    (p : a.Potential) (hclock : NativePullbackClockRegularity a.alpha.val.val a.b a.h 0 1)
    (ell : ℕ) (hell : 2 < ell) (Q Lside : ℝ) (hQ : 1 ≤ Q) (hLside : 0 ≤ Lside)
    (dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1))
    (hlog : 1 ≤ Real.log a.context.N) (hnd : 1/a.context.N ≤ a.context.d)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (htravel : a.cavityCapTravel ≤ a.xs)
    (c : NativeActualCapInterval (p.regularCanonicalModel hclock ell hell Q Lside hQ hLside
      dphys e hlog hnd 1 zero_lt_one le_rfl))
    (f : NativeWholeCapBroadSampler _ c) (i : Fin f.count)
    (hcase : (p.H c.a=0 ∧ p.H c.z=0) ∨ (c.a=0 ∧ p.H c.z=0) ∨ (p.H c.a=0 ∧ c.z=1))
    (houter : 2*cu*(Az+1)*a.xs ≤ a.alpha.val.val c.z)
    (hraw : NativeBandRawMaster (p.regularCanonicalModel hclock ell hell Q Lside hQ hLside
      dphys e hlog hnd (f.scale i)
      (a.context.hU.trans_le (f.actual_dyadic_group i).1) (f.actual_dyadic_group i).2.1))
    {cut : ℝ} (hcut : 0 < cut) (hsmall : 2*cut < a.context.U)
    (hlogcut : Real.log (1/cut) ≤ Lside) :
    (∫u in 0..1,(f.slice i).indicator (fun _=>1) (a.R u)*
      (orderedPathB (n+1) a.bf a.hf u-(orderedPathS (n+1) a.bf a.hf u)^2)) ≤
      a.canonicalBroadMassBudgetAtDiameter ell Q Lside cut (f.scale i)
        (∫r in f.slice i,deriv a.alpha.val.val r) (a.canonicalOuterBroadMassDiameter (f.scale i)) := by
  let base := p.regularCanonicalModel hclock ell hell Q Lside hQ hLside dphys e hlog hnd
    1 zero_lt_one le_rfl
  let v := f.scale i
  have hv : 0 < v := a.context.hU.trans_le (f.actual_dyadic_group i).1
  have hv1 : v ≤ 1 := (f.actual_dyadic_group i).2.1
  let b := p.regularCanonicalModel hclock ell hell Q Lside hQ hLside dphys e hlog hnd v hv hv1
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
  have hf := (p.regularCommonGeometry hclock).canonical_model_facts v hv hv1 ell hell Q Lside hQ hLside
    dphys e hlog hnd
  have hbudget := actual_native_positive_outer_broad_slice_comparison b s broad
    hcl hcu hAz a.hz a.hzxs htravel a.regular houter hcut hsmall hf.1 hf.2.1 hlogcut hs
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
  have hdiam : nativeOuterBroadDiameter b broad cl cu=a.canonicalOuterBroadMassDiameter v := by
    simp only [nativeOuterBroadDiameter,nativeOuterBroadTravel,hscale]
    rfl
  have hrev : b.reverse (nativeOuterBroadDiameter b broad cl cu)=
      a.canonicalMassReverseAtDiameter ell Q v (a.canonicalOuterBroadMassDiameter v) := by
    rw [hdiam]
    rfl
  have hrho : b.rho=v/4 := hf.2.2.2.1
  rw [hrev,hpower,hdiam,hrho] at hbudget
  exact hbudget

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
