module

public import ComparisonNativeActualMinimumComparableBudgets
public import ComparisonNativeActualOuterFloorThermalMass
public import ComparisonNativeOuterLocalMassBandAssembly
public import ComparisonNativeLocalThermalSignPartition
public import ComparisonNativeActualMinimumCapTravelUnit

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 9000000
attribute [local instance] Classical.propDecidable
namespace NativeOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}

theorem actual_comparable_outer_mass_thermal_of_explicit_budgets
    (a : NativeOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock)
    (p : a.Potential) {T H : ℝ} (hb : ∀u,a.b u=T) (hh : ∀u,a.h u=H)
    (ell : ℕ) (hell : 2 < ell+1) (Q Lside : ℝ) (hQ : 1 ≤ Q) (hLside : 0 ≤ Lside)
    (dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1))
    (hlog : 1 ≤ Real.log a.context.N) (hnd : 1/a.context.N ≤ a.context.d)
    (hraw : ∀(v : ℝ) (hv : 0 < v) (hv1 : v ≤ 1),
      NativeBandRawMaster (p.constantCanonicalModel hb hh (ell+1) hell Q Lside hQ hLside
        dphys e hlog hnd v hv hv1))
    {lo hi cut O B Kfloor : ℝ}
    (hlo : lo∈Icc (0:ℝ) 1) (hhi : hi∈Icc (0:ℝ) 1) (hlh : lo ≤ hi)
    (h8 : 8*a.context.U ≤ lo) (hshort : a.cavityCapTravel < 1)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (htravel : a.cavityCapTravel ≤ a.xs) (houter : 2*cu*(Az+1)*a.xs ≤ lo)
    (hcut : 0 < cut) (hsmall : 2*cut < a.context.U)
    (hlogcut : Real.log (1/cut) ≤ Lside) (hO : 0 ≤ O) (hB : 0 ≤ B)
    (hOrd : ∀v∈Icc (lo/16) hi, 0 < v → v ≤ 1 →
      a.canonicalOrdinaryMassBudgetAtDiameter (ell+1) Q Lside cut v (a.canonicalLocalMassDiameter v) ≤ O)
    (hBroad : ∀v∈Icc (lo/4) (2*hi), 0 < v → v ≤ 1 →
      ∀width∈Icc v (4*v), width ≤ 1 →
        a.canonicalComparableBroadMassBudgetAtDiameter (ell+1) Q Lside cut v width (a.canonicalOuterBroadMassDiameter v) ≤ B)
    (hKfloor : 0 ≤ Kfloor)
    (hamp : ∀u∈Ioc (0:ℝ) 1,
      orderedPathB (n+1) a.bf a.hf u ≤ Kfloor*(a.xs+u)^2) :
    (∫u in lo..hi,orderedPathB (n+1) a.bf a.hf u-(orderedPathS (n+1) a.bf a.hf u)^2) ≤
      (2*O+4*B)*(Nat.ceil (Real.log (1/a.context.U)/Real.log 2)+1)+
        Kfloor*(a.xs+hi)^2*a.context.N^delta*a.context.U^2/(lo/cu) := by
  let m := p.constantCanonicalModel hb hh (ell+1) hell Q Lside hQ hLside
    dphys e hlog hnd 1 zero_lt_one le_rfl
  let g := p.constantContactDyadicFamily hb hh ell hell Q Lside hQ hLside dphys e hlog hnd
  let A := nativeBroadMassSlice m.hc m.hk m.hkc m.hm m.hM m.alpha lo hi
  have hA : MeasurableSet A := measurableSet_Ioo
  have hscale : ∀r∈A,lo ≤ m.alpha.val.val r ∧ m.alpha.val.val r ≤ hi := by
    intro r hr
    exact (native_mass_slice_profile_mem m hlo hhi hr).imp le_of_lt le_of_lt
  have hcap := actual_native_outer_local_cap_contact_thermal_bound g A hA h8 hshort hO hB hscale
    (by
      intro j
      let v := m.U*(2:ℝ)^(j.val.val:ℕ)
      have hv := comparison_mass_dyadic_scale m.hU j.val
      have hp := a.actual_canonical_local_ordinary_mass_budget p hb hh (ell+1) hell Q Lside hQ hLside
        dphys e hlog hnd v hv.1 hv.2.2 (hraw v hv.1 hv.2.2) hcut hlogcut
      exact hp.trans (hOrd v j.property hv.1 hv.2.2))
    (by
      intro F c hcase _ _ q
      let f := nativeActualBroadCapSampler m c q.val.1
      let i := q.val.2
      have hv : 0 < f.scale i := a.context.hU.trans_le (f.actual_dyadic_group i).1
      have hv1 : f.scale i ≤ 1 := (f.actual_dyadic_group i).2.1
      have hparent : 2*cu*(Az+1)*a.xs ≤ a.alpha.val.val (c q.val.1.val).z := by
        obtain ⟨r,hrA,hrs⟩ := q.property
        have hrparent := (f.contracts i).2.2.2.1 hrs
        have hm := a.alpha.val.property.2 hrparent.2.le
        exact houter.trans ((hscale r hrA).1.trans hm)
      have hp := a.actual_canonical_comparable_outer_broad_mass_budget p hb hh (ell+1) hell Q Lside hQ hLside
        dphys e hlog hnd hcl hcu hAz htravel (c q.val.1.val) f i (hcase q.val.1.val) hparent
        (hraw (f.scale i) hv hv1) hcut hsmall hlogcut
      have hs := native_relevant_broad_slice_scale_bounds m c A hscale q
      have hw := native_whole_broad_slice_width_bounds f i
      exact hp.trans (hBroad (f.scale i) hs hv hv1
        (∫r in f.slice i,deriv m.alpha.val.val r) ⟨hw.1,hw.2.1⟩ hw.2.2))
  have hloPos : 0 < lo := (mul_pos (by norm_num) a.context.hU).trans_le h8
  have hrloPos : 0 < lo/cu := div_pos hloPos hcu
  have hcu1 : 1 ≤ cu := by
    have H := (a.regular 1 ⟨a.hz.2,le_rfl⟩).2
    simpa only [a.alpha.property.2.1,mul_one] using H
  have hrlo1 : lo/cu ≤ 1 := (div_le_one hcu).mpr (hlo.2.trans hcu1)
  have hthreshold : cu*Az*a.xs < lo := by
    have H : 0 < cu*(Az+2)*a.xs := mul_pos (mul_pos hcu (by linarith)) a.hxs
    nlinarith
  have hlower : ∀r∈A,lo/cu ≤ r := by
    intro r hr
    have hrIcc : r∈Icc (0:ℝ) 1 :=
      ⟨(comparisonSweepQuantile_bounds m.hc m.hk m.hkc m.hm m.hM m.alpha lo).1.trans hr.1.le,
        hr.2.le.trans (comparisonSweepQuantile_bounds m.hc m.hk m.hkc m.hm m.hM m.alpha hi).2⟩
    exact a.actual_mass_slab_radius_lower hcu hthreshold hrIcc (hscale r hr).1
  have hfloor := a.actual_outer_floor_thermal_mass_of_normalized_B p
    ((p.constantClockGeometry hb hh).canonical 1 zero_lt_one le_rfl
      (ell+1) hell Q Lside hQ hLside) dphys e hlog hnd A hA hrloPos hrlo1 hlower hKfloor
    (fun r hr=>(hscale r hr).2) hamp
  have hsplit := native_actual_local_thermal_sign_partition m A hA
  have hid := native_actual_mass_slice_thermal_integral m hlo hhi hlh
  change (∫u in 0..1,A.indicator (fun _=>1) (m.R u)*m.thermal u)=
    ∫u in lo..hi,m.thermal u at hid
  change (∫u in lo..hi,m.thermal u) ≤ _
  rw [←hid,hsplit]
  change (∫u in 0..1,(A∩(nativeNegativeSet m∪nativeActualContactSet m)).indicator
    (fun _=>1) (m.R u)*m.thermal u) ≤
      (2*O+4*B)*(Nat.ceil (Real.log (1/a.context.U)/Real.log 2)+1) at hcap
  change (∫u in 0..1,(A∩nativeActualPositiveSet m).indicator (fun _=>1) (m.R u)*m.thermal u) ≤
    Kfloor*(a.xs+hi)^2*a.context.N^delta*a.context.U^2/(lo/cu) at hfloor
  linarith

end NativeOverlapMinimum

theorem eventually_actual_minimum_comparable_outer_mass_of_explicit_budgets
    (ell : ℕ) (hell : 2 < ell+1) (Bclock : ℝ)
    {margin delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < margin) (hdelta : 0 < delta) (hroom : delta < 3*margin)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃(Q : ℝ) (_hQ : 1 ≤ Q) (Kfloor : ℝ), 0 < Kfloor ∧
      ∀ᶠn : ℕ in atTop,
      ∀(a : NativeOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock)
        (_p : a.Potential) (T H : ℝ) (_hb : ∀u,a.b u=T) (_hh : ∀u,a.h u=H)
        (dphys : ℕ) (_e : Fin (dphys+1) ≃ FeatureIndex (n+1))
        (_hlog : 1 ≤ Real.log a.context.N) (_hnd : 1/a.context.N ≤ a.context.d)
        (Lside : ℝ) (_hLside : 0 ≤ Lside) (lo hi cut O B : ℝ),
        lo∈Icc (0:ℝ) 1 → hi∈Icc (0:ℝ) 1 → lo ≤ hi → 8*a.context.U ≤ lo →
        2*cu*(Az+1)*a.xs ≤ lo →
        0 < cut → 2*cut < a.context.U → Real.log (1/cut) ≤ Lside → 0 ≤ O → 0 ≤ B →
        (∀v∈Icc (lo/16) hi, 0 < v → v ≤ 1 →
          a.canonicalOrdinaryMassBudgetAtDiameter (ell+1) Q Lside cut v
            (a.canonicalLocalMassDiameter v) ≤ O) →
        (∀v∈Icc (lo/4) (2*hi), 0 < v → v ≤ 1 →
          ∀width∈Icc v (4*v), width ≤ 1 →
            a.canonicalComparableBroadMassBudgetAtDiameter (ell+1) Q Lside cut v width
              (a.canonicalOuterBroadMassDiameter v) ≤ B) →
        (∫u in lo..hi,orderedPathB (n+1) a.bf a.hf u-(orderedPathS (n+1) a.bf a.hf u)^2) ≤
          (2*O+4*B)*(Nat.ceil (Real.log (1/a.context.U)/Real.log 2)+1)+
            Kfloor*(a.xs+hi)^2*a.context.N^delta*a.context.U^2/(lo/cu) := by
  obtain ⟨Q,hQ,hraw⟩ := eventually_actual_minimum_canonical_band_raw (D:=D) ell hell
    Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Kfloor,hKfloor,hamp⟩ := eventually_native_comparison_B_normalized (D:=D)
    Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  have hshort := eventually_actual_minimum_cap_travel_lt_one (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct)
    (D:=D) (Bclock:=Bclock) hC0 (by linarith : 0 < 3*margin+delta)
  have htravel := eventually_actual_minimum_cap_travel_small
    (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock) (epsilon:=1)
    hC0 (by linarith : 0 < 3*margin+delta) zero_lt_one
  refine ⟨Q,hQ,Kfloor,hKfloor,?_⟩
  filter_upwards [hraw,(tendsto_add_atTop_nat 1).eventually hamp,hshort,htravel]
    with n hnraw hnamp hnshort hntravel
  intro a p T H hb hh dphys e hlog hnd Lside hLside lo hi cut O B
    hlo hhi hlh h8 houter hcut hsmall hlogcut hO hB hOrd hBroad
  exact a.actual_comparable_outer_mass_thermal_of_explicit_budgets p hb hh ell hell Q Lside hQ hLside
    dphys e hlog hnd
    (fun v hv hv1=>hnraw a p (p.constantClockGeometry hb hh) v hv hv1 Lside hLside
      dphys e hlog hnd)
    hlo hhi hlh h8 (hnshort a) hcl hcu hAz (by simpa only [one_mul] using (hntravel a).1) houter
    hcut hsmall hlogcut hO hB hOrd hBroad hKfloor.le (hnamp a)

end OAI.SKFluctuations.LaplaceWindowFormalization
