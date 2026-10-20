module

public import ComparisonNativeActualRegularMassGeometry
public import ComparisonNativeActualHighMassBroadRates
public import ComparisonNativeActualHighMassOrdinaryRates
public import ComparisonNativeActualHighMassReverseRates
public import ComparisonNativeActualHighMassFloorNormalization
public import ComparisonNativeActualRegularOuterMassAssembly
public import ComparisonNativeActualMassSlabScale

@[expose] public section

noncomputable section
set_option maxHeartbeats 15000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators

theorem eventually_actual_regular_strong_high_mass_dyad
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D Cs c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs) (hc : 0 < c) (hcouter : 2*cu*(Az+1) ≤ c) :
    ∀ᶠn : ℕ in atTop,
      ∀(a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
        (_hclock : NativePullbackClockRegularity a.alpha.val.val a.b a.h 0 1),
        a.xs^2 ≤ Cs*laplaceComparisonStrength a.context.d a.lam a.xs →
        a.canonicalDirectTestBandScale ≤ 1 →
        ∀v : ℝ, 0 < v → 2*v ≤ 1 → c*a.canonicalDirectTestBandScale ≤ v →
          (∫u in v..2*v,orderedPathB (n+1) a.bf a.hf u-(orderedPathS (n+1) a.bf a.hf u)^2)/
            (a.xs^4*v/a.canonicalDirectTestBandScale^2) ≤
              a.context.N^(-(actualMassSavingExponent m delta/2)) := by
  by_cases hD : 0 < D
  swap
  · apply Eventually.of_forall
    intro n a
    exact False.elim (hD (a.context.hd.trans_le a.hdD))
  let Cdiam := 576+288*cu^3/cl^3+1
  let csource := c/16
  have hCdiam : 0 < Cdiam := by dsimp [Cdiam]; positivity
  have hCdiamOrd : 576 ≤ Cdiam := by
    dsimp [Cdiam]
    have HH : 0 ≤ 288*cu^3/cl^3 := by positivity
    linarith
  have hCdiamBroad : 288*cu^3/cl^3 ≤ Cdiam := by dsimp [Cdiam]; linarith
  have hcsource : 0 < csource := by dsimp [csource]; positivity
  obtain ⟨l,hl,HreverseFactory⟩ := NativeOverlapMinimum.exists_actual_high_mass_reverse_polynomial_order
    (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (Bclock:=Bclock)
    hm hdelta hC0 hD hCs hcsource hCdiam
  let ell := l-1
  have horder : ell+1=l := by dsimp [ell]; omega
  have hell : 2 < ell+1 := by rw [horder]; exact hl
  obtain ⟨Q,hQ,Kfloor,hKfloor,Hassembly⟩ := eventually_actual_regular_outer_mass_of_explicit_budgets
    (D:=D) ell hell Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  simp only [horder] at Hassembly
  have Hreverse := HreverseFactory Q hQ
  have Hordinary := NativeOverlapMinimum.eventually_high_mass_ordinary_budget_of_reverse_rate
    l hl Q hm hdelta hcl hAz hCt hC0 hCs hcsource hCdiam Hreverse
  have Hbroad := NativeOverlapMinimum.chosen_high_mass_broad_budget_polynomial_le
    l hl Q hQ hm hdelta hcl hAz hCt hC0 hCs hcsource hCdiam Hreverse
  let eta := actualMassSavingExponent m delta
  let Ccount := (1+Real.log (1+D^2))/Real.log 2+2
  let Cfloor := Kfloor*cu*(1/c+2)^2*(Cs+1)^2*C0^6
  let Ctotal := 24*Ccount+Cfloor
  have heta : 0 < eta := actualMassSavingExponent_pos hm hdelta
  have Hdecay := (tendsto_add_atTop_nat 1).eventually
    (native_mass_log_power_decay (q:=eta) (s:=eta/2) (by linarith) 1 Ctotal)
  have Hratio := (tendsto_add_atTop_nat 1).eventually
    (eventually_coefficient_rpow_le (c:=C0^3) (d:=c/8) (q:=-3*m) (r:=0) (by positivity) (by linarith))
  have Hgeom := NativeOverlapMinimum.eventually_exists_actual_common_geometry_regular
    (m:=m) (cl:=cl) (cu:=cu) (Az:=Az) (C0:=C0) (Ct:=Ct) (D:=D) (Bclock:=Bclock) hdelta
  have Hdepth := (tendsto_add_atTop_nat 1).eventually (eventually_comparisonLowerScale_depth hC0 hm)
  have Hlog := (tendsto_add_atTop_nat 1).eventually
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (1:ℝ)))
  have Hcut := eventually_actual_mass_polynomial_cut_feasible
    (m:=m) (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az) (C0:=C0) (Ct:=Ct) (D:=D) (Bclock:=Bclock)
  filter_upwards [Hassembly,Hordinary,Hbroad,Hdecay,Hratio,Hgeom,Hdepth,Hlog,Hcut]
    with n hnassembly hnordinary hnbroad hnrate hnratio hngeom hndepth hnlog hncut
  intro a hclock hsmall hW1 v hv hv2 hvlo
  let W := a.canonicalDirectTestBandScale
  let target := a.xs^4*v/W^2
  let bound := 4*a.context.N^(-eta)*target
  have hW : 0 < W := a.canonical_direct_test_band_pos
  have hxs := a.hxs
  have htarget : 0 < target := by dsimp [target]; positivity
  have hbound : 0 ≤ bound := by dsimp [bound]; positivity
  have hN : 1 ≤ a.context.N := by dsimp [NativeOverlapContext.N]; exact_mod_cast Nat.succ_pos n
  have hlog : 1 ≤ Real.log a.context.N := by simpa only [NativeOverlapContext.N,Function.comp_def] using hnlog
  have hlog0 : 0 ≤ Real.log a.context.N := zero_le_one.trans hlog
  have hnd : 1/a.context.N ≤ a.context.d := by
    have hd := hndepth a.context.E a.context.d a.context.hE a.context.hd a.hlower
    have hs : comparisonLowerScale (n+1 : ℕ) a.context.E a.context.d ≤ a.context.d := by
      unfold comparisonLowerScale
      exact (div_le_iff₀ a.context.hd).mpr (by simpa only [pow_two] using a.hupper)
    exact hd.trans hs
  obtain ⟨p,_⟩ := hngeom a hclock
  have hxsW := a.canonical_direct_test_band_ge_scale
  have h8 : 8*a.context.U ≤ v := by
    have Hr := a.canonical_mass_small_ratio hC0
    have HR : a.context.U/a.xs ≤ c/8 := Hr.trans (by
      simpa only [NativeOverlapContext.N,Real.rpow_zero,mul_one] using hnratio)
    have HU := (div_le_iff₀ a.hxs).mp HR
    nlinarith [mul_le_mul_of_nonneg_left hxsW hc.le]
  have houter : 2*cu*(Az+1)*a.xs ≤ v := by
    have hcoef : 0 ≤ 2*cu*(Az+1) := by positivity
    exact ((mul_le_mul_of_nonneg_left hxsW hcoef).trans
      (mul_le_mul_of_nonneg_right hcouter hW.le)).trans hvlo
  have hlo : v∈Icc (0:ℝ) 1 := ⟨hv.le,by linarith⟩
  have hhi : 2*v∈Icc (0:ℝ) 1 := ⟨by positivity,hv2⟩
  have hcutpos : 0 < a.context.N^(-(10:ℝ)) := Real.rpow_pos_of_pos a.context.hN _
  have hlogcut : Real.log (1/a.context.N^(-(10:ℝ))) ≤ 10*Real.log a.context.N := by
    rw [one_div,Real.log_inv,Real.log_rpow a.context.hN]
    ring_nf
    exact le_refl _
  have hLside : 0 ≤ 10*Real.log a.context.N := by linarith
  have Hphysical := hnassembly a p hclock (Fintype.card (FeatureIndex (n+1))-1)
    (cavityCanonicalFeatureEquiv n) hlog hnd (10*Real.log a.context.N) hLside v (2*v)
    (a.context.N^(-(10:ℝ))) bound bound hlo hhi (by linarith) h8 houter
    hcutpos (hncut a) hlogcut hbound hbound
    (by
      intro s hs hsp hs1
      have hslo : csource*W ≤ s := by dsimp [csource]; nlinarith [hs.1]
      have Hsource := a.canonical_ordinary_mass_budget_at_diameter_mono
        (Q:=Q) (cut:=a.context.N^(-(10:ℝ))) hl hsp hLside
        (a.canonical_local_mass_diameter_pos (by linarith) hsp).le
        (a.canonical_local_mass_diameter_le_chosen hCdiamOrd hlog0 hsp)
      have Hnumeric := hnordinary a hnd hsmall hW1 s hsp hs1 hslo
      have Hstarget : 0 < a.xs^4*s/W^2 := by positivity
      have Hsave := (div_le_iff₀ Hstarget).mp Hnumeric
      have Hscale : a.xs^4*s/W^2 ≤ 4*target := by
        dsimp [target]
        have Hs : s ≤ 4*v := by linarith [hs.2]
        have HH := mul_le_mul_of_nonneg_left Hs (show 0 ≤ a.xs^4/W^2 by positivity)
        convert HH using 1 <;> ring
      have HH := mul_le_mul_of_nonneg_left Hscale (Real.rpow_nonneg a.context.hN.le (-eta))
      exact Hsource.trans (Hsave.trans (by simpa only [bound,mul_assoc,mul_left_comm,mul_comm] using HH)))
    (by
      intro s hs hsp hs1 width hw hw1
      have hslo : csource*W ≤ s := by dsimp [csource]; nlinarith [hs.1,mul_pos hc hW]
      have hU := a.context.hU
      have hE := a.context.hE
      have hd := a.context.hd
      have hN0 := a.context.hN
      have htravel0 : 0 ≤ a.cavityCapTravel := by
        unfold NativeOverlapMinimum.cavityCapTravel
        have hLcap := a.context.hL
        have Hrl : 0 ≤ Real.log ((1+a.context.U)/a.context.U) :=
          Real.log_nonneg ((one_le_div hU).mpr (by linarith))
        positivity
      have houterD0 : 0 ≤ a.canonicalOuterBroadMassDiameter s := by
        unfold NativeOverlapMinimum.canonicalOuterBroadMassDiameter
        exact mul_nonneg (by positivity) (le_min htravel0 (by positivity))
      have Hsource := a.canonical_broad_mass_budget_at_diameter_mono
        (Q:=Q) (cut:=a.context.N^(-(10:ℝ))) hl hsp.le hLside
        (hsp.le.trans hw.1) houterD0
        (a.canonical_outer_mass_diameter_le_chosen hcl hcu hCdiamBroad hlog0 hsp)
      have Hnumeric := hnbroad a hlog hnd hsmall hW1 s width hsp hs1 hslo hw.1 hw.2 hw1
      have Hstarget : 0 < a.xs^4*s/W^2 := by positivity
      have Hsave := (div_le_iff₀ Hstarget).mp Hnumeric
      have Hscale : a.xs^4*s/W^2 ≤ 4*target := by
        dsimp [target]
        have Hs : s ≤ 4*v := by linarith [hs.2]
        have HH := mul_le_mul_of_nonneg_left Hs (show 0 ≤ a.xs^4/W^2 by positivity)
        convert HH using 1 <;> ring
      have HH := mul_le_mul_of_nonneg_left Hscale (Real.rpow_nonneg a.context.hN.le (-eta))
      exact Hsource.trans (Hsave.trans (by simpa only [bound,mul_assoc,mul_left_comm,mul_comm] using HH)))
  have HphysicalNorm := div_le_div_of_nonneg_right Hphysical htarget.le
  have Hcount := a.actual_mass_log_count_le hN hlog (by linarith [h8,hlo.2])
  have HcountTerm : ((2*bound+4*bound)*
      ((Nat.ceil (Real.log (1/a.context.U)/Real.log 2):ℝ)+1))/target ≤
      24*Ccount*Real.log a.context.N*a.context.N^(-eta) := by
    have HE : ((2*bound+4*bound)*
      ((Nat.ceil (Real.log (1/a.context.U)/Real.log 2):ℝ)+1))/target=
      24*a.context.N^(-eta)*((Nat.ceil (Real.log (1/a.context.U)/Real.log 2):ℝ)+1) := by
      dsimp [bound]
      field_simp
      ring
    rw [HE]
    have HH := mul_le_mul_of_nonneg_left Hcount (show 0 ≤ 24*a.context.N^(-eta) by positivity)
    convert HH using 1
    ring
  have Hfloor := mass_high_floor_slab_normalized_le (delta:=delta) (U:=a.context.U)
    a.hxs hW hv hcu hc hhi.1 le_rfl
    a.context.hN.le hKfloor.le hxsW hvlo
  have HfloorSource := a.canonical_direct_test_floor_strong_rate hC0 hCs hsmall
  have HfloorCoef : 0 ≤ Kfloor*cu*(1/c+2)^2 := by positivity
  have HfloorMul := mul_le_mul_of_nonneg_left HfloorSource HfloorCoef
  have Hbounds := actualMassSavingExponent_bounds m delta
  have HfloorPower : a.context.N^(-(6*m-delta)) ≤ a.context.N^(-eta) :=
    Real.rpow_le_rpow_of_exponent_le hN (by dsimp [eta]; nlinarith [Hbounds.2.1])
  have HfloorTerm : (Kfloor*(a.xs+2*v)^2*a.context.N^delta*a.context.U^2/(v/cu))/target ≤
      Cfloor*Real.log a.context.N*a.context.N^(-eta) := by
    apply Hfloor.trans
    have HH := mul_le_mul_of_nonneg_left HfloorPower (show 0 ≤ Cfloor by dsimp [Cfloor]; positivity)
    have HL := mul_le_mul_of_nonneg_left hlog (show 0 ≤ Cfloor*a.context.N^(-eta) by dsimp [Cfloor]; positivity)
    dsimp [Cfloor] at HH HL ⊢
    nlinarith only [HfloorMul,HH,HL]
  have Htotal : (∫u in v..2*v,
      orderedPathB (n+1) a.bf a.hf u-(orderedPathS (n+1) a.bf a.hf u)^2)/target ≤
      Ctotal*Real.log a.context.N*a.context.N^(-eta) := by
    apply HphysicalNorm.trans
    rw [add_div]
    have HH := add_le_add HcountTerm HfloorTerm
    convert HH using 1
    dsimp [Ctotal]
    ring
  exact Htotal.trans (by simpa only [NativeOverlapContext.N,pow_one] using hnrate)

end OAI.SKFluctuations.LaplaceWindowFormalization
