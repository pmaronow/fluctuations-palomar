module

public import ComparisonActualHighOnlyOuterComparableMassAssembly
public import ComparisonActualHighOnlyComparableContext
public import ComparisonActualHighOnlyLocalDiameterBudgetMonotonicity
public import ComparisonActualHighOnlyIntermediateMassBroadRates
public import ComparisonActualHighOnlyIntermediateMassOrdinaryRates
public import ComparisonActualHighOnlyIntermediateMassReverseRates
public import ComparisonNativeActualIntermediateMassSlabNormalization
public import ComparisonActualHighOnlyHighMassFloorNormalization
public import ComparisonActualHighOnlyMassSlabScale

@[expose] public section

noncomputable section
set_option maxHeartbeats 15000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators

theorem eventually_actual_high_only_regular_strong_intermediate_mass_dyad
    (C Bclock : ℝ) {m delta cl cu Az C0 Ct D Cs c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs) (hc : 0 < c) (hcouter : 2*cu*(Az+1) ≤ c) :
    ∀ᶠn : ℕ in atTop,
      ∀(a : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
        (_hclock : NativePullbackClockRegularity a.alpha.val.val a.b a.h 0 1),
        a.data.s≤1/4 → a.data.s≤a.xs → 64*a.data.s≤c*a.xs →
        a.xs^2 ≤ Cs*laplaceComparisonStrength a.data.d a.lam a.xs →
        a.canonicalDirectTestBandScale ≤ 1 →
        ∀v : ℝ, 0 < v → 2*v ≤ 1 → c*a.xs ≤ v →
          v ≤ C*a.canonicalDirectTestBandScale →
          (∫u in v..2*v,orderedPathB (n+1) a.bf a.hf u-(orderedPathS (n+1) a.bf a.hf u)^2)/
            (a.xs^4*v/(actualIntermediateMassEffectiveScale a.canonicalDirectTestBandScale v)^2) ≤
              a.data.N^(-(actualMassSavingExponent m delta/2)) := by
  by_cases hD : 0 < D
  swap
  · apply Eventually.of_forall
    intro n a
    exact False.elim (hD (a.data.hd.trans_le a.hdD))
  let Cdiam := 576+288*cu^3/cl^3+1
  let csource := c/16
  let Csource := 4*C
  have hCdiam : 0 < Cdiam := by dsimp [Cdiam]; positivity
  have hCdiamOrd : 576 ≤ Cdiam := by
    dsimp [Cdiam]
    have HH : 0 ≤ 288*cu^3/cl^3 := by positivity
    linarith
  have hCdiamBroad : 288*cu^3/cl^3 ≤ Cdiam := by dsimp [Cdiam]; linarith
  have hcsource : 0 < csource := by dsimp [csource]; positivity
  obtain ⟨l,hl,HreverseFactory⟩ := ActualHighOnlyOverlapMinimum.exists_actual_intermediate_mass_reverse_polynomial_order
    (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (Bclock:=Bclock)
    Csource hm hdelta hC0 hD hCs hcsource hCdiam
  obtain ⟨Qo,Qb,hQfloor,hQo,hQb,hKfloor,Hassembly⟩ := eventually_actual_high_only_outer_comparable_mass_of_explicit_budgets
    (D:=D) l hl Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  let Kfloor:=hQfloor
  have HordinaryReverse := HreverseFactory Qo hQo
  have HbroadReverse := HreverseFactory Qb hQb
  have Hordinary := ActualHighOnlyOverlapMinimum.eventually_intermediate_mass_ordinary_budget_of_reverse_rate
    l hl Qo hm hdelta hcl hAz hCt hC0 hCs hcsource hCdiam HordinaryReverse
  have Hbroad := ActualHighOnlyOverlapMinimum.chosen_intermediate_comparable_broad_budget_polynomial_le
    l hl Qb hQb hm hdelta hcl hcu hAz hCt hC0 hCs hcsource hCdiam HbroadReverse
  let eta := actualMassSavingExponent m delta
  let Ccount := (1+Real.log (1+D^2))/Real.log 2+2
  let Cfloor := Kfloor*cu*(1/c+2)^2*(max 1 C)^2*(Cs+1)^2*C0^6
  let Ctotal := 24*Ccount+Cfloor
  have heta : 0 < eta := actualMassSavingExponent_pos hm hdelta
  have Hdecay := (tendsto_add_atTop_nat 1).eventually
    (native_mass_log_power_decay (q:=eta) (s:=eta/2) (by linarith) 1 Ctotal)
  have Hratio := (tendsto_add_atTop_nat 1).eventually
    (eventually_coefficient_rpow_le (c:=C0^3) (d:=c/64) (q:=-3*m) (r:=0) (by positivity) (by linarith))
  have Hdepth := (tendsto_add_atTop_nat 1).eventually (eventually_comparisonLowerScale_depth hC0 hm)
  have Hlog := (tendsto_add_atTop_nat 1).eventually
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (1:ℝ)))
  have Hcut := eventually_actual_high_only_mass_polynomial_cut_feasible
    (m:=m) (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az) (C0:=C0) (Ct:=Ct) (D:=D) (Bclock:=Bclock)
  filter_upwards [Hassembly,Hordinary,Hbroad,Hdecay,Hratio,Hdepth,Hlog,Hcut]
    with n hnassembly hnordinary hnbroad hnrate hnratio hndepth hnlog hncut
  intro a hclock hs hsxs hsomit hsmall hW1 v hv hv2 hvlo hvupper
  let W := a.canonicalDirectTestBandScale
  let Beff := actualIntermediateMassEffectiveScale W v
  let target := a.xs^4*v/Beff^2
  let bound := 4*a.data.N^(-eta)*target
  have hW : 0 < W := a.canonical_direct_test_band_pos
  have hBeff : 0 < Beff := actualIntermediateMassEffectiveScale_pos hW hv
  have hxs := a.hxs
  have htarget : 0 < target := by dsimp [target]; positivity
  have hbound : 0 ≤ bound := by dsimp [bound]; positivity
  have hN : 1 ≤ a.data.N := by dsimp [ActualHighOnlyComparisonData.N]; exact_mod_cast Nat.succ_pos n
  have hlog : 1 ≤ Real.log a.data.N := by simpa only [ActualHighOnlyComparisonData.N,Function.comp_def] using hnlog
  have hlog0 : 0 ≤ Real.log a.data.N := zero_le_one.trans hlog
  have hnd : 1/a.data.N ≤ a.data.d := by
    have hd := hndepth a.data.E a.data.d a.data.hE a.data.hd a.hlower
    have hs : comparisonLowerScale (n+1 : ℕ) a.data.E a.data.d ≤ a.data.d := by
      unfold comparisonLowerScale
      exact (div_le_iff₀ a.data.hd).mpr (by simpa only [pow_two] using a.hupper)
    exact hd.trans hs
  obtain ⟨p⟩ := a.exists_potential_high_only hs
  have hxsW := a.canonical_direct_test_band_ge_scale
  have hUratio : a.data.U/a.xs≤c/64:=a.canonical_mass_small_ratio hC0 |>.trans (by
    simpa only [ActualHighOnlyComparisonData.N,Real.rpow_zero,mul_one] using hnratio)
  have hUscale : 64*a.data.U≤c*a.xs:=by
    have H:=(div_le_iff₀ a.hxs).mp hUratio
    linarith
  have hU : a.data.U≤v:=by nlinarith only [hUscale,hvlo,mul_pos hc a.hxs]
  have hstart : 32*a.data.s<v:=by nlinarith only [hsomit,hvlo,mul_pos hc a.hxs]
  have hwall : 8*a.massCoverBase<v:=by
    have H0:=mul_pos hc a.hxs
    unfold ActualHighOnlyOverlapMinimum.massCoverBase
    rw [mul_max_of_nonneg a.data.U a.data.s (by norm_num : (0:ℝ)≤8)]
    exact max_lt (by nlinarith only [hUscale,hvlo,H0]) (by nlinarith only [hsomit,hvlo,H0])
  have houter : 2*cu*(Az+1)*a.xs ≤ v :=
    (mul_le_mul_of_nonneg_right hcouter a.hxs.le).trans hvlo
  have hlo : v∈Icc (0:ℝ) 1 := ⟨hv.le,by linarith⟩
  have hhi : 2*v∈Icc (0:ℝ) 1 := ⟨by positivity,hv2⟩
  have hcutpos : 0 < a.data.N^(-(10:ℝ)) := Real.rpow_pos_of_pos a.data.hN _
  have hlogcut : Real.log (1/a.data.N^(-(10:ℝ))) ≤ 10*Real.log a.data.N := by
    rw [one_div,Real.log_inv,Real.log_rpow a.data.hN]
    ring_nf
    exact le_refl _
  have hLside : 0 ≤ 10*Real.log a.data.N := by linarith
  have Hphysical := hnassembly a hs hsxs p hclock v (2*v) (a.data.N^(-(10:ℝ)))
    (10*Real.log a.data.N) bound bound hlo hhi (by linarith) hU hstart hwall houter
    hcutpos (hncut a) hLside hlogcut hbound hbound
    (by
      intro s hs hsp hs1
      have hslo : csource*a.xs ≤ s := by dsimp [csource]; nlinarith [hs.1]
      have hsupper : s ≤ Csource*W := by dsimp [Csource]; nlinarith [hs.2]
      have Hsource := a.canonical_ordinary_mass_budget_at_diameter_mono
        (Q:=Qo) (cut:=a.data.N^(-(10:ℝ))) hl hsp hLside
        (a.canonical_local_mass_diameter_pos (by linarith) hsp).le
        (a.canonical_local_mass_diameter_le_chosen hCdiamOrd hlog0 hsp)
      have Hnumeric := hnordinary a hsmall hW1 s hsp hs1 hslo hsupper
      have HBsource := actualIntermediateMassEffectiveScale_pos hW hsp
      have Hstarget : 0 < a.xs^4*s/(actualIntermediateMassEffectiveScale W s)^2 := by positivity
      have Hsave := (div_le_iff₀ Hstarget).mp Hnumeric
      have Hscale : a.xs^4*s/(actualIntermediateMassEffectiveScale W s)^2 ≤ 4*target :=
        actual_intermediate_mass_target_local_le a.hxs hW hsp hv (by linarith [hs.2])
      have HH := mul_le_mul_of_nonneg_left Hscale (Real.rpow_nonneg a.data.hN.le (-eta))
      exact Hsource.trans (Hsave.trans (by simpa only [bound,mul_assoc,mul_left_comm,mul_comm] using HH)))
    (by
      intro s hs hsp hs1 width hw hw1
      have hslo : csource*a.xs ≤ s := by dsimp [csource]; nlinarith [hs.1,mul_pos hc a.hxs]
      have hsupper : s ≤ Csource*W := by dsimp [Csource]; nlinarith [hs.2]
      have hU := a.data.hU
      have hE := a.data.hE
      have hd := a.data.hd
      have hN0 := a.data.hN
      have htravel0 : 0 ≤ a.cavityCapTravel := by
        unfold ActualHighOnlyOverlapMinimum.cavityCapTravel
        have hLcap := a.data.hL
        have Hrl : 0 ≤ Real.log ((1+a.data.U)/a.data.U) :=
          Real.log_nonneg ((one_le_div hU).mpr (by linarith))
        positivity
      have houterD0 : 0 ≤ a.canonicalOuterBroadMassDiameter s := by
        unfold ActualHighOnlyOverlapMinimum.canonicalOuterBroadMassDiameter
        exact mul_nonneg (by positivity) (le_min htravel0 (by positivity))
      have Hsource := a.canonical_comparable_broad_mass_budget_at_diameter_mono
        (Q:=Qb) (cut:=a.data.N^(-(10:ℝ))) hl hsp.le hLside
        (hsp.le.trans hw.1) houterD0
        (a.canonical_outer_mass_diameter_le_chosen hcl hcu hCdiamBroad hlog0 hsp)
      have Hnumeric := hnbroad a hsmall hW1 s width hsp hs1 hslo hsupper hw.1 hw.2 hw1
      have HBsource := actualIntermediateMassEffectiveScale_pos hW hsp
      have Hstarget : 0 < a.xs^4*s/(actualIntermediateMassEffectiveScale W s)^2 := by positivity
      have Hsave := (div_le_iff₀ Hstarget).mp Hnumeric
      have Hscale : a.xs^4*s/(actualIntermediateMassEffectiveScale W s)^2 ≤ 4*target :=
        actual_intermediate_mass_target_local_le a.hxs hW hsp hv (by linarith [hs.2])
      have HH := mul_le_mul_of_nonneg_left Hscale (Real.rpow_nonneg a.data.hN.le (-eta))
      exact Hsource.trans (Hsave.trans (by simpa only [bound,mul_assoc,mul_left_comm,mul_comm] using HH)))
  have HphysicalNorm := div_le_div_of_nonneg_right Hphysical htarget.le
  have Hcount := a.actual_mass_log_count_le hN hlog (hU.trans hlo.2)
  have HcountTerm : ((2*bound+4*bound)*
      ((Nat.ceil (Real.log (1/a.data.U)/Real.log 2):ℝ)+1))/target ≤
      24*Ccount*Real.log a.data.N*a.data.N^(-eta) := by
    have HE : ((2*bound+4*bound)*
      ((Nat.ceil (Real.log (1/a.data.U)/Real.log 2):ℝ)+1))/target=
      24*a.data.N^(-eta)*((Nat.ceil (Real.log (1/a.data.U)/Real.log 2):ℝ)+1) := by
      dsimp [bound]
      field_simp
      ring
    rw [HE]
    have HH := mul_le_mul_of_nonneg_left Hcount (show 0 ≤ 24*a.data.N^(-eta) by positivity)
    convert HH using 1
    ring
  have Hfloor := mass_intermediate_floor_slab_normalized_le (delta:=delta) (U:=a.data.U)
    a.hxs hW hv hcu hc a.data.hN.le hKfloor.le hvlo hvupper
  have HfloorSource := a.canonical_direct_test_floor_strong_rate hC0 hCs hsmall
  have HfloorCoef : 0 ≤ Kfloor*cu*(1/c+2)^2*(max 1 C)^2 := by positivity
  have HfloorMul := mul_le_mul_of_nonneg_left HfloorSource HfloorCoef
  have Hbounds := actualMassSavingExponent_bounds m delta
  have HfloorPower : a.data.N^(-(6*m-delta)) ≤ a.data.N^(-eta) :=
    Real.rpow_le_rpow_of_exponent_le hN (by dsimp [eta]; nlinarith [Hbounds.2.1])
  have HfloorTerm : (Kfloor*(a.xs+2*v)^2*a.data.N^delta*a.data.U^2/(v/cu))/target ≤
      Cfloor*Real.log a.data.N*a.data.N^(-eta) := by
    apply Hfloor.trans
    have HH := mul_le_mul_of_nonneg_left HfloorPower (show 0 ≤ Cfloor by dsimp [Cfloor]; positivity)
    have HL := mul_le_mul_of_nonneg_left hlog (show 0 ≤ Cfloor*a.data.N^(-eta) by dsimp [Cfloor]; positivity)
    dsimp [Cfloor] at HH HL ⊢
    nlinarith only [HfloorMul,HH,HL]
  have Htotal : (∫u in v..2*v,
      orderedPathB (n+1) a.bf a.hf u-(orderedPathS (n+1) a.bf a.hf u)^2)/target ≤
      Ctotal*Real.log a.data.N*a.data.N^(-eta) := by
    apply HphysicalNorm.trans
    rw [add_div]
    have HH := add_le_add HcountTerm HfloorTerm
    convert HH using 1
    dsimp [Ctotal]
    ring
  exact Htotal.trans (by simpa only [ActualHighOnlyComparisonData.N,pow_one] using hnrate)

end OAI.SKFluctuations.LaplaceWindowFormalization
