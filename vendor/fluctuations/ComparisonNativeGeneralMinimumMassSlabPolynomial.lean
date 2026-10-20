module

public import ComparisonNativeGeneralMinimumLocalMassAssembly
public import ComparisonNativeActualMassSlabScale
public import ComparisonNativeActualMassBandRates
public import ComparisonNativeActualBroadMassRates

@[expose] public section

noncomputable section
set_option maxHeartbeats 10000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators

theorem eventually_general_minimum_complete_mass_slab_polynomial
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (c C : ℝ) (hc : 0 < c) (hcC : c ≤ C) :
    ∀ᶠn : ℕ in atTop,
      ∀(a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
        (Kb Kh : ℝ≥0),
      LipschitzOnWith Kb (fun r=>a.b (a.alpha.val.val r)) (Icc 0 1) →
      LipschitzOnWith Kh (fun r=>a.h (a.alpha.val.val r)) (Icc 0 1) →
      ∀W : ℝ, a.xs ≤ W → W ≤ 1 → C*W ≤ 1 →
        (∫u in c*W..C*W,orderedPathB (n+1) a.bf a.hf u-(orderedPathS (n+1) a.bf a.hf u)^2)/W^3 ≤
          a.context.N^(-(actualMassSavingExponent m delta/2)) := by
  obtain ⟨Q,hQ,Kfloor,Kwall,hKfloor,hKwall,Hassembly⟩ :=
    eventually_general_minimum_local_mass_of_explicit_budgets (D:=D) 2 (by norm_num)
      Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  let η := actualMassSavingExponent m delta
  let Ccount := (1+Real.log (1+D^2))/Real.log 2+2
  let Ctotal := 6*Ccount+648*Kwall*C0^3+Kfloor*(1+C)^2*C0^3
  have hη : 0 < η := actualMassSavingExponent_pos hm hdelta
  have hC : 0 ≤ C := hc.le.trans hcC
  have hlow : 0 < c/16 := by positivity
  have hhigh : 0 ≤ 2*C := by positivity
  have Hordinary := NativeOverlapMinimum.canonical_ordinary_mass_band_budget_polynomial_le
    (cu:=cu) (D:=D) (Bclock:=Bclock) 3 (by norm_num) Q (c/16) (2*C) hlow hhigh hm hdelta hcl hAz hCt hC0
  have Hbroad := NativeOverlapMinimum.canonical_broad_mass_band_budget_polynomial_le
    (cu:=cu) (D:=D) (Bclock:=Bclock) 3 (by norm_num) Q (c/16) (2*C) hlow hhigh hm hdelta hcl hAz hCt hC0
  have Hdecay := (tendsto_add_atTop_nat 1).eventually
    (native_mass_log_power_decay (q:=η) (s:=η/2) (by linarith) 1 Ctotal)
  have Hratio := (tendsto_add_atTop_nat 1).eventually
    (eventually_coefficient_rpow_le (c:=C0^3) (d:=c) (q:=-3*m) (r:=0) hc (by linarith))
  have HratioOne := (tendsto_add_atTop_nat 1).eventually
    (eventually_coefficient_rpow_le (c:=C0^3) (d:=1) (q:=-3*m) (r:=0) zero_lt_one (by linarith))
  have Hgeom := NativeOverlapMinimum.eventually_exists_actual_common_geometry_lipschitz
    (m:=m) (cl:=cl) (cu:=cu) (Az:=Az) (C0:=C0) (Ct:=Ct) (D:=D) (Bclock:=Bclock) hdelta
  have Hdepth := (tendsto_add_atTop_nat 1).eventually (eventually_comparisonLowerScale_depth hC0 hm)
  have Hlog := (tendsto_add_atTop_nat 1).eventually
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (1:ℝ)))
  have Hcut := eventually_actual_mass_polynomial_cut_feasible
    (m:=m) (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az) (C0:=C0) (Ct:=Ct) (D:=D) (Bclock:=Bclock)
  filter_upwards [Hassembly,Hordinary,Hbroad,Hdecay,Hratio,HratioOne,Hgeom,Hdepth,Hlog,Hcut]
    with n hnassembly hnordinary hnbroad hndecay hnratio hnratioOne hngeom hndepth hnlog hncut
  intro a Kb Kh hparent hfield W hxsW hW1 hCW1
  have hW : 0 < W := a.hxs.trans_le hxsW
  have hWcube : 0 < W^3 := pow_pos hW 3
  have hN : 1 ≤ a.context.N := by dsimp [NativeOverlapContext.N]; exact_mod_cast Nat.succ_pos n
  have hlog : 1 ≤ Real.log a.context.N := by simpa only [NativeOverlapContext.N,Function.comp_def] using hnlog
  have hnd : 1/a.context.N ≤ a.context.d := by
    have hd := hndepth a.context.E a.context.d a.context.hE a.context.hd a.hlower
    have hs : comparisonLowerScale (n+1 : ℕ) a.context.E a.context.d ≤ a.context.d := by
      unfold comparisonLowerScale
      exact (div_le_iff₀ a.context.hd).mpr (by simpa only [pow_two] using a.hupper)
    exact hd.trans hs
  obtain ⟨p,_⟩ := hngeom a Kb Kh hparent hfield
  have hlo : c*W∈Icc (0:ℝ) 1 := ⟨by positivity,(mul_le_mul_of_nonneg_right hcC hW.le).trans hCW1⟩
  have hhi : C*W∈Icc (0:ℝ) 1 := ⟨by positivity,hCW1⟩
  have hlh : c*W ≤ C*W := mul_le_mul_of_nonneg_right hcC hW.le
  have Ht : a.context.U/W ≤ C0^3*a.context.N^(-3*m) :=
    (div_le_div_of_nonneg_left a.context.hU.le a.hxs hxsW).trans (a.canonical_mass_small_ratio hC0)
  have Htc : a.context.U/W ≤ c := Ht.trans (by
    simpa only [NativeOverlapContext.N,Real.rpow_zero,mul_one] using hnratio)
  have HtOne : a.context.U/W ≤ 1 := Ht.trans (by
    simpa only [NativeOverlapContext.N,Real.rpow_zero,mul_one] using hnratioOne)
  have hU : a.context.U ≤ c*W := (div_le_iff₀ hW).mp Htc
  have hcutpos : 0 < a.context.N^(-(10:ℝ)) := Real.rpow_pos_of_pos a.context.hN _
  have hlogcut : Real.log (1/a.context.N^(-(10:ℝ))) ≤ 10*Real.log a.context.N := by
    rw [one_div,Real.log_inv,Real.log_rpow a.context.hN]
    ring_nf
    exact le_refl _
  have hLside : 0 ≤ 10*Real.log a.context.N := by linarith
  have hbudget0 : 0 ≤ a.context.N^(-η)*W^3 := by positivity
  have Hphysical := hnassembly a p Kb Kh hparent hfield (Fintype.card (FeatureIndex (n+1))-1)
    (cavityCanonicalFeatureEquiv n) hlog hnd (10*Real.log a.context.N) hLside
    (c*W) (C*W) (a.context.N^(-(10:ℝ))) (a.context.N^(-η)*W^3) (a.context.N^(-η)*W^3)
    hlo hhi hlh hU hcutpos (hncut a) hlogcut hbudget0 hbudget0
    (by
      intro v hvs hv hv1
      have hvl : (c/16)*W ≤ v := by nlinarith [hvs.1]
      have hvh : v ≤ (2*C)*W := by nlinarith [hvs.2]
      exact (div_le_iff₀ hWcube).mp (hnordinary a W hxsW hW1 v hv hv1 hvl hvh))
    (by
      intro v hvs hv _ width hw hw1
      have hvl : (c/16)*W ≤ v := by nlinarith [hvs.1,mul_pos hc hW]
      have hvh : v ≤ (2*C)*W := by nlinarith [hvs.2]
      exact (div_le_iff₀ hWcube).mp (hnbroad a W hxsW hW1 v width hv hvl hvh hw.1 hw.2 hw1))
  have HphysicalNorm := div_le_div_of_nonneg_right Hphysical hWcube.le
  have Hcount := a.actual_mass_log_count_le hN hlog (hU.trans hlo.2)
  have HcountTerm : ((2*(a.context.N^(-η)*W^3)+4*(a.context.N^(-η)*W^3))*
      ((Nat.ceil (Real.log (1/a.context.U)/Real.log 2):ℝ)+1))/W^3 ≤
      6*Ccount*Real.log a.context.N*a.context.N^(-η) := by
    have HE : ((2*(a.context.N^(-η)*W^3)+4*(a.context.N^(-η)*W^3))*
      ((Nat.ceil (Real.log (1/a.context.U)/Real.log 2):ℝ)+1))/W^3=
      6*a.context.N^(-η)*((Nat.ceil (Real.log (1/a.context.U)/Real.log 2):ℝ)+1) := by field_simp; ring
    rw [HE]
    have HH := mul_le_mul_of_nonneg_left Hcount (show 0 ≤ 6*a.context.N^(-η) by positivity)
    convert HH using 1
    ring
  have Hbounds := actualMassSavingExponent_bounds m delta
  have Hpower : a.context.N^(-3*m) ≤ a.context.N^(-η) :=
    Real.rpow_le_rpow_of_exponent_le hN (by dsimp [η]; nlinarith [Hbounds.2.1])
  have Htsave : a.context.U/W ≤ C0^3*a.context.N^(-η) :=
    Ht.trans (mul_le_mul_of_nonneg_left Hpower (by positivity))
  have Hwall := mass_wall_cubic_normalized_le a.hxs hxsW a.context.hU.le HtOne hKwall.le
  have HwallTerm : 8*Kwall*(a.xs+8*a.context.U)^2*a.context.U/W^3 ≤
      (648*Kwall*C0^3)*Real.log a.context.N*a.context.N^(-η) := by
    apply Hwall.trans
    have HH := mul_le_mul_of_nonneg_left Htsave (show 0 ≤ 648*Kwall by positivity)
    have HL := mul_le_mul_of_nonneg_left hlog
      (show 0 ≤ (648*Kwall*C0^3)*a.context.N^(-η) by positivity)
    nlinarith only [HH,HL]
  have Hfloor := mass_floor_cubic_normalized_le (delta:=delta) (Chi:=C) a.hxs hxsW hhi.1 le_rfl hKfloor.le
    a.context.hN.le a.context.hU.le
  have HfloorPower : a.context.N^(-delta) ≤ 1 := by
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_le hN (show -delta ≤ 0 by linarith)
  have HfloorTerm : Kfloor*(a.xs+C*W)^2*a.context.N^(-delta)*a.context.U/W^3 ≤
      (Kfloor*(1+C)^2*C0^3)*Real.log a.context.N*a.context.N^(-η) := by
    apply Hfloor.trans
    have HH := mul_le_mul HfloorPower Htsave (div_nonneg a.context.hU.le hW.le) zero_le_one
    have HC := mul_le_mul_of_nonneg_left HH (show 0 ≤ Kfloor*(1+C)^2 by positivity)
    have HL := mul_le_mul_of_nonneg_left hlog
      (show 0 ≤ (Kfloor*(1+C)^2*C0^3)*a.context.N^(-η) by positivity)
    nlinarith only [HC,HL]
  have Htotal : (∫u in c*W..C*W,
      orderedPathB (n+1) a.bf a.hf u-(orderedPathS (n+1) a.bf a.hf u)^2)/W^3 ≤
      Ctotal*Real.log a.context.N*a.context.N^(-η) := by
    apply HphysicalNorm.trans
    rw [add_div,add_div]
    have HH := add_le_add (add_le_add HcountTerm HwallTerm) HfloorTerm
    convert HH using 1
    dsimp [Ctotal]
    ring
  exact Htotal.trans (by simpa only [NativeOverlapContext.N,pow_one] using hndecay)

end OAI.SKFluctuations.LaplaceWindowFormalization
