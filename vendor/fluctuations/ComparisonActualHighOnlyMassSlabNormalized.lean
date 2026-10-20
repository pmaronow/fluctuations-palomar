module

public import ComparisonActualHighOnlyLocalMassAssembly
public import ComparisonActualHighOnlyMassSlabScale
public import ComparisonActualHighOnlyMassBandRates
public import ComparisonActualHighOnlyBroadMassRates

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 12000000
open ActualHighOnlyOverlapMinimum

theorem eventually_actual_high_only_complete_mass_slab_normalized_le
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (c C : ℝ) (hc : 0 < c) (hcC : c ≤ C) :
    ∃Cwall Cfloor : ℝ,0 ≤ Cwall ∧ 0 ≤ Cfloor ∧ ∀ᶠn:ℕ in atTop,
      ∀a:ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      a.data.s ≤ 1/4 → a.data.s ≤ a.xs →
      NativePullbackClockRegularity a.alpha.val.val a.b a.h 0 1 →
      ∀W : ℝ,a.xs ≤ W → W ≤ 1 → C*W ≤ 1 → 32*a.data.s < c*W →
        max a.data.U a.data.s/W ≤ 1 →
      (∫u in c*W..C*W,orderedPathB (n+1) a.bf a.hf u-(orderedPathS (n+1) a.bf a.hf u)^2)/W^3 ≤ 
        a.data.N^(-(actualMassSavingExponent m delta/2))+
          Cwall*(max a.data.U a.data.s/W)+Cfloor*(a.data.s/W+a.data.U/W) := by
  obtain ⟨Qo,Qb,Kfloor,Kwall,hQo,hQb,hKfloor,hKwall,Hassembly⟩:=
    eventually_actual_high_only_local_mass_of_explicit_budgets 3 (by norm_num) Bclock
      (D:=D) hm hdelta hroom hcl hcu hAz hC0 hCt
  let η:=actualMassSavingExponent m delta
  let Ccount:=(1+Real.log (1+D^2))/Real.log 2+2
  have hη : 0 < η:=actualMassSavingExponent_pos hm hdelta
  have hC : 0 ≤ C:=hc.le.trans hcC
  have Hordinary:=canonical_ordinary_mass_band_budget_polynomial_le (cu:=cu) (D:=D)
    (Bclock:=Bclock) 3 (by norm_num) Qo (c/16) (2*C) (by positivity) (by positivity)
    hm hdelta hcl hAz hCt hC0
  have Hbroad:=canonical_broad_mass_band_budget_polynomial_le (cu:=cu) (D:=D)
    (Bclock:=Bclock) 3 (by norm_num) Qb (c/16) (2*C) (by positivity) (by positivity)
    hm hdelta hcl hAz hCt hC0
  have Hdecay:=(tendsto_add_atTop_nat 1).eventually
    (native_mass_log_power_decay (q:=η) (s:=η/2) (by linarith) 1 (6*Ccount))
  have Hratio:=(tendsto_add_atTop_nat 1).eventually
    (eventually_coefficient_rpow_le (c:=C0^3) (d:=c) (q:=-3*m) (r:=0) hc (by linarith))
  have Hlog:=(tendsto_add_atTop_nat 1).eventually
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (1:ℝ)))
  have Hcut:=eventually_actual_high_only_mass_polynomial_cut_feasible
    (m:=m) (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az) (C0:=C0) (Ct:=Ct) (D:=D) (Bclock:=Bclock)
  refine ⟨648*Kwall,Kfloor*(1+C)^2,by positivity,by positivity,?_⟩
  filter_upwards [Hassembly,Hordinary,Hbroad,Hdecay,Hratio,Hlog,Hcut]
    with n hnassembly hnordinary hnbroad hndecay hnratio hnlog hncut
  intro a hs hsxs hclock W hxsW hW1 hCW1 hstart hLW
  have hW : 0 < W:=a.hxs.trans_le hxsW
  have hWcube : 0 < W^3:=pow_pos hW 3
  have hN : 1 ≤ a.data.N:=by dsimp only [ActualHighOnlyComparisonData.N];exact_mod_cast Nat.succ_pos n
  have hlog : 1 ≤ Real.log a.data.N:=by simpa only [ActualHighOnlyComparisonData.N,Function.comp_def] using hnlog
  have hlo : c*W∈Icc (0:ℝ) 1:=⟨by positivity,(mul_le_mul_of_nonneg_right hcC hW.le).trans hCW1⟩
  have hhi : C*W∈Icc (0:ℝ) 1:=⟨by positivity,hCW1⟩
  have hlh : c*W ≤ C*W:=mul_le_mul_of_nonneg_right hcC hW.le
  have Ht : a.data.U/W ≤ C0^3*a.data.N^(-3*m):=
    (div_le_div_of_nonneg_left a.data.hU.le a.hxs hxsW).trans (a.canonical_mass_small_ratio hC0)
  have Htc : a.data.U/W ≤ c:=Ht.trans (by
    simpa only [ActualHighOnlyComparisonData.N,Real.rpow_zero,mul_one] using hnratio)
  have hU : a.data.U ≤ c*W:=(div_le_iff₀ hW).mp Htc
  have hcutpos : 0 < a.data.N^(-(10:ℝ)):=Real.rpow_pos_of_pos a.data.hN _
  have hlogcut : Real.log (1/a.data.N^(-(10:ℝ))) ≤ 10*Real.log a.data.N:=by
    rw [one_div,Real.log_inv,Real.log_rpow a.data.hN]
    ring_nf
    exact le_rfl
  have hLside : 0 ≤ 10*Real.log a.data.N:=by linarith
  have hbudget0 : 0 ≤ a.data.N^(-η)*W^3:=by positivity
  obtain ⟨P⟩:=a.exists_potential_high_only hs
  have Hphysical:=hnassembly a hs hsxs P hclock (c*W) (C*W) (a.data.N^(-(10:ℝ)))
    (10*Real.log a.data.N) (a.data.N^(-η)*W^3) (a.data.N^(-η)*W^3)
    hlo hhi hlh hU hstart hcutpos (hncut a) hLside hlogcut hbudget0 hbudget0
    (by
      intro v hvs hv hv1
      have hvl : (c/16)*W ≤ v:=by nlinarith [hvs.1]
      have hvh : v ≤ (2*C)*W:=by nlinarith [hvs.2]
      exact (div_le_iff₀ hWcube).mp (hnordinary a W hxsW hW1 v hv hv1 hvl hvh))
    (by
      intro v hvs hv hv1 width hw hw1
      have hvl : (c/16)*W ≤ v:=by nlinarith [hvs.1,mul_pos hc hW]
      have hvh : v ≤ (2*C)*W:=by nlinarith [hvs.2]
      exact (div_le_iff₀ hWcube).mp (hnbroad a W hxsW hW1 v width hv hvl hvh hw.1 hw.2 hw1))
  have Hnorm:=div_le_div_of_nonneg_right Hphysical hWcube.le
  have Hcount:=a.actual_mass_log_count_le hN hlog (hU.trans hlo.2)
  have HcountTerm : ((2*(a.data.N^(-η)*W^3)+4*(a.data.N^(-η)*W^3))*
      ((Nat.ceil (Real.log (1/a.data.U)/Real.log 2):ℝ)+1))/W^3 ≤ a.data.N^(-(η/2)):=by
    have HE : ((2*(a.data.N^(-η)*W^3)+4*(a.data.N^(-η)*W^3))*
      ((Nat.ceil (Real.log (1/a.data.U)/Real.log 2):ℝ)+1))/W^3=
      6*a.data.N^(-η)*((Nat.ceil (Real.log (1/a.data.U)/Real.log 2):ℝ)+1):=by field_simp;ring
    rw [HE]
    have HH:=mul_le_mul_of_nonneg_left Hcount (show 0 ≤ 6*a.data.N^(-η) by positivity)
    apply (show 6*a.data.N^(-η)*((Nat.ceil (Real.log (1/a.data.U)/Real.log 2):ℝ)+1) ≤ 
      (6*Ccount)*Real.log a.data.N*a.data.N^(-η) from by convert HH using 1;ring).trans
    simpa only [ActualHighOnlyComparisonData.N,pow_one] using hndecay
  let L:=max a.data.U a.data.s
  have hL : 0 ≤ L:=a.data.hU.le.trans (le_max_left _ _)
  have Hwall:=mass_wall_cubic_normalized_le a.hxs hxsW hL hLW hKwall.le
  have HfloorPow : a.data.N^(-delta) ≤ 1:=by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hN (show -delta ≤ 0 by linarith)
  let Ufloor:=a.data.s+a.data.N^(-delta)*a.data.U
  have hUfloor : 0 ≤ Ufloor:=add_nonneg a.data.hs.1
    (mul_nonneg (Real.rpow_nonneg a.data.hN.le _) a.data.hU.le)
  have Hfloor:=mass_floor_cubic_normalized_le (N:=1) (delta:=0) (Chi:=C)
    a.hxs hxsW hhi.1 le_rfl hKfloor.le zero_le_one hUfloor
  simp only [Real.one_rpow,mul_one] at Hfloor
  have HFU : Ufloor/W ≤ a.data.s/W+a.data.U/W:=by
    rw [add_div]
    apply add_le_add le_rfl
    exact div_le_div_of_nonneg_right
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right HfloorPow a.data.hU.le) hW.le
  have HFprice:=mul_le_mul_of_nonneg_left HFU (show 0 ≤ Kfloor*(1+C)^2 by positivity)
  apply Hnorm.trans
  rw [add_div,add_div]
  exact add_le_add (add_le_add HcountTerm Hwall) (Hfloor.trans HFprice)

end OAI.SKFluctuations.LaplaceWindowFormalization
