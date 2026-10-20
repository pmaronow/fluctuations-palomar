module

public import ComparisonNativeActualLowerShellParameters
public import ComparisonNativeActualInitialUpperFromRegularSweep
public import ShellPressureGain
public import PhysicalEndpointBridge

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy PositiveLaplaceAssembly
open scoped Topology NNReal
set_option maxHeartbeats 32000000
set_option linter.unusedVariables false

theorem exists_actual_lower_pressure_comparison
    {beta : ℝ≥0} (hbeta : 0 < beta) (hTemp : 1 < (beta:ℝ)^2)
    {m : ℝ} (hm : 0 < m) (hmmax : m < 1/300) :
    ∃a b : ℝ,0 < a ∧ ∀ᶠn : ℕ in atTop,
      a*lowerEpsilon n*(lowerScale m n)^3-b*(n:ℝ)^(20*lowerDelta m)*lowerError m n ≤
        pressureIncrement (beta:ℝ) m n := by
  let T:ℝ:=(beta:ℝ)^2
  have hT : 0 < T := zero_lt_one.trans hTemp
  have hdelta : 0 < m/10000 := by positivity
  obtain ⟨cl,cu,hcl,hcu,hcl1,hcu1,Hregular⟩:=exists_actual_initial_shell_sweep_regular hbeta hTemp
    (delta:=m/10000) (C0:=1) hm hdelta (by linarith) zero_lt_one
    (by linarith) (by linarith) (by linarith)
  let c:=actualLowerShellNativeParameters m
  let epsilon:=fun n=>lowerEpsilon (n+1)
  let shell:=fun n=>(c n).d
  have HD:=actual_lower_shell_native_radius_tendsto_zero hmmax
  have Hnum n : (c n).d ≤ 1 ∧ Real.sqrt (c n).N*(c n).E ≤ (c n).d^2 ∧
      (c n).N^(-(2:ℝ)/3+m)*(c n).d ≤ 1*(c n).E := by
    have H:=actual_lower_shell_native_numeric hm hmmax n
    exact ⟨H.1,H.2.1,by simpa only [one_mul] using H.2.2.1⟩
  have HEps n : epsilon n∈Icc (0:ℝ) (((n+1:ℕ):ℝ)^(-(1:ℝ)/3)) :=
    ⟨Real.rpow_nonneg (c n).hN.le _,le_rfl⟩
  have HShell n : shell n∈Icc (0:ℝ) 1 := ⟨(c n).hd.le,(Hnum n).1⟩
  have HR:=Hregular c HD Hnum epsilon shell HEps HShell HD
  let Couter:=max 1 (1/cl)
  let k:=min 1 (1/Couter)
  let cShell:=1/(4*cu)
  have hOuter : 0 < Couter := zero_lt_one.trans_le (le_max_left _ _)
  have hk : 0 < k := lt_min zero_lt_one (one_div_pos.mpr hOuter)
  have hShell : 0 < cShell := by dsimp [cShell];positivity
  have HA := (actual_lower_shell_final_cutoff_ratio_tendsto_zero hm hmmax).eventually
    (eventually_le_nhds (by positivity : 0 < (1:ℝ)/(4*cu)))
  have HEpsSmall := (tendsto_add_atTop_nat 1).eventually (lowerEpsilon_eventually_le_scale_square hm hk)
  have Hgate : ∀ᶠn in atTop,(c n).d^2 ≤ T-1 := by
    have H:=(HD.pow 2).eventually (eventually_le_nhds (by dsimp only [T];linarith : (0:ℝ)^2 < T-1))
    simpa only [zero_pow (by norm_num : (2:ℕ) ≠ 0)] using H
  have Hq : ∀ᶠn in atTop,2 ≤ ((n+1:ℕ):ℝ)^(m/10000) :=
    ((tendsto_rpow_atTop hdelta).comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))).eventually (eventually_ge_atTop 2)
  have Hcost:=eventually_actual_shell_history_child_cost_of_regular (T:=T) (C0:=1)
    hm hdelta (by linarith) hcl hcu (hcl1.trans hcu1) zero_lt_one
  have Hshift : ∀ᶠn : ℕ in atTop,
      cShell^2/16*lowerEpsilon (n+1)*(lowerScale m (n+1))^3-
        1*((n+1:ℕ):ℝ)^(20*lowerDelta m)*lowerError m (n+1) ≤
          pressureIncrement (beta:ℝ) m (n+1) := by
    filter_upwards [HR,HA,HEpsSmall,Hgate,Hq,Hcost] with n hnReg hnA hnEps hnGate hnq hnCost
    let cn:=c n
    let s:=cn.d
    let eps:=epsilon n
    let b1:=initialShellMatrixClock T eps s
    have hN : 0 < cn.N := cn.hN
    have hN1 : 1 ≤ cn.N := by exact_mod_cast Nat.succ_pos n
    have hEps : 0 ≤ eps := (HEps n).1
    have hEps1 : eps ≤ 1 := (HEps n).2.trans
      (Real.rpow_le_one_of_one_le_of_nonpos hN1 (by norm_num))
    have hEpsT : eps ≤ T := hEps1.trans hTemp.le
    have hB : MonotoneOn b1 (Icc (0:ℝ) 1) :=
      (initialShellMatrixClock_monotone T s hEps).monotoneOn _
    have hH : MonotoneOn (fun _ : ℝ=>(0:ℝ)) (Icc (0:ℝ) 1) := fun _ _ _ _ _=>le_rfl
    have hLb : cn.d^2 ≤ b1 0 := by
      dsimp only [b1]
      unfold initialShellMatrixClock
      split_ifs <;> linarith only [hnGate,hEps1]
    have Hsharp:=hnCost cn b1 (fun _=>0) (cn.d^2) (sq_pos_of_pos cn.hd) le_rfl
      (Hnum n).1 hLb hB hH le_rfl (Hnum n).2.1 (Hnum n).2.2
      [] eps s (by intro u;simp only [historyMatrixClock,historyMatrixReduction,sub_zero];rfl)
      (by intro u;rfl) (by simp) hEps (by
        intro lam hlam alpha hattained
        exact hnReg lam ⟨(Real.rpow_pos_of_pos hN _).trans hlam.1,hlam.2.le⟩ alpha hattained)
    have hne:=cn.profile_nonempty hnq
    obtain ⟨alpha,hattained,_⟩:=variableEndpointComparisonSweepMinimum_attained
      cn.hc cn.hk cn.hkc cn.hm cn.hM (n+1) cn.hn b1 (fun _=>0) cn.hd.ne'
      (sq_nonneg cn.d) hLb hB hH le_rfl (comparisonCap_continuous _ _ _ _ _ _) hne
    let r:=cn.R alpha
    let e:=fun u=>laplaceComparisonStrength cn.d (cn.d^2) (r u)
    have Hr u : r u∈Icc (0:ℝ) 1 := comparisonSweepQuantile_bounds cn.hc cn.hk cn.hkc cn.hm cn.hM alpha u
    have Hrm : MonotoneOn r (Icc (0:ℝ) 1) :=
      (comparisonSweepQuantile_monotone cn.hc cn.hk cn.hkc cn.hm cn.hM alpha).monotoneOn _
    have Hstrength:=laplaceComparisonStrength_monotonicities cn.hd.ne' (sq_pos_of_pos cn.hd) (r₀:=0) le_rfl
    have Hem : AntitoneOn e (Icc (0:ℝ) 1) := fun u hu v hv huv=>Hstrength.1 (Hr u) (Hr v) (Hrm hu hv huv)
    have Herm : MonotoneOn (fun u=>e u*r u) (Icc (0:ℝ) 1) :=
      fun u hu v hv huv=>Hstrength.2 (Hr u) (Hr v) (Hrm hu hv huv)
    have Hep u : 0 < e u := laplaceComparisonStrength_pos cn.d (sq_pos_of_pos cn.hd) (r u)
    have Hb1T u : b1 u ≤ T := by
      dsimp only [b1]
      unfold initialShellMatrixClock
      split_ifs <;> linarith only [hEps]
    have Hdeltam : AntitoneOn (fun u=>T-b1 u) (Icc (0:ℝ) 1) :=
      fun u hu v hv huv=>sub_le_sub_left (hB hu hv huv) T
    have Hpen:=compensation_penalty_monotoneOn e r (Icc (0:ℝ) 1)
      (fun u _=>(Hep u).le) (fun u _=>(Hr u).1) Hrm Herm
    have Hchord:=chord_cost_monotoneOn (fun u=>T-b1 u) e r (Icc (0:ℝ) 1) Hdeltam Hem
      (fun u _=>sub_nonneg.mpr (Hb1T u)) (fun u _=>Hep u) (fun u _=>(Hr u).1) Herm
    have Had:=comparisonVariableEndpoint_clocks_admissible cn.hc cn.hk cn.hkc cn.hm cn.hM b1 (fun _=>0)
      cn.hd.ne' (sq_nonneg cn.d) hLb hB hH le_rfl alpha
    have Hbc0 : 0 ≤ b1 0-e 0 := sub_nonneg.mpr
      ((laplaceComparisonStrength_le cn.d (sq_nonneg cn.d) (r 0)).trans hLb)
    have Hcomparison : pathCompensatedPressure (n+1) b1 (fun _=>0) e r 0 ≤
        realOrderedSKPathPressure (n+1) b1 (fun _=>0) 0+cn.N^(20*(m/10000))*cn.E := by
      have H : variableEndpointComparisonSweepObjective cn.hc cn.hk cn.hkc cn.hm cn.hM
          (n+1) b1 (fun _=>0) cn.d (cn.d^2) alpha ≤
          realOrderedSKPathPressure (n+1) b1 (fun _=>0) 0+cn.N^(20*(m/10000))*cn.E := by
        rw [hattained]
        unfold variableEndpointComparisonSweepCost at Hsharp
        linarith
      simpa only [variableEndpointComparisonSweepObjective,variableEndpointStrengthSweepObjective,
        pathCompensatedPressure,r,e] using H
    let A:=comparisonConditionalScale cn.N (m/10000) cn.E (cn.d^2)
    have hA : 0 ≤ A := (comparison_conditional_scale_pos hN cn.hE (sq_pos_of_pos cn.hd)).le
    have Hreg : ∀t∈Icc (min A 1) 1,cl*t ≤ alpha.val.val t ∧ alpha.val.val t ≤ cu*t :=
      hnReg (cn.d^2) ⟨sq_pos_of_pos cn.hd,le_rfl⟩ alpha hattained
    have hAD : A ≤ s := (actual_lower_shell_native_numeric hm hmmax n).2.2.2.1
    have HradiusUpper u (hu : u∈Ioo (s/2) s) : r u ≤ Couter*s := by
      have hu01 : u∈Icc (0:ℝ) 1 := ⟨(by have hs:=cn.hd;linarith only [hu.1,hs]),hu.2.le.trans (Hnum n).1⟩
      have Henv:=cn.toOverlapContext.radius_le_outer_CDF_envelope alpha hcl hA (fun t ht=>(Hreg t ht).1) hu01
      have HU : u/cl ≤ Couter*s := by
        calc
          u/cl ≤ s/cl := div_le_div_of_nonneg_right hu.2.le hcl.le
          _ = (1/cl)*s := by ring
          _ ≤ Couter*s := mul_le_mul_of_nonneg_right (le_max_right _ _) cn.hd.le
      have HA' : A ≤ Couter*s := hAD.trans (by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (le_max_left (1:ℝ) (1/cl)) cn.hd.le)
      exact Henv.trans (max_le HA' HU)
    have HradiusLower u (hu : u∈Ioo (s/2) s) : cShell*s ≤ r u := by
      let r0:=s/(4*cu)
      have hr0 : 0 ≤ r0 := div_nonneg cn.hd.le (by positivity)
      have hr0s : r0 ≤ s := by
        apply (div_le_iff₀ (by positivity : 0 < 4*cu)).mpr
        have H:=mul_le_mul_of_nonneg_left (show (1:ℝ) ≤ 4*cu by linarith only [hcu1]) cn.hd.le
        simpa only [mul_one] using H
      have hr01 : r0∈Icc (0:ℝ) 1 := ⟨hr0,hr0s.trans (Hnum n).1⟩
      have hAr0 : A ≤ r0 := by
        have H:=(div_le_iff₀ cn.hd).mp hnA
        change A ≤ _ at H
        exact H.trans_eq (by dsimp only [r0];ring)
      have Hcdf:=(Hreg r0 ⟨(min_le_left _ _).trans hAr0,hr01.2⟩).2
      have Hcu : cu*r0=s/4 := by dsimp only [r0];field_simp
      have Hu : alpha.val.val r0 ≤ u := by
        rw [Hcu] at Hcdf
        have hs:=cn.hd
        linarith only [Hcdf,hu.1,hs]
      have Hu01 : u∈Icc (0:ℝ) 1 := ⟨(by have hs:=cn.hd;linarith only [hu.1,hs]),hu.2.le.trans (Hnum n).1⟩
      have H:= (cn.toOverlapContext.profile_le_mass_iff_radius_le alpha hr01 Hu01).mp Hu
      exact (show cShell*s=r0 by dsimp only [cShell,r0];ring) ▸ H
    have HstrengthShell u (hu : u∈Ioo (s/2) s) : eps ≤ e u := by
      have Hlow : 0 < r u := (mul_pos hShell cn.hd).trans_le (HradiusLower u hu)
      exact hnEps.trans (laplaceFinalStrength_shell_lower cn.hd hOuter Hlow (HradiusUpper u hu))
    have Hgain:=path_pressure_strict_shell_gain (n+1) cn.hn (fun _=>T) b1 e r
      (cn.N^(20*(m/10000))*cn.E) eps cShell s
      (by dsimp only [eps,epsilon,lowerEpsilon];positivity) hShell cn.hd (Hnum n).1
      (fun u _=>(Hep u).le) (fun u _=>Hb1T u) (fun _ _ _ _ _=>le_rfl) hB
      Had.1 (by simpa only [zero_add] using Had.2.1) hT.le ((sq_nonneg cn.d).trans hLb)
      Hbc0 (Hr 0).1 Hpen Hchord
      (fun u hu=>by dsimp only [b1];unfold initialShellMatrixClock;rw [ite_eq_left hu.2];ring)
      HstrengthShell HradiusLower 0 Hcomparison
    have Hfull:=physicalShellPressure_mono (n+1) cn.hn cn.hd hEps hEpsT (le_refl T)
    have Hbridge:=pressureIncrement_eq_physicalShell_gap (beta:ℝ) hmmax (n+1) cn.hn
    change physicalShellPressure (n+1) T s eps ≤ physicalShellPressure (n+1) T s T at Hfull
    rw [Hbridge]
    change _ ≤ physicalShellPressure (n+1) T s T-physicalShellPressure (n+1) T s 0
    change cShell^2*eps*s^3/16-cn.N^(20*(m/10000))*cn.E ≤
      physicalShellPressure (n+1) T s eps-realOrderedSKPathPressure (n+1) (fun _=>T) (fun _=>0) 0 at Hgain
    have Hbare : physicalShellPressure (n+1) T s 0=
        realOrderedSKPathPressure (n+1) (fun _=>T) (fun _=>0) 0 := by
      unfold physicalShellPressure
      congr 1
      funext u
      unfold initialShellMatrixClock
      split_ifs <;> simp only [sub_zero]
    rw [Hbare]
    dsimp only [cn,c,s,eps,epsilon,actualLowerShellNativeParameters,lowerDelta] at Hgain Hfull ⊢
    nlinarith only [Hgain,Hfull]
  refine ⟨cShell^2/16,1,by positivity,?_⟩
  rw [←map_add_atTop_eq_nat 1]
  exact Hshift

theorem actual_lowerComparison
    (beta : ℝ) (hbeta : 1 < beta) (m : ℝ) (hm : 0 < m) (hmmax : m < 1/300) :
    ∃a b : ℝ,0 < a ∧ ∀ᶠn : ℕ in atTop,
      a*lowerEpsilon n*(lowerScale m n)^3-b*(n:ℝ)^(20*lowerDelta m)*lowerError m n ≤
        pressureIncrement beta m n := by
  have hb : 0 < beta := zero_lt_one.trans hbeta
  have H:=exists_actual_lower_pressure_comparison (beta:=beta.toNNReal)
    (by simpa only [Real.toNNReal_pos] using hb) (by rw [Real.coe_toNNReal _ hb.le];nlinarith) hm hmmax
  simpa only [Real.coe_toNNReal _ hb.le] using H

end OAI.SKFluctuations.LaplaceWindowFormalization
