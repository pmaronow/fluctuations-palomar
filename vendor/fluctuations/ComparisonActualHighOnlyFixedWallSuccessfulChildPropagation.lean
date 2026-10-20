module

public import ComparisonActualHighOnlyFixedWallHistory
public import ComparisonActualHighOnlyRegularSuccessfulChildSequence
public import ComparisonActualHighOnlyOuterChildRadiusBounds
public import ComparisonActualHighOnlySuccessfulChildParentDirectJoin
public import ComparisonNativeActualChildParameterGrowth

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 26000000
namespace ActualHighOnlyOverlapMinimum

theorem eventually_fixed_wall_bad_parent_excludes_successful_child_sequence
    {m cl cu Az C0 Ct D Bclock T c0 : ℝ}
    (hm : 0 < m) (hmsmall : m ≤ (1:ℝ)/120)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0)
    (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hclmargin : cl < 2*T*Real.exp (-12*T))
    (hcumargin : T*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/
      (2*Real.exp (-12*T)) < cu)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ) → ActualHighOnlyOverlapMinimum (dim n+1)
      m (m/10000) cl cu Az C0 Ct D Bclock)
    (G : ActualFixedWallHighOnlyHistory M T c0)
    (a : (n : ℕ) → ActualHighOnlyChildBarrierCall (dim n+1) (m/10000))
    (x : ℕ → ℝ) (hxs : ∀ n, (M n).xs ≤ x n)
    (hxlim : Tendsto x atTop (𝓝 0))
    (hcontext : ∀ n, (a n).context = (M n).context)
    (hlam : ∀ n, (a n).lam = (M n).lam)
    (hR : ∀ n, (a n).R = (M n).R)
    (hchild : ∀ᶠ n in atTop, (a n).childRadius = c0*x n ∧
      (a n).childLam = (c0*x n)^2 ∧
      (a n).err ≤ ((dim n+1:ℕ):ℝ)^(20*(m/10000))*actualChildErrorBudget
        (dim n+1) (m/10000) c0 (M n).context.d (M n).lam (x n))
    (hEchild : ∀ᶠ n in atTop, (a n).childData.E = actualChildErrorBudget
      (dim n+1) (m/10000) c0 (M n).context.d (M n).lam (x n))
    (htarget : ∀ᶠ n in atTop, comparisonConditionalScale (M n).context.N
      (m/10000) (M n).context.E (M n).lam ≤ x n)
    (hweak : Tendsto (fun n => laplaceComparisonStrength (M n).context.d
      (M n).lam (x n)/(x n)^2) atTop (𝓝 0))
    (Hbad : ∀ᶠ n in atTop, ¬(cl*x n ≤ (M n).alpha.val.val (x n) ∧
      (M n).alpha.val.val (x n) ≤ cu*x n)) : False := by
  let delta : ℝ := m/10000
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  have hroom : delta < 3*m := by dsimp [delta]; linarith
  have hmargin : delta/4 < 3*m-99*delta := by dsimp [delta]; linarith
  have hcapmargin : 100*delta < (1:ℝ)/3+m := by dsimp [delta]; linarith
  have hgapmargin : 0 < 9*m-298*delta := by dsimp [delta]; linarith
  have HMlim : Tendsto (fun n=>(M n).xs) atTop (𝓝 0) :=
    squeeze_zero (fun n=>(M n).hxs.le) hxs hxlim
  obtain ⟨Gm⟩ := G.exists_context hm hmsmall hcl hAz hC0 hc0 hc01 hdim HMlim
  have homission : Tendsto (fun n=>(M n).data.s/x n) atTop (𝓝 0) := by
    apply squeeze_zero (fun n=>div_nonneg (M n).data.hs.1
      ((M n).hxs.trans_le (hxs n)).le) _ Gm.omission_ratio
    intro n
    exact div_le_div_of_nonneg_left (M n).data.hs.1
      (div_pos (mul_pos (Real.sqrt_pos.mpr (M n).context.hN)
        (M n).context.hE) (M n).context.hd)
      ((M n).hscale.trans (hxs n))
  have hx (n:ℕ) : 0 < x n := (M n).hxs.trans_le (hxs n)
  have hcl1 : cl≤1 := by
    have H1:=((M 0).regular 1 ⟨(M 0).hz.2,le_rfl⟩).1
    simpa only [mul_one,(M 0).alpha.property.2] using H1
  have hcu1 : 1≤cu := by
    have H1:=((M 0).regular 1 ⟨(M 0).hz.2,le_rfl⟩).2
    simpa only [mul_one,(M 0).alpha.property.2] using H1
  have hparent (n:ℕ) : (a n).context.E=(M n).context.E ∧
      (a n).context.d=(M n).context.d ∧ (a n).lam=(M n).lam ∧
      (a n).R=(M n).R ∧ (a n).context.s=(M n).context.s := by
    refine ⟨?_,?_,hlam n,hR n,?_⟩  <;> rw [hcontext n]
  have hcoeff (n:ℕ) (u:ℝ) : (a n).coefficient u=(M n).coefficient u := by
    change omittedStrengthCoefficient (a n).context.d (a n).context.s
      (a n).R (a n).lam u = omittedStrengthCoefficient
        (M n).context.d (M n).context.s (M n).R (M n).lam u
    rw [hcontext n,hlam n,hR n]
  have hschild (n:ℕ) : (a n).childData.s=(M n).data.s := by
    rw [(a n).sameInitialMass,hcontext n]
  have hbchild (n:ℕ) (u:ℝ) : (a n).childData.b u=
      (M n).b u-(M n).coefficient u := by
    have H:=congrFun (a n).childBareMatrix u
    change (a n).childData.b u=(a n).context.b u-(a n).coefficient u at H
    rw [hcontext n,hcoeff n u] at H
    exact H
  have hhchild (n:ℕ) (u:ℝ) : (a n).childData.h u=
      (M n).h u+(M n).coefficient u*(M n).R u := by
    have H:=congrFun (a n).childBareField u
    change (a n).childData.h u=(a n).context.h u+
      (a n).coefficient u*(a n).R u at H
    rw [hcontext n,hcoeff n u,hR n] at H
    exact H
  have Htotal := G.total_root
  have htotal : ∀ᶠn in atTop,∀u∈Icc (0:ℝ) 1,
      (a n).childData.h u+(a n).childData.b u≤ max Bclock T := by
    filter_upwards [Htotal] with n hn u hu
    rw [hbchild n u,hhchild n u,
      ←((M n).inherited_clock_coe hu).1,
      ←((M n).inherited_clock_coe hu).2]
    exact ((M n).inherited_total_clock_le hn.1 u hu).trans (le_max_right _ _)
  obtain ⟨Cold,hCold,HquantOld⟩:=actual_high_only_successful_child_outer_radius_bounds
    hm hdelta hcl hcu hAz hC0 hc0 dim hdim M a x hxs hxlim hparent hchild homission hweak
  let C:=max Cold (cl*Az/4)
  have hC : 1≤C:=hCold.trans (le_max_left _ _)
  have hAzC : Az≤4*C/cl := by
    apply (le_div_iff₀ hcl).mpr
    have H:=le_max_right Cold (cl*Az/4)
    nlinarith only [H]
  have hquant : ∀ᶠn in atTop,∀u∈Icc (C*x n) 1,
      u/(4*cu)≤(a n).Z u ∧ (a n).Z u≤4*u/cl := by
    filter_upwards [HquantOld] with n hn u hu
    exact hn u ⟨(mul_le_mul_of_nonneg_right (le_max_left _ _) (hx n).le).trans hu.1,hu.2⟩
  have Hdim : Tendsto (fun n=>dim n+1) atTop atTop :=
    (tendsto_add_atTop_nat 1).comp hdim
  have Hparam:=Hdim.eventually (eventually_actual_child_parameters_from_target
    hm hdelta (one_div_pos.mpr hC0) hc0 hmargin)
  have Hweak:=hweak.eventually (gt_mem_nhds zero_lt_one)
  have Hunit:=hxlim.eventually (eventually_le_nhds zero_lt_one)
  have hready : ∀ᶠn in atTop,
      (a n).childRadius=c0*x n ∧
      (a n).childLam=(c0*x n)^2 ∧
      (a n).childData.E=actualChildErrorBudget (dim n+1) delta c0
        (M n).context.d (M n).lam (x n) ∧
      (a n).childRadius≤ max D 1 ∧
      Real.sqrt ((dim n+1:ℕ):ℝ)*(a n).childData.E≤(a n).childRadius^2 ∧
      ((dim n+1:ℕ):ℝ)^(-(2:ℝ)/3+m)*(a n).childRadius≤C0*(a n).childData.E ∧
      (∀u∈Icc (0:ℝ) 1,(a n).childData.h u+(a n).childData.b u≤ max Bclock T) ∧
      (∀u∈Icc (C*x n) 1,u/(4*cu)≤(a n).Z u ∧ (a n).Z u≤4*u/cl) := by
    filter_upwards [hchild,hEchild,Hparam,Hweak,Hunit,htarget,htotal,hquant]
      with n hnChild hnE hnParam hnWeak hnUnit hnTarget hnTotal hnQuant
    have hlo : (1/C0)*((dim n+1:ℕ):ℝ)^(-(2:ℝ)/3+m)*
        (M n).context.d≤(M n).context.E := by
      have H:=(div_le_iff₀ hC0).mpr
        (by simpa only [mul_comm] using (M n).hlower)
      simpa only [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc,one_mul] using H
    have hup : (M n).context.E≤(M n).context.d^2/
        Real.sqrt ((dim n+1:ℕ):ℝ) :=
      (le_div_iff₀ (Real.sqrt_pos.mpr (M n).context.hN)).mpr
        (by simpa only [mul_comm] using (M n).hupper)
    have hparentweak : laplaceComparisonStrength (M n).context.d
        (M n).lam (x n)≤(x n)^2 :=
      (div_le_one₀ (sq_pos_of_pos (hx n))).mp hnWeak.le
    have HP:=hnParam (M n).context.d (M n).lam (M n).context.E (x n)
      (M n).context.hd (M n).hlam (M n).hld (M n).context.hE
      (hx n) hlo hup hnTarget hparentweak
    have hupper : Real.sqrt ((dim n+1:ℕ):ℝ)*(a n).childData.E≤
        (a n).childRadius^2 := by
      have H:=(le_div_iff₀ (Real.sqrt_pos.mpr (M n).context.hN)).mp HP.2.1
      rw [hnE,hnChild.1]
      simpa only [actualChildRadius,mul_comm] using H
    have hlower : ((dim n+1:ℕ):ℝ)^(-(2:ℝ)/3+m)*(a n).childRadius≤
        C0*(a n).childData.E := by
      have H:=mul_le_mul_of_nonneg_left HP.1 hC0.le
      have hcanc : C0*(1/C0)=1 := by field_simp
      rw [hnE,hnChild.1]
      simpa only [←mul_assoc,hcanc,one_mul,actualChildRadius] using H
    have hdD : (a n).childRadius≤ max D 1 := by
      rw [hnChild.1]
      have H:=(mul_le_mul_of_nonneg_right hc01 (hx n).le).trans
        (by simpa using hnUnit)
      exact H.trans (le_max_right _ _)
    exact ⟨hnChild.1,hnChild.2.1,hnE,hdD,hupper,hlower,hnTotal,hnQuant⟩
  obtain ⟨N,hN⟩:=eventually_atTop.mp hready
  let shift : ℕ→ℕ:=fun n=>n+N
  have hshift : StrictMono shift:=fun i j hij=>Nat.add_lt_add_right hij N
  have Hn (n:ℕ) := hN (shift n) (by dsimp [shift];omega)
  obtain ⟨Q,hQ⟩:=ActualHighOnlyChildBarrierCall.exists_regular_successful_child_sequence
    hc0 hc01 hcl hcu hcl1 hcu1 hC (le_max_right Ct 1)
    (fun n=>dim (shift n)) (fun n=>a (shift n)) (fun n=>x (shift n))
    (fun n=>hx (shift n))
    (fun n=>(Hn n).1)
    (fun n=>by rw [(Hn n).1];exact (Hn n).2.1)
    (fun n=>(Hn n).2.2.2.1)
    (fun n=>(Hn n).2.2.2.2.1)
    (fun n=>(Hn n).2.2.2.2.2.1)
    (fun n=>(Hn n).2.2.2.2.2.2.1)
    (fun n=>(Hn n).2.2.2.2.2.2.2)
  have hQxs (n:ℕ) : (Q n).xs=x (shift n):=(hQ n).2.2.1
  have hQd (n:ℕ) : (Q n).context.d=c0*x (shift n) := by
    rw [(hQ n).1]
    exact (Hn n).1
  have hQlam (n:ℕ) : (Q n).lam=(c0*x (shift n))^2 := by
    rw [(hQ n).2.2.2]
    exact (Hn n).2.1
  have hQE : ∀n,(Q n).context.E=actualChildErrorBudget
      (dim (shift n)+1) delta c0 (M (shift n)).context.d
      (M (shift n)).lam (x (shift n)) := by
    intro n
    rw [(hQ n).1]
    exact (Hn n).2.2.1
  have hQs : ∀n,(Q n).data.s=(M (shift n)).data.s := by
    intro n
    change (Q n).context.s=(M (shift n)).data.s
    rw [(hQ n).1]
    exact hschild (shift n)
  have hQb : ∀n,∀u,(Q n).b u=(M (shift n)).b u-
      (M (shift n)).coefficient u := by
    intro n u
    change (Q n).context.b u=(M (shift n)).b u-(M (shift n)).coefficient u
    rw [(hQ n).1]
    exact hbchild (shift n) u
  have hQh : ∀n,∀u,(Q n).h u=(M (shift n)).h u+
      (M (shift n)).coefficient u*(M (shift n)).R u := by
    intro n u
    change (Q n).context.h u=(M (shift n)).h u+
      (M (shift n)).coefficient u*(M (shift n)).R u
    rw [(hQ n).1]
    exact hhchild (shift n) u
  have hclW : cl/4 ≤ cl := by linarith
  have hcuW : cu ≤ 4*cu := by linarith
  let G0 := G.comp shift hshift
  let Gw := G0.weaken_constants hclW hcuW hAzC
    (le_max_left Ct 1) (le_max_left D 1) (le_max_left Bclock T)
  have hcapW : ∀ᶠn in atTop,(M (shift n)).z ≤ (4*C/cl)*x (shift n) := by
    apply Eventually.of_forall
    intro n
    exact (M (shift n)).hzxs.trans
      ((mul_le_mul_of_nonneg_left (hxs (shift n)) hAz).trans
        (mul_le_mul_of_nonneg_right hAzC (hx (shift n)).le))
  let Gchild := Gw.append_child Q (fun n=>x (shift n))
    (fun n=>hx (shift n))
    ((hxlim.comp hshift.tendsto_atTop).eventually (eventually_le_nhds zero_lt_one))
    (hshift.tendsto_atTop.eventually htarget) hcapW
    (hweak.comp hshift.tendsto_atTop)
    (Eventually.of_forall hQd) (Eventually.of_forall hQE)
    (Eventually.of_forall hQs) (Eventually.of_forall hQb) (Eventually.of_forall hQh)
  have hQlim : Tendsto (fun n=>(Q n).xs) atTop (𝓝 0) := by
    simpa only [hQxs,Function.comp_def] using hxlim.comp hshift.tendsto_atTop
  obtain ⟨GQ⟩ := Gchild.exists_context hm hmsmall
    (by positivity) (by positivity) hC0 hc0 hc01
    (hdim.comp hshift.tendsto_atTop) hQlim
  have hparent0 (n:ℕ) : (a (shift n)).context.E=(M (shift n)).context.E ∧
      (a (shift n)).context.d=(M (shift n)).context.d ∧
      (a (shift n)).lam=(M (shift n)).lam ∧
      (a (shift n)).R=(M (shift n)).R ∧
      (a (shift n)).context.s=(M (shift n)).context.s := hparent (shift n)
  have hQjoin (n:ℕ) : (Q n).R=(a (shift n)).Z ∧
      (Q n).xs=x (shift n) ∧ (Q n).context.d=c0*x (shift n) ∧
      (Q n).lam=(c0*x (shift n))^2 :=
    ⟨(hQ n).2.1,hQxs n,hQd n,hQlam n⟩
  obtain ⟨phi,hphi,kappa,hklo,hkup,Hprofile,Hstrict⟩:=
    successful_child_parent_direct_profile_of_context hm hdelta hroom hcl hcu
      hAz hC0 hc0 hc01 hC hmargin hcapmargin hgapmargin
      hclmargin hcumargin (fun n=>dim (shift n))
      (hdim.comp hshift.tendsto_atTop) (fun n=>M (shift n))
      (fun n=>a (shift n)) Q GQ (fun n=>x (shift n))
      (fun n=>hxs (shift n)) (hxlim.comp hshift.tendsto_atTop)
      hparent0 (hshift.tendsto_atTop.eventually hchild)
      (homission.comp hshift.tendsto_atTop)
      (hweak.comp hshift.tendsto_atTop) hQjoin
  have Hbad0:=hphi.tendsto_atTop.eventually
    (hshift.tendsto_atTop.eventually Hbad)
  obtain ⟨n,hn⟩:=(Hstrict.and Hbad0).exists
  exact hn.2 ⟨hn.1.1.le,hn.1.2.le⟩

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
