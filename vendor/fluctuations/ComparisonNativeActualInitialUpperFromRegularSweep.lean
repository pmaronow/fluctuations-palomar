module

public import ComparisonNativeActualShellChildBudget
public import ComparisonNativeActualBadScaleMassTransfer
public import ActualInitialUpperBound

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy PositiveLaplaceAssembly
open scoped Topology NNReal
set_option maxHeartbeats 14000000

namespace NativeOverlapContext

theorem radius_le_outer_CDF_envelope {n : ℕ} {delta cl A : ℝ}
    (c : NativeOverlapContext n delta) (alpha : c.Profile)
    (hcl : 0 < cl) (hA : 0 ≤ A)
    (hregular : ∀r∈Icc (min A 1) 1,cl*r ≤ alpha.val.val r)
    {u : ℝ} (hu : u∈Icc (0:ℝ) 1) :
    c.R alpha u ≤ max A (u/cl) := by
  by_cases hsmall : c.R alpha u ≤ A
  · exact hsmall.trans (le_max_left _ _)
  · have hr := comparisonSweepQuantile_bounds c.hc c.hk c.hkc c.hm c.hM alpha u
    have hreg := hregular (c.R alpha u)
      ⟨(min_le_left A 1).trans (le_of_not_ge hsmall),hr.2⟩
    have he : alpha.val.val (c.R alpha u)=u :=
      comparisonSweepQuantile_spec c.hc c.hk c.hkc c.hm c.hM alpha hu
    rw [he] at hreg
    exact ((le_div_iff₀ hcl).mpr (by nlinarith only [hreg])).trans (le_max_right _ _)

end NativeOverlapContext

def actualInitialUpperNativeParameters (m : ℝ) (n : ℕ) :
    NativeChildBarrierParameters (n+1) (m/10000) where
  E := wallInitialError m (n+1)
  d := wallInitialD m (n+1)
  hn := Nat.succ_pos n
  hE := by
    unfold wallInitialError wallInitialD
    exact mul_pos (Real.rpow_pos_of_pos (by positivity) _)
      (Real.rpow_pos_of_pos (by positivity) _)
  hd := by unfold wallInitialD;exact Real.rpow_pos_of_pos (by positivity) _

theorem actual_initial_upper_native_numeric {m : ℝ} (hm : 0 < m) (hmmax : m < 1/300)
    (n : ℕ) :
    let c:=actualInitialUpperNativeParameters m n
    c.d ≤ 1 ∧ Real.sqrt c.N*c.E ≤ c.d^2 ∧
      c.N^(-(2:ℝ)/3+m)*c.d ≤ c.E ∧
      comparisonConditionalScale c.N (m/10000) c.E (c.d^2) ≤ c.d ∧
      wallHighMass m (n+1) ≤ c.d := by
  dsimp only
  let c:=actualInitialUpperNativeParameters m n
  have hN : 0 < c.N := c.hN
  have hN1 : 1 ≤ c.N := by exact_mod_cast Nat.succ_pos n
  have hpow (a b : ℝ) (hab : a ≤ b) : c.N^a ≤ c.N^b :=
    Real.rpow_le_rpow_of_exponent_le hN1 hab
  have hd1 : c.d ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by
    change -(1:ℝ)/6+25*m ≤ 0
    linarith)
  have hEeq : c.E=c.N^(-(2:ℝ)/3+2*m)*c.d := rfl
  have hdeq : c.d=c.N^(-(1:ℝ)/6+25*m) := rfl
  have hupper : Real.sqrt c.N*c.E ≤ c.d^2 := by
    rw [hEeq,Real.sqrt_eq_rpow]
    have H := mul_le_mul_of_nonneg_right
      (hpow (-(1:ℝ)/6+2*m) (-(1:ℝ)/6+25*m) (by linarith)) c.hd.le
    rw [←hdeq] at H
    have he : c.N^((1:ℝ)/2)*c.N^(-(2:ℝ)/3+2*m)=c.N^(-(1:ℝ)/6+2*m) := by
      rw [←Real.rpow_add hN]
      congr 1
      ring
    simpa only [←mul_assoc,he,pow_two] using H
  have hlower : c.N^(-(2:ℝ)/3+m)*c.d ≤ c.E := by
    rw [hEeq]
    exact mul_le_mul_of_nonneg_right
      (hpow _ _ (by linarith)) c.hd.le
  have hscale : comparisonConditionalScale c.N (m/10000) c.E (c.d^2) ≤ c.d := by
    unfold comparisonConditionalScale
    rw [Real.sqrt_sq c.hd.le,hEeq,Real.sqrt_eq_rpow]
    have he : c.N^(m/10000)*c.N^((1:ℝ)/2)*
        (c.N^(-(2:ℝ)/3+2*m)*c.d)/c.d=c.N^(-(1:ℝ)/6+2*m+m/10000) := by
      field_simp [c.hd.ne']
      rw [←Real.rpow_add hN,←Real.rpow_add hN]
      congr 1
      ring
    rw [he,hdeq]
    exact hpow _ _ (by linarith)
  refine ⟨hd1,hupper,hlower,hscale,?_⟩
  change c.N^(-(1:ℝ)/6+5*m) ≤ c.N^(-(1:ℝ)/6+25*m)
  exact hpow _ _ (by linarith)

theorem actual_initial_upper_comparison_of_native_sweep_regular
    {T cl cu m : ℝ} (hT : 1 < T) (hcl : 0 < cl) (hcu : 0 < cu) (hclcu : cl ≤ cu)
    (hm : 0 < m) (hmmax : m < 1/300)
    (hregular : ∀ᶠn : ℕ in atTop,
      let c:=actualInitialUpperNativeParameters m n
      ∀lam∈Ioc (0:ℝ) (c.d^2),∀alpha : c.Profile,
        variableEndpointComparisonSweepObjective c.hc c.hk c.hkc c.hm c.hM
          (n+1) (fun _=>T) (fun _=>0) c.d lam alpha=
        variableEndpointComparisonSweepMinimum c.hc c.hk c.hkc c.hm c.hM
          (n+1) (fun _=>T) (fun _=>0) c.d lam →
        ∀r∈Icc (min (comparisonConditionalScale c.N (m/10000) c.E lam) 1) 1,
          cl*r ≤ alpha.val.val r ∧ alpha.val.val r ≤ cu*r) :
    ∀ᶠn : ℕ in atTop,actualInitialUpperComparison T (max 1 (1/cl)) m n := by
  have hdelta : 0 < m/10000 := by positivity
  have hs : Tendsto (fun n : ℕ=>n+1) atTop atTop := tendsto_add_atTop_nat 1
  have hsR : Tendsto (fun n : ℕ=>((n+1:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hs
  have hq := hsR.eventually ((tendsto_rpow_atTop hdelta).eventually (eventually_ge_atTop 2))
  have Hcost := eventually_actual_shell_history_child_cost_of_regular (T:=T) (C0:=1)
    hm hdelta (by linarith) hcl hcu hclcu zero_lt_one
  have Hshift : ∀ᶠn : ℕ in atTop,
      actualInitialUpperComparison T (max 1 (1/cl)) m (n+1) := by
    filter_upwards [hregular,Hcost,hq] with n hnregular hncost hnq
    let c:=actualInitialUpperNativeParameters m n
    have hnum := actual_initial_upper_native_numeric hm hmmax n
    change c.d ≤ 1 ∧ Real.sqrt c.N*c.E ≤ c.d^2 ∧
      c.N^(-(2:ℝ)/3+m)*c.d ≤ c.E ∧
      comparisonConditionalScale c.N (m/10000) c.E (c.d^2) ≤ c.d ∧
      wallHighMass m (n+1) ≤ c.d at hnum
    have hdT : c.d^2 ≤ T := by have hd:=c.hd; nlinarith [hnum.1]
    have hb : MonotoneOn (fun _ : ℝ=>T) (Icc (0:ℝ) 1) := fun _ _ _ _ _=>le_rfl
    have hh : MonotoneOn (fun _ : ℝ=>(0:ℝ)) (Icc (0:ℝ) 1) := fun _ _ _ _ _=>le_rfl
    have hcost := hncost c (fun _=>T) (fun _=>0) (c.d^2) (sq_pos_of_pos c.hd)
      le_rfl hnum.1 hdT hb hh le_rfl hnum.2.1 (by simpa only [one_mul] using hnum.2.2.1)
      [] 0 1 (by intro u;simp [historyMatrixClock,historyMatrixReduction,initialShellMatrixClock])
      (by intro u;rfl) (by simp) le_rfl (by
        intro lam hlam alpha hattained
        exact hnregular lam ⟨(Real.rpow_pos_of_pos c.hN _).trans hlam.1,hlam.2.le⟩ alpha hattained)
    have hne:=c.profile_nonempty hnq
    obtain ⟨alpha,hattained,_⟩ := variableEndpointComparisonSweepMinimum_attained
      c.hc c.hk c.hkc c.hm c.hM (n+1) c.hn (fun _=>T) (fun _=>0) c.hd.ne'
      (sq_nonneg c.d) hdT hb hh le_rfl (comparisonCap_continuous _ _ _ _ _ _) hne
    let r : boundedMassProfiles := ⟨c.R alpha,
      (fun u=>comparisonSweepQuantile_bounds c.hc c.hk c.hkc c.hm c.hM alpha u),
      comparisonSweepQuantile_monotone c.hc c.hk c.hkc c.hm c.hM alpha⟩
    refine ⟨r,?_,?_⟩
    · intro u hu hus
      let A:=comparisonConditionalScale c.N (m/10000) c.E (c.d^2)
      have hA : 0 ≤ A :=
        (comparison_conditional_scale_pos c.hN c.hE (sq_pos_of_pos c.hd)).le
      have hR := c.toOverlapContext.radius_le_outer_CDF_envelope alpha hcl hA
        (fun t ht=>(hnregular (c.d^2) ⟨sq_pos_of_pos c.hd,le_rfl⟩ alpha hattained t ht).1) hu
      have hclInv : 0 ≤ 1/cl := (one_div_pos.mpr hcl).le
      have huD : u ≤ c.d := hus.le.trans hnum.2.2.2.2
      have hU : u/cl ≤ max 1 (1/cl)*c.d := by
        calc
          u/cl ≤ c.d/cl := div_le_div_of_nonneg_right huD hcl.le
          _ = (1/cl)*c.d := by ring
          _ ≤ max 1 (1/cl)*c.d := mul_le_mul_of_nonneg_right (le_max_right _ _) c.hd.le
      have hAD : A ≤ max 1 (1/cl)*c.d :=
        hnum.2.2.2.1.trans (by nlinarith [le_max_left (1:ℝ) (1/cl)])
      exact hR.trans (max_le hAD hU)
    · have H : variableEndpointComparisonSweepObjective c.hc c.hk c.hkc c.hm c.hM
          (n+1) (fun _=>T) (fun _=>0) c.d (c.d^2) alpha ≤
          realOrderedSKPathPressure (n+1) (fun _=>T) (fun _=>0) 0+c.N^(20*(m/10000))*c.E := by
        rw [hattained]
        unfold variableEndpointComparisonSweepCost at hcost
        linarith
      simpa only [variableEndpointComparisonSweepObjective,variableEndpointStrengthSweepObjective,
        pathCompensatedPressure,r,c,actualInitialUpperNativeParameters,wallInitialComparisonError] using H
  obtain ⟨n0,Hn0⟩ := eventually_atTop.mp Hshift
  apply eventually_atTop.mpr
  refine ⟨n0+1,?_⟩
  intro n hn
  have H:=Hn0 (n-1) (by omega)
  simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using H

end OAI.SKFluctuations.LaplaceWindowFormalization
