module

public import ComparisonNativeActualInitialShellSweepRegular
public import LowerLedger

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 12000000

def actualLowerShellNativeParameters (m : ℝ) (n : ℕ) :
    NativeChildBarrierParameters (n+1) (m/10000) where
  E := lowerError m (n+1)
  d := lowerScale m (n+1)
  hn := Nat.succ_pos n
  hE := by unfold lowerError;exact Real.rpow_pos_of_pos (by positivity) _
  hd := by unfold lowerScale;exact Real.rpow_pos_of_pos (by positivity) _

theorem actual_lower_shell_native_numeric {m : ℝ} (hm : 0 < m) (hmmax : m < 1/300)
    (n : ℕ) :
    let c:=actualLowerShellNativeParameters m n
    c.d ≤ 1 ∧ Real.sqrt c.N*c.E ≤ c.d^2 ∧ c.N^(-(2:ℝ)/3+m)*c.d ≤ c.E ∧
      comparisonConditionalScale c.N (m/10000) c.E (c.d^2) ≤ c.d ∧
      comparisonConditionalScale c.N (m/10000) c.E (c.d^2)=c.N^(-(1:ℝ)/6+2*m+m/10000) := by
  dsimp only
  let c:=actualLowerShellNativeParameters m n
  have hN : 0 < c.N := c.hN
  have hN1 : 1 ≤ c.N := by exact_mod_cast Nat.succ_pos n
  have hpow (a b : ℝ) (hab : a ≤ b) : c.N^a ≤ c.N^b :=
    Real.rpow_le_rpow_of_exponent_le hN1 hab
  have hd1 : c.d ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by
    change -(1:ℝ)/6+5*m ≤ 0
    linarith)
  have hEeq : c.E=c.N^(-(2:ℝ)/3+2*m)*c.d := by
    change c.N^(-(5:ℝ)/6+7*m)=c.N^(-(2:ℝ)/3+2*m)*c.N^(-(1:ℝ)/6+5*m)
    rw [←Real.rpow_add hN]
    congr 1
    ring
  have hdeq : c.d=c.N^(-(1:ℝ)/6+5*m) := rfl
  have hupper : Real.sqrt c.N*c.E ≤ c.d^2 := by
    rw [hEeq,Real.sqrt_eq_rpow]
    have H:=mul_le_mul_of_nonneg_right
      (hpow (-(1:ℝ)/6+2*m) (-(1:ℝ)/6+5*m) (by linarith)) c.hd.le
    rw [←hdeq] at H
    have he : c.N^((1:ℝ)/2)*c.N^(-(2:ℝ)/3+2*m)=c.N^(-(1:ℝ)/6+2*m) := by
      rw [←Real.rpow_add hN]
      congr 1
      ring
    simpa only [←mul_assoc,he,pow_two] using H
  have hlower : c.N^(-(2:ℝ)/3+m)*c.d ≤ c.E := by
    rw [hEeq]
    exact mul_le_mul_of_nonneg_right (hpow _ _ (by linarith)) c.hd.le
  have hscaleEq : comparisonConditionalScale c.N (m/10000) c.E (c.d^2)=
      c.N^(-(1:ℝ)/6+2*m+m/10000) := by
    unfold comparisonConditionalScale
    rw [Real.sqrt_sq c.hd.le,hEeq,Real.sqrt_eq_rpow]
    field_simp [c.hd.ne']
    rw [←Real.rpow_add hN,←Real.rpow_add hN]
    congr 1
    ring
  have hscale : comparisonConditionalScale c.N (m/10000) c.E (c.d^2) ≤ c.d := by
    rw [hscaleEq,hdeq]
    exact hpow _ _ (by linarith)
  exact ⟨hd1,hupper,hlower,hscale,hscaleEq⟩

theorem actual_lower_shell_native_radius_tendsto_zero {m : ℝ} (hmmax : m < 1/300) :
    Tendsto (fun n=>(actualLowerShellNativeParameters m n).d) atTop (𝓝 0) := by
  have H:=(tendsto_rpow_neg_atTop (by linarith : 0 < (1:ℝ)/6-5*m)).comp
    (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have he : -((1:ℝ)/6-5*m)=-(1:ℝ)/6+5*m := by ring
  simpa only [actualLowerShellNativeParameters,lowerScale,Function.comp_def,he] using H

theorem actual_lower_shell_final_cutoff_ratio_tendsto_zero {m : ℝ}
    (hm : 0 < m) (hmmax : m < 1/300) :
    Tendsto (fun n=>comparisonConditionalScale (actualLowerShellNativeParameters m n).N (m/10000)
      (actualLowerShellNativeParameters m n).E ((actualLowerShellNativeParameters m n).d^2)/
        (actualLowerShellNativeParameters m n).d) atTop (𝓝 0) := by
  have H:=(tendsto_rpow_neg_atTop (by linarith : 0 < 3*m-m/10000)).comp
    (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  apply H.congr
  intro n
  rw [(actual_lower_shell_native_numeric hm hmmax n).2.2.2.2]
  change (((n+1:ℕ):ℝ)^(-(3*m-m/10000)))=
    (((n+1:ℕ):ℝ)^(-(1:ℝ)/6+2*m+m/10000))/(((n+1:ℕ):ℝ)^(-(1:ℝ)/6+5*m))
  rw [←Real.rpow_sub (by positivity)]
  congr 1
  ring

end OAI.SKFluctuations.LaplaceWindowFormalization
