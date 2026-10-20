module

public import ComparisonNativeActualHistoryLowField
public import ComparisonNativeActualConditionalMinimum
public import ComparisonNativeActualChildParameterGrowth

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 9000000
namespace NativeOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

def ActualHistoryErrorGrowth :
    List (NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)→ℝ→Prop
  | [],_=>True
  | P::ps,E=>2*P.context.E ≤ E ∧ ActualHistoryErrorGrowth ps P.context.E

theorem actual_history_error_sum_le
    (ps : List (NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock))
    {E : ℝ} (hE : 0 ≤ E) (hg : ActualHistoryErrorGrowth ps E) :
    (ps.map (fun P=>P.context.E)).sum ≤ E := by
  induction ps generalizing E with
  | nil => simpa using hE
  | cons P ps ih =>
    have HI:=ih P.context.hE.le hg.2
    simpa only [List.map_cons,List.sum_cons] using
      (show P.context.E+(ps.map (fun P=>P.context.E)).sum ≤ E by linarith [hg.1])

theorem strength_mul_conditional_scale_eq
    {N E lam : ℝ} (hlam : 0 < lam) :
    lam*comparisonConditionalScale N delta E lam=N^delta*Real.sqrt N*E*Real.sqrt lam := by
  have hs:=Real.sqrt_pos.mpr hlam
  unfold comparisonConditionalScale
  rw [←mul_div_assoc]
  apply (div_eq_iff hs.ne').mpr
  calc
    _ = (N^delta*Real.sqrt N*E)*lam := by ring
    _ = (N^delta*Real.sqrt N*E)*(Real.sqrt lam)^2 := by rw [Real.sq_sqrt hlam.le]
    _ = _ := by ring

theorem regular_cap_le_conditional_error
    (P : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    (hAz : 0 ≤ Az)
    (hxs : P.xs=comparisonConditionalScale P.context.N delta P.context.E P.lam) :
    P.lam*P.z ≤ Az*D*(P.context.N^delta*Real.sqrt P.context.N)*P.context.E := by
  have hs : Real.sqrt P.lam ≤ D := by
    have H:=Real.sqrt_le_sqrt P.hld
    rw [Real.sqrt_sq P.context.hd.le] at H
    exact H.trans P.hdD
  have H:=mul_le_mul_of_nonneg_left P.hzxs P.hlam.le
  have he : P.lam*(Az*P.xs)=Az*(P.context.N^delta*Real.sqrt P.context.N*P.context.E)*Real.sqrt P.lam := by
    rw [hxs]
    calc
      _ = Az*(P.lam*comparisonConditionalScale P.context.N delta P.context.E P.lam) := by ring
      _ = _ := by rw [strength_mul_conditional_scale_eq P.hlam]; ring
  rw [he] at H
  have hE:=P.context.hE
  have hN:=P.context.hN
  have H':=mul_le_mul_of_nonneg_left hs
    (show 0 ≤ Az*(P.context.N^delta*Real.sqrt P.context.N*P.context.E) by positivity)
  exact H.trans (by convert H' using 1; ring)

theorem conditional_error_le_radius_scale
    (M : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    (hxs : M.xs=comparisonConditionalScale M.context.N delta M.context.E M.lam) :
    (M.context.N^delta*Real.sqrt M.context.N)*M.context.E ≤ D*M.xs := by
  have hs : Real.sqrt M.lam ≤ D := by
    have H:=Real.sqrt_le_sqrt M.hld
    rw [Real.sqrt_sq M.context.hd.le] at H
    exact H.trans M.hdD
  have he : (M.context.N^delta*Real.sqrt M.context.N)*M.context.E=Real.sqrt M.lam*M.xs := by
    rw [hxs]
    unfold comparisonConditionalScale
    field_simp [Real.sqrt_ne_zero'.mpr M.hlam]
  rw [he]
  exact mul_le_mul_of_nonneg_right hs M.hxs.le

theorem actual_history_regular_caps_le_current_scale
    (M : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    (ps : List (NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock))
    (hAz : 0 ≤ Az)
    (hxs : M.xs=comparisonConditionalScale M.context.N delta M.context.E M.lam)
    (hparent : ∀P∈ps,P.xs=comparisonConditionalScale P.context.N delta P.context.E P.lam)
    (hg : ActualHistoryErrorGrowth ps M.context.E) :
    actualHistoryRegularCapSum ps ≤ Az*D^2*M.xs := by
  have hD : 0 < D:=M.context.hd.trans_le M.hdD
  have hsum : actualHistoryRegularCapSum ps ≤
      Az*D*(M.context.N^delta*Real.sqrt M.context.N)*(ps.map (fun P=>P.context.E)).sum := by
    clear hg
    induction ps with
    | nil => simp [actualHistoryRegularCapSum]
    | cons P ps ih =>
      have HP:=P.regular_cap_le_conditional_error hAz (hparent P (by simp))
      have HI:=ih (fun Q hQ=>hparent Q (by simp [hQ]))
      change P.lam*P.z+actualHistoryRegularCapSum ps ≤ _
      simp only [List.map_cons,List.sum_cons,mul_add]
      exact add_le_add HP HI
  have Herr:=mul_le_mul_of_nonneg_left (actual_history_error_sum_le ps M.context.hE.le hg)
    (show 0 ≤ Az*D*(M.context.N^delta*Real.sqrt M.context.N) by positivity)
  have Hscale:=mul_le_mul_of_nonneg_left (M.conditional_error_le_radius_scale hxs)
    (show 0 ≤ Az*D by positivity)
  exact hsum.trans (Herr.trans (by convert Hscale using 1 <;> ring))

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
