module

public import ComparisonNativeWeightedDefectLimit
public import ComparisonIntegerBinBalance

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 2200000

def nativeBinScaleLoss (L AS AC v rho : ℝ) : ℝ :=
  1+2*(76+64*L)+48*AS*L*(v/rho)+
    (66+64*L+65536*(1+L)^2)*AC*(v/rho)^2+32

theorem nativeConditionalLedgerBudget_le_bin_scale
    {L AS AC v rho P D Q y reverse : ℝ}
    (hL : 0≤L) (hAS : 0≤AS) (hAC : 0≤AC) (hv : 0<v) (hrho : 0<rho)
    (hP : 0<P) (hD : 0≤D) (hQ : 0≤Q) (hy : 0≤y) (hreverse : 0≤reverse)
    {k : ℕ} (hk : 1≤k) (cut : ℝ) :
    nativeConditionalLedgerBudget k v cut ((Q^2*y)/(k:ℝ)+D)
      (AS*L*(k:ℝ)/(P*rho)) (AC*v/(P*rho^2)) reverse L ≤
      nativeBinScaleLoss L AS AC v rho*v*
        (((Q^2*y)/(k:ℝ))^2+D^2+((k:ℝ)+1)/(P*v^2)+reverse)+
          16*(k:ℝ)*cut := by
  let A := 76+64*L
  let C := 66+64*L+65536*(1+L)^2
  let tau := 1/(P*v^2)
  let F := nativeBinScaleLoss L AS AC v rho
  let w := (Q^2*y)/(k:ℝ)
  have hkpos : 0<(k:ℝ) := by exact_mod_cast (by omega : 0<k)
  have hw : 0≤w := by dsimp [w]; positivity
  have hA : 0≤A := by dsimp [A]; positivity
  have hC : 0≤C := by dsimp [C]; positivity
  have htau : 0≤tau := by dsimp [tau]; positivity
  have hside : 0≤48*AS*L*(v/rho) := by positivity
  have hcov : 0≤C*AC*(v/rho)^2 := by positivity
  have hF : 0≤F := by dsimp [F,nativeBinScaleLoss]; positivity
  have hAcoef : 2*A≤F := by dsimp [F,nativeBinScaleLoss,A] at *; linarith
  have hScoef : 48*AS*L*(v/rho)≤F := by
    dsimp [F,nativeBinScaleLoss,A,C] at *; linarith
  have hCcoef : C*AC*(v/rho)^2≤F := by
    dsimp [F,nativeBinScaleLoss,A,C] at *; linarith
  have hRcoef : (32:ℝ)≤F := by dsimp [F,nativeBinScaleLoss,A,C] at *; linarith
  have hmean : A*v*(w+D)^2≤F*v*(w^2+D^2) := by
    have hsq : (w+D)^2≤2*(w^2+D^2) := by nlinarith [sq_nonneg (w-D)]
    have hm := mul_le_mul_of_nonneg_left hsq (mul_nonneg hA hv.le)
    have hc := mul_le_mul_of_nonneg_right hAcoef
      (mul_nonneg hv.le (add_nonneg (sq_nonneg w) (sq_nonneg D)))
    nlinarith
  have hsideEq : 48*(AS*L*(k:ℝ)/(P*rho))=
      (48*AS*L*(v/rho))*v*(k:ℝ)*tau := by
    dsimp [tau]
    field_simp [hP.ne',hv.ne',hrho.ne']
    <;> ring
  have hcovEq : C*(AC*v/(P*rho^2))=(C*AC*(v/rho)^2)*v*tau := by
    dsimp [tau]
    field_simp [hP.ne',hv.ne',hrho.ne']
    <;> ring
  have hs := mul_le_mul_of_nonneg_right hScoef
    (mul_nonneg (mul_nonneg hv.le hkpos.le) htau)
  have hc := mul_le_mul_of_nonneg_right hCcoef (mul_nonneg hv.le htau)
  have hr := mul_le_mul_of_nonneg_right hRcoef (mul_nonneg hv.le hreverse)
  unfold nativeConditionalLedgerBudget
  rw [hsideEq,hcovEq]
  dsimp only [F,w,tau,A,C] at hmean hs hc hr ⊢
  simp only [div_eq_mul_inv] at hmean hs hc hr ⊢
  nlinarith

theorem exists_integer_native_bin_scale
    {L AS AC v rho P D Q y reverse : ℝ}
    (hL : 0≤L) (hAS : 0≤AS) (hAC : 0≤AC) (hv : 0<v) (hrho : 0<rho)
    (hP : 0<P) (hD : 0≤D) (hQ : 0≤Q) (hy : 0≤y) (hreverse : 0≤reverse)
    (cut : ℝ) :
    ∃k : ℕ,1≤k ∧ (k:ℝ)≤((Q^2*y)^2*P*v^2)^((1:ℝ)/3)+2 ∧
      nativeConditionalLedgerBudget k v cut ((Q^2*y)/(k:ℝ)+D)
        (AS*L*(k:ℝ)/(P*rho)) (AC*v/(P*rho^2)) reverse L ≤
      nativeBinScaleLoss L AS AC v rho*v*
        (2*((Q^2*y)/(P*v^2))^((2:ℝ)/3)+3/(P*v^2)+D^2+reverse)+
          16*(k:ℝ)*cut := by
  let tau := 1/(P*v^2)
  have htau : 0<tau := by dsimp [tau]; positivity
  have hY : 0≤Q^2*y := mul_nonneg (sq_nonneg Q) hy
  obtain ⟨k,hk,hks,hbal⟩ := exists_integer_bin_balance_square hY htau
  have hscale : (Q^2*y)^((2:ℝ)/3)*tau^((2:ℝ)/3)=
      ((Q^2*y)/(P*v^2))^((2:ℝ)/3) := by
    rw [←Real.mul_rpow hY htau.le]
    congr 1
    dsimp [tau]
    ring
  have hcube : (Q^2*y)^2/tau=(Q^2*y)^2*P*v^2 := by
    dsimp [tau]
    field_simp [hP.ne',hv.ne']
    <;> ring
  refine ⟨k,hk,by simpa only [hcube] using hks,?_⟩
  have hn := nativeConditionalLedgerBudget_le_bin_scale hL hAS hAC hv hrho hP hD hQ hy hreverse hk cut
  have hF : 0≤nativeBinScaleLoss L AS AC v rho := by
    unfold nativeBinScaleLoss
    positivity
  rw [mul_assoc,hscale] at hbal
  have hscaled := mul_le_mul_of_nonneg_left hbal (mul_nonneg hF hv.le)
  dsimp only [tau] at hscaled
  simp only [div_eq_mul_inv] at hn hscaled ⊢
  nlinarith

theorem native_bin_width_coverage {Q y : ℝ} (hQ : 0<Q) (hy : 0<y)
    {k : ℕ} (hk : 1≤k) :
    0<(Q^2*y)/(k:ℝ) ∧ Q^2*y≤(k:ℝ)*((Q^2*y)/(k:ℝ)) := by
  have hkpos : 0<(k:ℝ) := by exact_mod_cast (by omega : 0<k)
  refine ⟨div_pos (mul_pos (sq_pos_of_pos hQ) hy) hkpos,?_⟩
  rw [mul_div_cancel₀ _ hkpos.ne']

end OAI.SKFluctuations.LaplaceWindowFormalization
