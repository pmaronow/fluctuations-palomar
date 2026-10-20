module

public import ComparisonNativeCavityConcentrationRadiusBandScale

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 8000000

def radiusPolynomialLedgerConstant (B C Y : ℝ) : ℝ :=
  (48+6*B^2*Y^2)*C+
    2*(256*B*Y*Real.sqrt (1+C)*Real.sqrt C+1+2*B^2*Y^2+2*B*Y*Real.sqrt 2)

theorem radiusPolynomialLedgerConstant_nonneg {B C Y : ℝ}
    (hB : 0≤B) (hC : 0≤C) (hY : 0≤Y) : 0≤radiusPolynomialLedgerConstant B C Y := by
  unfold radiusPolynomialLedgerConstant
  positivity

theorem comparisonRadiusMeanSquareBudget_polynomial_le (bins : ℕ)
    {s B C Y V T : ℝ} (hs : 0<s) (hs1 : s≤1)
    (hB : 0≤B) (hC : 0≤C) (hY : 0≤Y)
    (hblo : 1/s≤(bins:ℝ)) (hbhi : (bins:ℝ)≤2/s)
    (_hV0 : 0≤V) (hV : V ≤ s^16) (hT0 : 0≤T) (hT : T ≤ s^64) :
    comparisonRadiusMeanSquareBudget bins C (s^8) Y B (B*Y/(bins:ℝ)) V T (2*s^8)≤
      radiusPolynomialLedgerConstant B C Y*s^2 := by
  have hbp : 0<(bins:ℝ) := (one_div_pos.mpr hs).trans_le hblo
  have hs8 : 0<s^8 := pow_pos hs _
  have hs8one : s^8≤1 := pow_le_one₀ hs.le hs1
  have hbin : 1≤(bins:ℝ)*s := (div_le_iff₀ hs).mp hblo
  have hw : B*Y/(bins:ℝ)≤B*Y*s := by
    apply (div_le_iff₀ hbp).mpr
    have H:=mul_le_mul_of_nonneg_left hbin (mul_nonneg hB hY)
    nlinarith
  have hw2:=pow_le_pow_left₀ (div_nonneg (mul_nonneg hB hY) hbp.le) hw 2
  have hV16:=hV.trans (pow_le_pow_of_le_one hs.le hs1 (by norm_num : 2≤(16:ℕ)))
  have hfirst : (48*V+6*(B*Y/(bins:ℝ))^2)*C≤(48+6*B^2*Y^2)*C*s^2 := by
    have H:=mul_le_mul_of_nonneg_right
      (add_le_add (mul_le_mul_of_nonneg_left hV16 (by norm_num : (0:ℝ)≤48))
        (mul_le_mul_of_nonneg_left hw2 (by norm_num : (0:ℝ)≤6))) hC
    nlinarith
  have hfactor : 1+C/s^8≤(1+C)/s^8 := by
    apply (le_div_iff₀ hs8).mpr
    rw [add_mul,div_mul_cancel₀ _ hs8.ne']
    linarith
  have hnoiseinner : (1+C/s^8)*T≤(1+C)*s^56 := by
    have H:=mul_le_mul hfactor hT hT0 (div_nonneg (by linarith) hs8.le)
    have he : ((1+C)/s^8)*s^64=(1+C)*s^56 := by
      rw [show (64:ℕ)=56+8 by norm_num,pow_add]
      field_simp
    exact H.trans_eq he
  have hsqrtnoise : Real.sqrt ((1+C/s^8)*T)≤Real.sqrt (1+C)*s^28 := by
    have H:=Real.sqrt_le_sqrt hnoiseinner
    have he : Real.sqrt ((1+C)*s^56)=Real.sqrt (1+C)*s^28 := by
      rw [show (56:ℕ)=28*2 by norm_num,pow_mul,Real.sqrt_mul (by linarith : 0≤1+C),
        Real.sqrt_sq (pow_nonneg hs.le 28)]
    exact H.trans_eq he
  have hsqrtT : Real.sqrt T≤ s^32 := by
    have H:=Real.sqrt_le_sqrt hT
    rw [show (64:ℕ)=32*2 by norm_num,pow_mul,Real.sqrt_sq (pow_nonneg hs.le 32)] at H
    exact H
  have hsqrtE : Real.sqrt (2*s^8)=Real.sqrt 2*s^4 := by
    rw [show (8:ℕ)=4*2 by norm_num,pow_mul,Real.sqrt_mul (by norm_num : (0:ℝ)≤2),
      Real.sqrt_sq (pow_nonneg hs.le 4)]
  let A:=256*B*Y*Real.sqrt (1+C)*Real.sqrt C
  let E:=2*B*Y*Real.sqrt 2
  have hA : 0≤A := by dsimp [A];positivity
  have hE : 0≤E := by dsimp [E];positivity
  have hnoise : 256*B*Y*Real.sqrt ((1+C/s^8)*T)*Real.sqrt C≤A*s^28 := by
    have H:=mul_le_mul_of_nonneg_left hsqrtnoise (by positivity : 0≤256*B*Y*Real.sqrt C)
    dsimp only [A]
    nlinarith
  have hedge : 2*B*Y*Real.sqrt T*Real.sqrt (2*s^8)≤E*s^36 := by
    rw [hsqrtE]
    have H:=mul_le_mul_of_nonneg_left hsqrtT (by positivity : 0≤2*B*Y*Real.sqrt 2*s^4)
    dsimp only [E]
    rw [show (36:ℕ)=32+4 by norm_num,pow_add]
    nlinarith
  have hinside : 256*B*Y*Real.sqrt ((1+C/s^8)*T)*Real.sqrt C+T+B^2*Y^2*(2*s^8)+
      2*B*Y*Real.sqrt T*Real.sqrt (2*s^8)≤A*s^28+s^64+2*B^2*Y^2*s^8+E*s^36 := by
    nlinarith
  have hscaled := mul_le_mul hbhi hinside
    (by positivity : 0≤256*B*Y*Real.sqrt ((1+C/s^8)*T)*Real.sqrt C+T+B^2*Y^2*(2*s^8)+
      2*B*Y*Real.sqrt T*Real.sqrt (2*s^8)) (div_nonneg (by norm_num) hs.le)
  have he : (2/s)*(A*s^28+s^64+2*B^2*Y^2*s^8+E*s^36)=
      2*(A*s^27+s^63+2*B^2*Y^2*s^7+E*s^35) := by
    rw [show (28:ℕ)=27+1 by norm_num,show (64:ℕ)=63+1 by norm_num,
      show (8:ℕ)=7+1 by norm_num,show (36:ℕ)=35+1 by norm_num]
    simp only [pow_add,pow_one]
    field_simp
  rw [he] at hscaled
  have hp27:=pow_le_pow_of_le_one hs.le hs1 (by norm_num : 2≤(27:ℕ))
  have hp63:=pow_le_pow_of_le_one hs.le hs1 (by norm_num : 2≤(63:ℕ))
  have hp7:=pow_le_pow_of_le_one hs.le hs1 (by norm_num : 2≤(7:ℕ))
  have hp35:=pow_le_pow_of_le_one hs.le hs1 (by norm_num : 2≤(35:ℕ))
  have H27:=mul_le_mul_of_nonneg_left hp27 hA
  have H7:=mul_le_mul_of_nonneg_left hp7 (by positivity : 0≤2*B^2*Y^2)
  have H35:=mul_le_mul_of_nonneg_left hp35 hE
  have hlast : (bins:ℝ)*(256*B*Y*Real.sqrt ((1+C/s^8)*T)*Real.sqrt C+T+B^2*Y^2*(2*s^8)+
      2*B*Y*Real.sqrt T*Real.sqrt (2*s^8))≤2*(A+1+2*B^2*Y^2+E)*s^2 := by
    nlinarith
  unfold comparisonRadiusMeanSquareBudget radiusPolynomialLedgerConstant
  dsimp only [A,E] at hlast
  nlinarith

theorem radius_polynomial_bins_geometry {s : ℝ} (hs : 0<s) (hs1 : s≤1) :
    0<⌈1/s⌉₊ ∧ 1/s≤(⌈1/s⌉₊:ℝ) ∧ (⌈1/s⌉₊:ℝ)≤2/s := by
  have hi : 0<1/s := one_div_pos.mpr hs
  have hi1 : 1≤1/s := (le_div_iff₀ hs).mpr (by linarith)
  exact ⟨Nat.ceil_pos.mpr hi,Nat.le_ceil _,(Nat.ceil_lt_add_one hi.le).le.trans (by
    rw [show (2:ℝ)/s=1/s+1/s by ring]
    linarith)⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
