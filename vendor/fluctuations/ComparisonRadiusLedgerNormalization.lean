module

public import ComparisonNativeRadiusQuantitative
public import ComparisonRadiusSizeRates

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 3500000

theorem radius_sqrt_cubic_linear_scale {x A D : ℝ} (hx : 0<x) (hA : 0 ≤ A) (_hD : 0 ≤ D) :
    Real.sqrt (A*x^3)*Real.sqrt (D*x)=x^2*(Real.sqrt A*Real.sqrt D) := by
  rw [←Real.sqrt_mul (mul_nonneg hA (pow_nonneg hx.le 3))]
  have he : A*x^3*(D*x)=(x^2)^2*(A*D) := by ring
  rw [he,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (sq_nonneg x),Real.sqrt_mul hA]

theorem comparisonRadiusMeanSquareBudget_scale (bins : ℕ)
    {x L delta y B w V T E : ℝ} (hx : 0<x) (hL : 0 ≤ L) (hd : 0<delta)
    (hT : 0 ≤ T) (hE : 0 ≤ E) :
    comparisonRadiusMeanSquareBudget bins (L*x) (delta*x) (y*x) B (w*x) (V*x^2) (T*x^3) (E*x)=
      x^3*comparisonRadiusMeanSquareBudget bins L delta y B w V T E := by
  have he : 1+(L*x)/(delta*x)=1+L/delta := by field_simp
  unfold comparisonRadiusMeanSquareBudget
  rw [he]
  have hnoise := radius_sqrt_cubic_linear_scale hx (mul_nonneg (by positivity : 0 ≤ 1+L/delta) hT) hL
  have hedge := radius_sqrt_cubic_linear_scale hx hT hE
  have hn : Real.sqrt ((1+L/delta)*(T*x^3))*Real.sqrt (L*x)=
      x^2*(Real.sqrt ((1+L/delta)*T)*Real.sqrt L) := by
    simpa only [mul_assoc] using hnoise
  have hne : 256*B*(y*x)*Real.sqrt ((1+L/delta)*(T*x^3))*Real.sqrt (L*x)=
      256*B*y*x^3*Real.sqrt ((1+L/delta)*T)*Real.sqrt L := by
    calc
      _ = (256*B*(y*x))*(Real.sqrt ((1+L/delta)*(T*x^3))*Real.sqrt (L*x)) := by ring
      _ = _ := by rw [hn];ring
  have hec : 2*B*(y*x)*Real.sqrt (T*x^3)*Real.sqrt (E*x)=
      2*B*y*x^3*Real.sqrt T*Real.sqrt E := by
    calc
      _ = (2*B*(y*x))*(Real.sqrt (T*x^3)*Real.sqrt (E*x)) := by ring
      _ = _ := by rw [hedge];ring
  rw [hne,hec]
  ring

theorem comparisonRadiusMeanSquareBudget_geometry_mono (bins : ℕ)
    {L Lbar delta y ybar B w wbar V T E : ℝ}
    (hL0 : 0 ≤ L) (hL : L ≤ Lbar) (hd : 0<delta)
    (hy0 : 0 ≤ y) (hy : y ≤ ybar) (hB : 0 ≤ B)
    (hw0 : 0 ≤ w) (hw : w ≤ wbar) (hV : 0 ≤ V) (hT : 0 ≤ T) (hE : 0 ≤ E) :
    comparisonRadiusMeanSquareBudget bins L delta y B w V T E ≤
      comparisonRadiusMeanSquareBudget bins Lbar delta ybar B wbar V T E := by
  have hLb : 0 ≤ Lbar := hL0.trans hL
  have hyb : 0 ≤ ybar := hy0.trans hy
  have hwb : 0 ≤ wbar := hw0.trans hw
  have hcost := mul_le_mul (add_le_add_left
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hw0 hw 2) (by norm_num : (0:ℝ)≤6)) (48*V)) hL hL0 (by positivity)
  have hfactor : (1+L/delta)*T ≤ (1+Lbar/delta)*T :=
    mul_le_mul_of_nonneg_right (add_le_add_right (div_le_div_of_nonneg_right hL hd.le) 1) hT
  have hroots := mul_le_mul (Real.sqrt_le_sqrt hfactor) (Real.sqrt_le_sqrt hL)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hnoise := mul_le_mul hy hroots (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hyb
  have hn := mul_le_mul_of_nonneg_left hnoise (by positivity : 0 ≤ 256*B)
  have hstrip := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hy0 hy 2) (by positivity : 0 ≤ B^2*E)
  have hcross := mul_le_mul_of_nonneg_right hy (by positivity : 0 ≤ 2*B*Real.sqrt T*Real.sqrt E)
  have hrest : 256*B*y*Real.sqrt ((1+L/delta)*T)*Real.sqrt L+T+B^2*y^2*E+
      2*B*y*Real.sqrt T*Real.sqrt E ≤
      256*B*ybar*Real.sqrt ((1+Lbar/delta)*T)*Real.sqrt Lbar+T+B^2*ybar^2*E+
      2*B*ybar*Real.sqrt T*Real.sqrt E := by nlinarith
  unfold comparisonRadiusMeanSquareBudget
  exact add_le_add (by convert hcost using 1 <;> ring)
    (mul_le_mul_of_nonneg_left hrest (Nat.cast_nonneg bins))

theorem comparisonRadiusMeanSquareBudget_normalized_le (bins : ℕ) (hbins : 0<bins)
    {x L delta y B V T CL CY : ℝ}
    (hx : 0<x) (hL0 : 0 ≤ L) (hL : L ≤ CL*x) (hy0 : 0 ≤ y) (hy : y ≤ CY*x)
    (hdelta : 0<delta) (hB : 0 ≤ B) (hV : 0 ≤ V) (hT : 0 ≤ T) :
    comparisonRadiusMeanSquareBudget bins L (delta*x) y B (B*y/(bins:ℝ)) V T (2*delta*x)/x^3 ≤
      comparisonRadiusMeanSquareBudget bins CL delta CY B (B*CY/(bins:ℝ))
        (V/x^2) (T/x^3) (2*delta) := by
  have hLx : 0 ≤ L/x := div_nonneg hL0 hx.le
  have hyx : 0 ≤ y/x := div_nonneg hy0 hx.le
  have hVx : 0 ≤ V/x^2 := div_nonneg hV (sq_nonneg x)
  have hTx : 0 ≤ T/x^3 := div_nonneg hT (pow_nonneg hx.le 3)
  have hLb : L/x ≤ CL := (div_le_iff₀ hx).mpr hL
  have hyb : y/x ≤ CY := (div_le_iff₀ hx).mpr hy
  have hb : 0<(bins:ℝ) := by exact_mod_cast hbins
  have hscale := comparisonRadiusMeanSquareBudget_scale bins hx hLx hdelta hTx
    (by positivity : 0 ≤ 2*delta) (y:=y/x) (B:=B) (w:=B*(y/x)/(bins:ℝ)) (V:=V/x^2)
  have hLy : (L/x)*x=L := div_mul_cancel₀ _ hx.ne'
  have hyy : (y/x)*x=y := div_mul_cancel₀ _ hx.ne'
  have hwy : (B*(y/x)/(bins:ℝ))*x=B*y/(bins:ℝ) := by field_simp
  have hVeq : (V/x^2)*x^2=V := div_mul_cancel₀ _ (pow_ne_zero _ hx.ne')
  have hTeq : (T/x^3)*x^3=T := div_mul_cancel₀ _ (pow_ne_zero _ hx.ne')
  rw [hLy,hyy,hwy,hVeq,hTeq] at hscale
  have hnorm : comparisonRadiusMeanSquareBudget bins L (delta*x) y B (B*y/(bins:ℝ)) V T (2*delta*x)/x^3=
      comparisonRadiusMeanSquareBudget bins (L/x) delta (y/x) B (B*(y/x)/(bins:ℝ))
        (V/x^2) (T/x^3) (2*delta) := by
    rw [hscale]
    field_simp
  rw [hnorm]
  apply comparisonRadiusMeanSquareBudget_geometry_mono bins hLx hLb hdelta hyx hyb hB
    (by positivity) _ hVx hTx (by positivity)
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hyb hB) hb.le

theorem comparisonRadiusMeanSquareBudget_normalized_tendsto (bins : ℕ)
    (CL delta CY B : ℝ) (v t : ℕ→ℝ)
    (hv : Tendsto v atTop (𝓝 0)) (ht : Tendsto t atTop (𝓝 0)) :
    Tendsto (fun n=>comparisonRadiusMeanSquareBudget bins CL delta CY B (B*CY/(bins:ℝ))
      (v n) (t n) (2*delta)) atTop
      (𝓝 (6*(B*CY/(bins:ℝ))^2*CL+2*(bins:ℝ)*B^2*CY^2*delta)) := by
  have hc : Continuous (fun p:ℝ×ℝ=>comparisonRadiusMeanSquareBudget bins CL delta CY B
      (B*CY/(bins:ℝ)) p.1 p.2 (2*delta)) := by
    unfold comparisonRadiusMeanSquareBudget
    fun_prop
  have h := (hc.tendsto (0,0)).comp (hv.prodMk_nhds ht)
  have he : comparisonRadiusMeanSquareBudget bins CL delta CY B (B*CY/(bins:ℝ)) 0 0 (2*delta)=
      6*(B*CY/(bins:ℝ))^2*CL+2*(bins:ℝ)*B^2*CY^2*delta := by
    simp only [comparisonRadiusMeanSquareBudget,mul_zero,zero_mul,Real.sqrt_zero,add_zero,zero_add]
    ring
  rw [he] at h
  exact h

theorem comparisonRadiusOrderedDefect_tendsto_zero
    (x L y D T : ℕ→ℝ) (V : ℝ→ℕ→ℝ) {B CL CY : ℝ}
    (hB : 0 ≤ B) (hCL : 0 ≤ CL) (hCY : 0 ≤ CY)
    (hx : ∀n,0<x n) (hL0 : ∀n,0 ≤ L n) (hL : ∀n,L n ≤ CL*x n)
    (hy0 : ∀n,0 ≤ y n) (hy : ∀n,y n ≤ CY*x n)
    (hD : ∀n,0 ≤ D n) (hT : ∀n,0 ≤ T n)
    (hV : ∀tau,0<tau→∀n,0 ≤ V tau n)
    (hVlim : ∀tau,0<tau→Tendsto (fun n=>V tau n/(x n)^2) atTop (𝓝 0))
    (hTlim : Tendsto (fun n=>T n/(x n)^3) atTop (𝓝 0))
    (hledger : ∀bins : ℕ,0<bins→∀tau : ℝ,0<tau→∀ᶠn in atTop,
      D n ≤ comparisonRadiusMeanSquareBudget bins (L n) (tau*x n) (y n) B
        (B*y n/(bins:ℝ)) (V tau n) (T n) (2*tau*x n)) :
    Tendsto (fun n=>D n/(x n)^3) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun n=>ha.trans_le (div_nonneg (hD n) (pow_nonneg (hx n).le 3)))
  · intro epsilon hepsilon
    let C := 6*B^2*CY^2*CL+2*B^2*CY^2+1
    have hC : 0<C := by dsimp only [C];positivity
    obtain ⟨bins,hbins,tau,htau,hchoice⟩ := comparison_radius_height_strip_choices
      (by positivity : 0<epsilon/(2*C))
    have hb : 0<(bins:ℝ) := by exact_mod_cast hbins
    have hconstant : 6*(B*CY/(bins:ℝ))^2*CL+2*(bins:ℝ)*B^2*CY^2*tau < epsilon/2 := by
      have h1 : 6*(B*CY/(bins:ℝ))^2*CL ≤ C*(1/(bins:ℝ)^2) := by
        have hc1 : 6*B^2*CY^2*CL ≤ C := by
          dsimp only [C]
          nlinarith [mul_nonneg (sq_nonneg B) (sq_nonneg CY)]
        have hh := mul_le_mul_of_nonneg_right hc1 (by positivity : 0 ≤ 1/(bins:ℝ)^2)
        convert hh using 1 <;> field_simp <;> ring
      have h2 : 2*(bins:ℝ)*B^2*CY^2*tau ≤ C*((bins:ℝ)*tau) := by
        have hc2 : 2*B^2*CY^2 ≤ C := by
          have hpos : 0 ≤ 6*B^2*CY^2*CL := by positivity
          dsimp only [C];linarith
        have hh := mul_le_mul_of_nonneg_right hc2 (mul_nonneg hb.le htau.le)
        nlinarith
      have hh := mul_lt_mul_of_pos_left hchoice hC
      have hcanc : C*(epsilon/(2*C))=epsilon/2 := by field_simp
      rw [hcanc] at hh
      linarith
    have hlim := comparisonRadiusMeanSquareBudget_normalized_tendsto bins CL tau CY B _ _ (hVlim tau htau) hTlim
    have hsmall := (tendsto_order.mp hlim).2 (epsilon) (by linarith)
    filter_upwards [hledger bins hbins tau htau,hsmall] with n hn hs
    have hnormalized := comparisonRadiusMeanSquareBudget_normalized_le bins hbins
      (hx n) (hL0 n) (hL n) (hy0 n) (hy n) htau hB (hV tau htau n) (hT n)
    exact (div_le_div_of_nonneg_right hn (pow_nonneg (hx n).le 3)).trans hnormalized |>.trans_lt hs

end OAI.SKFluctuations.LaplaceWindowFormalization
