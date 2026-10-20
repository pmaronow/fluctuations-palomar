module

public import ComparisonActualShiftedAllMassAbsoluteDisagreementSelection
public import ComparisonNativeUpwardSmallParent

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 9000000

theorem eventually_actual_shifted_allmass_absolute_disagreement_mass_le
    {delta gamma Dbound m c0 eps ell : ℝ} (J : ℕ)
    (hdelta : 0 < delta) (hgamma : 0 < gamma) (hm : 0 < m) (hc0 : 0 < c0)
    (heps : 0 < eps) (hell : 0 < ell) :
    ∃eta : ℝ,0 < eta ∧ eta ≤ 1 ∧ ∀ᶠ n : ℕ in atTop,
      ∀(a : ActualShiftedAllMassParentChildCall n delta) (x leftBand rightBand : ℝ),
      a.context.d ≤ Dbound → Real.sqrt (n:ℝ)*a.context.E ≤ a.context.d^2 →
      gamma*(n:ℝ)^(-(2:ℝ)/3+m)*a.context.d ≤ a.context.E →
      x∈Ioc (0:ℝ) 1 → comparisonLowerScale n a.context.E a.context.d ≤ x →
      a.lam ≤ a.context.d^2 → a.e x ≤ eta^3*x^2 →
      a.childRadius=c0*x → a.childLam=(c0*x)^2 →
      a.err ≤ (n:ℝ)^(20*delta)*actualChildErrorBudget n delta c0 a.context.d a.lam x →
      a.context.r0 ≤ (eps*x)/(4*((J:ℝ)+2)) → a.context.s ≤ leftBand → rightBand ≤ 1 →
      (∀u∈Icc leftBand rightBand,a.R u ≤ (J:ℝ)*(eps*x)) →
      volume {u | u∈Icc leftBand rightBand ∧ 3*(eps*x) ≤ |a.Z u-a.R u|} ≤
        2*(J+1:ℝ≥0∞)*ENNReal.ofReal (ell*x) := by
  let C:ℝ:=(J:ℝ)+2
  let Cy:=C*eps
  let rho:=1/C
  let q:=ell/(2*Cy)
  let cScale:=min 1 (2*eps)
  let K:=min (c0^2) (c0^3/Cy)
  let eta:=min 1 (Real.sqrt K)
  have hJ0 : (0:ℝ) ≤ (J:ℝ):=Nat.cast_nonneg _
  have hC : 1 ≤ C := by dsimp [C];linarith
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  have hCy : 0 < Cy := mul_pos hC0 heps
  have hrho : 0 < rho := by dsimp [rho];positivity
  have hrho1 : rho ≤ 1 := by dsimp [rho];exact (div_le_one₀ hC0).mpr hC
  have hq : 0 < q := by dsimp [q];positivity
  have hcScale : 0 < cScale := lt_min zero_lt_one (by positivity)
  have hcScale1 : cScale ≤ 1 := min_le_left _ _
  have hK : 0 < K := by dsimp [K];positivity
  have heta : 0 < eta := lt_min zero_lt_one (Real.sqrt_pos.mpr hK)
  have heta1 : eta ≤ 1 := min_le_left _ _
  have heta2 : eta^2 ≤ K := by
    have hh:=pow_le_pow_left₀ heta.le (show eta ≤ Real.sqrt K from min_le_right _ _) 2
    rwa [Real.sq_sqrt hK.le] at hh
  have Hup:=eventually_actual_shifted_allmass_child_excludes_close_upward (Dbound:=Dbound)
    (cMove:=1) (qRamp:=q) (qBand:=q) hdelta hgamma hm hc0 hcScale hcScale1
    zero_lt_one le_rfl hrho hrho1 hq hq
  have Hdown:=eventually_actual_shifted_allmass_child_excludes_close_downward (Dbound:=Dbound)
    (qTravel:=q) (qBand:=q) hdelta hgamma hm hc0 hcScale hcScale1 hC hrho hrho1 hq hq
  refine ⟨eta,heta,heta1,?_⟩
  filter_upwards [Hup,Hdown] with n hnup hndown
  intro a x leftBand rightBand hdD hupper hlower hx hax hld hweak hdc hlc herr horigin ha hb hRupper
  by_contra hmass
  have hx0 : 0 < x := hx.1
  have hstep : 0 < eps*x := mul_pos heps hx0
  have hL : 0 < ell*x := mul_pos hell hx0
  have hwidth : 2*q*((J:ℝ)+2)*(eps*x) ≤ ell*x := by
    have he : 2*q*((J:ℝ)+2)*(eps*x)=ell*x := by
      dsimp [q,Cy,C];field_simp
    exact he.le
  obtain ⟨y,start,middle,finish,hy,hylo,hyhi,hstart,hfinish,ha',hmiddle,hmiddleFinish,hf,
    hqr,hqb,hsep⟩:=actual_shifted_allmass_absolute_disagreement_selects_close_band a J ha hb hstep hL hq.le hwidth
      hRupper (lt_of_not_ge hmass)
  have hscale : cScale*x ≤ y := by
    have hh:=mul_le_mul_of_nonneg_right (min_le_right (1:ℝ) (2*eps)) hx0.le
    dsimp only [cScale]
    nlinarith
  have hweak1 : a.e x ≤ x^2 := by
    have he : eta^3 ≤ 1 := by simpa using pow_le_pow_left₀ heta.le heta1 3
    exact hweak.trans (by nlinarith [mul_le_mul_of_nonneg_right he (sq_nonneg x)])
  have horiginY : a.context.r0 ≤ rho*y/8 := by
    have HCpos : 0 < (J:ℝ)+2 := by positivity
    have H := (le_div_iff₀ (by positivity : 0 < 4*((J:ℝ)+2))).mp horigin
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<8)).mpr
    dsimp only [rho,C]
    rw [div_mul_eq_mul_div,one_mul]
    apply (le_div_iff₀ HCpos).mpr
    nlinarith only [H,hylo]
  rcases hsep with hup|hdown
  · have hyC : y ≤ Cy*x := by simpa only [Cy,C,mul_assoc] using hyhi
    have hsmall:=actual_child_strength_dominates_weak_parent a.context.hd a.hlam hld
      hx0 hy.1 hc0 hCy hyC heta.le heta1 hweak heta2
    rw [←hlc,←hdc] at hsmall
    exact hnup a x y start middle finish hdD hupper hlower hx hy hax hscale hweak1
      hdc hlc herr horiginY ha' hmiddle hmiddleFinish hf hqr hqb hup.1 (Or.inr hsmall) hup.2
  · exact hndown a x y start middle middle finish hdD hupper hlower hx hy hax hscale hweak1
      hdc hlc herr horiginY ha' hmiddle.le le_rfl hmiddleFinish hf hqb hqr hdown.1 hdown.2.1 hdown.2.2

end OAI.SKFluctuations.LaplaceWindowFormalization
