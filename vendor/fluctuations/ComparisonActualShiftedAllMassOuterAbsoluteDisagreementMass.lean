module

public import ComparisonActualShiftedAllMassAbsoluteDisagreementSelection

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 12000000

theorem eventually_actual_shifted_allmass_outer_absolute_disagreement_mass_le
    {delta gamma Dbound m c0 ratio cMove eps ell : ℝ} (J : ℕ)
    (hdelta : 0 < delta) (hgamma : 0 < gamma) (hm : 0 < m) (hc0 : 0 < c0)
    (hratio : 0 < ratio) (hcMove : 0 < cMove) (hcMove1 : cMove ≤ 1)
    (heps : 0 < eps) (hell : 0 < ell) :
    ∀ᶠn : ℕ in atTop,∀(a : ActualShiftedAllMassParentChildCall n delta)
      (x y leftBand rightBand : ℝ),
      a.context.d ≤ Dbound → Real.sqrt (n:ℝ)*a.context.E ≤ a.context.d^2 →
      gamma*(n:ℝ)^(-(2:ℝ)/3+m)*a.context.d ≤ a.context.E →
      x∈Ioc (0:ℝ) 1 → comparisonLowerScale n a.context.E a.context.d ≤ x →
      ratio*x ≤ y → a.e x ≤ x^2 →
      a.childRadius=c0*x → a.childLam=(c0*x)^2 →
      a.err ≤ (n:ℝ)^(20*delta)*actualChildErrorBudget n delta c0 a.context.d a.lam x →
      a.context.r0 ≤ (eps*y)/(4*((J:ℝ)+2)) → a.context.s ≤ leftBand → rightBand ≤ 1 →
      (∀u∈Icc leftBand rightBand,a.R u ≤ (J:ℝ)*(eps*y)) →
      (∀u∈Icc leftBand 1,cMove*(((J:ℝ)+2)*eps*y) ≤ a.R u) →
      volume {u | u∈Icc leftBand rightBand ∧ 3*(eps*y) ≤ |a.Z u-a.R u|} ≤
        2*(J+1:ℝ≥0∞)*ENNReal.ofReal (ell*y) := by
  let C : ℝ := (J:ℝ)+2
  let rho := 1/C
  let q := ell/(2*C*eps)
  let cScale := min 1 (2*eps*ratio)
  have hC : 1 ≤ C := by dsimp only [C]; have H := Nat.cast_nonneg (α:=ℝ) J; linarith
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hrho : 0 < rho := by dsimp only [rho]; positivity
  have hrho1 : rho ≤ 1 := (div_le_one₀ hCpos).mpr hC
  have hq : 0 < q := by dsimp only [q]; positivity
  have hcScale : 0 < cScale := lt_min zero_lt_one (by positivity)
  have hcScale1 : cScale ≤ 1 := min_le_left _ _
  have Hup := eventually_actual_shifted_allmass_child_excludes_close_upward (Dbound:=Dbound)
    (cMove:=cMove) (qRamp:=q) (qBand:=q) hdelta hgamma hm hc0 hcScale hcScale1
    hcMove hcMove1 hrho hrho1 hq hq
  have Hdown := eventually_actual_shifted_allmass_child_excludes_close_downward (Dbound:=Dbound)
    (qTravel:=q) (qBand:=q) hdelta hgamma hm hc0 hcScale hcScale1 hC hrho hrho1 hq hq
  filter_upwards [Hup,Hdown] with n hnup hndown
  intro a x y leftBand rightBand hdD hupper hlower hx hax hxy hweak hdc hlc herr
    horigin ha hb hRupper hRlower
  by_contra hmass
  have hy : 0 < y := (mul_pos hratio hx.1).trans_le hxy
  have hstep : 0 < eps*y := mul_pos heps hy
  have hL : 0 < ell*y := mul_pos hell hy
  have hwidth : 2*q*((J:ℝ)+2)*(eps*y) ≤ ell*y := by
    have he : 2*q*((J:ℝ)+2)*(eps*y)=ell*y := by
      dsimp only [q,C]
      field_simp
    exact he.le
  obtain ⟨r,start,middle,finish,hr,hrlo,hrhi,hstart,_hfinish,ha',hmiddle,hmiddleFinish,hf,
    hqr,hqb,hsep⟩ := actual_shifted_allmass_absolute_disagreement_selects_close_band a J ha hb hstep hL hq.le
      hwidth hRupper (lt_of_not_ge hmass)
  have hscale : cScale*x ≤ r := by
    have H1 := mul_le_mul_of_nonneg_right (min_le_right (1:ℝ) (2*eps*ratio)) hx.1.le
    have H2 := mul_le_mul_of_nonneg_left hxy (show 0 ≤ 2*eps by positivity)
    dsimp only [cScale]
    nlinarith only [H1,H2,hrlo]
  have horiginR : a.context.r0 ≤ rho*r/8 := by
    have HCpos : 0 < (J:ℝ)+2 := by positivity
    have H := (le_div_iff₀ (by positivity : 0 < 4*((J:ℝ)+2))).mp horigin
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<8)).mpr
    dsimp only [rho,C]
    rw [div_mul_eq_mul_div,one_mul]
    apply (le_div_iff₀ HCpos).mpr
    nlinarith only [H,hrlo]
  rcases hsep with hup|hdown
  · have hroute : ∀u∈Icc start 1,cMove*r ≤ a.R u := by
      intro u hu
      have H := hRlower u ⟨hstart.1.trans hu.1,hu.2⟩
      have Hr := mul_le_mul_of_nonneg_left hrhi hcMove.le
      exact Hr.trans (by simpa only [mul_assoc] using H)
    exact hnup a x r start middle finish hdD hupper hlower hx hr hax hscale hweak
      hdc hlc herr horiginR ha' hmiddle hmiddleFinish hf hqr hqb hup.1 (Or.inl hroute) hup.2
  · exact hndown a x r start middle middle finish hdD hupper hlower hx hr hax hscale hweak
      hdc hlc herr horiginR ha' hmiddle.le le_rfl hmiddleFinish hf hqb hqr hdown.1 hdown.2.1 hdown.2.2

end OAI.SKFluctuations.LaplaceWindowFormalization
