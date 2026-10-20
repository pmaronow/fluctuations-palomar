module

public import ComparisonActualChildData
public import LowerLedger

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 2000000

theorem comparison_parent_scale_lower_bounds
    {n : ℕ} (hn : 0<(n:ℝ)) {m gamma d E : ℝ} (hgamma : 0<gamma) (hd : 0<d)
    (hlower : gamma*(n:ℝ)^(-(2:ℝ)/3+m)*d≤E)
    (hupper : E≤d^2/Real.sqrt n) :
    gamma*(n:ℝ)^(-(1:ℝ)/6+m)≤d ∧
    gamma^2*(n:ℝ)^(-(5:ℝ)/6+2*m)≤E ∧
    gamma*(n:ℝ)^(-(1:ℝ)/6+m)≤Real.sqrt n*E/d := by
  have hs : 0<Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr hn
  have hp : 0<(n:ℝ)^(-(2:ℝ)/3+m) := Real.rpow_pos_of_pos hn _
  have he : Real.sqrt (n:ℝ)*(n:ℝ)^(-(2:ℝ)/3+m)=(n:ℝ)^(-(1:ℝ)/6+m) := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_add hn]
    congr 1
    ring
  have hdlo : gamma*(n:ℝ)^(-(1:ℝ)/6+m)≤d := by
    have hb := mul_le_mul_of_nonneg_left (hlower.trans hupper) hs.le
    have hc : Real.sqrt (n:ℝ)*(d^2/Real.sqrt n)=d*d := by field_simp
    rw [hc] at hb
    have hr : Real.sqrt (n:ℝ)*(gamma*(n:ℝ)^(-(2:ℝ)/3+m)*d)=
        (gamma*(n:ℝ)^(-(1:ℝ)/6+m))*d := by rw [←he];ring
    rw [hr] at hb
    exact le_of_mul_le_mul_right hb hd
  have hElo : gamma^2*(n:ℝ)^(-(5:ℝ)/6+2*m)≤E := by
    have hh := mul_le_mul_of_nonneg_left hdlo (mul_nonneg hgamma.le hp.le)
    have hr : gamma*(n:ℝ)^(-(2:ℝ)/3+m)*(gamma*(n:ℝ)^(-(1:ℝ)/6+m))=
        gamma^2*(n:ℝ)^(-(5:ℝ)/6+2*m) := by
      calc
        _ = gamma^2*((n:ℝ)^(-(2:ℝ)/3+m)*(n:ℝ)^(-(1:ℝ)/6+m)) := by ring
        _ = _ := by rw [←Real.rpow_add hn];congr 1;congr 1;ring
    exact (hr ▸ hh).trans hlower
  refine ⟨hdlo,hElo,?_⟩
  apply (le_div_iff₀ hd).mpr
  have hh := mul_le_mul_of_nonneg_left hlower hs.le
  have hr : Real.sqrt (n:ℝ)*(gamma*(n:ℝ)^(-(2:ℝ)/3+m)*d)=
      (gamma*(n:ℝ)^(-(1:ℝ)/6+m))*d := by rw [←he];ring
  exact hr ▸ hh

theorem actual_child_nonceiling_cube_ratio
    {n : ℕ} {delta c0 d lam x : ℝ} (hc0 : 0<c0) (hlam : 0<lam) (hx : 0<x)
    (hbranch : actualChildErrorBudget n delta c0 d lam x=
      (n:ℝ)^(-100*delta)*laplaceComparisonStrength d lam x*x^3) :
    (actualChildCutoff n delta c0 d lam x)^3/(laplaceComparisonStrength d lam x*x)=
      (Real.sqrt (n:ℝ))^3*((n:ℝ)^(-100*delta))^3*
        (laplaceComparisonStrength d lam x*x^2)^2*x/c0^3 := by
  unfold actualChildCutoff
  rw [hbranch]
  unfold actualChildRadius
  have he : laplaceComparisonStrength d lam x≠0 := (laplaceComparisonStrength_pos d hlam x).ne'
  field_simp [he,hc0.ne',hx.ne']

theorem actual_child_margin_power_identity
    {n : ℕ} (hn : 0<(n:ℝ)) (m delta c0 p gamma xi : ℝ) :
    (Real.sqrt (n:ℝ))^3*((n:ℝ)^(-100*delta))^3*
      (p*(n:ℝ)^(1+delta)*(gamma^2*(n:ℝ)^(-(5:ℝ)/6+2*m))^2)^2*
      (xi*(n:ℝ)^(-(1:ℝ)/6+m))/c0^3=
      (p^2*gamma^8*xi/c0^3)*(n:ℝ)^(9*m-298*delta) := by
  rw [Real.sqrt_eq_rpow]
  simp only [mul_pow,←Real.rpow_mul_natCast hn.le]
  calc
    _ = (p^2*gamma^8*xi/c0^3)*
      (((((n:ℝ)^((1/2:ℝ)*3)*(n:ℝ)^((-100*delta)*3))*
        (n:ℝ)^((1+delta)*2))*(n:ℝ)^((-(5:ℝ)/6+2*m)*4))*
        (n:ℝ)^(-(1:ℝ)/6+m)) := by ring
    _ = _ := by
      rw [←Real.rpow_add hn,←Real.rpow_add hn,←Real.rpow_add hn,←Real.rpow_add hn]
      congr 1
      congr 1
      ring

theorem actual_child_nonceiling_gap_lower
    {n : ℕ} (hn : 0<(n:ℝ)) {m delta c0 d lam x E gamma p xi : ℝ}
    (hc0 : 0<c0) (hlam : 0<lam) (hx : 0<x)
    (hgamma : 0<gamma) (hp : 0<p) (hxi : 0<xi)
    (hE : gamma^2*(n:ℝ)^(-(5:ℝ)/6+2*m)≤E)
    (hxlower : xi*(n:ℝ)^(-(1:ℝ)/6+m)≤x)
    (hstrength : p*(n:ℝ)^(1+delta)*E^2≤laplaceComparisonStrength d lam x*x^2)
    (hbranch : actualChildErrorBudget n delta c0 d lam x=
      (n:ℝ)^(-100*delta)*laplaceComparisonStrength d lam x*x^3) :
    (p^2*gamma^8*xi/c0^3)*(n:ℝ)^(9*m-298*delta)≤
      (actualChildCutoff n delta c0 d lam x)^3/(laplaceComparisonStrength d lam x*x) := by
  have hE0 : 0≤E := (by positivity : 0≤gamma^2*(n:ℝ)^(-(5:ℝ)/6+2*m)).trans hE
  rw [actual_child_nonceiling_cube_ratio hc0 hlam hx hbranch]
  rw [←actual_child_margin_power_identity hn m delta c0 p gamma xi]
  have hE2 := pow_le_pow_left₀ (by positivity : 0≤gamma^2*(n:ℝ)^(-(5:ℝ)/6+2*m)) hE 2
  have hinner : p*(n:ℝ)^(1+delta)*(gamma^2*(n:ℝ)^(-(5:ℝ)/6+2*m))^2≤
      laplaceComparisonStrength d lam x*x^2 :=
    (mul_le_mul_of_nonneg_left hE2 (by positivity)).trans hstrength
  have hinner2 := pow_le_pow_left₀ (by positivity : 0≤
    p*(n:ℝ)^(1+delta)*(gamma^2*(n:ℝ)^(-(5:ℝ)/6+2*m))^2) hinner 2
  apply div_le_div_of_nonneg_right _ (pow_nonneg hc0.le _)
  have h1 := mul_le_mul_of_nonneg_left hinner2
    (by positivity : 0≤(Real.sqrt (n:ℝ))^3*((n:ℝ)^(-100*delta))^3)
  exact mul_le_mul h1 hxlower (by positivity) (by positivity)

theorem actual_child_nonceiling_gap_eventually
    (m delta c0 p gamma xi : ℝ) (hc0 : 0<c0) (hp : 0<p) (hgamma : 0<gamma) (hxi : 0<xi)
    (hmargin : 0<9*m-298*delta) (K : ℝ) :
    ∀ᶠ n : ℕ in atTop,∀d lam x E : ℝ,
      0<lam → 0<x →
      gamma^2*(n:ℝ)^(-(5:ℝ)/6+2*m)≤E →
      xi*(n:ℝ)^(-(1:ℝ)/6+m)≤x →
      p*(n:ℝ)^(1+delta)*E^2≤laplaceComparisonStrength d lam x*x^2 →
      actualChildErrorBudget n delta c0 d lam x=
        (n:ℝ)^(-100*delta)*laplaceComparisonStrength d lam x*x^3 →
      K*laplaceComparisonStrength d lam x*x≤(actualChildCutoff n delta c0 d lam x)^3 := by
  have hcoef : 0<p^2*gamma^8*xi/c0^3 := by positivity
  have hg := eventually_coefficient_rpow_le (c:=K) (d:=p^2*gamma^8*xi/c0^3)
    (q:=0) (r:=9*m-298*delta) hcoef hmargin
  filter_upwards [hg,eventually_gt_atTop (0:ℕ)] with n hn hnpos d lam x E hlam hx hE hxlo hs hb
  have hnreal : 0<(n:ℝ) := by exact_mod_cast hnpos
  have hg0 : K≤(p^2*gamma^8*xi/c0^3)*(n:ℝ)^(9*m-298*delta) := by simpa using hn
  have hgap := actual_child_nonceiling_gap_lower hnreal hc0 hlam hx hgamma hp hxi hE hxlo hs hb
  simpa only [mul_assoc] using
    (le_div_iff₀ (mul_pos (laplaceComparisonStrength_pos d hlam x) hx)).mp (hg0.trans hgap)

theorem actual_child_nonceiling_clocks_eventually
    (m delta c0 p gamma eta C : ℝ) (hc0 : 0<c0) (hc01 : c0≤1)
    (hp : 0<p) (hgamma : 0<gamma) (heta : 0<eta) (heta1 : eta≤1) (hC : 1≤C)
    (hmargin : 0<9*m-298*delta) :
    ∀ᶠ n : ℕ in atTop,∀d lam x E : ℝ,
      0<d → 0<lam → lam≤d^2 → x∈Ioc (0:ℝ) 1 →
      gamma*(n:ℝ)^(-(2:ℝ)/3+m)*d≤E → E≤d^2/Real.sqrt n →
      Real.sqrt n*E/d≤x →
      p*(n:ℝ)^(1+delta)*E^2≤laplaceComparisonStrength d lam x*x^2 →
      actualChildErrorBudget n delta c0 d lam x=
        (n:ℝ)^(-100*delta)*laplaceComparisonStrength d lam x*x^3 →
      ∀r∈Icc (0:ℝ) 1,r≤C*x →
        laplaceComparisonStrength d lam r≤eta^2*(actualChildCutoff n delta c0 d lam x)^2 ∧
        laplaceComparisonStrength d lam r*r≤C*eta^3*(actualChildCutoff n delta c0 d lam x)^3 := by
  have hg := actual_child_nonceiling_gap_eventually m delta c0 p gamma gamma hc0 hp hgamma hgamma
    hmargin (1/eta^3)
  filter_upwards [hg,eventually_gt_atTop (0:ℕ)] with n hn hnpos d lam x E hd hlam hld hx hlo hup hax hs hb
  have hnreal : 0<(n:ℝ) := by exact_mod_cast hnpos
  have hparent := comparison_parent_scale_lower_bounds hnreal hgamma hd hlo hup
  have hxlo := hparent.2.2.trans hax
  have hratio := hn d lam x E hlam hx.1 hparent.2.1 hxlo hs hb
  have hgap : laplaceComparisonStrength d lam x*x≤
      eta^3*(actualChildCutoff n delta c0 d lam x)^3 := by
    have hdiv : (laplaceComparisonStrength d lam x*x)/eta^3≤
        (actualChildCutoff n delta c0 d lam x)^3 := by
      simpa only [div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm,one_mul] using hratio
    have h := (div_le_iff₀ (pow_pos heta 3)).mp hdiv
    simpa only [mul_comm] using h
  have hc := actual_child_cutoff_pos_le_radius (delta:=delta) (d:=d) hnreal hc0 hlam hx.1
  have hcx : actualChildCutoff n delta c0 d lam x≤x := hc.2.trans
    (by dsimp [actualChildRadius];exact mul_le_of_le_one_left hx.1.le hc01)
  intro r hr hrC
  exact actual_child_clock_increments hd hlam hld hx hc.1 hcx heta.le heta1 hgap hC hr hrC

end OAI.SKFluctuations.LaplaceWindowFormalization
