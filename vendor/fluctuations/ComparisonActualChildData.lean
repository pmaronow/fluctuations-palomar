module

public import StrengthParameterCalculus

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 1600000

def actualChildRadius (c0 x : ℝ) : ℝ := c0*x

def actualChildErrorBudget (n : ℕ) (delta c0 d lam x : ℝ) : ℝ :=
  min ((actualChildRadius c0 x)^2/Real.sqrt n)
    ((n:ℝ)^(-100*delta)*laplaceComparisonStrength d lam x*x^3)

def actualChildCutoff (n : ℕ) (delta c0 d lam x : ℝ) : ℝ :=
  Real.sqrt n*actualChildErrorBudget n delta c0 d lam x/actualChildRadius c0 x

theorem actual_child_budget_pos {n : ℕ} (hn : 0<(n:ℝ))
    {delta c0 d lam x : ℝ} (hc0 : 0<c0) (hlam : 0<lam) (hx : 0<x) :
    0<actualChildErrorBudget n delta c0 d lam x := by
  unfold actualChildErrorBudget actualChildRadius
  apply lt_min
  · exact div_pos (sq_pos_of_pos (mul_pos hc0 hx)) (Real.sqrt_pos.mpr hn)
  · exact mul_pos (mul_pos (Real.rpow_pos_of_pos hn _) (laplaceComparisonStrength_pos d hlam x))
      (pow_pos hx _)

theorem actual_child_budget_ceiling (n : ℕ) (delta c0 d lam x : ℝ) :
    actualChildErrorBudget n delta c0 d lam x ≤ (actualChildRadius c0 x)^2/Real.sqrt n :=
  min_le_left _ _

theorem actual_child_cutoff_pos_le_radius {n : ℕ} (hn : 0<(n:ℝ))
    {delta c0 d lam x : ℝ} (hc0 : 0<c0) (hlam : 0<lam) (hx : 0<x) :
    0<actualChildCutoff n delta c0 d lam x ∧
      actualChildCutoff n delta c0 d lam x ≤ actualChildRadius c0 x := by
  have hd' : 0<actualChildRadius c0 x := mul_pos hc0 hx
  have hs : 0<Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr hn
  constructor
  · exact div_pos (mul_pos hs (actual_child_budget_pos hn hc0 hlam hx)) hd'
  · unfold actualChildCutoff
    apply (div_le_iff₀ hd').mpr
    have h := mul_le_mul_of_nonneg_left (actual_child_budget_ceiling n delta c0 d lam x) hs.le
    have he : Real.sqrt (n:ℝ)*((actualChildRadius c0 x)^2/Real.sqrt n)=
        actualChildRadius c0 x*actualChildRadius c0 x := by field_simp
    exact h.trans_eq he

theorem actual_child_parameter_range {n : ℕ} (hn : 0<(n:ℝ))
    {delta c0 d lam x lower : ℝ} (hc0 : 0<c0) (hlam : 0<lam) (hx : 0<x)
    (hceiling : lower*actualChildRadius c0 x ≤ (actualChildRadius c0 x)^2/Real.sqrt n)
    (hsource : lower*actualChildRadius c0 x ≤
      (n:ℝ)^(-100*delta)*laplaceComparisonStrength d lam x*x^3) :
    lower*actualChildRadius c0 x ≤ actualChildErrorBudget n delta c0 d lam x ∧
    actualChildErrorBudget n delta c0 d lam x ≤ (actualChildRadius c0 x)^2/Real.sqrt n ∧
    0<actualChildCutoff n delta c0 d lam x ∧
    actualChildCutoff n delta c0 d lam x ≤ actualChildRadius c0 x := by
  exact ⟨le_min hceiling hsource,actual_child_budget_ceiling n delta c0 d lam x,
    actual_child_cutoff_pos_le_radius hn hc0 hlam hx⟩

theorem actual_child_budget_growth {n : ℕ} {delta c0 d lam x g E : ℝ}
    (hceiling : g*E ≤ (actualChildRadius c0 x)^2/Real.sqrt n)
    (hsource : g*E ≤ (n:ℝ)^(-100*delta)*laplaceComparisonStrength d lam x*x^3) :
    g*E ≤ actualChildErrorBudget n delta c0 d lam x := le_min hceiling hsource

theorem actual_child_cutoff_inherits {n : ℕ} (hn : 0<(n:ℝ))
    {delta c0 d lam x a : ℝ} (hc0 : 0<c0) (hx : 0<x)
    (hceiling : a*actualChildRadius c0 x/Real.sqrt n ≤ (actualChildRadius c0 x)^2/Real.sqrt n)
    (hsource : a*actualChildRadius c0 x/Real.sqrt n ≤
      (n:ℝ)^(-100*delta)*laplaceComparisonStrength d lam x*x^3) :
    a ≤ actualChildCutoff n delta c0 d lam x := by
  have hd' : 0<actualChildRadius c0 x := mul_pos hc0 hx
  have hs : 0<Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr hn
  have hbudget := le_min hceiling hsource
  unfold actualChildCutoff
  apply (le_div_iff₀ hd').mpr
  have h := mul_le_mul_of_nonneg_left hbudget hs.le
  have he : Real.sqrt (n:ℝ)*(a*actualChildRadius c0 x/Real.sqrt n)=a*actualChildRadius c0 x := by
    field_simp
  exact he ▸ h

theorem actual_strength_ceiling_of_child_gap
    {d lam x a eta : ℝ} (hd : 0<d) (hlam : 0<lam) (hld : lam≤d^2)
    (hx : 0<x) (ha : 0<a) (hax : a≤x) (heta : 0≤eta) (heta1 : eta≤1)
    (hgap : laplaceComparisonStrength d lam x*x ≤ eta^3*a^3) :
    lam ≤ eta^2*a^2 := by
  have hlo := laplaceComparisonStrength_lower hd hlam hx
  rcases min_le_iff.mp hlo with hl|hl
  · have h1 : lam*a ≤ lam*x := mul_le_mul_of_nonneg_left hax hlam.le
    have h2 : lam*x ≤ laplaceComparisonStrength d lam x*x :=
      mul_le_mul_of_nonneg_right hl hx.le
    have he : eta^3≤eta^2 := by nlinarith [mul_nonneg (sq_nonneg eta) (sub_nonneg.mpr heta1)]
    have h3 : eta^3*a^3≤eta^2*a^3 := mul_le_mul_of_nonneg_right he (pow_nonneg ha.le _)
    have h4 : lam*a≤(eta^2*a^2)*a := by
      calc
        lam*a ≤ lam*x := h1
        _ ≤ laplaceComparisonStrength d lam x*x := h2
        _ ≤ eta^3*a^3 := hgap
        _ ≤ eta^2*a^3 := h3
        _ = (eta^2*a^2)*a := by ring
    exact le_of_mul_le_mul_right h4 ha
  · have h1 : d^3 ≤ laplaceComparisonStrength d lam x*x := (div_le_iff₀ hx).mp hl
    have h2 : d^3≤(eta*a)^3 := by nlinarith [hgap]
    have hda : d≤eta*a := (pow_le_pow_iff_left₀ hd.le (mul_nonneg heta ha.le) (by decide : (3:ℕ)≠0)).mp h2
    have hs := pow_le_pow_left₀ hd.le hda 2
    exact hld.trans (by simpa only [mul_pow] using hs)

theorem actual_radius_strength_le_outer
    {d lam x r C : ℝ} (hd : d≠0) (hlam : 0≤lam)
    (hx : x∈Icc (0:ℝ) 1) (hr : r∈Icc (0:ℝ) 1) (hC : 1≤C) (hrC : r≤C*x) :
    laplaceComparisonStrength d lam r*r ≤ C*(laplaceComparisonStrength d lam x*x) := by
  have hmono := laplaceComparisonStrength_monotonicities_nonneg hd hlam
  have he0 := laplaceComparisonStrength_nonneg d x hlam
  by_cases hrx : r≤x
  · exact (hmono.2 hr hx hrx).trans
      (by nlinarith [mul_nonneg he0 hx.1,mul_nonneg (sub_nonneg.mpr hC) (mul_nonneg he0 hx.1)])
  · have he := hmono.1 hx hr (le_of_not_ge hrx)
    calc
      laplaceComparisonStrength d lam r*r ≤ laplaceComparisonStrength d lam x*r :=
        mul_le_mul_of_nonneg_right he hr.1
      _ ≤ laplaceComparisonStrength d lam x*(C*x) := mul_le_mul_of_nonneg_left hrC he0
      _ = C*(laplaceComparisonStrength d lam x*x) := by ring

theorem actual_child_clock_increments
    {d lam x a eta C r : ℝ} (hd : 0<d) (hlam : 0<lam) (hld : lam≤d^2)
    (hx : x∈Ioc (0:ℝ) 1) (ha : 0<a) (hax : a≤x) (heta : 0≤eta) (heta1 : eta≤1)
    (hgap : laplaceComparisonStrength d lam x*x ≤ eta^3*a^3)
    (hC : 1≤C) (hr : r∈Icc (0:ℝ) 1) (hrC : r≤C*x) :
    laplaceComparisonStrength d lam r ≤ eta^2*a^2 ∧
    laplaceComparisonStrength d lam r*r ≤ C*eta^3*a^3 := by
  constructor
  · exact (laplaceComparisonStrength_le d hlam.le r).trans
      (actual_strength_ceiling_of_child_gap hd hlam hld hx.1 ha hax heta heta1 hgap)
  · exact (actual_radius_strength_le_outer hd.ne' hlam.le ⟨hx.1.le,hx.2⟩ hr hC hrC).trans
      (by have h:=mul_le_mul_of_nonneg_left hgap (by linarith : 0≤C);nlinarith [h])

theorem actual_child_bare_endpoint_inheritance
    {d lam x a eta C r y epsilon b h T : ℝ}
    (hd : 0<d) (hlam : 0<lam) (hld : lam≤d^2)
    (hx : x∈Ioc (0:ℝ) 1) (ha : 0<a) (hax : a≤x) (heta : 0≤eta) (heta1 : eta≤1)
    (hgap : laplaceComparisonStrength d lam x*x ≤ eta^3*a^3)
    (hC : 1≤C) (hr : r∈Icc (0:ℝ) 1) (hrC : r≤C*x) (hay : a≤y)
    (hb : |b-T|≤epsilon*y^2) (hh : |h|≤epsilon*y^3) :
    |(b-laplaceComparisonStrength d lam r)-T|≤(epsilon+eta^2)*y^2 ∧
    |h+laplaceComparisonStrength d lam r*r|≤(epsilon+C*eta^3)*y^3 := by
  have hs := actual_child_clock_increments hd hlam hld hx ha hax heta heta1 hgap hC hr hrC
  have he := laplaceComparisonStrength_nonneg d r hlam.le
  have hy : 0≤y := ha.le.trans hay
  have hs2 := pow_le_pow_left₀ ha.le hay 2
  have hs3 := pow_le_pow_left₀ ha.le hay 3
  constructor
  · have heBound : |laplaceComparisonStrength d lam r|≤eta^2*y^2 := by
      rw [abs_of_nonneg he]
      exact hs.1.trans (mul_le_mul_of_nonneg_left hs2 (sq_nonneg eta))
    have ht := (abs_sub (b-T) (laplaceComparisonStrength d lam r)).trans (add_le_add hb heBound)
    convert ht using 1 <;> ring
  · have heBound : |laplaceComparisonStrength d lam r*r|≤C*eta^3*y^3 := by
      rw [abs_of_nonneg (mul_nonneg he hr.1)]
      exact hs.2.trans (mul_le_mul_of_nonneg_left hs3 (by positivity))
    have ht := (abs_add_le h (laplaceComparisonStrength d lam r*r)).trans (add_le_add hh heBound)
    convert ht using 1 <;> ring

end OAI.SKFluctuations.LaplaceWindowFormalization
