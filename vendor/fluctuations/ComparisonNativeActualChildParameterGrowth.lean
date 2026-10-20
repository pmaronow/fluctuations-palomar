module

public import ComparisonRadiusSizeRates

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 9000000

theorem actual_child_ceiling_growth_of_weak_direct
    {N delta c0 E x e : ℝ} (hN : 0 < N) (hE : 0 < E)
    (hweak : e ≤ x^2) (hdirect : N^(1+delta)*E^2 ≤ e*x^2) :
    c0^2*N^(delta/2)*E ≤ (c0*x)^2/Real.sqrt N := by
  have hp : (N^((1+delta)/2))^2=N^(1+delta) := by
    rw [←Real.rpow_mul_natCast hN.le];congr 1;ring
  have hs : (N^((1+delta)/2)*E)^2 ≤ (x^2)^2 := by
    rw [mul_pow,hp]
    exact hdirect.trans (by nlinarith [mul_le_mul_of_nonneg_right hweak (sq_nonneg x)])
  have hx2 : N^((1+delta)/2)*E ≤ x^2 :=
    (sq_le_sq₀ (by positivity) (sq_nonneg x)).mp hs
  have hpow : N^((1+delta)/2)=N^(delta/2)*Real.sqrt N := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_add hN];congr 1;ring
  have hh:=mul_le_mul_of_nonneg_left hx2 (sq_nonneg c0)
  apply (le_div_iff₀ (Real.sqrt_pos.mpr hN)).mpr
  rw [hpow] at hh
  nlinarith

theorem eventually_actual_child_parameters_from_target
    {m delta gamma c0 : ℝ} (_hm : 0 < m) (hdelta : 0 < delta)
    (hgamma : 0 < gamma) (hc0 : 0 < c0) (hmargin : delta/4 < 3*m-99*delta) :
    ∀ᶠ n : ℕ in atTop,∀d lam E x : ℝ,
      0 < d → 0 < lam → lam ≤ d^2 → 0 < E → 0 < x →
      gamma*(n:ℝ)^(-(2:ℝ)/3+m)*d ≤ E → E ≤ d^2/Real.sqrt n →
      (n:ℝ)^delta*Real.sqrt n*E/Real.sqrt lam ≤ x →
      laplaceComparisonStrength d lam x ≤ x^2 →
      gamma*(n:ℝ)^(-(2:ℝ)/3+m)*actualChildRadius c0 x ≤
          actualChildErrorBudget n delta c0 d lam x ∧
      actualChildErrorBudget n delta c0 d lam x ≤ (actualChildRadius c0 x)^2/Real.sqrt n ∧
      (n:ℝ)^(delta/4)*E ≤ actualChildErrorBudget n delta c0 d lam x ∧
      Real.sqrt n*E/d ≤ actualChildCutoff n delta c0 d lam x ∧
      0 < actualChildCutoff n delta c0 d lam x ∧
      actualChildCutoff n delta c0 d lam x ≤ actualChildRadius c0 x := by
  have Hc:=eventually_coefficient_rpow_le (c:=1) (d:=c0^2) (q:=delta/4) (r:=delta/2)
    (by positivity) (by linarith)
  have Hs:=eventually_coefficient_rpow_le (c:=1) (d:=gamma^3) (q:=delta/4) (r:=3*m-99*delta)
    (by positivity) hmargin
  have Ha:=eventually_coefficient_rpow_le (c:=1) (d:=c0) (q:=0) (r:=delta) hc0 hdelta
  have Hb:=eventually_coefficient_rpow_le (c:=c0) (d:=gamma^3) (q:=0) (r:=3*m-99*delta)
    (by positivity) (by linarith)
  filter_upwards [Hc,Hs,Ha,Hb,eventually_ge_atTop (1:ℕ)] with n hnc hns hna hnb hn
  intro d lam E x hd hlam hld hE hx hlo hup hrange hweak
  have hN1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hN : 0 < (n:ℝ) := zero_lt_one.trans_le hN1
  have hsqrt : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr hN
  have hsL : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hrootd : Real.sqrt lam ≤ d := by simpa only [Real.sqrt_sq hd.le] using Real.sqrt_le_sqrt hld
  let parentA:=Real.sqrt (n:ℝ)*E/d
  let dc:=actualChildRadius c0 x
  let ec:=dc^2/Real.sqrt (n:ℝ)
  let es:=(n:ℝ)^(-100*delta)*laplaceComparisonStrength d lam x*x^3
  have hdc : 0 < dc := mul_pos hc0 hx
  have ha : 0 < parentA := div_pos (mul_pos hsqrt hE) hd
  have htarget : (n:ℝ)^delta*parentA ≤ x := by
    have hh:=div_le_div_of_nonneg_left (show 0 ≤ (n:ℝ)^delta*Real.sqrt n*E by positivity) hsL hrootd
    have he : (n:ℝ)^delta*parentA=(n:ℝ)^delta*Real.sqrt n*E/d := by dsimp [parentA];ring
    rw [he];exact hh.trans hrange
  have hax : parentA ≤ x := by
    have hpow:=Real.one_le_rpow hN1 hdelta.le
    have hh:=mul_le_mul_of_nonneg_right hpow ha.le
    nlinarith
  have hp:=comparison_parent_scale_lower_bounds hN hgamma hd hlo hup
  have hxlo : gamma*(n:ℝ)^(-(1:ℝ)/6+m) ≤ x := hp.2.2.trans hax
  have hdirect : (n:ℝ)^(1+delta)*E^2 ≤ laplaceComparisonStrength d lam x*x^2 := by
    have h:=comparison_radius_target_strength_size hN1 hdelta.le hd hlam hld hE hup hx
      (C:=1) le_rfl hx (by simp) hrange
    have he : (n:ℝ)^(1+delta)=(n:ℝ)^delta*(n:ℝ) := by
      calc
        _ = (n:ℝ)^(delta+1) := by congr 1;ring
        _ = _ := by rw [Real.rpow_add hN,Real.rpow_one]
    simpa only [div_one,he] using h
  have hceiling : c0^2*(n:ℝ)^(delta/2)*E ≤ ec :=
    actual_child_ceiling_growth_of_weak_direct hN hE hweak hdirect
  have hcg : (n:ℝ)^(delta/4)*E ≤ ec := by
    have hh:=mul_le_mul_of_nonneg_right hnc hE.le
    simp only [one_mul] at hh
    exact hh.trans hceiling
  have hbase : (n:ℝ)^(1-99*delta)*E^2*x ≤ es := by
    have hh:=mul_le_mul_of_nonneg_left hdirect (show 0 ≤ (n:ℝ)^(-100*delta)*x by positivity)
    have he : (n:ℝ)^(-100*delta)*(n:ℝ)^(1+delta)=(n:ℝ)^(1-99*delta) := by
      rw [←Real.rpow_add hN];congr 1;ring
    calc
      _ = ((n:ℝ)^(-100*delta)*x)*((n:ℝ)^(1+delta)*E^2) := by rw [←he];ring
      _ ≤ _ := hh
      _ = es := by dsimp [es];ring
  have hlowprod (z : ℝ) (hz : gamma*(n:ℝ)^(-(1:ℝ)/6+m) ≤ z) :
      gamma^3*(n:ℝ)^(-1+3*m) ≤ E*z := by
    have hh:=mul_le_mul hp.2.1 hz (by positivity) hE.le
    have he : (gamma^2*(n:ℝ)^(-(5:ℝ)/6+2*m))*(gamma*(n:ℝ)^(-(1:ℝ)/6+m))=
        gamma^3*(n:ℝ)^(-1+3*m) := by
      calc
        _ = gamma^3*((n:ℝ)^(-(5:ℝ)/6+2*m)*(n:ℝ)^(-(1:ℝ)/6+m)) := by ring
        _ = _ := by rw [←Real.rpow_add hN];congr 1;congr 1;ring
    rwa [he] at hh
  have hcombined : (n:ℝ)^(1-99*delta)*(gamma^3*(n:ℝ)^(-1+3*m))=
      gamma^3*(n:ℝ)^(3*m-99*delta) := by
    calc
      _ = gamma^3*((n:ℝ)^(1-99*delta)*(n:ℝ)^(-1+3*m)) := by ring
      _ = _ := by rw [←Real.rpow_add hN];congr 1;congr 1;ring
  have hsg : (n:ℝ)^(delta/4)*E ≤ es := by
    have hh:=mul_le_mul_of_nonneg_left (hlowprod x hxlo)
      (show 0 ≤ (n:ℝ)^(1-99*delta)*E by positivity)
    have hlow : gamma^3*(n:ℝ)^(3*m-99*delta)*E ≤ (n:ℝ)^(1-99*delta)*E^2*x := by
      calc
        _ = ((n:ℝ)^(1-99*delta)*(gamma^3*(n:ℝ)^(-1+3*m)))*E := by rw [hcombined]
        _ ≤ _ := by nlinarith [hh]
    have hsave:=mul_le_mul_of_nonneg_right hns hE.le
    simp only [one_mul] at hsave
    exact hsave.trans (hlow.trans hbase)
  have hdcA : parentA ≤ dc := by
    simp only [Real.rpow_zero,mul_one] at hna
    have h1:=mul_le_mul_of_nonneg_right hna ha.le
    have h2:=mul_le_mul_of_nonneg_left htarget hc0.le
    change parentA ≤ c0*x
    nlinarith
  have hcp : (dc/d)*E ≤ ec := by
    have hh:=mul_le_mul_of_nonneg_left hdcA hdc.le
    apply (le_div_iff₀ hsqrt).mpr
    dsimp [parentA] at hh
    convert hh using 1 <;> ring
  have hsp : (dc/d)*E ≤ es := by
    have hh:=mul_le_mul_of_nonneg_left (hlowprod d hp.1)
      (show 0 ≤ (n:ℝ)^(1-99*delta) by positivity)
    rw [hcombined] at hh
    simp only [Real.rpow_zero,mul_one] at hnb
    have hc : c0 ≤ (n:ℝ)^(1-99*delta)*(E*d) := hnb.trans hh
    have hj:=mul_le_mul_of_nonneg_right hc (show 0 ≤ E*x/d by positivity)
    have hl : c0*(E*x/d)=(dc/d)*E := by dsimp [dc,actualChildRadius];ring
    have hr : ((n:ℝ)^(1-99*delta)*(E*d))*(E*x/d)=(n:ℝ)^(1-99*delta)*E^2*x := by field_simp
    rw [hl,hr] at hj
    exact hj.trans hbase
  have hbudgetP : (dc/d)*E ≤ actualChildErrorBudget n delta c0 d lam x := le_min hcp hsp
  have hchildlo : gamma*(n:ℝ)^(-(2:ℝ)/3+m)*dc ≤ actualChildErrorBudget n delta c0 d lam x := by
    have hh:=mul_le_mul_of_nonneg_left hlo (show 0 ≤ dc/d by positivity)
    have he : (dc/d)*(gamma*(n:ℝ)^(-(2:ℝ)/3+m)*d)=gamma*(n:ℝ)^(-(2:ℝ)/3+m)*dc := by field_simp
    rw [he] at hh
    exact hh.trans hbudgetP
  have hcut : parentA ≤ actualChildCutoff n delta c0 d lam x := by
    apply actual_child_cutoff_inherits hN hc0 hx
    · convert hcp using 1; dsimp [parentA,dc,ec]; field_simp
    · convert hsp using 1; dsimp [parentA,dc,es]; field_simp
  exact ⟨hchildlo,actual_child_budget_ceiling n delta c0 d lam x,le_min hcg hsg,
    hcut,actual_child_cutoff_pos_le_radius hN hc0 hlam hx⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
