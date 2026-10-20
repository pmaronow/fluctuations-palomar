module

public import ComparisonActualChildMargins
public import ConcreteComparisonStrength

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter Hierarchy
open scoped Topology
set_option maxHeartbeats 2500000

theorem comparison_radius_floor_lower
    {N delta U C x r : ℝ} (hN : 0 < N) (hU : 0 < U)
    (_hC : 0 ≤ C) (_hx : 0 < x) (hr : 0 ≤ r) (hrx : r ≤ C*x)
    (hshift : N^(2*delta)*U ≤ x) :
    N^delta*U^2/((C+1)^2*x^2) ≤ comparisonFloor N delta U r := by
  unfold comparisonFloor
  have hden : 0 < r+N^(2*delta)*U := by positivity
  have hbound : r+N^(2*delta)*U ≤ (C+1)*x := by nlinarith
  have hs := pow_le_pow_left₀ hden.le hbound 2
  have he : ((C+1)*x)^2=(C+1)^2*x^2 := by ring
  rw [he] at hs
  exact div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hden) hs

theorem comparison_radius_variance_budget_normalized
    {N delta E g x C tau ca Cs p D A : ℝ}
    (hN : 0 < N) (hE : 0 < E) (hg : 0 < g) (hx : 0 < x)
    (hC : 0 ≤ C) (htau : 0 < tau) (hca : 0 < ca) (hCs : 0 ≤ Cs)
    (hp : 0 < p) (hlog : 0 ≤ Real.log N) (_hD : 0 ≤ D) (hDx : D ≤ Cs*x)
    (hA : ca*x ≤ A) (hshift : N^(2*delta)*comparisonSmallMass N E ≤ x)
    (hsize : p*N*E^2 ≤ g*x^2) :
    (4*D/(A*(tau*x)^2*comparisonFloor N delta (comparisonSmallMass N E) (C*x)*
      (N*(((1/3)/Real.log N)*g))))/x^2 ≤
      (12*Cs*(C+1)^2/(ca*tau^2*p))*Real.log N/N^delta := by
  by_cases hl : Real.log N=0
  · simp only [hl,div_zero,zero_mul,mul_zero,zero_div,le_refl]
  have hlogp : 0 < Real.log N := lt_of_le_of_ne hlog (Ne.symm hl)
  have hU : 0 < comparisonSmallMass N E := by unfold comparisonSmallMass; positivity
  have hfloor := comparison_radius_floor_lower hN hU hC hx
    (mul_nonneg hC hx.le) le_rfl hshift
  have hAp : 0 < A := (mul_pos hca hx).trans_le hA
  have hk : 0 < comparisonFloor N delta (comparisonSmallMass N E) (C*x) :=
    comparisonFloor_pos hN hU (mul_nonneg hC hx.le)
  have hF : 0 < N*(((1/3)/Real.log N)*g) := by positivity
  have hden := mul_le_mul hA hfloor (by positivity : 0 ≤
    N^delta*(comparisonSmallMass N E)^2/((C+1)^2*x^2)) hAp.le
  have hbound := mul_le_mul_of_nonneg_right hden
    (by positivity : 0 ≤ (tau*x)^2*(N*(((1/3)/Real.log N)*g))*x^2)
  have hcancel : ((ca*x)*(N^delta*(comparisonSmallMass N E)^2/((C+1)^2*x^2)))*
      ((tau*x)^2*(N*(((1/3)/Real.log N)*g))*x^2)=
      ca*tau^2*N^delta*g*x^3/(3*Real.log N*N*E^2*(C+1)^2) := by
    unfold comparisonSmallMass
    field_simp
  rw [hcancel] at hbound
  have hnum : 4*D ≤ 4*Cs*x := by linarith
  apply (div_le_iff₀ (sq_pos_of_pos hx)).mpr
  apply (div_le_iff₀ (by positivity : 0 <
    A*(tau*x)^2*comparisonFloor N delta (comparisonSmallMass N E) (C*x)*
      (N*(((1/3)/Real.log N)*g)))).mpr
  have hscaled := mul_le_mul_of_nonneg_left hbound (by positivity : 0 ≤
    (12*Cs*(C+1)^2/(ca*tau^2*p))*Real.log N/N^delta)
  have he : ((12*Cs*(C+1)^2/(ca*tau^2*p))*Real.log N/N^delta)*
      (ca*tau^2*N^delta*g*x^3/(3*Real.log N*N*E^2*(C+1)^2))=
      4*Cs*x*(g*x^2/(p*N*E^2)) := by
    field_simp
    ring
  rw [he] at hscaled
  have hsize1 : 1 ≤ g*x^2/(p*N*E^2) := (le_div_iff₀ (by positivity)).mpr (by simpa using hsize)
  have hc := mul_le_mul_of_nonneg_left hsize1 (by positivity : 0 ≤ 4*Cs*x)
  have he2 : ((12*Cs*(C+1)^2/(ca*tau^2*p))*Real.log N/N^delta)*
      (A*comparisonFloor N delta (comparisonSmallMass N E) (C*x)*
        ((tau*x)^2*(N*(((1/3)/Real.log N)*g))*x^2))=
      (((12*Cs*(C+1)^2/(ca*tau^2*p))*Real.log N/N^delta)*x^2)*
        (A*(tau*x)^2*comparisonFloor N delta (comparisonSmallMass N E) (C*x)*
          (N*(((1/3)/Real.log N)*g))) := by ring
  have hc1 : 4*Cs*x ≤ 4*Cs*x*(g*x^2/(p*N*E^2)) := by simpa only [mul_one] using hc
  exact hnum.trans (hc1.trans (he2 ▸ hscaled))

theorem comparison_radius_covariance_budget_normalized
    {N E g x ca Cs p D A : ℝ} (hN : 0 < N) (hE : 0 < E)
    (hg : 0 < g) (hx : 0 < x) (hca : 0 < ca) (hCs : 0 ≤ Cs)
    (hp : 0 < p) (hlog : 0 ≤ Real.log N) (_hD : 0 ≤ D) (hDx : D ≤ Cs*x)
    (hA : ca*x ≤ A) (hsize : p*N*E^2 ≤ g*x^2) :
    (8*D/(A^2*(N*(((1/3)/Real.log N)*g))))/x^3 ≤
      (24*Cs/(ca^2*p))*Real.log N*(comparisonSmallMass N E/x)^2 := by
  by_cases hl : Real.log N=0
  · simp only [hl,div_zero,zero_mul,mul_zero,zero_div,le_refl]
  have hlogp : 0 < Real.log N := lt_of_le_of_ne hlog (Ne.symm hl)
  have hAp : 0 < A := (mul_pos hca hx).trans_le hA
  have hF : 0 < N*(((1/3)/Real.log N)*g) := by positivity
  have hA2 := pow_le_pow_left₀ (mul_pos hca hx).le hA 2
  have hden := mul_le_mul_of_nonneg_right hA2
    (by positivity : 0 ≤ (N*(((1/3)/Real.log N)*g))*x^3)
  have hscaled := mul_le_mul_of_nonneg_left hden
    (by unfold comparisonSmallMass; positivity : 0 ≤
      (24*Cs/(ca^2*p))*Real.log N*(comparisonSmallMass N E/x)^2)
  have he : ((24*Cs/(ca^2*p))*Real.log N*(comparisonSmallMass N E/x)^2)*
      ((ca*x)^2*((N*(((1/3)/Real.log N)*g))*x^3))=
      8*Cs*x*(g*x^2/(p*N*E^2)) := by
    unfold comparisonSmallMass
    field_simp
    ring
  rw [he] at hscaled
  have hsize1 : 1 ≤ g*x^2/(p*N*E^2) := (le_div_iff₀ (by positivity)).mpr (by simpa using hsize)
  have hc := mul_le_mul_of_nonneg_left hsize1 (by positivity : 0 ≤ 8*Cs*x)
  apply (div_le_iff₀ (pow_pos hx 3)).mpr
  apply (div_le_iff₀ (by positivity : 0 < A^2*(N*(((1/3)/Real.log N)*g)))).mpr
  have he2 : ((24*Cs/(ca^2*p))*Real.log N*(comparisonSmallMass N E/x)^2)*
      (A^2*((N*(((1/3)/Real.log N)*g))*x^3))=
      (((24*Cs/(ca^2*p))*Real.log N*(comparisonSmallMass N E/x)^2)*x^3)*
        (A^2*(N*(((1/3)/Real.log N)*g))) := by ring
  have hnum : 8*D ≤ 8*Cs*x := by linarith
  have hc1 : 8*Cs*x ≤ 8*Cs*x*(g*x^2/(p*N*E^2)) := by simpa only [mul_one] using hc
  exact hnum.trans (hc1.trans (he2 ▸ hscaled))

theorem comparison_radius_small_mass_ratio
    {n : ℕ} (hn : 0 < (n:ℝ)) {m gamma d E x : ℝ}
    (hgamma : 0 < gamma) (hd : 0 < d)
    (hlower : gamma*(n:ℝ)^(-(2:ℝ)/3+m)*d ≤ E)
    (hupper : E ≤ d^2/Real.sqrt n)
    (hax : Real.sqrt n*E/d ≤ x) :
    comparisonSmallMass n E/x ≤ (1/gamma^3)*(n:ℝ)^(-3*m) := by
  have hparent := comparison_parent_scale_lower_bounds hn hgamma hd hlower hupper
  have hE : 0 < E := (by positivity : 0 < gamma^2*(n:ℝ)^(-(5:ℝ)/6+2*m)).trans_le hparent.2.1
  have hxlo := hparent.2.2.trans hax
  have hx : 0 < x := (by positivity : 0 < gamma*(n:ℝ)^(-(1:ℝ)/6+m)).trans_le hxlo
  have hp := mul_le_mul hxlo hparent.2.1 (by positivity) hx.le
  have hpN := mul_le_mul_of_nonneg_right hp hn.le
  have he : (gamma*(n:ℝ)^(-(1:ℝ)/6+m))*(gamma^2*(n:ℝ)^(-(5:ℝ)/6+2*m))*(n:ℝ)=
      gamma^3*(n:ℝ)^(3*m) := by
    nth_rw 3 [←Real.rpow_one (n:ℝ)]
    calc
      _ = gamma^3*((n:ℝ)^(-(1:ℝ)/6+m)*(n:ℝ)^(-(5:ℝ)/6+2*m)*(n:ℝ)^(1:ℝ)) := by ring
      _ = _ := by
        rw [←Real.rpow_add hn,←Real.rpow_add hn]
        congr 1
        congr 1
        ring
  rw [he] at hpN
  have hi : 1/(x*E*(n:ℝ)) ≤ 1/(gamma^3*(n:ℝ)^(3*m)) :=
    one_div_le_one_div_of_le (by positivity) hpN
  have heinv : 1/(gamma^3*(n:ℝ)^(3*m))=(1/gamma^3)*(n:ℝ)^(-3*m) := by
    rw [show -3*m=-(3*m) by ring,Real.rpow_neg hn.le]
    field_simp
  rw [heinv] at hi
  simpa only [comparisonSmallMass,div_div,mul_comm,mul_left_comm,mul_assoc] using hi

theorem comparison_radius_target_strength_size
    {N delta d lam E x z C : ℝ} (hN : 1 ≤ N) (hdelta : 0 ≤ delta)
    (hd : 0 < d) (hlam : 0 < lam) (hld : lam ≤ d^2) (hE : 0 < E)
    (hupper : E ≤ d^2/Real.sqrt N) (hx : 0 < x)
    (hC : 1 ≤ C) (hz : 0 < z) (hzx : z ≤ C*x)
    (hrange : N^delta*Real.sqrt N*E/Real.sqrt lam ≤ x) :
    (N^delta/C)*N*E^2 ≤ laplaceComparisonStrength d lam z*x^2 := by
  have hNp : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hCp : 0 < C := lt_of_lt_of_le (by norm_num) hC
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNp
  have hsL : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hq : 1 ≤ N^delta := Real.one_le_rpow hN hdelta
  have htarget := (div_le_iff₀ hsL).mp hrange
  have htarget2 := pow_le_pow_left₀ (by positivity : 0 ≤ N^delta*Real.sqrt N*E) htarget 2
  have hrootN := Real.sq_sqrt hNp.le
  have hrootL := Real.sq_sqrt hlam.le
  have htarget2' : (N^delta)^2*N*E^2 ≤ lam*x^2 := by
    simpa only [mul_pow,hrootN,hrootL,mul_assoc,mul_comm,mul_left_comm] using htarget2
  have hlamSize : (N^delta/C)*N*E^2 ≤ lam*x^2 := by
    have hqC : N^delta/C ≤ (N^delta)^2 := by
      apply (div_le_iff₀ hCp).mpr
      nlinarith [mul_nonneg (by positivity : 0 ≤ (N^delta)^2) (sub_nonneg.mpr hC)]
    have hh := mul_le_mul_of_nonneg_right hqC (by positivity : 0 ≤ N*E^2)
    have hh1 : (N^delta/C)*N*E^2 ≤ (N^delta)^2*N*E^2 := by simpa only [mul_assoc] using hh
    exact hh1.trans htarget2'
  have hrootd : Real.sqrt lam ≤ d := by
    have hs := Real.sqrt_le_sqrt hld
    simpa only [Real.sqrt_sq hd.le] using hs
  have hEroot : Real.sqrt N*E ≤ d^2 := by
    have hh := (le_div_iff₀ hsN).mp hupper
    simpa only [mul_comm] using hh
  have hprod : Real.sqrt lam*(Real.sqrt N*E) ≤ d^3 := by
    have hh := mul_le_mul hrootd hEroot (mul_pos hsN hE).le hd.le
    simpa only [pow_succ,mul_comm] using hh
  have hfield : N^delta*N*E^2 ≤ d^3*x := by
    have h1 := mul_le_mul_of_nonneg_left htarget (mul_pos hsN hE).le
    have h2 := mul_le_mul_of_nonneg_right hprod hx.le
    have he : (Real.sqrt N*E)*(N^delta*Real.sqrt N*E)=N^delta*N*E^2 := by
      calc
        _ = N^delta*(Real.sqrt N)^2*E^2 := by ring
        _ = _ := by rw [hrootN]
    rw [he] at h1
    exact h1.trans (by simpa only [mul_assoc,mul_left_comm,mul_comm] using h2)
  have hfieldSize : (N^delta/C)*N*E^2 ≤ (d^3/z)*x^2 := by
    rw [show (d^3/z)*x^2=(d^3*x^2)/z by ring]
    apply (le_div_iff₀ hz).mpr
    have h1 := mul_le_mul_of_nonneg_left hzx (by positivity : 0 ≤ (N^delta/C)*N*E^2)
    have h2 := mul_le_mul_of_nonneg_right hfield hx.le
    have he : ((N^delta/C)*N*E^2)*(C*x)=(N^delta*N*E^2)*x := by
      field_simp [hCp.ne']
    have h3 : ((N^delta/C)*N*E^2)*z ≤ d^3*x^2 := by rw [he] at h1; nlinarith [h1,h2]
    simpa only [div_mul_eq_mul_div] using h3
  have hlo := mul_le_mul_of_nonneg_right (laplaceComparisonStrength_lower hd hlam hz) (sq_nonneg x)
  rw [min_mul_of_nonneg _ _ (sq_nonneg x)] at hlo
  exact (le_min hlamSize hfieldSize).trans hlo

theorem comparison_radius_log_power_tendsto {q : ℝ} (hq : 0 < q) :
    Tendsto (fun n : ℕ => Real.log (n:ℝ)/(n:ℝ)^q) atTop (𝓝 0) :=
  (isLittleO_log_rpow_atTop hq).tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop

theorem comparison_radius_physical_count_budget_le
    {N P g B : ℝ} (hN : 0 < N) (hP : N ≤ P) (hg : 0 < g)
    (hlog : 0 < Real.log N) (hB : 0 ≤ B) :
    B/(P*(((1/3)/Real.log N)*g)) ≤ B/(N*(((1/3)/Real.log N)*g)) := by
  have hfactor : 0 < ((1/3)/Real.log N)*g := by positivity
  exact div_le_div_of_nonneg_left hB (mul_pos hN hfactor)
    (mul_le_mul_of_nonneg_right hP hfactor.le)

theorem comparison_radius_floor_shift_eventually
    {m delta gamma : ℝ} (hgamma : 0 < gamma) (hmargin : 2*delta < 3*m) :
    ∀ᶠ n : ℕ in atTop, ∀ d E x : ℝ, 0 < d →
      gamma*(n:ℝ)^(-(2:ℝ)/3+m)*d ≤ E → E ≤ d^2/Real.sqrt n →
      Real.sqrt n*E/d ≤ x →
      (n:ℝ)^(2*delta)*comparisonSmallMass n E ≤ x := by
  have hsmall := eventually_coefficient_rpow_le
    (c:=1/gamma^3) (d:=1) (q:=2*delta-3*m) (r:=0) (by norm_num) (by linarith)
  filter_upwards [hsmall,eventually_gt_atTop (0:ℕ)] with n hn hnpos d E x hd hlo hup hax
  have hnreal : 0 < (n:ℝ) := by exact_mod_cast hnpos
  have hparent := comparison_parent_scale_lower_bounds hnreal hgamma hd hlo hup
  have hxlo := hparent.2.2.trans hax
  have hx : 0 < x := (by positivity : 0 < gamma*(n:ℝ)^(-(1:ℝ)/6+m)).trans_le hxlo
  have hr := comparison_radius_small_mass_ratio hnreal hgamma hd hlo hup hax
  have hmul := mul_le_mul_of_nonneg_left hr
    (Real.rpow_pos_of_pos hnreal (2*delta)).le
  have he : (n:ℝ)^(2*delta)*((1/gamma^3)*(n:ℝ)^(-3*m))=
      (1/gamma^3)*(n:ℝ)^(2*delta-3*m) := by
    rw [mul_left_comm,←Real.rpow_add hnreal]
    congr 1
    congr 1
    ring
  rw [he] at hmul
  have hratio : ((n:ℝ)^(2*delta)*comparisonSmallMass n E)/x ≤ 1 := by
    have hh := hmul.trans (by simpa only [Real.rpow_zero,mul_one] using hn)
    simpa only [mul_div_assoc] using hh
  exact (div_le_iff₀ hx).mp hratio |>.trans_eq (one_mul x)

theorem comparison_radius_ratio_log_power_bound
    {N m gamma U x B : ℝ} (hN : 0 < N) (hgamma : 0 < gamma)
    (hB : 0 ≤ B) (hlog : 0 ≤ Real.log N) (hU : 0 ≤ U/x)
    (hratio : U/x ≤ (1/gamma^3)*N^(-3*m)) :
    B*Real.log N*(U/x)^2 ≤ (B/gamma^6)*Real.log N/N^(6*m) := by
  have hs := pow_le_pow_left₀ hU hratio 2
  have hh := mul_le_mul_of_nonneg_left hs (mul_nonneg hB hlog)
  have he : B*Real.log N*((1/gamma^3)*N^(-3*m))^2=
      (B/gamma^6)*Real.log N/N^(6*m) := by
    rw [mul_pow,←Real.rpow_mul_natCast hN.le]
    simp only [Nat.cast_ofNat]
    have hpow : (-3*m)*(2:ℝ)=-(6*m) := by ring
    rw [hpow,Real.rpow_neg hN.le]
    field_simp
  exact hh.trans_eq he

theorem comparison_radius_target_above_lower_scale
    {N delta d lam E x : ℝ} (hN : 1 ≤ N) (hdelta : 0 ≤ delta)
    (hd : 0 < d) (hlam : 0 < lam) (hld : lam ≤ d^2)
    (hE : 0 < E) (hx : 0 < x)
    (hrange : N^delta*Real.sqrt N*E/Real.sqrt lam ≤ x) :
    Real.sqrt N*E/d ≤ x := by
  have hNp : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hq : 1 ≤ N^delta := Real.one_le_rpow hN hdelta
  have hrootd : Real.sqrt lam ≤ d := by
    simpa only [Real.sqrt_sq hd.le] using Real.sqrt_le_sqrt hld
  have ht := (div_le_iff₀ (Real.sqrt_pos.mpr hlam)).mp hrange
  have hqmul := mul_le_mul_of_nonneg_right hq
    (mul_pos (Real.sqrt_pos.mpr hNp) hE).le
  have hdx := mul_le_mul_of_nonneg_right hrootd hx.le
  apply (div_le_iff₀ hd).mpr
  have hfirst : Real.sqrt N*E ≤ N^delta*Real.sqrt N*E := by
    simpa only [one_mul,mul_assoc] using hqmul
  exact hfirst.trans (ht.trans (by simpa only [mul_comm] using hdx))

theorem comparison_radius_actual_target_budgets_eventually
    {m delta gamma C tau ca Cs : ℝ}
    (hgamma : 0 < gamma) (hdelta : 0 ≤ delta) (hmargin : 2*delta < 3*m)
    (hC : 1 ≤ C) (htau : 0 < tau) (hca : 0 < ca) (hCs : 0 ≤ Cs) :
    ∀ᶠ n : ℕ in atTop, ∀ d lam E x z D A : ℝ,
      0 < d → 0 < lam → lam ≤ d^2 → 0 < E →
      gamma*(n:ℝ)^(-(2:ℝ)/3+m)*d ≤ E → E ≤ d^2/Real.sqrt n →
      0 < x → 0 < z → z ≤ C*x →
      (n:ℝ)^delta*Real.sqrt n*E/Real.sqrt lam ≤ x →
      0 ≤ Real.log (n:ℝ) → 0 ≤ D → D ≤ Cs*x → ca*x ≤ A →
      ((4*D/(A*(tau*x)^2*comparisonFloor n delta (comparisonSmallMass n E) (C*x)*
        ((n+1:ℝ)*(((1/3)/Real.log n)*laplaceComparisonStrength d lam z))))/x^2 ≤
        (12*Cs*C*(C+1)^2/(ca*tau^2))*Real.log n/(n:ℝ)^delta) ∧
      ((8*D/(A^2*((n+1:ℝ)*(((1/3)/Real.log n)*laplaceComparisonStrength d lam z))))/x^3 ≤
        (24*Cs*C/(ca^2*gamma^6))*Real.log n/(n:ℝ)^(6*m)) := by
  have hshift := comparison_radius_floor_shift_eventually hgamma hmargin
  filter_upwards [hshift,eventually_ge_atTop (1:ℕ)] with n hnshift hn1
    d lam E x z D A hd hlam hld hE hlo hup hx hz hzx hrange hlog hD hDx hA
  have hN : 1 ≤ (n:ℝ) := by exact_mod_cast hn1
  have hNp : 0 < (n:ℝ) := lt_of_lt_of_le (by norm_num) hN
  have hCp : 0 < C := lt_of_lt_of_le (by norm_num) hC
  have hp : 0 < 1/C := one_div_pos.mpr hCp
  have hax := comparison_radius_target_above_lower_scale hN hdelta hd hlam hld hE hx hrange
  have hshiftNow := hnshift d E x hd hlo hup hax
  have hg := laplaceComparisonStrength_pos d hlam z
  have hstrength := comparison_radius_target_strength_size hN hdelta hd hlam hld hE hup hx hC hz hzx hrange
  have hq : 1 ≤ (n:ℝ)^delta := Real.one_le_rpow hN hdelta
  have hsize : (1/C)*(n:ℝ)*E^2 ≤ laplaceComparisonStrength d lam z*x^2 := by
    have hh := mul_le_mul_of_nonneg_right hq (by positivity : 0 ≤ 1/C)
    have hh1 : 1/C ≤ (n:ℝ)^delta/C := by simpa only [one_mul,div_eq_mul_inv] using hh
    have hh2 := mul_le_mul_of_nonneg_right hh1 (by positivity : 0 ≤ (n:ℝ)*E^2)
    have hh3 : (1/C)*(n:ℝ)*E^2 ≤ ((n:ℝ)^delta/C)*(n:ℝ)*E^2 := by simpa only [mul_assoc] using hh2
    exact hh3.trans hstrength
  have hv := comparison_radius_variance_budget_normalized hNp hE hg hx
    (le_of_lt hCp) htau hca hCs hp hlog hD hDx hA hshiftNow hsize
  have ht := comparison_radius_covariance_budget_normalized hNp hE hg hx hca hCs hp hlog hD hDx hA hsize
  have hr := comparison_radius_small_mass_ratio hNp hgamma hd hlo hup hax
  have hUratio : 0 ≤ comparisonSmallMass n E/x := by unfold comparisonSmallMass; positivity
  have htpow := comparison_radius_ratio_log_power_bound hNp hgamma
    (by positivity : 0 ≤ 24*Cs/(ca^2*(1/C))) hlog hUratio hr
  have hVcoef : 12*Cs*(C+1)^2/(ca*tau^2*(1/C))=12*Cs*C*(C+1)^2/(ca*tau^2) := by field_simp
  have hTcoef : (24*Cs/(ca^2*(1/C)))/gamma^6=24*Cs*C/(ca^2*gamma^6) := by field_simp
  rw [hVcoef] at hv
  rw [hTcoef] at htpow
  have htfinal := ht.trans htpow
  by_cases hl : Real.log (n:ℝ)=0
  · simpa only [hl,div_zero,zero_mul,mul_zero,zero_div] using And.intro hv htfinal
  have hlogp : 0 < Real.log (n:ℝ) := lt_of_le_of_ne hlog (Ne.symm hl)
  have hAp : 0 < A := (mul_pos hca hx).trans_le hA
  have hU : 0 < comparisonSmallMass n E := by unfold comparisonSmallMass; positivity
  have hk : 0 < comparisonFloor n delta (comparisonSmallMass n E) (C*x) :=
    comparisonFloor_pos hNp hU (mul_pos hCp hx).le
  have hcount : (n:ℝ) ≤ (n+1:ℝ) := by norm_num
  have hvarCount := comparison_radius_physical_count_budget_le hNp hcount hg hlogp
    (by positivity : 0 ≤ 4*D/(A*(tau*x)^2*comparisonFloor n delta (comparisonSmallMass n E) (C*x)))
  have hcovCount := comparison_radius_physical_count_budget_le hNp hcount hg hlogp
    (by positivity : 0 ≤ 8*D/A^2)
  have hvarNorm := div_le_div_of_nonneg_right hvarCount (sq_nonneg x)
  have hcovNorm := div_le_div_of_nonneg_right hcovCount (pow_nonneg hx.le 3)
  constructor
  · have hh : (4*D/(A*(tau*x)^2*comparisonFloor n delta (comparisonSmallMass n E) (C*x)*
        ((n+1:ℝ)*(((1/3)/Real.log n)*laplaceComparisonStrength d lam z))))/x^2 ≤
      (4*D/(A*(tau*x)^2*comparisonFloor n delta (comparisonSmallMass n E) (C*x)*
        ((n:ℝ)*(((1/3)/Real.log n)*laplaceComparisonStrength d lam z))))/x^2 := by
      simpa only [div_div] using hvarNorm
    exact hh.trans hv
  · have hh : (8*D/(A^2*((n+1:ℝ)*(((1/3)/Real.log n)*laplaceComparisonStrength d lam z))))/x^3 ≤
      (8*D/(A^2*((n:ℝ)*(((1/3)/Real.log n)*laplaceComparisonStrength d lam z))))/x^3 := by
      simpa only [div_div] using hcovNorm
    exact hh.trans htfinal

theorem comparison_radius_height_strip_choices {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ k : ℕ, 0 < k ∧ ∃ tau : ℝ, 0 < tau ∧
      1/(k:ℝ)^2+(k:ℝ)*tau < epsilon := by
  obtain ⟨k,hk⟩ := exists_nat_gt (max 1 (2/epsilon))
  have hkp : 0 < (k:ℝ) := (by norm_num : (0:ℝ) < 1).trans (lt_of_le_of_lt (le_max_left _ _) hk)
  have hk1 : 1 < (k:ℝ) := lt_of_le_of_lt (le_max_left _ _) hk
  have hkE : 2/epsilon < (k:ℝ) := lt_of_le_of_lt (le_max_right _ _) hk
  have hsmall : 1/(k:ℝ)^2 < epsilon/2 := by
    have hke := (div_lt_iff₀ he).mp hkE
    apply (div_lt_iff₀ (sq_pos_of_pos hkp)).mpr
    nlinarith [mul_pos he (show 0 < (k:ℝ)^2-(k:ℝ) by nlinarith)]
  refine ⟨k,by exact_mod_cast hkp,epsilon/(4*(k:ℝ)),by positivity,?_⟩
  have hc : (k:ℝ)*(epsilon/(4*(k:ℝ)))=epsilon/4 := by field_simp
  rw [hc]
  linarith

end OAI.SKFluctuations.LaplaceWindowFormalization
