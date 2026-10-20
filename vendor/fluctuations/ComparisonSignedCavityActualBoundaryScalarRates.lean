module

public import ComparisonSignedCavityGroupedBoundaryRates
public import CavityExteriorResamplingClock

@[expose] public section

noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy

theorem savedExteriorScale_lower_of_bounded_clock {r W v B : ℝ}
    (hr : 0<r) (hW : 0<W) (hv : 0<v) (_hB : 0<B)
    (hWB : W≤B) (hv1 : v≤1) :
    r^3/Real.sqrt (B^3) ≤ savedExteriorScale r W v := by
  have hden : W^3*v ≤ B^3 := by
    calc
      _ ≤ W^3*1 := mul_le_mul_of_nonneg_left hv1 (by positivity)
      _ ≤ B^3 := by simpa using pow_le_pow_left₀ hW.le hWB 3
  unfold savedExteriorScale
  exact div_le_div_of_nonneg_left (by positivity) (Real.sqrt_pos.2 (by positivity))
    (Real.sqrt_le_sqrt hden)

theorem eventually_omitted_site_le_saved_boundary {m delta B : ℝ}
    (hgap : delta<1/2+3*m) (hB : 0<B) :
    ∀ᶠ n : ℕ in atTop,∀ r W v : ℝ,
      0<r → 0<W → 0<v → W≤B → v≤1 →
      (n:ℝ)^(-(1:ℝ)/6+m) ≤ r →
      1/(n:ℝ) ≤ (n:ℝ)^(-delta)*savedExteriorScale r W v := by
  have ht := ((tendsto_rpow_atTop (show 0<1/2+3*m-delta by linarith)).comp
    tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (Real.sqrt (B^3)))
  filter_upwards [ht,eventually_gt_atTop (0:ℕ)] with n hn hn0
  change Real.sqrt (B^3) ≤ (n:ℝ)^(1/2+3*m-delta) at hn
  intro r W v hr hW hv hWB hv1 hlow
  have hN : 0<(n:ℝ) := by exact_mod_cast hn0
  have hsqrt : 0<Real.sqrt (B^3) := Real.sqrt_pos.2 (by positivity)
  have hp := pow_le_pow_left₀ (Real.rpow_nonneg hN.le _) hlow 3
  rw [←Real.rpow_mul_natCast hN.le] at hp
  have he : (n:ℝ)*((n:ℝ)^(-delta)*(n:ℝ)^((-(1:ℝ)/6+m)*(3:ℕ)))=
      (n:ℝ)^(1/2+3*m-delta) := by
    calc
      _ = (n:ℝ)^(1:ℝ)*((n:ℝ)^(-delta)*(n:ℝ)^((-(1:ℝ)/6+m)*(3:ℕ))) := by simp
      _ = (n:ℝ)^(1+(-delta+(-(1:ℝ)/6+m)*(3:ℕ))) := by
        rw [←Real.rpow_add hN,←Real.rpow_add hN]
      _ = _ := by congr 1; ring
  have hh : Real.sqrt (B^3) ≤ (n:ℝ)*((n:ℝ)^(-delta)*r^3) := by
    apply hn.trans
    rw [←he]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hN.le _)) hN.le
  have hquot : 1/(n:ℝ) ≤ ((n:ℝ)^(-delta)*r^3)/Real.sqrt (B^3) := by
    apply (le_div_iff₀ hsqrt).2
    rw [div_mul_eq_mul_div,one_mul]
    apply (div_le_iff₀ hN).2
    simpa only [mul_comm] using hh
  apply hquot.trans
  have hscale := mul_le_mul_of_nonneg_left
    (savedExteriorScale_lower_of_bounded_clock hr hW hv hB hWB hv1)
    (Real.rpow_nonneg hN.le (-delta))
  simpa only [mul_div_assoc] using hscale

def actualBoundaryScalarConstant (Cb Cr Cc c : ℝ) : ℝ :=
  4*(Cb+1)*(Cr+1)*(Cc+1)/c

theorem actual_boundary_scalar_budget_le (a : ℕ) (ha : 0<a)
    {β row completion site s Cb Cr Cc c scale rho : ℝ}
    (hCb : 0≤Cb) (hCr : 0≤Cr) (hCc : 0≤Cc) (hc : 0<c)
    (hscale : 0 < scale) (hrho : c*scale ≤ rho) (hs : 0 ≤ s)
    (hβ : |β|≤Cb) (hrow0 : 0≤row) (hrow : row≤Cr)
    (hcompletion0 : 0≤completion) (hcompletion : completion≤Cc)
    (hsite0 : 0 ≤ site) (hsite : site ≤ 2*s) :
    |β|^(2*a)*row*(2:ℝ)^(2*a-1)*
      (completion*(2*s)^(2*a)+site^(2*a)) ≤
      (actualBoundaryScalarConstant Cb Cr Cc c*s/scale*rho)^(2*a) := by
  have hRpow : Cr≤(Cr+1)^(2*a) := by
    apply (le_add_of_nonneg_right (by norm_num : (0:ℝ)≤1)).trans
    simpa only [pow_one] using pow_le_pow_right₀
      (show 1≤Cr+1 by linarith) (show 1≤2*a by omega)
  have hCpow : Cc+1≤(Cc+1)^(2*a) := by
    simpa only [pow_one] using pow_le_pow_right₀
      (show 1≤Cc+1 by linarith) (show 1≤2*a by omega)
  have hinner : completion*(2*s)^(2*a)+site^(2*a) ≤
      (Cc+1)^(2*a)*(2*s)^(2*a) := by
    calc
      _ ≤ Cc*(2*s)^(2*a)+(2*s)^(2*a) := add_le_add
        (mul_le_mul_of_nonneg_right hcompletion (by positivity))
        (pow_le_pow_left₀ hsite0 hsite (2*a))
      _ = (Cc+1)*(2*s)^(2*a) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hCpow (by positivity)
  have hβpow : |β|^(2*a)≤(Cb+1)^(2*a) :=
    pow_le_pow_left₀ (abs_nonneg _) (hβ.trans (by linarith)) _
  have htwo : (2:ℝ)^(2*a-1)≤(2:ℝ)^(2*a) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hbudget : |β|^(2*a)*row*(2:ℝ)^(2*a-1)*
      (completion*(2*s)^(2*a)+site^(2*a)) ≤
      (4*(Cb+1)*(Cr+1)*(Cc+1)*s)^(2*a) := by
    calc
      _ ≤ (Cb+1)^(2*a)*(Cr+1)^(2*a)*(2:ℝ)^(2*a)*
          ((Cc+1)^(2*a)*(2*s)^(2*a)) := by
        apply mul_le_mul (mul_le_mul (mul_le_mul hβpow (hrow.trans hRpow)
          hrow0 (by positivity)) htwo (by positivity) (by positivity)) hinner
          (by positivity) (by positivity)
      _ = _ := by
        rw [show (4:ℝ)=2*2 by norm_num]
        simp only [mul_pow]
        ring
  apply hbudget.trans
  apply pow_le_pow_left₀ (by positivity)
  unfold actualBoundaryScalarConstant
  have hconst : 0≤4*(Cb+1)*(Cr+1)*(Cc+1)*s := by positivity
  have hratio : 1 ≤ rho/(c*scale) := (le_div_iff₀ (mul_pos hc hscale)).2
    (by simpa only [one_mul] using hrho)
  calc
    _ ≤ (4*(Cb+1)*(Cr+1)*(Cc+1)*s)*(rho/(c*scale)) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hratio hconst
    _ = _ := by field_simp

def actualBoundaryUniformRowFactor (N : ℕ) (B : ℝ) : ℝ :=
  Real.exp (2*(7*(N:ℝ)+8*(N:ℝ)^2*(N+1:ℝ))*B)

theorem native_boundary_row_factor_le_of_bounded_clock (n N : ℕ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (b h : ℕ→ℝ) {B : ℝ} (hB : 0≤B) (hN : T.leaves≤N)
    (hclock : finitePhysicalMixedClock (n+1) as b h as.length+
      b as.length+h as.length≤B) :
    nativeBoundaryRowFactor n T b h ≤ actualBoundaryUniformRowFactor N B := by
  unfold nativeBoundaryRowFactor actualBoundaryUniformRowFactor
  apply Real.exp_le_exp.mpr
  have hle : (T.leaves:ℝ)≤(N:ℝ) := by exact_mod_cast hN
  calc
    _ ≤ 2*(7*(T.leaves:ℝ)+8*(T.leaves:ℝ)^2*(T.leaves+1:ℝ))*B :=
      mul_le_mul_of_nonneg_left hclock (by positivity)
    _ ≤ _ := by gcongr

private theorem leaves_relabel_spin {S V : Type*} [Fintype S] [Fintype V]
    (e : S≃V) {as : List PositiveMass} (T : ClockTree S as) :
    (T.relabelSpin e).leaves=T.leaves := by
  induction T with
  | leaf => rfl
  | step a T ih => exact ih
  | fork T U ihT ihU =>
      simp only [ClockTree.relabelSpin,ClockTree.leaves,ihT,ihU]

theorem native_boundary_completion_factor_le_of_bounded_clock (n N : ℕ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (b : ℕ→ℝ) {B : ℝ} (hB : 0≤B) (hN : T.leaves≤N)
    (hclock : b as.length/2≤B) :
    nativeBoundaryCompletionFactor n T b ≤ actualBoundaryUniformRowFactor N B := by
  dsimp only [nativeBoundaryCompletionFactor,actualBoundaryUniformRowFactor]
  rw [leaves_relabel_spin]
  apply Real.exp_le_exp.mpr
  have hle : (T.leaves:ℝ)≤(N:ℝ) := by exact_mod_cast hN
  calc
    _ ≤ 2*(7*(T.leaves:ℝ)+8*(T.leaves:ℝ)^2*(T.leaves+1:ℝ))*B :=
      mul_le_mul_of_nonneg_left hclock (by positivity)
    _ ≤ _ := by gcongr

theorem saved_boundary_layer_scale_identity {r W v p0 : ℝ}
    (hr : 0<r) (hW : 0<W) (hv : 0<v) :
    v*(W*savedExteriorScale r W v)*(p0*savedExteriorScale r W v/r)=
      p0*r^5/W^2 := by
  calc
    _ = p0*W*v/r*(savedExteriorScale r W v)^2 := by ring
    _ = _ := by
      rw [savedExteriorScale_sq hW hv]
      field_simp

theorem saved_boundary_layer_scale_le {r W v p0 : ℝ}
    (hr : 0<r) (hW : 0<W) (hv : 0<v) (hrW : r≤W) (hp0 : 0≤p0) :
    v*(W*savedExteriorScale r W v)*(p0*savedExteriorScale r W v/r)≤p0*W*r^2 := by
  rw [saved_boundary_layer_scale_identity hr hW hv]
  apply (div_le_iff₀ (pow_pos hW 2)).2
  calc
    _ = (p0*r^2)*r^3 := by ring
    _ ≤ (p0*r^2)*W^3 := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hr.le hrW 3) (by positivity)
    _ = _ := by ring

theorem saved_boundary_layer_with_saving_le {r W v p0 eta : ℝ}
    (hr : 0<r) (hW : 0<W) (hv : 0<v) (hrW : r≤W) (hp0 : 0≤p0) :
    v*(eta*W*savedExteriorScale r W v)*(eta*p0*savedExteriorScale r W v/r)≤
      eta^2*(p0*W*r^2) := by
  calc
    _ = eta^2*(v*(W*savedExteriorScale r W v)*(p0*savedExteriorScale r W v/r)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (saved_boundary_layer_scale_le hr hW hv hrW hp0)
      (sq_nonneg eta)

end OAI.SKFluctuations.Cavity
