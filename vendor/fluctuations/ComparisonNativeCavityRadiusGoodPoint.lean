module

public import ComparisonNativeCavityConcentrationRadiusBandScale

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 5000000

theorem radius_integral_good_point {a z threshold : ℝ} {f : ℝ→ℝ}
    (haz : a<z) (hf : IntegrableOn f (Ioo a z))
    (hsmall : (∫r in Ioo a z,f r)<threshold*(z-a)) :
    ∃r∈Ioo a z,f r≤threshold := by
  by_contra h
  push Not at h
  have H:=integral_mono_ae (integrable_const threshold) hf
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      exact (h r hr).le)
  have he : (∫_r in Ioo a z,threshold)=threshold*(z-a) := by
    rw [setIntegral_const,measureReal_def,Real.volume_Ioo,ENNReal.toReal_ofReal (sub_pos.mpr haz).le]
    simp only [smul_eq_mul,mul_comm]
  rw [he] at H
  exact (not_lt_of_ge H) hsmall

theorem eventually_radius_good_point_of_scaled_integral
    (f : ℕ→ℝ→ℝ) (W a z : ℕ→ℝ) {c : ℝ} (hc : 0<c)
    (hW : ∀n,0<W n) (hlength : ∀n,c*W n≤z n-a n)
    (hf : ∀n,IntegrableOn (f n) (Ioo (a n) (z n)))
    (hlim : Tendsto (fun n=>(∫r in Ioo (a n) (z n),f n r)/(W n)^3) atTop (𝓝 0)) :
    ∀eta : ℝ,0<eta→∀ᶠn : ℕ in atTop,
      ∃r∈Ioo (a n) (z n),f n r≤eta*(W n)^2 := by
  intro eta heta
  have he : ∀ᶠn : ℕ in atTop,
      (∫r in Ioo (a n) (z n),f n r)/(W n)^3<c*eta :=
    hlim.eventually (eventually_lt_nhds (mul_pos hc heta))
  filter_upwards [he] with n hn
  have hw:=hW n
  have hlen:=hlength n
  have haz : a n<z n := by nlinarith [mul_pos hc hw]
  apply radius_integral_good_point haz (hf n)
  have H : (∫r in Ioo (a n) (z n),f n r)<(c*eta)*(W n)^3 :=
    (div_lt_iff₀ (pow_pos hw 3)).mp hn
  have Hlen:=mul_le_mul_of_nonneg_left hlen (mul_nonneg heta.le (sq_nonneg (W n)))
  apply H.trans_le
  nlinarith only [Hlen]

namespace NativeOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

def cavityRadiusPointDefect (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (r : ℝ) : ℝ :=
  orderedPathB (n+1) M.bf M.hf (M.alpha.val.val r)-
    (orderedPathS (n+1) M.bf M.hf (M.alpha.val.val r))^2

theorem cavityRadiusPointDefect_nonneg
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {r : ℝ} (hr : r∈Icc (0:ℝ) 1) : 0≤M.cavityRadiusPointDefect r := by
  have H:=comparisonVariableEndpoint_radius_moments M.context.hc M.context.hk
    M.context.hkc M.context.hm M.context.hM (n+1) (by omega)
    M.b M.h M.context.hd.ne' M.hlam.le M.hlb M.hb M.hh M.hh0 M.alpha
  exact sub_nonneg.mpr ((H.2.2 r hr).2.1)

theorem cavityRadiusPointDefect_integrableOn
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {a z : ℝ} (ha : 0≤a) (hz : z≤1) :
    IntegrableOn M.cavityRadiusPointDefect (Ioo a z) := by
  have H:=comparisonVariableEndpoint_radius_moments M.context.hc M.context.hk
    M.context.hkc M.context.hm M.context.hM (n+1) (by omega)
    M.b M.h M.context.hd.ne' M.hlam.le M.hlb M.hb M.hh M.hh0 M.alpha
  have hS2 : MonotoneOn (fun r=>(orderedPathS (n+1) M.bf M.hf (M.alpha.val.val r))^2)
      (Icc (0:ℝ) 1) := by
    intro r hr s hs hrs
    exact pow_le_pow_left₀ ((H.2.2 r hr).1.1) (H.1 hr hs hrs) 2
  have hiB:=H.2.1.integrableOn_isCompact (μ:=volume) isCompact_Icc
  have hiS:=hS2.integrableOn_isCompact (μ:=volume) isCompact_Icc
  exact (hiB.sub hiS).mono_set (fun r hr=>⟨ha.trans hr.1.le,hr.2.le.trans hz⟩)

theorem cavityRadiusDefect_eq_point_integral
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (a z : ℝ) :
    M.cavityRadiusDefect a z=∫r in Ioo a z,M.cavityRadiusPointDefect r := rfl

end NativeOverlapMinimum

theorem actual_minimum_cavity_radius_good_point
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D C ca c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hmargin : 2*delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az) (hC0 : 0<C0) (hCt : 0≤Ct)
    (hC : 1≤C) (hca : 0<ca) (hc : 0<c)
    (M : (n : ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W a z : ℕ→ℝ) (ha : ∀n,0<a n) (haz : ∀n,a n≤z n) (hz : ∀n,z n≤1)
    (hxsW : ∀n,(M n).xs≤W n) (hWz : ∀n,W n≤z n) (hsize : ∀n,z n≤C*W n)
    (houter : ∀n,ca*W n≤(M n).alpha.val.val (a n)) (hlength : ∀n,c*W n≤z n-a n)
    (dphys : ℕ→ℕ) (e : ∀n,Fin (dphys n+1)≃FeatureIndex (n+1)) (Kb Kh : ℕ→ℝ≥0)
    (hparent : ∀n,LipschitzOnWith (Kb n) (fun r=>(M n).b ((M n).alpha.val.val r)) (Icc (a n) (z n)))
    (hfield : ∀n,LipschitzOnWith (Kh n) (fun r=>(M n).h ((M n).alpha.val.val r)) (Icc (a n) (z n))) :
    ∀eta : ℝ,0<eta→∀ᶠn : ℕ in atTop,
      ∃r∈Ioo (a n) (z n),(M n).cavityRadiusPointDefect r≤eta*(W n)^2 := by
  have H:=actual_minimum_cavity_radius_Eq19_band_scale_tendsto_zero Bclock hm hdelta hmargin
    hcl hcu hAz hC0 hCt hC hca M W a z ha haz hz hxsW hWz hsize houter dphys e Kb Kh hparent hfield
  exact eventually_radius_good_point_of_scaled_integral (fun n=>(M n).cavityRadiusPointDefect)
    W a z hc (fun n=>(M n).hxs.trans_le (hxsW n)) hlength
    (fun n=>(M n).cavityRadiusPointDefect_integrableOn (ha n).le (hz n)) H

theorem actual_minimum_cavity_radius_bare_SK_good_star
    (Bclock T : ℝ) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hmargin : 2*delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az) (hC0 : 0<C0) (hCt : 0≤Ct)
    (M : (n : ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hW1 : ∀n,W n≤1)
    (hband : ∀n,max 1 (2*Az)*(M n).xs≤W n)
    (hb_const : ∀n u,(M n).b u=T) (hh_zero : ∀n u,(M n).h u=0) :
    ∀eta : ℝ,0<eta→∀ᶠn : ℕ in atTop,
      ∃r∈Ioo (W n/2) (W n),
        (M n).cavityRadiusPointDefect r≤eta*(W n)^2 ∧
        (cl/2)*W n≤(M n).alpha.val.val r ∧ (M n).alpha.val.val r≤cu*W n := by
  have hxsW n : (M n).xs≤W n := by
    have H:=mul_le_mul_of_nonneg_right (le_max_left 1 (2*Az)) (M n).hxs.le
    nlinarith [hband n]
  have hWp n : 0<W n := (M n).hxs.trans_le (hxsW n)
  have hthreshold n : (M n).z≤W n/2 := by
    have H:=mul_le_mul_of_nonneg_right (le_max_right 1 (2*Az)) (M n).hxs.le
    nlinarith [(M n).hzxs,hband n]
  have houter n : (cl/2)*W n≤(M n).alpha.val.val (W n/2) := by
    have H:=((M n).regular (W n/2) ⟨hthreshold n,by linarith [hW1 n,hWp n]⟩).1
    nlinarith only [H]
  have H:=actual_minimum_cavity_radius_Eq19_band_scale_bare_SK_tendsto_zero
    (C:=1) (ca:=cl/2) Bclock T hm hdelta hmargin hcl hcu hAz hC0 hCt
    (by norm_num) (by positivity) M W (fun n=>W n/2) W
    (fun n=>div_pos (hWp n) (by norm_num)) (fun n=>by linarith [hWp n]) hW1 hxsW
    (fun _=>le_rfl) (fun n=>by simp) houter hb_const hh_zero
  have HP:=eventually_radius_good_point_of_scaled_integral (fun n=>(M n).cavityRadiusPointDefect)
    W (fun n=>W n/2) W (c:=1/2) (by norm_num) hWp (fun n=>by nlinarith)
    (fun n=>(M n).cavityRadiusPointDefect_integrableOn (div_pos (hWp n) (by norm_num)).le (hW1 n)) H
  intro eta heta
  filter_upwards [HP eta heta] with n hn
  obtain ⟨r,hr,hdef⟩:=hn
  have hreg:=(M n).regular r ⟨(hthreshold n).trans hr.1.le,hr.2.le.trans (hW1 n)⟩
  refine ⟨r,hr,hdef,?_,?_⟩
  · have H:=mul_le_mul_of_nonneg_left hr.1.le hcl.le
    nlinarith only [H,hreg.1]
  · exact hreg.2.trans (mul_le_mul_of_nonneg_left hr.2.le hcu.le)

end OAI.SKFluctuations.LaplaceWindowFormalization
