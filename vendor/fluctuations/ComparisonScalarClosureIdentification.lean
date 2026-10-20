module

public import ComparisonStrengthRescaling

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy
open scoped Topology ENNReal
set_option maxHeartbeats 2600000

def comparisonRescaledScalarResponse (Gamma : ℝ→ℝ) (T x q : ℝ) : ℝ :=
  (Gamma (T*x*q)-x*q)/x^3

theorem comparison_scalar_clock_scaled_exact {h0 b0 e s T x t : ℝ}
    (hT : T≠0) (hx : x≠0) :
    comparisonNativeScalarClock h0 b0 e (x*t) s/(T*x) =
      s/x-x^2/T*((e/x^2)*(s/x-t)-((b0-T)*s+h0)/x^3) := by
  unfold comparisonNativeScalarClock
  field_simp
  ring

theorem comparison_scalar_response_closure_exact (Gamma : ℝ→ℝ)
    {h0 b0 e s T x t : ℝ} (hT : T≠0) (hx : x≠0) :
    (e/x^2)/T*(s/x-t) =
      comparisonRescaledScalarResponse Gamma T x
        (comparisonNativeScalarClock h0 b0 e (x*t) s/(T*x))+
      (s-Gamma (comparisonNativeScalarClock h0 b0 e (x*t) s))/x^3+
      (((b0-T)*s+h0)/x^3)/T := by
  have harg : T*x*(comparisonNativeScalarClock h0 b0 e (x*t) s/(T*x))=
      comparisonNativeScalarClock h0 b0 e (x*t) s := by field_simp
  unfold comparisonRescaledScalarResponse
  rw [harg]
  unfold comparisonNativeScalarClock
  field_simp
  ring

theorem comparison_scalar_bare_remainder_tendsto
    (h0 b0 s x : ℕ→ℝ) {T sl : ℝ} (_hx : ∀n,x n≠0)
    (hs : Tendsto (fun n=>s n/x n) atTop (𝓝 sl))
    (hb : Tendsto (fun n=>(b0 n-T)/(x n)^2) atTop (𝓝 0))
    (hh : Tendsto (fun n=>h0 n/(x n)^3) atTop (𝓝 0)) :
    Tendsto (fun n=>((b0 n-T)*s n+h0 n)/(x n)^3) atTop (𝓝 0) := by
  have he n : ((b0 n-T)*s n+h0 n)/(x n)^3=
      ((b0 n-T)/(x n)^2)*(s n/x n)+h0 n/(x n)^3 := by field_simp
  simp_rw [he]
  simpa using (hb.mul hs).add hh

theorem comparison_scalar_clock_scaled_tendsto
    (h0 b0 e s x : ℕ→ℝ) {T t hl sl : ℝ}
    (hT : T≠0) (hx0 : ∀n,x n≠0) (hx : Tendsto x atTop (𝓝 0))
    (he : Tendsto (fun n=>e n/(x n)^2) atTop (𝓝 hl))
    (hs : Tendsto (fun n=>s n/x n) atTop (𝓝 sl))
    (hb : Tendsto (fun n=>(b0 n-T)/(x n)^2) atTop (𝓝 0))
    (hh : Tendsto (fun n=>h0 n/(x n)^3) atTop (𝓝 0)) :
    Tendsto (fun n=>comparisonNativeScalarClock (h0 n) (b0 n) (e n) (x n*t) (s n)/(T*x n))
      atTop (𝓝 sl) := by
  have hz := comparison_scalar_bare_remainder_tendsto h0 b0 s x hx0 hs hb hh
  have hlim := hs.sub (((hx.pow 2).div_const T).mul ((he.mul (hs.sub_const t)).sub hz))
  simpa only [comparison_scalar_clock_scaled_exact hT (hx0 _),zero_pow (by norm_num : 2≠0),
    zero_div,zero_mul,sub_zero] using hlim

theorem comparison_scalar_closure_identification_pointwise
    (Gamma : ℕ→ℝ→ℝ) (h0 b0 e s x : ℕ→ℝ) (g : ℝ→ℝ)
    {T t hl sl : ℝ} {A : Set ℝ}
    (hT : T≠0) (hx0 : ∀n,x n≠0) (hx : Tendsto x atTop (𝓝 0))
    (he : Tendsto (fun n=>e n/(x n)^2) atTop (𝓝 hl))
    (hs : Tendsto (fun n=>s n/x n) atTop (𝓝 sl))
    (hb : Tendsto (fun n=>(b0 n-T)/(x n)^2) atTop (𝓝 0))
    (hh : Tendsto (fun n=>h0 n/(x n)^3) atTop (𝓝 0))
    (hG : TendstoUniformlyOn (fun n=>comparisonRescaledScalarResponse (Gamma n) T (x n)) g atTop A)
    (hgc : ContinuousWithinAt g A sl)
    (hKA : ∀ᶠ n in atTop,comparisonNativeScalarClock (h0 n) (b0 n) (e n) (x n*t) (s n)/(T*x n)∈A)
    (hrho : Tendsto (fun n=>(s n-Gamma n (comparisonNativeScalarClock (h0 n) (b0 n) (e n)
      (x n*t) (s n)))/(x n)^3) atTop (𝓝 0)) :
    g sl=hl/T*(sl-t) := by
  have hclock := comparison_scalar_clock_scaled_tendsto h0 b0 e s x (t:=t) hT hx0 hx he hs hb hh
  have hclockA := tendsto_nhdsWithin_iff.mpr ⟨hclock,hKA⟩
  have hscalar := hG.tendsto_comp hgc hclockA
  have hz := comparison_scalar_bare_remainder_tendsto h0 b0 s x hx0 hs hb hh
  have hright := (hscalar.add hrho).add (hz.div_const T)
  have hleft := (he.div_const T).mul (hs.sub_const t)
  have hright' : Tendsto (fun n=>(e n/(x n)^2)/T*(s n/x n-t)) atTop (𝓝 (g sl)) := by
    convert hright using 1
    · ext n
      exact comparison_scalar_response_closure_exact (Gamma n) hT (hx0 n)
    · simp
  exact tendsto_nhds_unique hright' hleft

section Measure
variable {Ω : Type*} [MeasurableSpace Ω]

theorem comparison_L1_zero_exists_ae_subsequence (mu : Measure Ω) (rho : ℕ→Ω→ℝ)
    (hi : ∀n,Integrable (rho n) mu)
    (hlim : Tendsto (fun n=>∫t,|rho n t|∂mu) atTop (𝓝 0)) :
    ∃phi : ℕ→ℕ,StrictMono phi ∧
      ∀ᵐ t∂mu,Tendsto (fun n=>rho (phi n) t) atTop (𝓝 0) := by
  have hnorm n : eLpNorm (rho n-(0:Ω→ℝ)) 1 mu=ENNReal.ofReal (∫t,|rho n t|∂mu) := by
    simp only [sub_zero]
    rw [eLpNorm_one_eq_lintegral_enorm (hi n).aestronglyMeasurable,
      ←ofReal_integral_norm_eq_lintegral_enorm (hi n)]
    simp only [Real.norm_eq_abs]
  have helim : Tendsto (fun n=>eLpNorm (rho n-(0:Ω→ℝ)) 1 mu) atTop (𝓝 0) := by
    simp_rw [hnorm]
    convert (ENNReal.continuous_ofReal.tendsto (0:ℝ)).comp hlim using 1 <;> first | rfl | simp
  exact (tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero helim).exists_seq_tendsto_ae
end Measure

theorem comparison_scalar_closure_identification_ae
    (mu : Measure ℝ) (Gamma : ℕ→ℝ→ℝ) (h0 b0 e s : ℕ→ℝ→ℝ) (x : ℕ→ℝ)
    (g hl sl : ℝ→ℝ) {T : ℝ} {A : Set ℝ}
    (hT : T≠0) (hx0 : ∀n,x n≠0) (hx : Tendsto x atTop (𝓝 0))
    (hG : TendstoUniformlyOn (fun n=>comparisonRescaledScalarResponse (Gamma n) T (x n)) g atTop A)
    (hgc : ∀ᵐ t∂mu,ContinuousWithinAt g A (sl t))
    (hKA : ∀n,∀ᵐ t∂mu,comparisonNativeScalarClock (h0 n t) (b0 n t) (e n t)
      (x n*t) (s n t)/(T*x n)∈A)
    (hcoeff : ∀ᵐ t∂mu,
      Tendsto (fun n=>e n t/(x n)^2) atTop (𝓝 (hl t)) ∧
      Tendsto (fun n=>s n t/x n) atTop (𝓝 (sl t)) ∧
      Tendsto (fun n=>(b0 n t-T)/(x n)^2) atTop (𝓝 0) ∧
      Tendsto (fun n=>h0 n t/(x n)^3) atTop (𝓝 0))
    (hrhoi : ∀n,Integrable (fun t=>(s n t-Gamma n (comparisonNativeScalarClock
      (h0 n t) (b0 n t) (e n t) (x n*t) (s n t)))/(x n)^3) mu)
    (hrhoL1 : Tendsto (fun n=>∫t,|(s n t-Gamma n (comparisonNativeScalarClock
      (h0 n t) (b0 n t) (e n t) (x n*t) (s n t)))/(x n)^3|∂mu) atTop (𝓝 0)) :
    (∀ᵐ t∂mu,g (sl t)=hl t/T*(sl t-t)) ∧
    ∃phi : ℕ→ℕ,StrictMono phi ∧∀ᵐ t∂mu,
      Tendsto (fun n=>(s (phi n) t-Gamma (phi n) (comparisonNativeScalarClock
        (h0 (phi n) t) (b0 (phi n) t) (e (phi n) t) (x (phi n)*t) (s (phi n) t)))/
        (x (phi n))^3) atTop (𝓝 0) := by
  obtain ⟨phi,hphi,hrho⟩ := comparison_L1_zero_exists_ae_subsequence mu _ hrhoi hrhoL1
  refine ⟨?_,phi,hphi,hrho⟩
  have hKAall : ∀ᵐ t∂mu,∀n,comparisonNativeScalarClock (h0 n t) (b0 n t) (e n t)
      (x n*t) (s n t)/(T*x n)∈A := ae_all_iff.mpr hKA
  filter_upwards [hcoeff,hgc,hKAall,hrho] with t ht hgt hkt hrt
  exact comparison_scalar_closure_identification_pointwise
    (fun n=>Gamma (phi n)) (fun n=>h0 (phi n) t) (fun n=>b0 (phi n) t)
    (fun n=>e (phi n) t) (fun n=>s (phi n) t) (x ∘ phi) g hT
    (fun n=>hx0 (phi n)) (hx.comp hphi.tendsto_atTop)
    (ht.1.comp hphi.tendsto_atTop) (ht.2.1.comp hphi.tendsto_atTop)
    (ht.2.2.1.comp hphi.tendsto_atTop) (ht.2.2.2.comp hphi.tendsto_atTop)
    (hG.seq_tendstoUniformlyOn phi hphi.tendsto_atTop) hgt
    (Eventually.of_forall (fun n=>hkt (phi n))) hrt

end OAI.SKFluctuations.LaplaceWindowFormalization
