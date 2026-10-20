module

public import CavityWeightedExteriorResampling
public import CavityProjectedResamplingClock

@[expose] public section

noncomputable section
set_option maxHeartbeats 1500000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations
open Hierarchy

def savedWeightedExteriorScale (x W v s : ℝ) : ℝ :=
  x^3*Real.sqrt s/(Real.sqrt (W^3)*v)

theorem savedWeightedExteriorScale_sq {x W v s : ℝ} (hW : 0 < W) (hs : 0 ≤ s) :
    (savedWeightedExteriorScale x W v s)^2=x^6*s/(W^3*v^2) := by
  unfold savedWeightedExteriorScale
  rw [div_pow,mul_pow,mul_pow,Real.sq_sqrt hs,Real.sq_sqrt (by positivity)]
  congr 1
  ring

theorem weighted_projection_coefficient_from_primitives
    {N L P a D ca c W v s : ℝ} (hN : 0 < N) (hL : 0 < L) (ha : 0 < a)
    (hD : 0 < D) (hca : 0 < ca) (hc : 0 < c) (hW : 0 < W) (hv : 0 < v) (hs : 0 ≤ s)
    (hmass : ca*v ≤ a) (hclock : c*W^3/L ≤ D) :
    (P*L^2/(a*Real.sqrt (N*D)))^2*s ≤ 
      (P^2/(ca^2*c))*L^5*s/(N*W^3*v^2) := by
  have hasq : (ca*v)^2 ≤ a^2 := pow_le_pow_left₀ (by positivity) hmass 2
  have hden : (ca*v)^2*(N*(c*W^3/L)) ≤ a^2*(N*D) :=
    mul_le_mul hasq (mul_le_mul_of_nonneg_left hclock hN.le) (by positivity) (sq_nonneg _)
  calc
    _=P^2*L^4*s/(a^2*(N*D)) := by
      rw [div_pow,mul_pow,mul_pow,Real.sq_sqrt (by positivity)]
      ring
    _ ≤ P^2*L^4*s/((ca*v)^2*(N*(c*W^3/L))) := by
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _=_ := by field_simp

theorem weighted_projection_coefficient_scale {N C L x W v s : ℝ} (d : ℕ)
    (hN : 0 < N) (hx : 0 < x) (hW : 0 < W) (hv : 0 < v) (hs : 0 ≤ s) :
    C*L^d*s/(N*W^3*v^2)=
      C*L^d/(N*x^6)*(savedWeightedExteriorScale x W v s)^2 := by
  rw [savedWeightedExteriorScale_sq hW hs]
  field_simp

theorem eventually_weighted_projection_coefficient
    (P ca c : ℝ) (hca : 0 < ca) (hc : 0 < c)
    {m delta : ℝ} (hgap : 2*delta < 6*m) :
    ∀ᶠ n : ℕ in atTop, ∀ (a D x W v s : ℝ),
      0 < a → 0 < D → 0 < x → 0 < W → 0 < v → 0 ≤ s →
      ca*v ≤ a → c*W^3/Real.log (n:ℝ) ≤ D → (n:ℝ)^(-(1:ℝ)/6+m) ≤ x →
      (P*(Real.log (n:ℝ))^2/(a*Real.sqrt ((n:ℝ)*D)))^2*s ≤ 
        ((n:ℝ)^(-delta)*savedWeightedExteriorScale x W v s)^2 := by
  let C := P^2/(ca^2*c)
  filter_upwards [eventually_log_polynomial_saving 5 hgap C,
    eventually_gt_atTop (1:ℕ)] with n hn hnpos
  intro a D x W v s ha hD hx hW hv hs hmass hclock hlow
  have hN : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hL : 0 < Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast hnpos)
  have hb := weighted_projection_coefficient_from_primitives hN hL ha hD hca hc hW hv hs hmass hclock
    (P:=P)
  apply hb.trans
  rw [weighted_projection_coefficient_scale 5 hN hx hW hv hs]
  have hsmall := reciprocal_sixth_small_scale hN hx hlow
  have hsave := mul_le_mul_of_nonneg_left hsmall
    (show 0 ≤ C*(Real.log (n:ℝ))^5 by dsimp [C]; positivity)
  have hsave' : C*(Real.log (n:ℝ))^5/((n:ℝ)*x^6) ≤ C*(Real.log (n:ℝ))^5*(n:ℝ)^(-6*m) := by
    simpa only [div_eq_mul_inv,mul_assoc,one_mul] using hsave
  have hf := mul_le_mul_of_nonneg_right (hsave'.trans (by simpa only [neg_mul] using hn))
    (sq_nonneg (savedWeightedExteriorScale x W v s))
  have he : (n:ℝ)^(-(2*delta))*(savedWeightedExteriorScale x W v s)^2=
      ((n:ℝ)^(-delta)*savedWeightedExteriorScale x W v s)^2 := by
    rw [mul_pow,←Real.rpow_mul_natCast hN.le]
    congr 1
    ring
  rw [he] at hf
  exact hf

theorem eventually_physical_weighted_exterior_resampling_raw
    (k : ℕ) (B : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ (P : Type) [MeasurableSpace P]
      (ext : List (GaussianStep (FeatureIndex n)))
      (T : ReplicaTree (FeatureIndex n) (Spin n) ext) (H : T.Assignment → ℝ) (s : T.Slot)
      (tail pre skip : List (GaussianStep (FeatureIndex n))) (a a₀ aₑ D pH sj : ℝ),
      0 < a → 0 < D → D ≤ B → 0 ≤ pH → 0 ≤ sj →
      OrderedSteps a (pre++tail) → OrderedSteps a₀ ((skip++pre)++tail) → OrderedSteps aₑ ext →
    ∀ (μ : Measure P) [IsFiniteMeasure μ]
      (xₑ x : P → FeatureIndex n → ℝ) (hxₑ : Measurable xₑ) (hx : Measurable x)
      (d : Fin pre.length → ℝ), (∀ j, 0 ≤ d j) → (∑ j, d j=D) →
      (∀ j i, (hierarchyClocks pre j (Sum.inl i):ℝ)=d j) →
      (∫ p, T.expect (uniformWeight n) (finiteFeature n)
        (fun σ=>|H σ|^(8*(k+1))) (xₑ p) ∂μ) ≤ pH^(8*(k+1)) →
      physicalOverlapMoment n (2*(k+1)) ext μ xₑ hxₑ 0 ≤ sj^(4*(k+1)) →
    physicalWeightedExteriorResamplingMoment n (k+1) T H s tail (skip++pre) μ xₑ x hx ≤ 
      (2*(projectionLpConstant (2*k+1)*(Real.log (n:ℝ))^2/(a*Real.sqrt ((n:ℝ)*D))) *
        pH*Real.sqrt sj)^(4*(k+1)) := by
  filter_upwards [eventually_physical_weighted_exterior_terminal_projection k B] with n hn
  intro P _ ext T H s tail pre skip a a₀ aₑ D pH sj ha hD hDB hpH hsj ho hs hₑ μ _
    xₑ x hxₑ hx d hd hdD hc hH hR
  have heH : pH^(8*(k+1))=(pH^(4*(k+1)))^2 := by rw [←pow_mul]; congr 1; omega
  have heR : sj^(4*(k+1))=(sj^(2*(k+1)))^2 := by rw [←pow_mul]; congr 1; omega
  have hH' := Real.sqrt_le_sqrt hH
  rw [heH,Real.sqrt_sq (pow_nonneg hpH _)] at hH'
  have hR' := Real.sqrt_le_sqrt hR
  rw [heR,Real.sqrt_sq (pow_nonneg hsj _)] at hR'
  have ht := hn P ext T H s tail pre skip a a₀ aₑ D ha hD hDB ho hs hₑ μ xₑ x hxₑ hx d hd hdD hc
  have hr := physical_weighted_exterior_resampling_le_residual n (k+1) (Nat.succ_pos k)
    T hₑ H s tail (skip++pre) hs μ xₑ x hxₑ hx
  let A := projectionLpConstant (2*k+1)*(Real.log (n:ℝ))^2/(a*Real.sqrt ((n:ℝ)*D))
  have hAn : 0 ≤ A := div_nonneg (mul_nonneg (projectionLpConstant_pos _).le (sq_nonneg _))
    (mul_nonneg ha.le (Real.sqrt_nonneg _))
  have hprod := mul_le_mul hH' hR' (Real.sqrt_nonneg _) (pow_nonneg hpH _)
  have hraw := mul_le_mul_of_nonneg_left hprod (pow_nonneg hAn (4*(k+1)))
  apply hr.trans
  apply (mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ (2:ℝ)^(4*(k+1)))).trans
  calc
    _ ≤ (2:ℝ)^(4*(k+1))*(A^(4*(k+1))*(pH^(4*(k+1))*sj^(2*(k+1)))) :=
      mul_le_mul_of_nonneg_left (by simpa only [A,mul_assoc] using hraw) (by positivity)
    _=_ := by
      dsimp only [A]
      have heS : (Real.sqrt sj)^(4*(k+1))=sj^(2*(k+1)) := by
        rw [show 4*(k+1)=2*(2*(k+1)) by omega,pow_mul,Real.sq_sqrt hsj]
      rw [mul_pow,mul_pow,mul_pow,heS]
      ring

theorem eventually_physical_weighted_exterior_resampling_from_primitives
    (k : ℕ) (B ca c : ℝ) (hca : 0 < ca) (hc : 0 < c)
    {m delta : ℝ} (hgap : 2*delta < 6*m) :
    ∀ᶠ n : ℕ in atTop, ∀ (P : Type) [MeasurableSpace P]
      (ext : List (GaussianStep (FeatureIndex n)))
      (T : ReplicaTree (FeatureIndex n) (Spin n) ext) (H : T.Assignment → ℝ) (s : T.Slot)
      (tail pre skip : List (GaussianStep (FeatureIndex n))) (a a₀ aₑ D pH sj r W v : ℝ),
      0 < a → 0 < D → D ≤ B → 0 ≤ pH → 0 ≤ sj → 0 < r → 0 < W → 0 < v →
      ca*v ≤ a → c*W^3/Real.log (n:ℝ) ≤ D → (n:ℝ)^(-(1:ℝ)/6+m) ≤ r →
      OrderedSteps a (pre++tail) → OrderedSteps a₀ ((skip++pre)++tail) → OrderedSteps aₑ ext →
    ∀ (μ : Measure P) [IsFiniteMeasure μ]
      (xₑ x : P → FeatureIndex n → ℝ) (hxₑ : Measurable xₑ) (hx : Measurable x)
      (d : Fin pre.length → ℝ), (∀ j, 0 ≤ d j) → (∑ j, d j=D) →
      (∀ j i, (hierarchyClocks pre j (Sum.inl i):ℝ)=d j) →
      (∫ p, T.expect (uniformWeight n) (finiteFeature n)
        (fun σ=>|H σ|^(8*(k+1))) (xₑ p) ∂μ) ≤ pH^(8*(k+1)) →
      physicalOverlapMoment n (2*(k+1)) ext μ xₑ hxₑ 0 ≤ sj^(4*(k+1)) →
    physicalWeightedExteriorResamplingMoment n (k+1) T H s tail (skip++pre) μ xₑ x hx ≤
      (2*(n:ℝ)^(-delta)*pH*savedWeightedExteriorScale r W v sj)^(4*(k+1)) := by
  filter_upwards [eventually_physical_weighted_exterior_resampling_raw k B,
    eventually_weighted_projection_coefficient (projectionLpConstant (2*k+1)) ca c hca hc hgap] with n hn hsav
  intro P _ ext T H s tail pre skip a a₀ aₑ D pH sj r W v ha hD hDB hpH hsj hr hW hv
    hmass hclock hlow ho hs hₑ μ _ xₑ x hxₑ hx d hd hdD hdclock hH hR
  have hp := hn P ext T H s tail pre skip a a₀ aₑ D pH sj ha hD hDB hpH hsj ho hs hₑ
    μ xₑ x hxₑ hx d hd hdD hdclock hH hR
  have hb := hsav a D r W v sj ha hD hr hW hv hsj hmass hclock hlow
  have hsq := mul_le_mul_of_nonneg_left hb (show 0 ≤ 4*pH^2 by positivity)
  have hsq' : (2*(projectionLpConstant (2*k+1)*(Real.log (n:ℝ))^2/(a*Real.sqrt ((n:ℝ)*D)))*
      pH*Real.sqrt sj)^2 ≤ (2*(n:ℝ)^(-delta)*pH*savedWeightedExteriorScale r W v sj)^2 := by
    calc
      _=4*pH^2*((projectionLpConstant (2*k+1)*(Real.log (n:ℝ))^2/(a*Real.sqrt ((n:ℝ)*D)))^2*sj) := by
        rw [mul_pow,mul_pow,mul_pow,Real.sq_sqrt hsj]
        ring
      _ ≤ _ := hsq
      _=_ := by ring
  have hf := pow_le_pow_left₀ (sq_nonneg _) hsq' (2*(k+1))
  simp only [←pow_mul,show 2*(2*(k+1))=4*(k+1) by omega] at hf
  exact hp.trans hf

end OAI.SKFluctuations
