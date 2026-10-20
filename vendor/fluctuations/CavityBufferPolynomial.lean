module

public import CavityStarPolynomial

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations
open Hierarchy

 theorem eventually_physical_buffer_polynomial (k : ℕ) (Bclock : ℝ)
    {kappa c1 delta D R Q : ℝ} (hkappa : 0 < kappa)
    (hD : 0 ≤ D) (hR : 0 ≤ R) (hdelta : delta < kappa/8-c1) :
    ∀ᶠ n : ℕ in atTop, ∀
      (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
      (q0 : FeatureIndex n → ℝ≥0) (xs : ℝ) (hxs : 0 < xs)
      (w : PhysicalBandWindow n steps xs) (d : GaussianStep (FeatureIndex n) → ℝ≥0)
      (K e L v : ℝ),
      (∀ st ∈ steps, ∀ i : Fin n, st.2 (Sum.inl i) = d st) →
      physicalFieldDuration d steps ≤ Bclock →
      (∀ s ∈ Ioc w.a w.b, w.D₀ ≤
        physicalFieldDuration d (steps.take (radiusGridCut w.radius (s+w.η))) -
          physicalFieldDuration d (steps.take (radiusGridCut w.radius s))) →
      (∀ r ∈ Icc (2*w.a) ((2:ℝ)^w.depth*w.b), w.D₀ ≤
        physicalFieldDuration d (steps.take (radiusGridCut w.radius r)) -
          physicalFieldDuration d (steps.take (radiusGridCut w.radius (3*r/4)))) →
      physicalRawRatio n (k+1) steps 0 xs (Measure.pi fun i => gaussianReal 0 (q0 i))
        id measurable_id ≤ Q →
      1 ≤ K → w.b ≤ K*w.a → w.mass ≤ K*w.C*w.a →
      0 < e → 0 < L → 0 < w.A →
      w.η = (1/Real.sqrt (w.A*((n:ℝ)*e*w.a^4)))*w.a →
      (1/Real.sqrt (w.A*((n:ℝ)*e*w.a^4)))*w.a*e/L ≤ w.D₀ →
      w.generalScaleFactor k K L ≤ D*(Real.log (n:ℝ))^8 →
      w.A/((n:ℝ)*e*w.a^4) ≤ R*(n:ℝ)^(-kappa) →
      (n:ℝ)^(-c1)*w.a ≤ w.mass → w.a ≤ v →
      physicalBufferCenteredNorm n steps q0 (physicalWindowWeight steps 0 w.selected)
        (2*(k+1):ℕ) ≤ (n:ℝ)^(-delta)*v := by
  let C := Real.sqrt (1+(2*((k+1:ℕ):ℝ))^2/3)*Q^2
  have hgap : 2*(delta/2) < kappa/8-c1 := by linarith
  filter_upwards [eventually_physical_buffer_centered_moment k Bclock,
    PhysicalBandWindow.eventually_coefficient_polynomial k hkappa hD hR,
    eventually_log_polynomial_saving 0 hgap C,
    eventually_gt_atTop (0:ℕ)] with n hbuffer hcoeff hsave hn
  intro steps ha q0 xs hxs w d K e L v hd hB hfirst hdyad hQ hK hb hm he hL hA
    heta hclock hscale hratio hmass hav
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast hn
  have hwa : 0 < w.a := hxs.trans_le w.xa
  have hc := hcoeff steps ha xs hxs w K e L hK hb hm he hL hA heta hclock hscale hratio
  have hloss := w.loss_polynomial k hn0 hwa hc hmass
  have hbuf := hbuffer steps ha q0 xs hxs w d Q hd hB hfirst hdyad hQ
  change momentNorm _ _ (2*((k+1:ℕ):ℝ)) ≤ _ at hbuf
  have hl := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hloss (by norm_num : (0:ℝ) ≤ 2))
    (sq_nonneg Q)
  have hbuf' : physicalBufferCenteredNorm n steps q0
      (physicalWindowWeight steps 0 w.selected) (2*(k+1):ℕ) ≤ (w.loss k/2)*Q^2 := by
    simpa only [physicalBufferCenteredNorm,Nat.cast_mul,Nat.cast_ofNat] using hbuf
  have hcb : physicalBufferCenteredNorm n steps q0
      (physicalWindowWeight steps 0 w.selected) (2*(k+1):ℕ) ≤
      C*(n:ℝ)^(-(kappa/8-c1))*w.a := by
    apply hbuf'.trans
    convert hl using 1 <;> dsimp only [C]
    rw [show -(kappa/8)+c1=-(kappa/8-c1) by ring]
    ring
  have hsave' : C*(n:ℝ)^(-(kappa/8-c1)) ≤ (n:ℝ)^(-delta) := by
    simpa only [pow_zero,mul_one,show -2*(delta/2) = -delta by ring] using hsave
  calc _ ≤ C*(n:ℝ)^(-(kappa/8-c1))*w.a := hcb
       _ ≤ (n:ℝ)^(-delta)*w.a := mul_le_mul_of_nonneg_right hsave' hwa.le
       _ ≤ (n:ℝ)^(-delta)*v := mul_le_mul_of_nonneg_left hav (Real.rpow_nonneg hn0.le _)

end OAI.SKFluctuations
