module

public import ComparisonNativeStarBufferSelection

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 4000000

namespace NativeStarBuffer

def bandScaleConstant (k : ℕ) (K Ccap Fcap cFloor Ddepth Lcap : ℝ) : ℝ :=
  (Ddepth+3)^3*(4*(K+1)*Ccap*nearPairMomentConstant (k+1)^(((k+1:ℕ):ℝ)⁻¹)*
    (1+(K+1)*Ccap)^2+4*K*Ccap*(projectionLpConstant k)^2*(Fcap^2/(cFloor/4)^2)*Lcap)

theorem generalScaleFactor_le_log8 {n : ℕ} {steps : List (GaussianStep (FeatureIndex n))}
    {xs : ℝ} (w : PhysicalBandWindow n steps xs) (k : ℕ)
    {K Ccap Fcap cFloor Ddepth Lcap L : ℝ}
    (hK : 1 ≤ K) (hC : w.C ≤ Ccap) (hF : w.F ≤ Fcap)
    (hc : 0<cFloor) (hcw : cFloor ≤ w.c₀)
    (hD : 0 ≤ Ddepth) (_hLcap : 0 ≤ Lcap) (hL : 0 ≤ L)
    (hlog : 1 ≤ Real.log (n:ℝ))
    (hdepth : (w.depth:ℝ) ≤ Ddepth*Real.log (n:ℝ))
    (hLmax : L ≤ Lcap*Real.log (n:ℝ)) :
    w.generalScaleFactor k K L ≤ bandScaleConstant k K Ccap Fcap cFloor Ddepth Lcap*
      (Real.log (n:ℝ))^8 := by
  let t := Real.log (n:ℝ)
  let A := 4*(K+1)*Ccap*nearPairMomentConstant (k+1)^(((k+1:ℕ):ℝ)⁻¹)*(1+(K+1)*Ccap)^2
  let P := 4*K*Ccap*(projectionLpConstant k)^2*(Fcap^2/(cFloor/4)^2)
  have ht : 1 ≤ t := hlog
  have ht0 : 0 ≤ t := by linarith
  have hwC := w.C_nonneg
  have hn := nearPairMomentConstant_nonneg (k+1)
  have hC0 : 0 ≤ Ccap := w.C_nonneg.trans hC
  have hF0 : 0 ≤ w.F := by linarith [w.F_mass,w.C_nonneg]
  have hFp : 0 ≤ Fcap := hF0.trans hF
  have hK0 : 0 ≤ K := by linarith
  have hnear : w.generalNearScaleConstant k K ≤ A := by
    unfold PhysicalBandWindow.generalNearScaleConstant
    dsimp only [A]
    gcongr
  have hratio : w.F^2/(w.c₀/4)^2 ≤ Fcap^2/(cFloor/4)^2 := by
    gcongr
  have hfar : w.generalFarScaleConstant k K ≤ P*t^4 := by
    calc
      w.generalFarScaleConstant k K =
          (4*K*w.C*(projectionLpConstant k)^2)*(Real.log (n:ℝ))^4*(w.F^2/(w.c₀/4)^2) := rfl
      _ ≤ (4*K*Ccap*(projectionLpConstant k)^2)*(Real.log (n:ℝ))^4*(Fcap^2/(cFloor/4)^2) := by
        gcongr
      _ = P*t^4 := by dsimp only [P,t];ring
  have hA0 : 0 ≤ A := by dsimp only [A];positivity
  have hP0 : 0 ≤ P := by dsimp only [P];positivity
  have ht5 : 1 ≤ t^5 := one_le_pow₀ ht
  have hnear5 : w.generalNearScaleConstant k K ≤ A*t^5 :=
    hnear.trans (by nlinarith)
  have hfar5 : w.generalFarScaleConstant k K*L ≤ P*Lcap*t^5 := by
    calc
      _ ≤ (P*t^4)*(Lcap*t) := mul_le_mul hfar hLmax hL (by positivity)
      _ = _ := by ring
  have hdepth3 : (w.depth+3:ℕ)^3 ≤ (Ddepth+3)^3*t^3 := by
    have hd : (w.depth+3:ℕ) ≤ (Ddepth+3)*t := by
      push_cast
      nlinarith
    have hh := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (w.depth+3:ℕ)) hd 3
    simpa only [mul_pow] using hh
  calc
    w.generalScaleFactor k K L = (w.depth+3:ℕ)^3*(w.generalNearScaleConstant k K+w.generalFarScaleConstant k K*L) := rfl
    _ ≤ ((Ddepth+3)^3*t^3)*(A*t^5+P*Lcap*t^5) :=
      mul_le_mul hdepth3 (add_le_add hnear5 hfar5)
        (by unfold PhysicalBandWindow.generalNearScaleConstant PhysicalBandWindow.generalFarScaleConstant;positivity)
        (by positivity)
    _ = bandScaleConstant k K Ccap Fcap cFloor Ddepth Lcap*t^8 := by
      dsimp only [bandScaleConstant,A,P]
      ring

theorem selected_mass_gap {n N : ℕ} {steps : List (GaussianStep (FeatureIndex n))}
    (D : CutBlocks n steps N) {i : ℕ} (hi : i<N) :
    physicalCutMass 0 steps (D.central i)-physicalCutMass 0 steps (D.fork i)=2*D.quarter := by
  rw [CutBlocks.central,CutBlocks.fork,D.cut_mass _ (by omega),D.cut_mass _ (by omega)]
  push_cast
  ring

theorem bandScaleConstant_nonneg (k : ℕ) {K Ccap Fcap cFloor Ddepth Lcap : ℝ}
    (hK : 0 ≤ K) (hC : 0 ≤ Ccap) (hD : 0 ≤ Ddepth) (hL : 0 ≤ Lcap) :
    0 ≤ bandScaleConstant k K Ccap Fcap cFloor Ddepth Lcap := by
  have hn := nearPairMomentConstant_nonneg (k+1)
  unfold bandScaleConstant
  positivity

theorem eventually_physical_buffer_polynomial_native_scale (k : ℕ) (Bclock : ℝ)
    {kappa c1 delta R Q K Ccap Fcap cFloor Ddepth Lcap : ℝ}
    (hkappa : 0<kappa) (hR : 0 ≤ R) (hdelta : delta<kappa/8-c1)
    (hK : 1 ≤ K) (hCcap : 0 ≤ Ccap) (hcFloor : 0<cFloor)
    (hDepth : 0 ≤ Ddepth) (hLcap : 0 ≤ Lcap) :
    ∀ᶠn : ℕ in atTop,∀
      (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
      (q0 : FeatureIndex n→ℝ≥0) (xs : ℝ) (hxs : 0<xs)
      (w : PhysicalBandWindow n steps xs) (d : GaussianStep (FeatureIndex n)→ℝ≥0)
      (e L v : ℝ),
      (∀st∈steps,∀i:Fin n,st.2 (Sum.inl i)=d st)→
      physicalFieldDuration d steps ≤ Bclock→
      (∀s∈Ioc w.a w.b,w.D₀ ≤ physicalFieldDuration d (steps.take (radiusGridCut w.radius (s+w.η)))-
        physicalFieldDuration d (steps.take (radiusGridCut w.radius s)))→
      (∀r∈Icc (2*w.a) ((2:ℝ)^w.depth*w.b),w.D₀ ≤
        physicalFieldDuration d (steps.take (radiusGridCut w.radius r))-
        physicalFieldDuration d (steps.take (radiusGridCut w.radius (3*r/4))))→
      physicalRawRatio n (k+1) steps 0 xs (Measure.pi fun i=>gaussianReal 0 (q0 i)) id measurable_id ≤ Q→
      w.b ≤ K*w.a→w.mass ≤ K*w.C*w.a→0<e→0<L→0<w.A→
      w.η=(1/Real.sqrt (w.A*((n:ℝ)*e*w.a^4)))*w.a→
      (1/Real.sqrt (w.A*((n:ℝ)*e*w.a^4)))*w.a*e/L ≤ w.D₀→
      w.C ≤ Ccap→w.F ≤ Fcap→cFloor ≤ w.c₀→1 ≤ Real.log (n:ℝ)→
      (w.depth:ℝ) ≤ Ddepth*Real.log (n:ℝ)→L ≤ Lcap*Real.log (n:ℝ)→
      w.A/((n:ℝ)*e*w.a^4) ≤ R*(n:ℝ)^(-kappa)→
      (n:ℝ)^(-c1)*w.a ≤ w.mass→w.a ≤ v→
      physicalBufferCenteredNorm n steps q0 (physicalWindowWeight steps 0 w.selected)
        (2*(k+1):ℕ) ≤ (n:ℝ)^(-delta)*v := by
  have hD := bandScaleConstant_nonneg k (Fcap:=Fcap) (cFloor:=cFloor) (by linarith : 0 ≤ K) hCcap hDepth hLcap
  filter_upwards [eventually_physical_buffer_polynomial k Bclock hkappa hD hR hdelta] with n hn
  intro steps ha q0 xs hxs w d e L v hd hB hfirst hdyad hQ hb hm he hL hA heta hclock
    hC hF hc hlog hdepth hLmax hratio hmass hav
  have hscale := generalScaleFactor_le_log8 w k hK hC hF hcFloor hc hDepth hLcap hL.le hlog hdepth hLmax
  exact hn steps ha q0 xs hxs w d K e L v hd hB hfirst hdyad hQ hK hb hm he hL hA
    heta hclock hscale hratio hmass hav

end NativeStarBuffer
end OAI.SKFluctuations
