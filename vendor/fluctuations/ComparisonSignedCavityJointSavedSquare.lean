module

public import ComparisonSignedCavityJointForestHolder
public import ComparisonSignedCavityActualMixedStarProjectionPowers

@[expose] public section

noncomputable section
set_option maxHeartbeats 10000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity

theorem jointFiniteExpect_saved_square_mixed
    {P S : Type} [MeasurableSpace P] [Fintype S]
    (μ : Measure P) [IsFiniteMeasure μ] (w : P→S→ℝ)
    (hw : ∀z s,0 ≤ w z s) (hsum : ∀z,∑s,w z s=1)
    (hwm : ∀s,Measurable (fun z=>w z s))
    (Z : S→ℝ) (A Y : P→S→ℝ)
    (hA : ∀s,Measurable (fun z=>A z s)) (hY : ∀s,Measurable (fun z=>Y z s))
    (CA CY : ℝ) (_hCY : 0 ≤ CY)
    (hAb : ∀z s,|A z s| ≤ CA) (hYb : ∀z s,|Y z s| ≤ CY)
    {B H R : ℝ} (_hB : 0 ≤ B) (hH : 0 ≤ H) (hR : 0 ≤ R)
    (hZ4 : jointFiniteExpect μ w (fun _ s=>Z s^4) ≤ H^4)
    (hA4 : jointFiniteExpect μ w (fun z s=>A z s^4) ≤ B^4)
    (hY4 : jointFiniteExpect μ w (fun z s=>Y z s^4) ≤ R^4) :
    |jointFiniteExpect μ w (fun z s=>A z s^2*Z s*Y z s)| ≤ B^2*H*R := by
  let CZ:=∑s,|Z s|
  have hCZ : 0 ≤ CZ:=Finset.sum_nonneg fun _ _=>abs_nonneg _
  have hZb (s) : |Z s| ≤ CZ:=Finset.single_le_sum (f:=fun s=>|Z s|) (fun _ _=>abs_nonneg _) (Finset.mem_univ s)
  have hZYb (z s) : |Z s*Y z s| ≤ CZ*CY := by
    rw [abs_mul]
    exact mul_le_mul (hZb s) (hYb z s) (abs_nonneg _) hCZ
  have HZY:=jointFiniteExpect_mul_sq_le μ w hw hsum hwm
    (fun _ s=>Z s^2) (fun z s=>Y z s^2)
    (fun _=>measurable_const) (fun s=>(hY s).pow_const 2) (CZ^2) (CY^2) (sq_nonneg _)
    (fun _ s=>by simpa only [abs_pow] using pow_le_pow_left₀ (abs_nonneg _) (hZb s) 2)
    (fun z s=>by simpa only [abs_pow] using pow_le_pow_left₀ (abs_nonneg _) (hYb z s) 2)
  have Hout:=jointFiniteExpect_mul_sq_le μ w hw hsum hwm
    (fun z s=>A z s^2) (fun z s=>Z s*Y z s)
    (fun s=>(hA s).pow_const 2) (fun s=>measurable_const.mul (hY s))
    (CA^2) (CZ*CY) (sq_nonneg _)
    (fun z s=>by simpa only [abs_pow] using pow_le_pow_left₀ (abs_nonneg _) (hAb z s) 2) hZYb
  have heZ : (fun (_:P) s=>(Z s^2)^2)=(fun _ s=>Z s^4):=by funext z s;ring
  have heY : (fun z s=>(Y z s^2)^2)=(fun z s=>Y z s^4):=by funext z s;ring
  have heA : (fun z s=>(A z s^2)^2)=(fun z s=>A z s^4):=by funext z s;ring
  have heZY : (fun z s=>(Z s*Y z s)^2)=(fun z s=>Z s^2*Y z s^2):=by funext z s;ring
  have heOut : (fun z s=>A z s^2*(Z s*Y z s))=(fun z s=>A z s^2*Z s*Y z s):=by funext z s;ring
  rw [heZ,heY] at HZY
  rw [heA,heZY,heOut] at Hout
  have hYn:=jointFiniteExpect_nonneg μ w hw (fun z s=>Y z s^4) (fun _ _=>by positivity)
  have hZYn:=jointFiniteExpect_nonneg μ w hw (fun z s=>Z s^2*Y z s^2) (fun _ _=>by positivity)
  have HZYsq:=HZY.trans (mul_le_mul hZ4 hY4 hYn (by positivity))
  have HZYbound : jointFiniteExpect μ w (fun z s=>Z s^2*Y z s^2) ≤ (H*R)^2 := by
    apply (sq_le_sq₀ hZYn (sq_nonneg _)).mp
    convert HZYsq using 1
    ring
  have Hfinal:=Hout.trans (mul_le_mul hA4 HZYbound hZYn (by positivity))
  apply (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ B^2*H*R)).mp
  rw [sq_abs]
  convert Hfinal using 1
  ring

end OAI.SKFluctuations.Cavity
