module

public import SKConstants.Completion.N19n.Stability
public import SKConstants.Completion.N19n.CommonGram
import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open SKConstantsOAI.ZeroTemperatureSK
open scoped NNReal Topology Matrix.Norms.L2Operator
namespace SKConstants.Completion.N19n
open GaussianProposal Blueprint Blueprint4 N19 LBase
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {Ω : Type} [MeasurableSpace Ω]

theorem coarse_lowerScale_eventually (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (hf : FineExponents p) (hb : CoarseCommon p) :
    ∀ᶠ n : ℕ in atTop,
      (curvatureLowerConstant β * Real.exp (-1)) * (n : ℝ)^(-(p.a+p.b)) ≤
        Real.sqrt ((meshSize p.a n : ℝ) * actualParisiFullSusceptibilitySquareExpected W β
          (readoutTime p.a p.b n)) := by
  have ha : 0 < p.a := lt_trans hf.2.2.1 hf.2.2.2.1
  have hba : p.b/4 ≤ p.a := by linarith [hf.1, hb.2.1]
  have ha1 : p.a < 1 := by linarith [hf.2.2.1, hf.2.2.2.2.2]
  filter_upwards [schedule_eventually p.a p.b hb.1 hba ha1] with n hs
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hH := (horizon_bounds p.a p.b hb.1 hba n hs.1 hs.2.1).2
  change (readoutTime p.a p.b n : ℝ) ≤ p.b * Real.log n + 1 at hH
  have hδ : (meshSize p.a n : ℝ) = (n : ℝ)^(-p.a) := by
    exact Real.coe_toNNReal _ (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hδ1 : (meshSize p.a n : ℝ) ≤ 1 := by
    rw [hδ]
    exact Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith)
  have hprof := actualParisiFullSusceptibilitySquareExpected_bounds W β (readoutTime p.a p.b n)
  have hprod : (meshSize p.a n : ℝ) *
      actualParisiFullSusceptibilitySquareExpected W β (readoutTime p.a p.b n) ≤ 1 :=
    (mul_le_mul hδ1 hprof.2 hprof.1 (by norm_num)).trans (by norm_num)
  have hroot : (meshSize p.a n : ℝ) *
      actualParisiFullSusceptibilitySquareExpected W β (readoutTime p.a p.b n) ≤
      Real.sqrt ((meshSize p.a n : ℝ) *
        actualParisiFullSusceptibilitySquareExpected W β (readoutTime p.a p.b n)) := by
    exact Real.le_sqrt_of_sq_le (by nlinarith [mul_nonneg (meshSize p.a n).coe_nonneg hprof.1])
  have he : Real.exp (-1) * (n : ℝ)^(-p.b) ≤ Real.exp (-(readoutTime p.a p.b n : ℝ)) := by
    rw [Real.rpow_def_of_pos hn0, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have hp := (mul_le_mul_of_nonneg_left he (curvatureLowerConstant_pos β hβ).le).trans
    (actual_square_profile_exp_lower W β hβ _ (readoutTime p.a p.b n).coe_nonneg)
  calc
    _ = (meshSize p.a n : ℝ) *
        (curvatureLowerConstant β * (Real.exp (-1) * (n : ℝ)^(-p.b))) := by
      rw [hδ, show -(p.a+p.b) = -p.a + -p.b by ring, Real.rpow_add hn0]
      ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left hp (meshSize p.a n).coe_nonneg).trans hroot

theorem coarse_incrementScale_eventually (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (hf : FineExponents p) (hb : CoarseCommon p) :
    ∀ᶠ n : ℕ in atTop, ∀ j : Fin (queryCount p.a p.b n),
      (curvatureLowerConstant β * Real.exp (-1)) * (n : ℝ)^(-(p.a+p.b)) ≤
        scalarMeshPaperIncrementScale (actualParisiFullSusceptibilitySquareExpected W β)
          (growingQueryTime (meshSize p.a n)) (j.val+1) := by
  filter_upwards [coarse_lowerScale_eventually W β hβ p hf hb,
    eventually_ge_atTop (1 : ℕ)] with n hn hn1 j
  exact hn.trans (growing_incrementScale_lower W β hβ _
    (paperGrowingQueryMeshSize_pos p.a n (by omega)) _ j)

theorem coarse_picard_eventually (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (hf : FineExponents p) (hb : CoarseCommon p) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp ((actualParisiFullScalarDrift β).rate * (readoutTime p.a p.b n)) ≤
        Real.exp (actualParisiFullScalarDrift β).rate *
          (n : ℝ)^((actualParisiFullScalarDrift β).rate * p.b) := by
  have hba : p.b/4 ≤ p.a := by linarith [hf.1, hb.2.1]
  have ha1 : p.a < 1 := by linarith [hf.2.2.1, hf.2.2.2.2.2]
  filter_upwards [schedule_eventually p.a p.b hb.1 hba ha1] with n hs
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hH := (horizon_bounds p.a p.b hb.1 hba n hs.1 hs.2.1).2
  change (readoutTime p.a p.b n : ℝ) ≤ p.b * Real.log n + 1 at hH
  rw [Real.rpow_def_of_pos hn0, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [(actualParisiFullScalarDrift β).rate_pos]

theorem coupledGapFactor_le_polynomial (n q : ℕ) (L A : ℝ)
    (hn : 1 ≤ n) (hq : q ≤ n) (hL : 0 ≤ L) (hA : 1 ≤ A) :
    coupledScalarQueryGapFactor n q L A ≤ 300 * (n : ℝ)^3 * A * (L+1) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hqR : (q : ℝ) ≤ n := by exact_mod_cast hq
  have hs : Real.sqrt (n : ℝ) ≤ n :=
    Real.sqrt_le_iff.mpr ⟨Nat.cast_nonneg n, by nlinarith [sq_nonneg ((n : ℝ)-1)]⟩
  have hE : queryEndpointGapFactor n A ≤ 8 * (n : ℝ) * A := by
    unfold queryEndpointGapFactor
    have hnA : (n : ℝ) ≤ n*A := le_mul_of_one_le_right (by positivity) hA
    have hAn : A ≤ n*A := le_mul_of_one_le_left (by linarith) hnR
    have hrA := mul_le_mul_of_nonneg_right hs (by linarith : 0 ≤ A)
    nlinarith
  have hD : queryDirectionGapFactor q L ≤ 24 * (n : ℝ) * (L+1) := by
    unfold queryDirectionGapFactor
    have hqL := mul_le_mul_of_nonneg_right hqR hL
    have hnL := le_mul_of_one_le_left hL hnR
    nlinarith
  have hE0 : 0 ≤ queryEndpointGapFactor n A := by unfold queryEndpointGapFactor; positivity
  have hD0 : 0 ≤ queryDirectionGapFactor q L := by unfold queryDirectionGapFactor; positivity
  have hnE := mul_le_mul_of_nonneg_left hE (Nat.cast_nonneg n)
  have hm := mul_le_mul (add_le_add_right hnE 1) hD hD0 (by positivity)
  have hbase : 1 ≤ (n : ℝ)^2*A := by nlinarith [sq_nonneg ((n : ℝ)-1)]
  have hnl : 1 ≤ (n : ℝ)*(L+1) := by nlinarith
  unfold coupledScalarQueryGapFactor
  nlinarith [mul_nonneg (show 0 ≤ (n : ℝ)^2*A by positivity)
    (show 0 ≤ (n : ℝ)*(L+1)-1 by linarith)]

theorem coarse_factors_eventually_polynomial (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (hf : FineExponents p) (hb : CoarseCommon p) (u : ℝ) (hu : 0 ≤ u) :
    ∃ k : ℝ, 0 < k ∧ ∀ᶠ n : ℕ in atTop,
      actualReplayGapFactor W β (meshSize p.a n) (rankCount p.a p.b n)
        (queryCount p.a p.b n) ((n : ℝ)^u) ≤ (n : ℝ)^k ∧
      Real.exp ((actualParisiFullScalarDrift β).rate * (readoutTime p.a p.b n)) ≤ (n : ℝ)^k := by
  let R := (actualParisiFullScalarDrift β).rate
  let c := curvatureLowerConstant β * Real.exp (-1)
  let v := R*p.b + (p.a+p.b)
  let C := 12 * Real.exp R / c
  have hR : 0 < R := (actualParisiFullScalarDrift β).rate_pos
  have hc : 0 < c := by dsimp [c]; exact mul_pos (curvatureLowerConstant_pos β hβ) (Real.exp_pos _)
  have hC : 0 < C := by dsimp [C]; positivity
  have ha : 0 < p.a := lt_trans hf.2.2.1 hf.2.2.2.1
  have hv : 0 ≤ v := add_nonneg (mul_nonneg hR.le hb.1.le) (add_nonneg ha.le hb.1.le)
  let k := max (4+u+v) (R*p.b+1)
  have hk : 0 < k := (by dsimp [k]; apply lt_max_of_lt_left; positivity)
  refine ⟨k, hk, ?_⟩
  filter_upwards [coarse_lowerScale_eventually W β hβ p hf hb,
    coarse_picard_eventually W β hβ p hf hb,
    constant_rpow_le_small_rpow (3+u+v) (4+u+v) (300*(C+1)) 1
      (by linarith) (by positivity) (by norm_num),
    constant_rpow_le_small_rpow (R*p.b) (R*p.b+1) (Real.exp R) 1
      (by linarith) (Real.exp_pos _).le (by norm_num),
    eventually_ge_atTop (1 : ℕ)] with n hs he h300 hExp hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  let S := Real.sqrt ((meshSize p.a n : ℝ) * actualParisiFullSusceptibilitySquareExpected W β
    (readoutTime p.a p.b n))
  have hS0 : 0 < S := growing_incrementScale_lower_pos W β hβ _
    (paperGrowingQueryMeshSize_pos p.a n (by omega)) _
  have hlow : 0 < c * (n : ℝ)^(-(p.a+p.b)) := by positivity
  have hi : 1/S ≤ (1/c) * (n : ℝ)^(p.a+p.b) := by
    calc
      _ ≤ 1 / (c * (n : ℝ)^(-(p.a+p.b))) := one_div_le_one_div_of_le hlow hs
      _ = _ := by rw [one_div, mul_inv_rev, Real.rpow_neg hn0.le, inv_inv]; ring
  let L := scalarQueryTargetGapFactor (actualParisiFullScalarDrift β)
    (readoutTime p.a p.b n) 2 S
  have hL0 : 0 ≤ L := by dsimp [L, scalarQueryTargetGapFactor]; positivity
  have hL : L ≤ C * (n : ℝ)^v := by
    calc
      _ = 12 * Real.exp (R * (readoutTime p.a p.b n)) * (1/S) := by
        dsimp [L, scalarQueryTargetGapFactor, R]; ring
      _ ≤ 12 * (Real.exp R * (n : ℝ)^(R*p.b)) * ((1/c)*(n : ℝ)^(p.a+p.b)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left he (by norm_num)) hi (by positivity) (by positivity)
      _ = _ := by simp only [C, v, Real.rpow_add hn0]; ring
  have hF : actualReplayGapFactor W β (meshSize p.a n) (rankCount p.a p.b n)
      (queryCount p.a p.b n) ((n : ℝ)^u) ≤ 300*(C+1)*(n : ℝ)^(3+u+v) := by
    have hA : 1 ≤ (n : ℝ)^u := Real.one_le_rpow hnR hu
    have hvpow : 1 ≤ (n : ℝ)^v := Real.one_le_rpow hnR hv
    have hstep := coupledGapFactor_le_polynomial n (queryCount p.a p.b n) L ((n : ℝ)^u)
      hn (by unfold queryCount; exact min_le_right _ _) hL0 hA
    have heq : actualReplayGapFactor W β (meshSize p.a n) (rankCount p.a p.b n)
        (queryCount p.a p.b n) ((n : ℝ)^u) =
        coupledScalarQueryGapFactor n (queryCount p.a p.b n) L ((n : ℝ)^u) := by
      unfold actualReplayGapFactor
      rw [rankCount_add]
      rfl
    rw [heq]
    calc
      _ ≤ 300*(n : ℝ)^3*(n : ℝ)^u*(L+1) := hstep
      _ ≤ 300*(n : ℝ)^3*(n : ℝ)^u*((C+1)*(n : ℝ)^v) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith
      _ = _ := by
        simp only [Real.rpow_add hn0, Real.rpow_ofNat]
        ring
  have h300' : 300*(C+1)*(n : ℝ)^(3+u+v) ≤ (n : ℝ)^(4+u+v) := by
    simpa only [one_mul] using h300
  have hExp' : Real.exp R*(n : ℝ)^(R*p.b) ≤ (n : ℝ)^(R*p.b+1) := by
    simpa only [one_mul] using hExp
  constructor
  · exact hF.trans (h300'.trans
      (Real.rpow_le_rpow_of_exponent_le hnR (le_max_left _ _)))
  · exact he.trans (hExp'.trans
      (Real.rpow_le_rpow_of_exponent_le hnR (le_max_right _ _)))

end SKConstants.Completion.N19n
