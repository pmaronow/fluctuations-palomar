module

public import SKConstants.ScalarPicardPathStability
public import SKConstants.ScalarQueryPathStability
import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology BigOperators
set_option backward.isDefEq.respectTransparency false
namespace SKConstants

theorem euclidean_norm_le_sqrt_card_of_coord {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) (C : ℝ) (hC : 0≤C)
    (hx : ∀ i, |x i|≤C) : ‖x‖≤Real.sqrt (n : ℝ)*C := by
  have hs : ‖x‖^2≤(n : ℝ)*C^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ i : Fin n, C^2 := Finset.sum_le_sum (fun i hi => by
        have h := hx i
        nlinarith [sq_abs (x i),abs_nonneg (x i)])
      _ = _ := by simp
  have he : (Real.sqrt (n : ℝ)*C)^2=(n : ℝ)*C^2 := by
    rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg n)]
  nlinarith [norm_nonneg x,mul_nonneg (Real.sqrt_nonneg (n : ℝ)) hC]

theorem scalarMeshPaperTarget_coordinate_difference_le
    (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (m : ℝ → ℝ → ℝ) (hm : ∀ t, LipschitzWith 1 (m t))
    (scale : ℕ → ℝ) (H : ℝ≥0) (δ τ : ℕ → ℝ≥0) (n K k : ℕ)
    (hs : 0<scale (K-k)) (s t : ScalarMeshPaperPast H δ τ n) (i : Fin n) :
    |scalarMeshPaperTarget b f g hf hg m scale H δ τ n K k s i-
        scalarMeshPaperTarget b f g hf hg m scale H δ τ n K k t i|≤
      (4*(|s.1.1 i-t.1.1 i|+
        scalarStieltjesPathBound f H*‖s.2 i-t.2 i‖+
        scalarStieltjesPathBound g H*‖s.1.2.1 i-t.1.2.1 i‖)*
        Real.exp (b.rate*H))/scale (K-k) := by
  let Y := scalarMeshPaperObservation b f g hf hg H δ τ n s i
  let Z := scalarMeshPaperObservation b f g hf hg H δ τ n t i
  let a := scalarMeshPaperQueryTime τ K (k+1)
  let v := scalarMeshPaperQueryTime τ K k
  let E := |s.1.1 i-t.1.1 i|+
    scalarStieltjesPathBound f H*‖s.2 i-t.2 i‖+
    scalarStieltjesPathBound g H*‖s.1.2.1 i-t.1.2.1 i‖
  have hY : ‖Y-Z‖≤2*E*Real.exp (b.rate*H) :=
    scalarTwoDriverPicardPath_norm_difference_le b f g hf hg H _ _ _ _ _ _
  have hl (u : ℝ) :
      |m u (Y (projIcc 0 (H : ℝ) H.coe_nonneg u))-
        m u (Z (projIcc 0 (H : ℝ) H.coe_nonneg u))|≤‖Y-Z‖ := by
    have h := (hm u).dist_le_mul (Y (projIcc 0 (H : ℝ) H.coe_nonneg u))
      (Z (projIcc 0 (H : ℝ) H.coe_nonneg u))
    simp only [Real.dist_eq,NNReal.coe_one,one_mul] at h
    exact h.trans ((Y-Z).norm_coe_le_norm _)
  have hv := hl v
  have ha := hl a
  have he : scalarMeshPaperTarget b f g hf hg m scale H δ τ n K k s i-
      scalarMeshPaperTarget b f g hf hg m scale H δ τ n K k t i =
      ((m v (Y (projIcc 0 (H : ℝ) H.coe_nonneg v))-
        m v (Z (projIcc 0 (H : ℝ) H.coe_nonneg v)))-
       (m a (Y (projIcc 0 (H : ℝ) H.coe_nonneg a))-
        m a (Z (projIcc 0 (H : ℝ) H.coe_nonneg a))))/scale (K-k) := by
    dsimp [scalarMeshPaperTarget,Y,Z,v,a]
    ring
  rw [he,abs_div,abs_of_pos hs]
  apply div_le_div_of_nonneg_right _ hs.le
  have hh := norm_sub_le
    (m v (Y (projIcc 0 (H : ℝ) H.coe_nonneg v))-
      m v (Z (projIcc 0 (H : ℝ) H.coe_nonneg v)))
    (m a (Y (projIcc 0 (H : ℝ) H.coe_nonneg a))-
      m a (Z (projIcc 0 (H : ℝ) H.coe_nonneg a)))
  simp only [Real.norm_eq_abs] at hh
  change _≤4*E*Real.exp (b.rate*H)
  nlinarith

end SKConstants
