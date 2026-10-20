module

public import SKConstants.ScalarQueryGapRecursion
public import SKConstants.ScalarQueryTargetStability
import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal Topology BigOperators Matrix Matrix.Norms.L2Operator Classical
set_option backward.isDefEq.respectTransparency false
namespace SKConstants

def scalarMeshPathGap {H : ℝ≥0} {δ τ : ℕ → ℝ≥0} {n : ℕ}
    (s t : ScalarMeshPaperPast H δ τ n) : ℝ := ∑ i, ‖s.2 i-t.2 i‖

theorem scalarMeshPathGap_nonneg {H : ℝ≥0} {δ τ : ℕ → ℝ≥0} {n : ℕ}
    (s t : ScalarMeshPaperPast H δ τ n) : 0 ≤ scalarMeshPathGap s t := by
  exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)

theorem scalarMeshPathGap_coord_le {H : ℝ≥0} {δ τ : ℕ → ℝ≥0} {n : ℕ}
    (s t : ScalarMeshPaperPast H δ τ n) (i : Fin n) : ‖s.2 i-t.2 i‖ ≤ scalarMeshPathGap s t := by
  exact Finset.single_le_sum (f := fun j : Fin n => ‖s.2 j-t.2 j‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_univ i)

theorem scalarMeshPaperTrace_static (H : ℝ≥0) (δ τ : ℕ → ℝ≥0) (r n K : ℕ)
    (target : ℕ → ScalarMeshPaperPast H δ τ n → Fin n → ℝ)
    (s : GaussianProposal.PaperState r n K (ScalarMeshPaperPast H δ τ n))
    (z : GaussianProposal.StoppedNoise (Fin n) K) (j : Fin (K+1)) :
    (GaussianProposal.paperScalarPastTrace r n target (scalarMeshPaperUpdate H δ τ n K)
      K s z j).1=s.1.1 := by
  exact GaussianProposal.paperScalarPastTrace_invariant r n target
    (scalarMeshPaperUpdate H δ τ n K) Prod.fst (fun _ _ _ => rfl) K s z j

theorem scalarMeshPaperUpdate_pathGap_le (H : ℝ≥0) (δ τ : ℕ → ℝ≥0) (n K k : ℕ)
    (hh : 0<δ (K-k)) (s t : ScalarMeshPaperPast H δ τ n)
    (z w : EuclideanSpace ℝ (Fin n ⊕ Unit)) :
    scalarMeshPathGap (scalarMeshPaperUpdate H δ τ n K k s z)
      (scalarMeshPaperUpdate H δ τ n K k t w)≤
      scalarMeshPathGap s t+
      Real.sqrt (δ (K-k))*(n : ℝ)*‖WithLp.toLp 2 (fun i => z (.inl i)-w (.inl i))‖+
      3*∑ i, ‖s.1.2.2 (K-k) i-t.1.2.2 (K-k) i‖ := by
  let d : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i => z (.inl i)-w (.inl i))
  have hc (i : Fin n) : |z (.inl i)-w (.inl i)|≤‖d‖ := by
    simpa only [d,WithLp.ofLp_toLp,Real.norm_eq_abs] using PiLp.norm_apply_le d i
  calc
    _ ≤ ∑ i, (‖s.2 i-t.2 i‖+Real.sqrt (δ (K-k))*|z (.inl i)-w (.inl i)|+
        3*‖s.1.2.2 (K-k) i-t.1.2.2 (K-k) i‖) := by
      exact Finset.sum_le_sum (fun i _ =>
        scalarAppendQueryInterval_norm_difference_le H (δ (K-k)) hh _ _ _ _ _ _ _)
    _ ≤ ∑ i, (‖s.2 i-t.2 i‖+Real.sqrt (δ (K-k))*‖d‖+
        3*‖s.1.2.2 (K-k) i-t.1.2.2 (K-k) i‖) := by
      apply Finset.sum_le_sum
      intro i _
      gcongr
      exact hc i
    _ = _ := by
      simp only [Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_const,
        Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,scalarMeshPathGap]
      dsimp [d]
      ring

theorem scalarMeshPaperTarget_normalized_difference_le
    (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (m : ℝ → ℝ → ℝ) (hm : ∀ t, LipschitzWith 1 (m t))
    (scale : ℕ → ℝ) (H : ℝ≥0) (δ τ : ℕ → ℝ≥0) (n K k : ℕ)
    (hs : 0<scale (K-k)) (s t : ScalarMeshPaperPast H δ τ n)
    (c η C : ℝ) (hc : 0≤ c) (hη : 0≤η) (hC : 0≤ C)
    (hcN : c*Real.sqrt (n : ℝ)≤1)
    (hseed : ∀ i, |s.1.1 i-t.1.1 i|≤η)
    (hD : ∀ i, ‖s.1.2.1 i-t.1.2.1 i‖≤η)
    (hfC : scalarStieltjesPathBound f H≤ C) (hgC : scalarStieltjesPathBound g H≤ C) :
    ‖c • WithLp.toLp 2 (scalarMeshPaperTarget b f g hf hg m scale H δ τ n K k s)-
      c • WithLp.toLp 2 (scalarMeshPaperTarget b f g hf hg m scale H δ τ n K k t)‖≤
      4*((1+C)*η+C*scalarMeshPathGap s t)*Real.exp (b.rate*H)/scale (K-k) := by
  let R := 4*((1+C)*η+C*scalarMeshPathGap s t)*Real.exp (b.rate*H)/scale (K-k)
  have hG := scalarMeshPathGap_nonneg s t
  have hR : 0≤ R := by dsimp [R]; positivity
  have hcoord (i : Fin n) :
      |scalarMeshPaperTarget b f g hf hg m scale H δ τ n K k s i-
        scalarMeshPaperTarget b f g hf hg m scale H δ τ n K k t i|≤ R := by
    have h := scalarMeshPaperTarget_coordinate_difference_le b f g hf hg m hm scale H δ τ n K k hs s t i
    apply h.trans
    dsimp [R]
    apply div_le_div_of_nonneg_right _ hs.le
    have hB := scalarMeshPathGap_coord_le s t i
    have h1 := mul_le_mul_of_nonneg_right hfC (norm_nonneg (s.2 i-t.2 i))
    have h2 := mul_le_mul_of_nonneg_left hB hC
    have h3 := mul_le_mul_of_nonneg_right hgC (norm_nonneg (s.1.2.1 i-t.1.2.1 i))
    have h4 := mul_le_mul_of_nonneg_left (hD i) hC
    have hsum : |s.1.1 i-t.1.1 i|+
        scalarStieltjesPathBound f H*‖s.2 i-t.2 i‖+
        scalarStieltjesPathBound g H*‖s.1.2.1 i-t.1.2.1 i‖≤
        (1+C)*η+C*scalarMeshPathGap s t := by linarith [hseed i]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum (by norm_num)) (Real.exp_pos _).le
  let x : EuclideanSpace ℝ (Fin n) :=
    WithLp.toLp 2 (scalarMeshPaperTarget b f g hf hg m scale H δ τ n K k s)-
      WithLp.toLp 2 (scalarMeshPaperTarget b f g hf hg m scale H δ τ n K k t)
  have hx : ‖x‖≤ Real.sqrt (n : ℝ)*R :=
    euclidean_norm_le_sqrt_card_of_coord x R hR hcoord
  rw [←smul_sub,norm_smul,Real.norm_eq_abs,abs_of_nonneg hc]
  calc
    _ ≤ c*(Real.sqrt (n : ℝ)*R) := mul_le_mul_of_nonneg_left hx hc
    _ ≤ R := by nlinarith [mul_le_mul_of_nonneg_right hcN hR]
    _ = _ := rfl

def scalarQueryTargetGapFactor (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (H : ℝ≥0) (C sMin : ℝ) : ℝ := 4*(1+C)*Real.exp (b.rate*H)/sMin

theorem scalarMeshPaperTargetTrace_difference_le
    (b : SKConstantsOAI.ZeroTemperatureSK.BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (m : ℝ → ℝ → ℝ) (hm : ∀ t, LipschitzWith 1 (m t))
    (scale : ℕ → ℝ) (H : ℝ≥0) (δ τ : ℕ → ℝ≥0) (r K : ℕ)
    (s t : ScalarMeshPaperPast H δ τ (r+K))
    (z w : GaussianProposal.StoppedNoise (Fin (r+K)) K)
    (c η C sMin : ℝ) (hc : 0≤ c) (hη : 0≤η) (hC : 0≤ C) (hsMin : 0<sMin)
    (hcN : c*Real.sqrt (r+K : ℝ)≤1)
    (hseed : ∀ i, |s.1.1 i-t.1.1 i|≤η)
    (hD : ∀ i, ‖s.1.2.1 i-t.1.2.1 i‖≤η)
    (hfC : scalarStieltjesPathBound f H≤ C) (hgC : scalarStieltjesPathBound g H≤ C)
    (j : Fin K) (hscale : sMin≤ scale (j.val+1)) :
    let target := scalarMeshPaperTarget b f g hf hg m scale H δ τ (r+K) K
    let update := scalarMeshPaperUpdate H δ τ (r+K) K
    ‖c • WithLp.toLp 2 (GaussianProposal.paperTargetTrace r (r+K) target update K (s,1) z j)-
      c • WithLp.toLp 2 (GaussianProposal.paperTargetTrace r (r+K) target update K (t,1) w j)‖≤
      scalarQueryTargetGapFactor b H C sMin*(η+
        scalarMeshPathGap (GaussianProposal.paperScalarPastTrace r (r+K) target update K (s,1) z j.castSucc)
          (GaussianProposal.paperScalarPastTrace r (r+K) target update K (t,1) w j.castSucc)) := by
  dsimp only
  let target := scalarMeshPaperTarget b f g hf hg m scale H δ τ (r+K) K
  let update := scalarMeshPaperUpdate H δ τ (r+K) K
  let S := GaussianProposal.paperScalarPastTrace r (r+K) target update K (s,1) z j.castSucc
  let T := GaussianProposal.paperScalarPastTrace r (r+K) target update K (t,1) w j.castSucc
  have hindex : K-(K-1-j.val)=j.val+1 := by omega
  have hs : 0<scale (K-(K-1-j.val)) := by rw [hindex]; exact hsMin.trans_le hscale
  have hS : S.1=s.1 := scalarMeshPaperTrace_static H δ τ r (r+K) K target (s,1) z j.castSucc
  have hT : T.1=t.1 := scalarMeshPaperTrace_static H δ τ r (r+K) K target (t,1) w j.castSucc
  have hh := scalarMeshPaperTarget_normalized_difference_le b f g hf hg m hm scale H δ τ
    (r+K) K (K-1-j.val) hs S T c η C hc hη hC (by exact_mod_cast hcN)
    (by intro i; rw [hS,hT]; exact hseed i)
    (by intro i; rw [hS,hT]; exact hD i) hfC hgC
  rw [GaussianProposal.paperTargetTrace_eq_current_state,
    GaussianProposal.paperTargetTrace_eq_current_state]
  apply hh.trans
  rw [hindex]
  have hG := scalarMeshPathGap_nonneg S T
  have hsum : (1+C)*η+C*scalarMeshPathGap S T≤(1+C)*(η+scalarMeshPathGap S T) := by nlinarith
  have hnum : 4*((1+C)*η+C*scalarMeshPathGap S T)*Real.exp (b.rate*H)≤
      4*(1+C)*Real.exp (b.rate*H)*(η+scalarMeshPathGap S T) := by
    nlinarith [mul_le_mul_of_nonneg_right hsum (Real.exp_pos (b.rate*H)).le]
  have hn : 0≤4*((1+C)*η+C*scalarMeshPathGap S T)*Real.exp (b.rate*H) := by positivity
  calc
    _ ≤ (4*((1+C)*η+C*scalarMeshPathGap S T)*Real.exp (b.rate*H))/sMin :=
      div_le_div_of_nonneg_left hn hsMin (by simpa only [hindex] using hscale)
    _ ≤ (4*(1+C)*Real.exp (b.rate*H)*(η+scalarMeshPathGap S T))/sMin :=
      div_le_div_of_nonneg_right hnum hsMin.le
    _ = _ := by dsimp [scalarQueryTargetGapFactor,S,T]; ring

end SKConstants
