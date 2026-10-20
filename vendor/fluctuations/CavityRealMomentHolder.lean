module

public import CavityMomentAllocation

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy

 theorem finite_weighted_holder {A : Type*} [Fintype A] (w F G : A → ℝ)
    (hw : ∀ a, 0 ≤ w a) {p q : ℝ} (hpq : p.HolderConjugate q) :
    (∑ a, w a*|F a*G a|) ≤
      (∑ a, w a*|F a|^p)^(1/p)*(∑ a, w a*|G a|^q)^(1/q) := by
  let f := fun a => (w a)^(1/p)*|F a|
  let g := fun a => (w a)^(1/q)*|G a|
  have hf (a : A) : 0 ≤ f a := mul_nonneg (Real.rpow_nonneg (hw a) _) (abs_nonneg _)
  have hg (a : A) : 0 ≤ g a := mul_nonneg (Real.rpow_nonneg (hw a) _) (abs_nonneg _)
  have hfg (a : A) : f a*g a = w a*|F a*G a| := by
    dsimp [f,g]
    rw [abs_mul]
    calc
      _ = ((w a)^(1/p)*(w a)^(1/q))*(|F a| * |G a|) := by ring
      _ = (w a)^(1/p+1/q)*(|F a| * |G a|) := by
        rw [Real.rpow_add_of_nonneg (hw a) hpq.one_div_nonneg hpq.symm.one_div_nonneg]
      _ = _ := by simp only [one_div,hpq.inv_add_inv_eq_one,Real.rpow_one]
  have hfp (a : A) : (f a)^p = w a*|F a|^p := by
    dsimp [f]
    rw [Real.mul_rpow (Real.rpow_nonneg (hw a) _) (abs_nonneg _),
      ←Real.rpow_mul (hw a),div_mul_cancel₀ 1 hpq.ne_zero,Real.rpow_one]
  have hgq (a : A) : (g a)^q = w a*|G a|^q := by
    dsimp [g]
    rw [Real.mul_rpow (Real.rpow_nonneg (hw a) _) (abs_nonneg _),
      ←Real.rpow_mul (hw a),div_mul_cancel₀ 1 hpq.symm.ne_zero,Real.rpow_one]
  have H := Real.inner_le_Lp_mul_Lq_of_nonneg Finset.univ hpq (fun a _ => hf a) (fun a _ => hg a)
  simpa only [hfg,hfp,hgq] using H

 theorem finite_weighted_three_holder {A : Type*} [Fintype A] (w F G H : A → ℝ)
    (hw : ∀ a, 0 ≤ w a) {p : ℝ} (hp : 2 < p) :
    (∑ a, w a*|F a*G a*H a|) ≤
      (∑ a, w a*|F a|^p)^(1/p)*(∑ a, w a*|G a|^p)^(1/p)*
        (∑ a, w a*|H a|^(p/(p-2)))^((p-2)/p) := by
  have hp0 : 0 < p := by linarith
  have hpm : 0 < p-2 := by linarith
  have hconj : (p/2).HolderConjugate (p/(p-2)) := by
    rw [Real.holderConjugate_iff]
    constructor
    · linarith
    · field_simp
      <;> ring
  have h22 : (2:ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hpair := finite_weighted_holder w (fun a => |F a|^(p/2)) (fun a => |G a|^(p/2)) hw h22
  have hpp : p/2*2=p := by ring
  have hpairs : (∑ a, w a*|F a*G a|^(p/2)) ≤
      (∑ a, w a*|F a|^p)^(1/2:ℝ)*(∑ a, w a*|G a|^p)^(1/2:ℝ) := by
    simpa only [abs_mul,abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _),
      Real.mul_rpow (abs_nonneg _) (abs_nonneg _),←Real.rpow_mul (abs_nonneg _),hpp] using hpair
  have hpowe := Real.rpow_le_rpow
    (Finset.sum_nonneg fun a _ => mul_nonneg (hw a) (Real.rpow_nonneg (abs_nonneg _) _))
    hpairs hconj.one_div_nonneg
  have Hfirst := finite_weighted_holder w (fun a => F a*G a) H hw hconj
  apply Hfirst.trans
  have hHmom : 0 ≤ (∑ a, w a*|H a|^(p/(p-2)))^(1/(p/(p-2))) :=
    Real.rpow_nonneg (Finset.sum_nonneg fun a _ => mul_nonneg (hw a) (Real.rpow_nonneg (abs_nonneg _) _)) _
  have Hfinal := mul_le_mul_of_nonneg_right hpowe hHmom
  have hnorm : (1/2:ℝ)*(1/(p/2))=1/p := by field_simp
  have hinv : 1/(p/(p-2))=(p-2)/p := by field_simp
  have hnF : 0 ≤ ∑ a, w a*|F a|^p := Finset.sum_nonneg fun a _ =>
    mul_nonneg (hw a) (Real.rpow_nonneg (abs_nonneg _) _)
  have hnG : 0 ≤ ∑ a, w a*|G a|^p := Finset.sum_nonneg fun a _ =>
    mul_nonneg (hw a) (Real.rpow_nonneg (abs_nonneg _) _)
  rw [Real.mul_rpow (Real.rpow_nonneg hnF _) (Real.rpow_nonneg hnG _),
    ←Real.rpow_mul hnF,←Real.rpow_mul hnG,hnorm] at Hfinal
  simpa only [hinv] using Hfinal

end OAI.SKFluctuations.Hierarchy
