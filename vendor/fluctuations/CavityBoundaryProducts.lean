module

public import CavityThreeLeafPruning
public import CavityHeterogeneousPairMoments
public import CavityPhysicalFreshTooth

@[expose] public section

noncomputable section
set_option maxHeartbeats 1500000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy

def boundaryAffineFactor (n : ℕ) (h b : ℝ) (c d : Spin n) : ℝ :=
  h+b*orderedOverlap n c d

def boundaryAffineProduct (n : ℕ) {a : ℕ}
    (h b : Fin a → ℝ) (c d : Fin a → Spin n) : ℝ :=
  ∏ i, boundaryAffineFactor n (h i) (b i) (c i) (d i)

def boundaryTelescopingFactor {a : ℕ} (f g : Fin a → ℝ) (i j : Fin a) : ℝ :=
  if j = i then f j-g j else if j < i then g j else f j

theorem boundary_product_resampling_telescopes {a : ℕ} (f g : Fin a → ℝ) :
    (∏ i, f i)-(∏ i, g i) =
      ∑ i, ∏ j, boundaryTelescopingFactor f g i j := by
  induction a with
  | zero => simp
  | succ a ih =>
    let ft : Fin a → ℝ := fun j => f j.succ
    let gt : Fin a → ℝ := fun j => g j.succ
    have hzero : (∏ j, boundaryTelescopingFactor f g 0 j) =
        (f 0-g 0)*(∏ j, ft j) := by
      rw [Fin.prod_univ_succ]
      simp [boundaryTelescopingFactor,ft]
    have hsucc (i : Fin a) : (∏ j, boundaryTelescopingFactor f g i.succ j) =
        g 0*(∏ j, boundaryTelescopingFactor ft gt i j) := by
      rw [Fin.prod_univ_succ]
      have hne : (0 : Fin (a+1)) ≠ i.succ := by intro h; have := congrArg Fin.val h; simp at this
      simp [boundaryTelescopingFactor,ft,gt,hne]
    rw [Fin.prod_univ_succ,Fin.prod_univ_succ,Fin.sum_univ_succ,hzero]
    simp_rw [hsucc]
    rw [← Finset.mul_sum,← ih ft gt]
    dsimp only [ft,gt]
    ring

theorem boundary_affine_product_resampling (n : ℕ) {a : ℕ}
    (h b : Fin a → ℝ) (c c' d : Fin a → Spin n) :
    boundaryAffineProduct n h b c d-boundaryAffineProduct n h b c' d =
      ∑ i, ∏ j, if j = i then
        b j*(orderedOverlap n (c j) (d j)-orderedOverlap n (c' j) (d j))
      else if j < i then boundaryAffineFactor n (h j) (b j) (c' j) (d j)
      else boundaryAffineFactor n (h j) (b j) (c j) (d j) := by
  rw [boundaryAffineProduct,boundaryAffineProduct,
    boundary_product_resampling_telescopes]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.prod_congr rfl
  intro j _
  by_cases he : j = i
  · simp only [boundaryTelescopingFactor,if_pos he,boundaryAffineFactor]
    ring
  · simp only [boundaryTelescopingFactor,if_neg he]

theorem finite_weighted_product_scales {A : Type} [Fintype A] {a : ℕ}
    (ha : 0<a) (w : A → ℝ) (F : Fin a → A → ℝ) (hw : ∀ σ, 0≤w σ)
    (rho : Fin a → ℝ) (hrho : ∀ i, 0<rho i)
    (hm : ∀ i, (∑ σ, w σ*|F i σ|^a) ≤ (rho i)^a) :
    |∑ σ, w σ*(∏ i, F i σ)| ≤ ∏ i, rho i := by
  let Fn : Fin a → A → ℝ := fun i σ => F i σ/rho i
  have hn (i : Fin a) : (∑ σ, w σ*|Fn i σ|^a) ≤ (1:ℝ)^a := by
    dsimp [Fn]
    simp only [abs_div,abs_of_pos (hrho i),div_pow,←mul_div_assoc,←Finset.sum_div,one_pow]
    exact (div_le_one (pow_pos (hrho i) _)).2 (hm i)
  have H := finite_weighted_product_abs_le ha w (fun _ => 1) Fn hw
    (by norm_num : (0:ℝ)≤1) (fun _ => by norm_num) hn
  simp only [mul_one,one_mul,one_pow] at H
  let R := ∏ i, rho i
  have hR : 0<R := Finset.prod_pos fun i _ => hrho i
  have he : (∑ σ, w σ*(∏ i, F i σ)) = R*(∑ σ, w σ*(∏ i, Fn i σ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    simp only [Fn,Finset.prod_div_distrib]
    change w σ*(∏ i, F i σ)=R*(w σ*((∏ i, F i σ)/R))
    field_simp [hR.ne']
  rw [he,abs_mul,abs_of_pos hR]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left H hR.le

end OAI.SKFluctuations.Cavity
