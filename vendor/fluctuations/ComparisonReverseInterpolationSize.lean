module

public import ComparisonConditionalOptimizedSize

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter
open scoped Topology
set_option maxHeartbeats 4800000

def comparisonReverseMoment (l : ℕ) (D Q y : ℝ) : ℝ :=
  D^(((l:ℝ)-2)/((l:ℝ)-1))*((2*Q)^(2*l)*y^l)^(1/((l:ℝ)-1))

theorem comparison_reverse_factorization {l : ℕ} (hl : 2<l)
    {D Q y : ℝ} (hD : 0<D) (hQ : 0<Q) (hy : 0<y) :
    comparisonReverseMoment l D Q y=
      (2*Q)^((2*(l:ℝ))/((l:ℝ)-1))*D*y*(y/D)^(1/((l:ℝ)-1)) := by
  have hlR : (2:ℝ)<l := by exact_mod_cast hl
  have hl1 : (l:ℝ)-1≠0 := by linarith
  have h1 : ((l:ℝ)-2)/((l:ℝ)-1)=1-1/((l:ℝ)-1) := by field_simp;ring
  have h2 : (l:ℝ)*(1/((l:ℝ)-1))=1+1/((l:ℝ)-1) := by field_simp;ring
  unfold comparisonReverseMoment
  rw [Real.mul_rpow (by positivity) (by positivity),←Real.rpow_natCast (2*Q) (2*l),
    ←Real.rpow_natCast y l,←Real.rpow_mul (by positivity : 0≤2*Q),←Real.rpow_mul hy.le,
    h1,h2,Real.rpow_sub hD,Real.rpow_add hy,Real.rpow_one,Real.rpow_one,
    Real.div_rpow hy.le hD.le]
  push_cast
  have he : (2*(l:ℝ))*(1/((l:ℝ)-1))=(2*(l:ℝ))/((l:ℝ)-1) := by ring
  rw [he]
  ring

theorem comparison_reverse_polynomial_loss {l : ℕ} (hl : 2<l)
    {N D Q y T eps : ℝ} (hN : 1≤N) (hD : 0<D) (hQ : 1≤Q) (hy : 0<y)
    (hratio : y/D≤N^T) (horder : T/((l:ℝ)-1)≤eps) :
    comparisonReverseMoment l D Q y≤(2*Q)^4*D*y*N^eps := by
  have hNp : 0<N := zero_lt_one.trans_le hN
  have hQp : 0<Q := zero_lt_one.trans_le hQ
  have hlR : (2:ℝ)<l := by exact_mod_cast hl
  have hl1 : 0<(l:ℝ)-1 := by linarith
  rw [comparison_reverse_factorization hl hD hQp hy]
  have hrawexp : (2*(l:ℝ))/((l:ℝ)-1)≤4 := (div_le_iff₀ hl1).mpr (by linarith)
  have hraw := Real.rpow_le_rpow_of_exponent_le (by linarith : 1≤2*Q) hrawexp
  norm_num at hraw
  have hratio' := Real.rpow_le_rpow (div_pos hy hD).le hratio (by positivity : 0≤1/((l:ℝ)-1))
  rw [←Real.rpow_mul hNp.le] at hratio'
  have hexp : T*(1/((l:ℝ)-1))≤eps := by simpa only [mul_one_div] using horder
  have hratio'' := hratio'.trans (Real.rpow_le_rpow_of_exponent_le hN hexp)
  have hh := mul_le_mul hraw hratio'' (Real.rpow_nonneg (div_pos hy hD).le _)
    (by positivity : 0≤(2*Q)^4)
  have ht := mul_le_mul_of_nonneg_right hh (mul_pos hD hy).le
  nlinarith

theorem exists_comparison_reverse_moment_order {T eps : ℝ} (heps : 0<eps) :
    ∃l : ℕ,2<l ∧ T/((l:ℝ)-1)≤eps := by
  obtain ⟨l,hl⟩ := exists_nat_gt (max (T/eps+1) 2)
  have hl2 : 2<l := by exact_mod_cast (lt_of_le_of_lt (le_max_right _ _) hl)
  refine ⟨l,hl2,?_⟩
  have hlR : (2:ℝ)<l := by exact_mod_cast hl2
  apply (div_le_iff₀ (by linarith : 0<(l:ℝ)-1)).mpr
  have hh : T/eps+1<(l:ℝ) := lt_of_le_of_lt (le_max_left _ _) hl
  have hm := (div_lt_iff₀ heps).mp (show T/eps<(l:ℝ)-1 by linarith)
  nlinarith

theorem comparison_reverse_ratio_of_scales {N D y a b : ℝ}
    (hN : 0<N) (hD : 0<D) (hy : 0≤y) (hlo : N^(-a)≤D) (hhi : y≤N^b) :
    y/D≤N^(a+b) := by
  have hh : y/D≤N^b/N^(-a) := by
    calc
      _≤N^b/D := div_le_div_of_nonneg_right hhi hD.le
      _≤N^b/N^(-a) := div_le_div_of_nonneg_left (Real.rpow_pos_of_pos hN b).le (Real.rpow_pos_of_pos hN (-a)) hlo
  have he : N^b/N^(-a)=N^(a+b) := by rw [←Real.rpow_sub hN];congr 1;ring
  exact hh.trans_eq he

end OAI.SKFluctuations.LaplaceWindowFormalization
