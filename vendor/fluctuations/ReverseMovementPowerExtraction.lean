module

public import Mathlib

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
namespace OAI.SKFluctuations.Hierarchy

theorem reverse_movement_power_extraction {N Δ A Q y ell p a eps₀ : ℝ}
    (hN : 0<N) (hΔ : 0≤Δ) (hA : 0<A) (hQ : 0<Q) (hy : 0<y) (hell : 0<ell)
    (hp : 2<p) (hmean : Δ≤A*ell) (hraw : Q≤N^eps₀)
    (hyN : y≤N^a) (hellN : N^(-10:ℝ)≤ell) :
    Δ^((p-2)/(p-1))*((2*Q)^(2*p)*y^p)^(1/(p-1))≤
      ((2:ℝ)^(2*p/(p-1))*A^((p-2)/(p-1)))*
        N^(2*p*eps₀/(p-1)+(a+10)/(p-1))*y*ell := by
  let β : ℝ := 1/(p-1)
  let α : ℝ := (p-2)/(p-1)
  have hpm : 0<p-1 := by linarith
  have hβ : 0<β := one_div_pos.mpr hpm
  have hα : 0≤α := div_nonneg (by linarith) hpm.le
  have hαid : α=1-β := by dsimp [α,β]; field_simp; ring
  have hγid : p*β=1+β := by dsimp [β]; field_simp; ring
  have hc : 0≤(2:ℝ)^(2*p*β)*A^α := by positivity
  have hr : y/ell≤N^(a+10) := by
    calc
      _≤N^a/N^(-10:ℝ) := div_le_div₀ (Real.rpow_nonneg hN.le _) hyN
        (Real.rpow_pos_of_pos hN _) hellN
      _=N^(a+10) := by rw [←Real.rpow_sub hN]; congr 1; ring
  have hrp := Real.rpow_le_rpow (div_nonneg hy.le hell.le) hr hβ.le
  rw [←Real.rpow_mul hN.le] at hrp
  have hQp := Real.rpow_le_rpow hQ.le hraw (by dsimp [β]; positivity : 0≤2*p*β)
  rw [←Real.rpow_mul hN.le] at hQp
  have hfactor : (A*ell)^α*((2*Q)^(2*p)*y^p)^β=
      ((2:ℝ)^(2*p*β)*A^α)*Q^(2*p*β)*(y*ell)*(y/ell)^β := by
    rw [Real.mul_rpow hA.le hell.le,Real.mul_rpow (by positivity) (by positivity),
      ←Real.rpow_mul (by positivity),←Real.rpow_mul hy.le,
      Real.mul_rpow (by norm_num) hQ.le,Real.div_rpow hy.le hell.le,hαid,hγid,
      Real.rpow_sub hell,Real.rpow_add hy]
    simp only [Real.rpow_one]
    field_simp
  calc
    _≤(A*ell)^α*((2*Q)^(2*p)*y^p)^β :=
      mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hΔ hmean hα) (by positivity)
    _=((2:ℝ)^(2*p*β)*A^α)*Q^(2*p*β)*(y*ell)*(y/ell)^β := hfactor
    _≤((2:ℝ)^(2*p*β)*A^α)*N^(eps₀*(2*p*β))*(y*ell)*N^((a+10)*β) := by
      apply mul_le_mul _ hrp (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQp hc) (by positivity)
    _=_ := by
      rw [show ((2:ℝ)^(2*p*β)*A^α)*N^(eps₀*(2*p*β))*(y*ell)*N^((a+10)*β)=
        ((2:ℝ)^(2*p*β)*A^α)*(N^(eps₀*(2*p*β))*N^((a+10)*β))*y*ell by ring,
        ←Real.rpow_add hN]
      dsimp only [α,β]
      congr 3 <;> field_simp <;> ring

theorem exists_reverse_movement_order {a eps₀ eps : ℝ}
    (ha : 0≤a) (heps₀ : 0≤eps₀) (heps : 0<eps) (hgap : eps₀<eps/4) :
    ∃ l : ℕ, 2<(l:ℝ) ∧
      2*(l:ℝ)*eps₀/((l:ℝ)-1)+(a+10)/((l:ℝ)-1)<eps := by
  have hmargin : 0<eps-2*eps₀ := by linarith
  obtain ⟨l,hl⟩ := exists_nat_gt (max (3:ℝ) (1+(2*eps₀+a+10)/(eps-2*eps₀)))
  have hl3 : 3<(l:ℝ) := (le_max_left _ _).trans_lt hl
  have hlB : 1+(2*eps₀+a+10)/(eps-2*eps₀)<(l:ℝ) := (le_max_right _ _).trans_lt hl
  have hpm : 0<(l:ℝ)-1 := by linarith
  have hC : 2*eps₀+a+10<((l:ℝ)-1)*(eps-2*eps₀) := by
    apply (div_lt_iff₀ hmargin).1
    linarith
  refine ⟨l,by linarith,?_⟩
  have he : 2*(l:ℝ)*eps₀/((l:ℝ)-1)+(a+10)/((l:ℝ)-1)=
      2*eps₀+(2*eps₀+a+10)/((l:ℝ)-1) := by field_simp; ring
  rw [he]
  have H := (div_lt_iff₀ hpm).2 (by nlinarith :
    2*eps₀+a+10<(eps-2*eps₀)*((l:ℝ)-1))
  linarith

theorem eventually_absorb_fixed_coefficient {e eps : ℝ} (hgap : e<eps) (C : ℝ) :
    ∀ᶠ n : ℕ in atTop, C*(n:ℝ)^e≤(n:ℝ)^eps := by
  have ht := (tendsto_rpow_atTop (sub_pos.mpr hgap)).comp
    tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually (eventually_ge_atTop C),eventually_gt_atTop (0:ℕ)] with n hC hn
  have hN : 0<(n:ℝ) := by exact_mod_cast hn
  calc
    _≤(n:ℝ)^(eps-e)*(n:ℝ)^e :=
      mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hN.le _)
    _=(n:ℝ)^eps := by rw [←Real.rpow_add hN]; congr 1; ring

end OAI.SKFluctuations.Hierarchy
