module

public import SKConstants.GaussianActualQueryStability
import Mathlib.Tactic

@[expose] public section
noncomputable section
open scoped BigOperators Classical
namespace SKConstants

def queryDirectionGapPrefix {K : ℕ} (u : Fin K → ℝ) (j : Fin (K+1)) : ℝ :=
  ∑ i : Fin K, if i.val<j.val then u i else 0

@[simp] theorem queryDirectionGapPrefix_zero {K : ℕ} (u : Fin K → ℝ) :
    queryDirectionGapPrefix u 0=0 := by simp [queryDirectionGapPrefix]

theorem queryDirectionGapPrefix_castSucc {K : ℕ} (u : Fin K → ℝ) (j : Fin K) :
    queryDirectionGapPrefix u j.castSucc=∑ i∈Finset.Iio j, u i := by
  unfold queryDirectionGapPrefix
  simp only [Fin.val_castSucc]
  exact GaussianProposal.sum_ite_lt_eq_sum_Iio u j

theorem queryDirectionGapPrefix_succ {K : ℕ} (u : Fin K → ℝ) (j : Fin K) :
    queryDirectionGapPrefix u j.succ=∑ i∈Finset.Iic j, u i := by
  unfold queryDirectionGapPrefix
  rw [←Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_Iic,Fin.le_def,Fin.val_succ]
  omega

theorem queryDirectionGapPrefix_step {K : ℕ} (u : Fin K → ℝ) (j : Fin K) :
    queryDirectionGapPrefix u j.succ=queryDirectionGapPrefix u j.castSucc+u j := by
  have he (i : Fin K) : (if i.val<j.succ.val then u i else 0)=
      (if i.val<j.castSucc.val then u i else 0)+(if i=j then u i else 0) := by
    by_cases hij : i=j
    · subst i
      simp only [Fin.val_succ,Fin.val_castSucc,Nat.lt_succ_self,ite_true,lt_self_iff_false,
        ite_false,zero_add]
    · by_cases hlt : i.val<j.val
      · have hs : i.val<j.val+1 := by omega
        simp only [Fin.val_succ,Fin.val_castSucc,hlt,hs,hij,ite_true,ite_false,add_zero]
      · have hge : ¬i.val<j.succ.val := by
          simp only [Fin.val_succ]
          have hn : i.val≠j.val := fun h => hij (Fin.ext h)
          omega
        simp only [Fin.val_castSucc,hlt,hij,hge,ite_false,zero_add]
  unfold queryDirectionGapPrefix
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  simp

theorem queryDirectionGapPrefix_nonneg {K : ℕ} (u : Fin K → ℝ)
    (hu : ∀ i, 0≤u i) (j : Fin (K+1)) : 0≤queryDirectionGapPrefix u j := by
  exact Finset.sum_nonneg (fun i _ => ite_nonneg (hu i) le_rfl)

theorem coupledQueryGap_geometric_bound {K : ℕ}
    (B : Fin (K+1) → ℝ) (u : Fin K → ℝ) (η A E : ℝ)
    (hη : 0≤η) (hA : 0≤A) (hE : 0≤E)
    (hB : ∀ j, 0≤B j) (hu : ∀ j, 0≤u j) (hB0 : B 0≤η)
    (hdir : ∀ j : Fin K, u j≤A*(η+B j.castSucc+queryDirectionGapPrefix u j.castSucc))
    (hpath : ∀ j : Fin K, B j.succ≤B j.castSucc+
      E*(η+queryDirectionGapPrefix u j.succ)+3*η)
    (j : Fin (K+1)) :
    B j+queryDirectionGapPrefix u j+η≤2*η*((E+1)*A+E+4)^j.val := by
  let C := (E+1)*A+E+4
  have hC : 0≤C := by dsimp [C]; positivity
  refine Fin.induction ?_ (fun k ih => ?_) j
  · simp only [queryDirectionGapPrefix_zero,Fin.val_zero,pow_zero,mul_one,add_zero]
    linarith
  · have hs : 0≤B k.castSucc+queryDirectionGapPrefix u k.castSucc+η := by
      exact add_nonneg (add_nonneg (hB _) (queryDirectionGapPrefix_nonneg u hu _)) hη
    have hd := hdir k
    have hb := hpath k
    rw [queryDirectionGapPrefix_step] at hb ⊢
    have hn := queryDirectionGapPrefix_nonneg u hu k.castSucc
    have he1 : 0≤E+1 := by linarith
    have hd' := mul_le_mul_of_nonneg_left hd he1
    have hstep : B k.succ+(queryDirectionGapPrefix u k.castSucc+u k)+η≤
        C*(B k.castSucc+queryDirectionGapPrefix u k.castSucc+η) := by
      dsimp [C]
      nlinarith [hB k.castSucc,mul_nonneg hE (hB k.castSucc)]
    calc
      _ ≤ C*(B k.castSucc+queryDirectionGapPrefix u k.castSucc+η) := hstep
      _ ≤ C*(2*η*C^k.castSucc.val) := mul_le_mul_of_nonneg_left ih hC
      _ = _ := by simp only [Fin.val_succ,Fin.val_castSucc,pow_succ]; ring

end SKConstants
