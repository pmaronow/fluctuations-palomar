module

public import ComparisonNativeFiniteErrorGrowth
public import ComparisonActualHighOnlyOverlapMinimum

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 14000000
namespace ActualHighOnlyOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem actual_error_power_range (M : ActualHighOnlyOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    (hC0 : 0 < C0) :
    (1/C0)^2*M.data.N^(-(5:ℝ)/6+2*m) ≤ M.data.E ∧
      M.data.E ≤ D^2*M.data.N^(-(1:ℝ)/2) := by
  have hgamma : 0 < 1/C0 := one_div_pos.mpr hC0
  have hlo : (1/C0)*M.data.N^(-(2:ℝ)/3+m)*M.data.d ≤ M.data.E := by
    have H := (div_le_iff₀ hC0).mpr (by simpa only [mul_comm] using M.hlower)
    simpa only [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc,one_mul] using H
  have hup : M.data.E ≤ M.data.d^2/Real.sqrt M.data.N :=
    (le_div_iff₀ (Real.sqrt_pos.mpr M.data.hN)).mpr
      (by simpa only [mul_comm] using M.hupper)
  refine ⟨(comparison_parent_scale_lower_bounds M.data.hN hgamma M.data.hd hlo hup).2.1,?_⟩
  have hd2 : M.data.d^2 ≤ D^2 := pow_le_pow_left₀ M.data.hd.le M.hdD 2
  calc
    M.data.E ≤ M.data.d^2/Real.sqrt M.data.N := hup
    _ ≤ D^2/Real.sqrt M.data.N := div_le_div_of_nonneg_right hd2 (Real.sqrt_nonneg _)
    _ = D^2*M.data.N^(-(1:ℝ)/2) := by
      rw [Real.sqrt_eq_rpow,div_eq_mul_inv,←Real.rpow_neg M.data.hN.le]
      congr 2
      ring

theorem actual_error_growth_along_finite_chain (depth : ℕ)
    (chain : Fin (depth+1) → ActualHighOnlyOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    (hstep : ∀j : Fin depth,
      (n:ℝ)^(delta/4)*(chain j.castSucc).data.E ≤ (chain j.succ).data.E) :
    (n:ℝ)^((depth:ℝ)*delta/4)*(chain 0).data.E ≤
      (chain (Fin.last depth)).data.E := by
  let g : ℝ := (n:ℝ)^(delta/4)
  have hg : 0 ≤ g := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have Hiter : ∀k : ℕ,∀hk : k ≤ depth,
      g^k*(chain 0).data.E ≤ (chain ⟨k,by omega⟩).data.E := by
    intro k
    induction k with
    | zero => intro hk; simp
    | succ k ih =>
      intro hk
      have hk' : k < depth := by omega
      have H := (mul_le_mul_of_nonneg_left (ih (by omega)) hg).trans (hstep ⟨k,hk'⟩)
      simpa only [pow_succ,mul_assoc,mul_comm,mul_left_comm,Fin.succ] using H
  have H := Hiter depth le_rfl
  have he : g^depth=(n:ℝ)^((depth:ℝ)*delta/4) := by
    dsimp [g]
    rw [←Real.rpow_mul_natCast (Nat.cast_nonneg n)]
    congr 1
    ring
  simpa only [he,Fin.last] using H

theorem eventually_no_actual_error_growth_chain (hm : 0 < m) (hdelta : 0 < delta)
    (hC0 : 0 < C0) :
    ∀ᶠn : ℕ in atTop,
      ¬ ∃chain : Fin (actualPropagationDepth delta+1) →
        ActualHighOnlyOverlapMinimum n m delta cl cu Az C0 Ct D Bclock,
        ∀j : Fin (actualPropagationDepth delta),
          (n:ℝ)^(delta/4)*(chain j.castSucc).data.E ≤ (chain j.succ).data.E := by
  let depth := actualPropagationDepth delta
  have hdepth : 10 ≤ (depth:ℝ)*delta := actual_propagation_depth_budget hdelta
  have hexp : -(1:ℝ)/2 < (depth:ℝ)*delta/4-(5:ℝ)/6+2*m := by linarith
  have hbound := eventually_coefficient_rpow_le (c:=D^2+1) (d:=(1/C0)^2)
    (q:=-(1:ℝ)/2) (r:=(depth:ℝ)*delta/4-(5:ℝ)/6+2*m)
    (by positivity) hexp
  filter_upwards [hbound,eventually_gt_atTop (0:ℕ)] with n hn hn0
  rintro ⟨chain,hstep⟩
  have hN : 0 < (n:ℝ) := by exact_mod_cast hn0
  have hpow : 0 < (n:ℝ)^(-(1:ℝ)/2) := Real.rpow_pos_of_pos hN _
  have hlo := (chain 0).actual_error_power_range hC0 |>.1
  have hup := (chain (Fin.last depth)).actual_error_power_range hC0 |>.2
  have H := actual_error_growth_along_finite_chain depth chain hstep
  have hmul := mul_le_mul_of_nonneg_left hlo
    (Real.rpow_nonneg hN.le ((depth:ℝ)*delta/4))
  have he : (n:ℝ)^((depth:ℝ)*delta/4)*
      ((1/C0)^2*(n:ℝ)^(-(5:ℝ)/6+2*m)) =
      (1/C0)^2*(n:ℝ)^((depth:ℝ)*delta/4-(5:ℝ)/6+2*m) := by
    rw [mul_left_comm,←Real.rpow_add hN]
    congr 2
    ring
  rw [he] at hmul
  have Htotal := hmul.trans (H.trans hup)
  dsimp only [ActualHighOnlyComparisonData.N] at Htotal
  nlinarith

theorem eventually_no_bad_root_of_actual_error_growth_child
    (hm : 0 < m) (hdelta : 0 < delta) (hC0 : 0 < C0) :
    ∀ᶠn : ℕ in atTop,
      ∀Bad : ActualHighOnlyOverlapMinimum n m delta cl cu Az C0 Ct D Bclock → Prop,
      (∀P,Bad P → ∃Q,Bad Q ∧ (n:ℝ)^(delta/4)*P.data.E ≤ Q.data.E) →
      ∀P,¬ Bad P := by
  filter_upwards [eventually_no_actual_error_growth_chain (cl:=cl) (cu:=cu) (Az:=Az)
    (Ct:=Ct) (D:=D) (Bclock:=Bclock) hm hdelta hC0] with n hn
  intro Bad next P hP
  obtain ⟨chain,_,_,H⟩ := physical_propagation_finite_descendant_selection Bad
    (fun P Q => (n:ℝ)^(delta/4)*P.data.E ≤ Q.data.E) next P hP
    (actualPropagationDepth delta)
  exact hn ⟨chain,H⟩

theorem actual_error_growth_chain_along_false
    (hm : 0 < m) (hdelta : 0 < delta) (hC0 : 0 < C0)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (chain : Fin (actualPropagationDepth delta+1) →
      (k:ℕ)→ActualHighOnlyOverlapMinimum (dim k+1) m delta cl cu Az C0 Ct D Bclock)
    (hstep : ∀j : Fin (actualPropagationDepth delta),∀ᶠk : ℕ in atTop,
      ((dim k+1:ℕ):ℝ)^(delta/4)*(chain j.castSucc k).data.E ≤
        (chain j.succ k).data.E) : False := by
  have hs : Tendsto (fun k=>dim k+1) atTop atTop :=
    (tendsto_add_atTop_nat 1).comp hdim
  have Hno := hs.eventually (eventually_no_actual_error_growth_chain (cl:=cl) (cu:=cu)
    (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock) hm hdelta hC0)
  have Hsteps := Filter.eventually_all.mpr hstep
  have Hfalse : ∀ᶠk : ℕ in atTop,False := by
    filter_upwards [Hno,Hsteps] with k hk hgrowth
    exact hk ⟨(fun j=>chain j k),hgrowth⟩
  exact Hfalse.exists.elim (fun _ h=>h)

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
