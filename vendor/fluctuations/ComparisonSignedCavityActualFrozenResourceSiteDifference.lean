module

public import ComparisonSignedCavityActualFrozenResourceOmission

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 20000000

theorem native_full_square_bounded_kernel_pairing
    {n : ℕ} {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (ho : MassOrdered 0 as) (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ)
    (xroot : FullCoordinate n→ℝ) (F H : T.Assignment→ℝ)
    (B rho : ℝ) (hB : 0 ≤ B) (hrho : 0 ≤ rho)
    (hF : T.disorderExpect (fullWeight n) (fullFeature n) v q (fun σ=>(F σ)^2) xroot ≤ B^2)
    (hH : ∀σ,|H σ| ≤ rho) :
    |T.disorderExpect (fullWeight n) (fullFeature n) v q (fun σ=>H σ*F σ) xroot| ≤ rho*B := by
  have hw:=T.disorderWeight_probability (fullWeight_pos n) (fullFeature n) ho v q xroot
  have HH : T.disorderExpect (fullWeight n) (fullFeature n) v q (fun σ=>(H σ)^2) xroot ≤ rho^2:=by
    unfold ClockTree.disorderExpect
    calc
      _ ≤ ∑σ,T.disorderWeight (fullWeight n) (fullFeature n) v q σ xroot*rho^2:=by
        apply Finset.sum_le_sum
        intro σ _
        exact mul_le_mul_of_nonneg_left
          (by nlinarith [sq_abs (H σ),abs_nonneg (H σ),hH σ]) (hw.1 σ)
      _=rho^2:=by rw [←Finset.sum_mul,hw.2,one_mul]
  have HF0 : 0 ≤ T.disorderExpect (fullWeight n) (fullFeature n) v q (fun σ=>(F σ)^2) xroot:=by
    unfold ClockTree.disorderExpect
    exact Finset.sum_nonneg fun σ _=>mul_nonneg (hw.1 σ) (sq_nonneg _)
  have HC:=mul_le_mul HH hF HF0 (sq_nonneg rho)
  have Hcs:=T.disorderExpect_mul_sq_le (fullWeight_pos n) (fullFeature n) ho v q H F xroot
  have hab:=abs_nonneg (T.disorderExpect (fullWeight n) (fullFeature n) v q (fun σ=>H σ*F σ) xroot)
  have hrB:=mul_nonneg hrho hB
  nlinarith [sq_abs (T.disorderExpect (fullWeight n) (fullFeature n) v q (fun σ=>H σ*F σ) xroot)]

def nativeOriginalResourceSiteDeletedDifference
    {n : ℕ} {as : List PositiveMass} {i star : ℕ} {T : ClockTree (Spin n×Bool) as}
    (P : NativeResourceTerm i star T) (v₀ : FullCoordinate n→ℝ)
    (q₀ : ℕ→FullCoordinate n→ℝ) (x₀ : FullCoordinate n→ℝ)
    (U : ℕ) (b h K C : ℕ→ℝ) (s t : T.Slot) : ℝ :=
  T.disorderExpect (fullWeight n) (fullFeature n) 0
    (cavityPath n U 1 1 (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) b h K)
    (fun σ=>(spinValue (T.atSlot σ s).2*spinValue (T.atSlot σ t).2-
      deletedOverlap n (joinSpin (T.atSlot σ s)) (joinSpin (T.atSlot σ t)))*
      P.value (fullWeight n) (fullFeature n) v₀ q₀
        (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)) C x₀ σ) 0

theorem native_original_resource_site_deleted_difference_abs_le
    {n : ℕ} {as : List PositiveMass} {i star : ℕ} (T : ClockTree (Spin n×Bool) as)
    (ho : MassOrdered 0 as) (P : NativeResourceTerm i star T)
    (v₀ : FullCoordinate n→ℝ) (q₀ : ℕ→FullCoordinate n→ℝ) (x₀ : FullCoordinate n→ℝ)
    (U : ℕ) (b h K C : ℕ→ℝ) (s t : T.Slot)
    (A x W : ℝ) (hA : 0 < A) (hx : 0 < x) (hxW : x ≤ W)
    (hi : i ≤ star) (hstar : star < as.length) (hsite : 1/(n+1:ℕ) ≤ x)
    (hm₀ : P.PairMomentBudget (fullWeight n) (fullFeature n) v₀ q₀
      (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)) C x₀ A x W 1)
    (hm : P.live.PairMomentBudget (fullWeight n) (fullFeature n) 0
      (cavityPath n U 1 1 (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) b h K)
      (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)) C 0 A x W 1) :
    |nativeOriginalResourceSiteDeletedDifference P v₀ q₀ x₀ U b h K C s t| ≤
      |P.coefficient| *
        (2*((P.live.factors.length:ℝ)/((n+1:ℕ)*x))*(2*(A+2))^P.resources.length+
          A^P.resources.length/(n+1:ℕ))*nativeResourceScale x W 1 P.resources := by
  let q:=cavityPath n U 1 1 (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) b h K
  let F:=P.value (fullWeight n) (fullFeature n) v₀ q₀
    (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)) C x₀
  let D:=fun σ=>F σ-nativeOriginalFrozenRestoredResourceValue P v₀ q₀ x₀ C σ
  let H:=fun σ : T.Assignment=>spinValue (T.atSlot σ s).2*spinValue (T.atSlot σ t).2-
    orderedOverlap (n+1) (joinSpin (T.atSlot σ s)) (joinSpin (T.atSlot σ t))
  let J:=fun σ : T.Assignment=>orderedOverlap (n+1) (joinSpin (T.atSlot σ s))
    (joinSpin (T.atSlot σ t))-deletedOverlap n (joinSpin (T.atSlot σ s)) (joinSpin (T.atSlot σ t))
  let B:=|P.coefficient| *((P.live.factors.length:ℝ)/((n+1:ℕ)*x))*
    ((2*(A+2))^P.resources.length*nativeResourceScale x W 1 P.resources)
  let V:=|P.coefficient| *nativeResourceEnvelope A x W 1 P.resources
  have hW : 0 < W:=hx.trans_le hxW
  have hraw : 0 < nativeResourceScale x W 1 P.resources:=
    native_resource_raw_scale_pos _ hx hW
  have hB : 0 ≤ B:=by dsimp only [B];positivity
  have hV : 0 ≤ V:=mul_nonneg (abs_nonneg _) (nativeResourceEnvelope_pos _ hA hx hW zero_lt_one).le
  have HD:=native_frozen_resource_omission_square P ho v₀ q₀ x₀ 0 q 0 C A x W hA hx hxW hi hstar hsite hm₀ hm
  have HF:=P.frozen_original_square_moment_le (fullWeight_pos n) (fullFeature n) ho
    v₀ q₀ x₀ 0 q (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)) C 0
    A x W 1 hA hx hW zero_lt_one hi hstar hm₀ hm
  have H2:=native_full_square_bounded_kernel_pairing T ho 0 q 0 D H B 2 hB (by norm_num) HD (by
    intro σ
    dsimp only [H]
    apply (abs_sub _ _).trans
    rw [abs_mul,abs_spinValue,abs_spinValue,one_mul]
    linarith [orderedOverlap_abs_le_one (n+1) (joinSpin (T.atSlot σ s)) (joinSpin (T.atSlot σ t))])
  have H1:=native_full_square_bounded_kernel_pairing T ho 0 q 0 F J V (1/(n+1:ℕ)) hV (by positivity) HF (by
    intro σ
    dsimp only [J]
    rw [abs_sub_comm,abs_deletedOverlap_sub])
  have HE:=native_original_frozen_resource_site_pair_eq_overlap_add_omission T ho P v₀ q₀ x₀ U b h K C s t
  dsimp only at HE
  have Hidentity : nativeOriginalResourceSiteDeletedDifference P v₀ q₀ x₀ U b h K C s t=
      T.disorderExpect (fullWeight n) (fullFeature n) 0 q (fun σ=>H σ*D σ) 0+
        T.disorderExpect (fullWeight n) (fullFeature n) 0 q (fun σ=>J σ*F σ) 0:=by
    dsimp only [nativeOriginalResourceSiteDeletedDifference,H,D,J,F,q,ClockTree.disorderExpect] at HE ⊢
    simp only [sub_mul,mul_sub,Finset.sum_sub_distrib] at HE ⊢
    simp only [←mul_assoc] at HE ⊢
    linear_combination HE
  rw [Hidentity]
  apply (abs_add_le _ _).trans
  apply (add_le_add H2 H1).trans_eq
  dsimp only [B,V,nativeResourceEnvelope_scale]
  rw [nativeResourceEnvelope_scale]
  ring

end OAI.SKFluctuations.Cavity
