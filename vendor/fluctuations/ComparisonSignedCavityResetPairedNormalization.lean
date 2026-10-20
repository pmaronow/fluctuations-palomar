module

public import ComparisonSignedCavityActualResetAllRate
public import ComparisonSignedCavityGeneratedProjectionScales
public import ComparisonSignedCavityStarIncomingBandScale

@[expose] public section

noncomputable section
set_option maxHeartbeats 22000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
open Classical
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum

theorem sourceMonomialScale_mono_initial {a : ℕ} (initial : Finset (Fin a))
    {x y W : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hW : 0 ≤ W) :
    sourceMonomialScale x W initial ≤ sourceMonomialScale y W initial := by
  unfold sourceMonomialScale
  gcongr

theorem native_reset_paired_budget_normalize (n a b d : ℕ) (eta : ℝ)
    {saving Cp Ch κ xs W v raw s H B Hbar : ℝ} {Cpower Cbase : ℕ→ℝ}
    (hsaving : 0 ≤ saving) (hCp : 0 ≤ Cp) (hCh : 0 ≤ Ch) (hκ : 0 ≤ κ)
    (hC : ∀j,0 ≤ Cpower j ∧ 0 ≤ Cbase j)
    (hxs : 0 ≤ xs) (hW : 0 < W) (hv : 0 < v) (hs : 0 < s)
    (hH : 0 ≤ H) (_hB : 0 ≤ B) (hHbar : 0 ≤ Hbar)
    (hHH : H ≤ Hbar) (hBB : B ≤ Hbar*s)
    (hraw : savedWeightedExteriorScale xs W v raw ≤ κ*savedWeightedExteriorScale xs W v s) :
    nativeResetPairedBudget n a b d eta saving Cp Ch Cpower Cbase xs W v raw H B ≤
      ((n:ℝ)^(-eta))^2*
        (Cp*Ch^a*κ*nativeSavedIncomingScale xs W s v+
          (∑j∈Finset.range d,Cpower j*(Cbase j)^b)*nativeSavedIncomingScale xs W W v)*
        (Hbar*s*W^d) := by
  have hε : 0 ≤ ((n:ℝ)^(-eta))^2:=sq_nonneg _
  have hρ : 0 ≤ ((n+1:ℕ):ℝ)^(-saving)*W:=by positivity
  have hρW : ((n+1:ℕ):ℝ)^(-saving)*W ≤ W := by
    apply mul_le_of_le_one_left hW.le
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_cast;omega) (by linarith)
  have hP : 0 ≤ savedProjectedScale xs W v:=by unfold savedProjectedScale;positivity
  have hEs : 0 ≤ savedWeightedExteriorScale xs W v s:=by unfold savedWeightedExteriorScale;positivity
  have hHbars : 0 ≤ Hbar*s:=mul_nonneg hHbar hs.le
  have HI : Cp*((n:ℝ)^(-eta))^2*savedProjectedScale xs W v*savedWeightedExteriorScale xs W v raw*
      (Ch^a*H)*(((n+1:ℕ):ℝ)^(-saving)*W)^d ≤
      ((n:ℝ)^(-eta))^2*(Cp*Ch^a*κ*nativeSavedIncomingScale xs W s v)*(Hbar*s*W^d) := by
    calc
      _ ≤ Cp*((n:ℝ)^(-eta))^2*savedProjectedScale xs W v*(κ*savedWeightedExteriorScale xs W v s)*
          (Ch^a*Hbar)*W^d := by gcongr
      _ = _ := by unfold nativeSavedIncomingScale;field_simp
  have HP (j : ℕ) (hj : j∈Finset.range d) :
      Cpower j*((n:ℝ)^(-eta))^2*(savedProjectedScale xs W v)^2*((Cbase j)^b*B)*
        (((n+1:ℕ):ℝ)^(-saving)*W)^(d-1) ≤
      ((n:ℝ)^(-eta))^2*(Cpower j*(Cbase j)^b*nativeSavedIncomingScale xs W W v)*(Hbar*s*W^d) := by
    have h1:0 ≤ Cpower j:=(hC j).1
    have h2:0 ≤ Cbase j:=(hC j).2
    have hd:0<d:=by have:=Finset.mem_range.mp hj;omega
    calc
      _ ≤ Cpower j*((n:ℝ)^(-eta))^2*(savedProjectedScale xs W v)^2*((Cbase j)^b*(Hbar*s))*W^(d-1) := by gcongr
      _ = _ := by
        have HH:=native_saved_power_product_normalize d hd xs W v (Hbar*s) hW hv
        calc
          _=Cpower j*((n:ℝ)^(-eta))^2*(Cbase j)^b*
              ((savedProjectedScale xs W v)^2*(Hbar*s)*W^(d-1)):=by ring
          _=_:=by rw [HH];ring
  unfold nativeResetPairedBudget
  apply (add_le_add HI (Finset.sum_le_sum HP)).trans
  apply le_of_eq
  rw [mul_add,add_mul]
  congr 1
  simp only [Finset.sum_mul,Finset.mul_sum]

end OAI.SKFluctuations.LaplaceWindowFormalization
