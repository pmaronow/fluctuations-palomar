module

public import ComparisonActualHighWallInitialFullB0FractionalFactor
public import ComparisonRadiusFractionalRootDomination

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped NNReal BigOperators
set_option maxHeartbeats 16000000

theorem exists_actual_high_wall_initial_full_B0_endpoint_envelope
    (depth : ℕ) (j : Fin depth)
    (K : ℝ) (hK : 0 ≤ K)
    (C CiU CiB CiM : Fin (1+j.val)→ℝ)
    (hC : ∀a,0 ≤ C a)
    (hCiU : ∀a,0 < CiU a) (hCiB : ∀a,0 < CiB a)
    (hCiM : ∀a,0 < CiM a)
    (Cf Cr : ℝ) (hCf : 0 ≤ Cf) (hCr : 0 < Cr) :
    ∃Cenv : ℝ,0 < Cenv ∧ ∀D d N eta : ℝ,0 ≤ D → 0 < d → 0 ≤ N →
      actualHighWallInitialFullB0Envelope (1+j.val) C CiU CiB CiM Cf Cr (K*D) d N eta ≤
        Cenv*((D/d)^((8:ℝ)⁻¹)+(D/d)^((4:ℝ)⁻¹)+
          (D/d)^(((2*(depth+2):ℕ):ℝ)⁻¹)+N^(-eta)+d^3) := by
  let wu:=fun a : Fin (1+j.val)=>(K/CiU a)^((8:ℝ)⁻¹)
  let wb:=fun a : Fin (1+j.val)=>(K/CiB a)^((8:ℝ)⁻¹)
  let wm:=fun a : Fin (1+j.val)=>(K/CiM a)^((4:ℝ)⁻¹)
  let wf:=(K/Cr)^(((2*((1+j.val)+1):ℕ):ℝ)⁻¹)
  let A:=∑a : Fin (1+j.val),C a*(wu a+wb a+wm a+1)
  let B:=Cf*(Cr*wf+1)
  let Cenv:=A+B+1
  have hwu a : 0 ≤ wu a:=Real.rpow_nonneg (div_nonneg hK (hCiU a).le) _
  have hwb a : 0 ≤ wb a:=Real.rpow_nonneg (div_nonneg hK (hCiB a).le) _
  have hwm a : 0 ≤ wm a:=Real.rpow_nonneg (div_nonneg hK (hCiM a).le) _
  have hwf : 0 ≤ wf:=Real.rpow_nonneg (div_nonneg hK hCr.le) _
  have hA : 0 ≤ A:=by
    apply Finset.sum_nonneg
    intro a _
    exact mul_nonneg (hC a) (by positivity [hwu a,hwb a,hwm a])
  have hB : 0 ≤ B:=by dsimp only [B];positivity
  have henv : 0 < Cenv:=by dsimp only [Cenv];linarith
  refine ⟨Cenv,henv,?_⟩
  intro D d N eta hD hd hN
  let f:=D/d
  let bundle:=f^((8:ℝ)⁻¹)+f^((4:ℝ)⁻¹)+
    f^(((2*(depth+2):ℕ):ℝ)⁻¹)+N^(-eta)+d^3
  have hf : 0 ≤ f:=div_nonneg hD hd.le
  have hu : 0 ≤ f^((8:ℝ)⁻¹):=Real.rpow_nonneg hf _
  have hb : 0 ≤ f^((4:ℝ)⁻¹):=Real.rpow_nonneg hf _
  have hp : 0 ≤ f^(((2*(depth+2):ℕ):ℝ)⁻¹):=Real.rpow_nonneg hf _
  have hn : 0 ≤ N^(-eta):=Real.rpow_nonneg hN _
  have hd3 : 0 ≤ d^3:=pow_nonneg hd.le _
  have hbundle : 0 ≤ bundle:=by dsimp only [bundle];positivity
  have huB : f^((8:ℝ)⁻¹) ≤ bundle:=by dsimp only [bundle];linarith
  have hbB : f^((4:ℝ)⁻¹) ≤ bundle:=by dsimp only [bundle];linarith
  have hnB : N^(-eta) ≤ bundle:=by dsimp only [bundle];linarith
  have hdB : d^3 ≤ bundle:=by dsimp only [bundle];linarith
  have hfrozen : f^(((2*((1+j.val)+1):ℕ):ℝ)⁻¹) ≤ bundle:=by
    have H:=radius_frozen_level_root_le_initial_endpoint_sum hf depth j.val j.isLt
    have H' : f^(((2*(j.val+2):ℕ):ℝ)⁻¹) ≤ bundle:=
      H.trans (by dsimp only [bundle];linarith)
    have heq : 2*((1+j.val)+1)=2*(j.val+2):=by omega
    rw [heq]
    exact H'
  have Hlive : (∑a : Fin (1+j.val),C a*(
      wu a*f^((8:ℝ)⁻¹)+wb a*f^((8:ℝ)⁻¹)+wm a*f^((4:ℝ)⁻¹)+N^(-eta))) ≤ A*bundle:=by
    calc
      _ ≤ ∑a : Fin (1+j.val),C a*((wu a+wb a+wm a+1)*bundle):=by
        apply Finset.sum_le_sum
        intro a _
        apply mul_le_mul_of_nonneg_left _ (hC a)
        have H1:=mul_le_mul_of_nonneg_left huB (hwu a)
        have H2:=mul_le_mul_of_nonneg_left huB (hwb a)
        have H3:=mul_le_mul_of_nonneg_left hbB (hwm a)
        nlinarith only [H1,H2,H3,hnB]
      _ = A*bundle:=by dsimp only [A];rw [Finset.sum_mul];apply Finset.sum_congr rfl;intro a _;ring
  have Hfrozen : Cf*(Cr*(wf*f^(((2*((1+j.val)+1):ℕ):ℝ)⁻¹))+d^3) ≤ B*bundle:=by
    calc
      _ = Cf*((Cr*wf)*f^(((2*((1+j.val)+1):ℕ):ℝ)⁻¹)+d^3):=by ring
      _ ≤ Cf*((Cr*wf)*bundle+bundle):=
        mul_le_mul_of_nonneg_left (add_le_add
          (mul_le_mul_of_nonneg_left hfrozen (mul_nonneg hCr.le hwf)) hdB) hCf
      _ = B*bundle:=by dsimp only [B];ring
  rw [actual_high_wall_initial_full_B0_envelope_fractional_factor
    (1+j.val) C CiU CiB CiM Cf Cr K D d N eta hK hD hd hCiU hCiB hCiM hCr]
  change (∑a : Fin (1+j.val),C a*(
    wu a*f^((8:ℝ)⁻¹)+wb a*f^((8:ℝ)⁻¹)+wm a*f^((4:ℝ)⁻¹)+N^(-eta)))+
    Cf*(Cr*(wf*f^(((2*((1+j.val)+1):ℕ):ℝ)⁻¹))+d^3) ≤ Cenv*bundle
  have H:=add_le_add Hlive Hfrozen
  have Hlast : A*bundle+B*bundle ≤ Cenv*bundle:=by
    dsimp only [Cenv]
    nlinarith only [hbundle]
  exact H.trans Hlast

end OAI.SKFluctuations.Cavity
