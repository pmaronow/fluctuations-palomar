module

public import ComparisonSignedCavityResetPairedRowAlgebra
public import ComparisonSignedCavityProjectionSpinePairedRow
public import CavityScalarGammaTopology

@[expose] public section

noncomputable section
set_option maxHeartbeats 24000000
open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology NNReal
open Classical
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem native_list_sum_filter_of_zero {A : Type} (L : List A) (p : A→Bool) (F : A→ℝ)
    (hF : ∀a∈L,p a=false → F a=0) :
    ((L.filter p).map F).sum=(L.map F).sum := by
  induction L with
  | nil=>simp
  | cons a L ih=>
    have hL:=ih (fun b hb=>hF b (List.mem_cons_of_mem a hb))
    by_cases ha:p a=true
    · simp [ha,hL]
    · have hf:p a=false:=Bool.eq_false_iff.mpr ha
      simp [hf,hL,hF a List.mem_cons_self hf]

def nativeProjectedGammaTopology (as : List PositiveMass) (U : ℕ) (V : ℝ)
    (R : ℝ→ℝ) (K : ℕ→ℝ) (j : ℕ) (diag : Bool) : ℝ :=
  scalarGammaFromTopology as U K j (if diag then 1 else 0)*
    (if U ≤ j ∧ V ≤ R (partitionPoint 0 as j) then 1 else 0)

theorem native_reset_projected_gamma_row_high_form
    (n : ℕ) {pre mid tail : List PositiveMass}
    (T : ClockTree (Spin n×Bool) (pre++(mid++tail))) (P : NativeGeneratedTest T)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (U : ℕ) (V : ℝ) (q : ℕ→RestCoordinate n→ℝ) (K : ℕ→ℝ) (d : ℕ) (center : ℝ)
    (ho : MassOrdered 0 (pre++(mid++tail))) (hU : pre.length+mid.length < U) :
    nativeResetProjectedGammaRow n T P M U V q K d center=
      ((nativeHighMarkedRows T P.target (pre.length+mid.length) 0).map fun p=>
        p.coeff*nativeProjectedGammaTopology (pre++(mid++tail)) U V M.R K
          (p.tree.splitIndex (p.embed P.target) p.mark) (decide (p.mark=p.embed P.target))*
        nativeResetPairedProjectionValue n T P M p q d center).sum := by
  unfold nativeResetProjectedGammaRow
  have HF:=native_list_sum_filter_of_zero (T.markedAttach 0)
    (fun p=>decide (pre.length+mid.length < p.tree.splitIndex (p.embed P.target) p.mark))
    (fun p=>p.coeff*fullScalarCutGamma p.tree U K (p.embed P.target) p.mark*
      (if U ≤ p.tree.splitIndex (p.embed P.target) p.mark ∧
          V ≤ M.R (partitionPoint 0 (pre++(mid++tail)) (p.tree.splitIndex (p.embed P.target) p.mark)) then
        nativeResetPairedProjectionValue n T P M p q d center else 0)) (by
      intro p _ hp
      have hn:¬pre.length+mid.length < p.tree.splitIndex (p.embed P.target) p.mark:=of_decide_eq_false hp
      have hx:¬U ≤ p.tree.splitIndex (p.embed P.target) p.mark:=fun h=>hn (hU.trans_le h)
      simp [hx])
  rw [←HF,←nativeHighMarkedRows_eq_filter]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p _
  rw [fullScalarCutGamma_marked_eq_topology T ho]
  simp only [nativeProjectedGammaTopology,MarkedPlacement.hit,decide_eq_true_eq]
  split_ifs <;> ring

end OAI.SKFluctuations.Cavity
