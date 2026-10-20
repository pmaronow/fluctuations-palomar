module

public import ComparisonSignedCavityActualTerminalDepth
public import ComparisonSignedCavityActualExpansionTerminal

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization.NativeOverlapMinimum
open Hierarchy Hierarchy.ClockTree

theorem exists_actual_mixed_terminal_depth
    {m delta cl cu Az C0 Ct D Bclock gamma : ℝ}
    (hm : 0 < m) (hC0 : 0 < C0) (hgamma : 0 < gamma) :
    ∃depth : ℕ,0 < depth ∧ ∃saving : ℝ,0 < saving ∧
      ∀C : ℝ,0≤C→∀ᶠn : ℕ in atTop,
        ∀a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        ∀ops : List NativeActualExpansionOp,depth≤nativeActualExpansionMarkedCount ops→
          C*(a.context.N^(-gamma))^(nativeActualExpansionMarkedCount ops)≤
            a.context.N^(-saving)*a.xs^2 := by
  obtain ⟨depth,hd,_,saving,hs,H⟩:=exists_actual_terminal_depth
    (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock) hm hC0 hgamma
  refine ⟨depth,hd,saving,hs,?_⟩
  intro C hC
  filter_upwards [H C hC] with n hn
  intro a ops hops
  apply le_trans _ (hn a)
  apply mul_le_mul_of_nonneg_left _ hC
  rw [←Real.rpow_mul_natCast a.context.hN.le]
  apply Real.rpow_le_rpow_of_exponent_le
  · change (1:ℝ)≤(n+1:ℕ)
    exact_mod_cast (show 1≤n+1 by omega)
  · have HO : (depth:ℝ)≤nativeActualExpansionMarkedCount ops:=by exact_mod_cast hops
    nlinarith

end OAI.SKFluctuations.LaplaceWindowFormalization.NativeOverlapMinimum
