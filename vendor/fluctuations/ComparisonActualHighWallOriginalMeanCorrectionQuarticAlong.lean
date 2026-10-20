module

public import ComparisonActualHighWallOriginalMeanCorrection

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 18000000
set_option backward.isDefEq.respectTransparency false

theorem eventually_actual_high_wall_original_mean_correction_quartic_price_along
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hC0 : 0 < C0)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock,
      M.xs=M.data.d →
      ∀us : List PositiveMass,(∀u∈us,u.val ≤ 1) → ∀ᶠk in atTop,
        let as:=finiteCutMasses us k
        ∀i U : ℕ,i < U → U ≤ as.length →
          |actualGeneralTargetOriginalMeanCorrection (n:=dim n) M.bf M.hf as i U| ≤
            C*M.data.d^4 := by
  let B:=max Bclock 0
  let C:=768*B^2+2*B+1
  have hB : 0 ≤ B:=le_max_right _ _
  have hC : 0 < C:=by dsimp only [C];positivity
  refine ⟨C,hC,?_⟩
  filter_upwards [hdim.eventually (eventually_actual_high_wall_omitted_product_cubic_cost
    (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock)
    hm hC0)] with n hn
  intro M hwork us hus
  have htotal : ∀u∈Icc (0:ℝ) 1,(M.hf u:ℝ)+(M.bf u:ℝ) ≤ B:=by
    intro u hu
    exact (M.data.total_clock_le M.alpha u hu).trans (M.hT.trans (le_max_left _ _))
  have H:=eventually_actual_general_target_original_mean_correction_budget (dim n) M.bf M.hf
    (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha)
    (M.data.root_field_zero M.alpha) B hB htotal us hus
  have Hinv : (1:ℝ)/(dim n+1:ℕ) ≤ M.data.d^4:=by
    have HH:=mul_le_mul_of_nonneg_right (hn M hwork) M.data.hd.le
    convert HH using 1 <;> field_simp [M.data.hd.ne']
  filter_upwards [H] with k hk
  dsimp only at hk ⊢
  intro i U hi hU
  apply (hk i U hi hU).trans
  have HH:=mul_le_mul_of_nonneg_left Hinv hC.le
  simpa only [C,div_eq_mul_inv,one_div,one_mul] using HH

end OAI.SKFluctuations.Cavity
