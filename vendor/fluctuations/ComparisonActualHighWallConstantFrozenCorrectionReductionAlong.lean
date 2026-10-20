module

public import ComparisonActualGeneralConstantRemainderReadout
public import ComparisonActualHighWallFrozenConstantChildrenAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySeqFocus false

theorem eventually_actual_high_wall_constant_source_frozen_correction_cubic_reduction_along
    (Bclock Cmass : ℝ) (hCm : 0 ≤ Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock,
        M.xs=M.data.d →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        ∀(star U : ℕ) (hs : star < U) (hU : U ≤ as.length),
          partitionPoint 0 as star ≤ Cmass*M.data.d →
        |actualGeneralConstantSourceFrozenCorrection (n:=dim n) M.bf M.hf as star U hs hU M.data.d| ≤
          C*M.data.d^3+|actualGeneralTargetOriginalTaylorPart (n:=dim n) M.bf M.hf as star U| := by
  obtain ⟨Cm,hCm0,HM⟩:=eventually_actual_high_wall_original_mean_correction_cubic_price_along
    (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D) Bclock hm hC0 dim hdim
  obtain ⟨Cf,hCf,HF⟩:=eventually_actual_high_wall_constant_children_initial_frozen_quartic_price_along
    (D:=D) Bclock Cmass hCm hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim
  let B:=max Bclock 0
  let C:=Cm+1+B*Cf
  refine ⟨C,by dsimp only [C,B];positivity,?_⟩
  have Hsite:=hdim.eventually (eventually_actual_high_wall_omitted_product_cubic_cost
    (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock) hm hC0)
  filter_upwards [HM,HF,Hsite] with n hnM hnF hnSite
  intro M hwork L us hus hret hmesh
  have Hmesh:=eventually_native_finite_physical_mean_uniform_center (dim n) M.bf M.hf
    (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha) (M.data.root_field_zero M.alpha)
    us hus ((1:ℝ)/(dim n+1:ℕ)) (by positivity)
  filter_upwards [hnM M hwork us hus,hnF M hwork L us hus hret hmesh,Hmesh] with k hkM hkF hkMesh
  dsimp only at hkM hkF hkMesh ⊢
  intro star U hs hU hmass
  let as:=finiteCutMasses us k
  let remainder:=actualGeneralConstantSourceRemainder (n:=dim n) M.bf M.hf as star U
  let taylor:=actualGeneralTargetOriginalTaylorPart (n:=dim n) M.bf M.hf as star U
  have ho:=finiteCutMasses_ordered us hus k
  have Hsite4 : (1:ℝ)/(dim n+1:ℕ) ≤ M.data.d^4:=by
    have HH:=mul_le_mul_of_nonneg_right (hnSite M hwork) M.data.hd.le
    convert HH using 1 <;> field_simp [M.data.hd.ne']
  have Hd43 : M.data.d^4 ≤ M.data.d^3:=by
    have H:=mul_le_mul_of_nonneg_left M.data.hd1 (pow_nonneg M.data.hd.le 3)
    nlinarith only [H]
  have Hrem : |remainder| ≤ (Cm+1)*M.data.d^3+|taylor|:=by
    dsimp only [remainder,taylor]
    rw [actual_general_constant_source_remainder_eq_original_mean_and_Taylor (n:=dim n) M.bf M.hf
      (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha) as ho star U hs hU]
    have Habs (x y z : ℝ) : |x+y+z| ≤ |x|+|y|+|z|:=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    apply (Habs _ _ _).trans
    have Hmean:=hkM star U hs hU
    have Hcenter:=(hkMesh star (hs.le.trans hU)).trans (Hsite4.trans Hd43)
    nlinarith only [Hmean,Hcenter]
  have Hb : (M.bf (partitionPoint 0 as star):ℝ) ≤ B:=by
    have HT:=M.data.total_clock_le M.alpha _ (partitionPoint_mem as ho star)
    linarith [M.hT,le_max_left Bclock 0,(M.hf (partitionPoint 0 as star)).coe_nonneg]
  have Hb0 : 0 ≤ (M.bf (partitionPoint 0 as star):ℝ):=NNReal.coe_nonneg _
  have Hfrozen:=hkF star U hs hU hmass
  have Hfactor:=mul_le_mul_of_nonneg_left Hb M.data.hd.le
  have HH:=mul_le_mul Hfactor Hfrozen (abs_nonneg _) (mul_nonneg M.data.hd.le (le_max_right Bclock 0))
  have Hd53 : M.data.d^5 ≤ M.data.d^3:=by
    have H2:=pow_le_pow_left₀ M.data.hd.le M.data.hd1 2
    norm_num only [one_pow] at H2
    have HH:=mul_le_mul_of_nonneg_right H2 (pow_nonneg M.data.hd.le 3)
    nlinarith only [HH]
  have Hterm : (M.bf (partitionPoint 0 as star):ℝ)*M.data.d*
      |((actualGeneralConstantSourceChildren (n:=dim n) M.bf M.hf as star U hs hU).map
        (fun Q=>actualGeneralFourStateResponse M.bf M.hf U M.data.d Q.freeze)).sum| ≤ B*Cf*M.data.d^3:=by
    have HH' : (M.bf (partitionPoint 0 as star):ℝ)*M.data.d*
        |((actualGeneralConstantSourceChildren (n:=dim n) M.bf M.hf as star U hs hU).map
          (fun Q=>actualGeneralFourStateResponse M.bf M.hf U M.data.d Q.freeze)).sum| ≤ B*Cf*M.data.d^5:=by
      convert HH using 1 <;> ring
    exact HH'.trans (mul_le_mul_of_nonneg_left Hd53 (by dsimp only [B];positivity : 0 ≤ B*Cf))
  unfold actualGeneralConstantSourceFrozenCorrection
  apply (abs_sub _ _).trans
  rw [abs_mul,abs_of_nonneg (mul_nonneg Hb0 M.data.hd.le)]
  exact (add_le_add Hrem Hterm).trans_eq (by dsimp only [C,remainder,taylor];ring)

end OAI.SKFluctuations.Cavity
