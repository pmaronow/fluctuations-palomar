module

public import ComparisonSignedCavitySecondLowScalarPathSupport
public import ComparisonSignedCavityObservedSecondLowJoin

@[expose] public section

noncomputable section
set_option maxHeartbeats 12000000
namespace OAI.SKFluctuations.Cavity
open MeasureTheory ProbabilityTheory Filter Set Hierarchy LaplaceWindowFormalization
open scoped BigOperators Topology NNReal

def NativeSecondLowPathSupport {S : Type*} {as : List PositiveMass}
    (T : ClockTree S as) (U : ℕ) (a z f c e d : T.Slot) : Prop :=
    (U ≤ T.splitIndex a f ∧ U ≤ T.splitIndex c e ∧ U ≤ T.splitIndex d z) ∨
    (U ≤ T.splitIndex a f ∧ U ≤ T.splitIndex c d ∧ U ≤ T.splitIndex e z) ∨
    (U ≤ T.splitIndex a c ∧ U ≤ T.splitIndex f e ∧ U ≤ T.splitIndex d z) ∨
    (U ≤ T.splitIndex a c ∧ U ≤ T.splitIndex f d ∧ U ≤ T.splitIndex e z) ∨
    (U ≤ T.splitIndex a e ∧ U ≤ T.splitIndex d f ∧ U ≤ T.splitIndex c z) ∨
    (U ≤ T.splitIndex a e ∧ U ≤ T.splitIndex d c ∧ U ≤ T.splitIndex f z) ∨
    (U ≤ T.splitIndex a d ∧ U ≤ T.splitIndex e f ∧ U ≤ T.splitIndex c z) ∨
    (U ≤ T.splitIndex a d ∧ U ≤ T.splitIndex e c ∧ U ≤ T.splitIndex f z)

theorem native_second_low_joint_rest_test_zero_of_first_high (n U : ℕ)
    (b h K : ℕ→ℝ) {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (P : T.cavityLeft.Assignment→ℝ)
    (p : ClockTree.MarkedPlacement T) (r : ClockTree.MarkedPlacement p.tree)
    (s : ClockTree.MarkedPlacement r.tree) (t : ClockTree.MarkedPlacement s.tree)
    (H : U ≤ r.tree.splitIndex (r.embed p.mark) r.mark) :
    nativeSecondLowJointRestTest n U b h K P p r s t=fun _=>0 := by
  funext τ
  rw [native_second_low_joint_rest_test_product]
  simp only [restLowKernel,nativeSecondLowScalarValue,not_lt.mpr H,ite_false,
    zero_mul,mul_zero,sub_zero]

theorem native_second_low_joint_rest_test_zero_of_second_high (n U : ℕ)
    (b h K : ℕ→ℝ) {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (P : T.cavityLeft.Assignment→ℝ)
    (p : ClockTree.MarkedPlacement T) (r : ClockTree.MarkedPlacement p.tree)
    (s : ClockTree.MarkedPlacement r.tree) (t : ClockTree.MarkedPlacement s.tree)
    (H : U ≤ t.tree.splitIndex (t.embed s.mark) t.mark) :
    nativeSecondLowJointRestTest n U b h K P p r s t=fun _=>0 := by
  funext τ
  rw [native_second_low_joint_rest_test_product]
  simp only [restLowKernel,nativeSecondLowScalarValue,not_lt.mpr H,ite_false,
    mul_zero,sub_zero]

theorem native_second_low_joint_nonzero_path (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (ho : MassOrdered 0 as) (hU : U ≤ as.length)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot) (haz : T.splitIndex a z < U)
    (p : ClockTree.MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (r : ClockTree.MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0)
    (s : ClockTree.MarkedPlacement r.tree) (hs : s∈r.tree.markedAttach 0)
    (t : ClockTree.MarkedPlacement s.tree) (ht : t∈s.tree.markedAttach 0)
    (H : t.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
        (nativeSecondLowJointRestTest n U b h K P p r s t) 0*
      fullScalarCutMoment t.tree U K
        (insertedSiteSlots (insertedSiteSlots [a,z] p r) s t)≠0) :
    NativeSecondLowPathSupport t.tree U
      (t.embed (s.embed (r.embed (p.embed a)))) (t.embed (s.embed (r.embed (p.embed z))))
      (t.embed (s.embed (r.embed p.mark))) (t.embed (s.embed r.mark)) (t.embed s.mark) t.mark := by
  have Hf : r.tree.splitIndex (r.embed p.mark) r.mark < U := by
    by_contra HF
    have HZ:=native_second_low_joint_rest_test_zero_of_first_high n U b h K P p r s t
      (not_lt.mp HF)
    rw [HZ] at H
    simp [ClockTree.disorderExpect] at H
  have He : t.tree.splitIndex (t.embed s.mark) t.mark < U := by
    by_contra HE
    have HZ:=native_second_low_joint_rest_test_zero_of_second_high n U b h K P p r s t
      (not_lt.mp HE)
    rw [HZ] at H
    simp [ClockTree.disorderExpect] at H
  have Ha : t.tree.splitIndex (t.embed (s.embed (r.embed (p.embed a))))
      (t.embed (s.embed (r.embed (p.embed z)))) < U := by
    rw [(s.tree.markedAttach_embed_preserves 0 t ht).2,
      (r.tree.markedAttach_embed_preserves 0 s hs).2,
      (p.tree.markedAttach_embed_preserves 0 r hr).2,
      (T.markedAttach_embed_preserves 0 p hp).2]
    exact haz
  have Hf' : t.tree.splitIndex (t.embed (s.embed (r.embed p.mark)))
      (t.embed (s.embed r.mark)) < U := by
    rw [(s.tree.markedAttach_embed_preserves 0 t ht).2,
      (r.tree.markedAttach_embed_preserves 0 s hs).2]
    exact Hf
  apply native_second_low_scalar_nonzero_path t.tree ho U hU K _ _ _ _ _ _ Ha Hf' He
  intro HS
  apply H
  simp only [insertedSiteSlots,List.map_cons,List.map_nil,List.cons_append,List.nil_append]
  rw [HS,mul_zero]

theorem native_second_low_path_scalar_factor
    {n : ℕ} {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (ho : MassOrdered 0 as) (U : ℕ) (hU : U ≤ as.length) (K : ℕ→ℝ)
    (a z f c e d : T.Slot)
    (haz : T.splitIndex a z < U) (hfc : T.splitIndex f c < U) (hed : T.splitIndex e d < U)
    (haf : U ≤ T.splitIndex a f) (hce : U ≤ T.splitIndex c e) (hdz : U ≤ T.splitIndex d z) :
    fullScalarCutMoment T U K [a,z,f,c,e,d]=
      fullScalarCutGamma T U K a f*fullScalarCutGamma T U K c e*fullScalarCutGamma T U K d z := by
  classical
  let B:=T.cutBlock U hU
  have hAF : B a=B f:=(T.cutBlock_eq_iff U hU a f).mpr haf
  have hCE : B c=B e:=(T.cutBlock_eq_iff U hU c e).mpr hce
  have hDZ : B d=B z:=(T.cutBlock_eq_iff U hU d z).mpr hdz
  have hne (u v : T.Slot) (H : T.splitIndex u v < U) : B u≠B v := by
    intro HE
    have HL:=(T.cutBlock_eq_iff U hU u v).mp HE
    omega
  have hAZ : B a≠B z:=hne a z haz
  have hAC : B a≠B c:=by rw [hAF];exact hne f c hfc
  have hCZ : B c≠B z:=by rw [hCE,←hDZ];exact hne e d hed
  have hlow (u v : T.Slot) (H : B u≠B v) : T.splitIndex u v < U :=
    cut_block_ne_split_lt T U hU u v H
  have HA : ∀u∈[a,f],∀v∈[c,e,z,d],T.splitIndex u v < U := by
    intro u hu v hv
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hu hv
    rcases hu with rfl|rfl <;> rcases hv with rfl|rfl|rfl|rfl <;>
      apply hlow <;> first
      | exact hAC
      | exact hAZ
      | simpa only [←hAF,←hCE,hDZ] using hAC
      | simpa only [←hAF,←hCE,hDZ] using hAZ
  have HD : ∀u∈[c,e],∀v∈[z,d],T.splitIndex u v < U := by
    intro u hu v hv
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hu hv
    rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
      apply hlow <;> simpa only [←hCE,hDZ] using hCZ
  exact fullScalarCutMoment_second_low_path T ho U (by omega) hU K a z f c e d HA HD

end OAI.SKFluctuations.Cavity
