module

public import ComparisonSignedCavityHighConnectedAssembly

@[expose] public section

noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy

theorem fullScalarCutMoment_six_nonjoins_zero {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (U : ℕ) (K : ℕ→ℝ) (a z e f c d : T.Slot) (hU : U ≤ as.length)
    (haz : T.splitIndex a z < U) (hcd : T.splitIndex c d < U)
    (hef : U ≤ T.splitIndex e f)
    (hnj : ¬joins (T.cutBlock U hU a) (T.cutBlock U hU z)
      (T.cutBlock U hU c) (T.cutBlock U hU d)) :
    fullScalarCutMoment T U K [a,z,e,f,c,d]=0 := by
  classical
  letI : DecidableEq (T.CutBlock U hU) := Classical.decEq _
  have hU0 : 0 < U := by omega
  by_contra H
  have HF : T.disorderExpect (fullWeight n) (fullFeature n) 0
      (cutFullVariance n 0 U 0 0 0 0 K)
      (fun σ=>(1:ℝ)*siteMonomial T σ [a,z,e,f,c,d]) 0 ≠ 0 := by
    rw [cut_full_monomial_eq_retained n 0 U 0 0 K T ho (fun _=>1) [a,z,e,f,c,d],
      T.cavityLeft.disorderExpect_one (restWeight_pos n) (restFeature n) ho,one_mul]
    exact H
  have HE:=cutDisorderExpect_graph_nonzero_even n 0 U hU0 0 0 0 K T hU
    (fun _=>1) 0 (by intro i;rfl) (by intro i;rfl) [a,z,e,f,c,d] HF
  let B:=T.cutBlock U hU
  have hEF : B e=B f := (T.cutBlock_eq_iff U hU e f).mpr hef
  have H4 : ∀ w : T.CutBlock U hU,Even ([B a,B z,B c,B d].count w) := by
    intro w
    have H6:=HE w
    change Even ([B a,B z,B e,B f,B c,B d].count w) at H6
    rw [Nat.even_iff] at H6 ⊢
    simp only [List.count_cons,List.count_nil,←hEF] at H6 ⊢
    omega
  apply hnj
  exact one_low_edge_selection (B a) (B z) (B c) (B d)
    (fun h=>not_le.mpr haz ((T.cutBlock_eq_iff U hU a z).mp h))
    (fun h=>not_le.mpr hcd ((T.cutBlock_eq_iff U hU c d).mp h)) H4

def nativeSixConnectedKernel {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (U : ℕ) (K : ℕ→ℝ)
    (a z e f c d : T.Slot) : ℝ :=
  fullScalarCutMoment T U K [a,z,e,f,c,d]-
    fullScalarCutGamma T U K e f*
      (fullScalarCutGamma T U K a c*fullScalarCutGamma T U K z d+
        fullScalarCutGamma T U K a d*fullScalarCutGamma T U K z c)

theorem native_six_connected_nonjoins_zero {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (U : ℕ) (K : ℕ→ℝ) (a z e f c d : T.Slot) (hU : U ≤ as.length)
    (haz : T.splitIndex a z < U) (hcd : T.splitIndex c d < U)
    (hef : U ≤ T.splitIndex e f)
    (hnj : ¬joins (T.cutBlock U hU a) (T.cutBlock U hU z)
      (T.cutBlock U hU c) (T.cutBlock U hU d)) :
    nativeSixConnectedKernel T U K a z e f c d=0 := by
  have H6:=fullScalarCutMoment_six_nonjoins_zero T ho U K a z e f c d hU haz hcd hef hnj
  have H4:=cutDisorderExpect_one_low_edge_zero n 0 U (by omega : 0 < U) 0 0 0 K T hU
    (fun _=>1) 0 (by intro i;rfl) (by intro i;rfl) a z c d (not_le.mpr haz) (not_le.mpr hcd) hnj
  rw [cut_full_monomial_eq_retained n 0 U 0 0 K T ho (fun _=>1) [a,z,c,d],
    T.cavityLeft.disorderExpect_one (restWeight_pos n) (restFeature n) ho,one_mul,
    fullScalarCutMoment_low_pairing T ho U K a z c d hU haz hcd] at H4
  unfold nativeSixConnectedKernel
  rw [H6,H4,mul_zero,sub_zero]

theorem fullScalarCutMoment_six_reorder {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (U : ℕ) (K : ℕ→ℝ) (a z e f c d : T.Slot) :
    fullScalarCutMoment T U K [a,z,e,f,c,d]=fullScalarCutMoment T U K [a,c,z,d,e,f] := by
  unfold fullScalarCutMoment scalarCutMoment
  congr 1
  funext σ
  simp only [List.map_cons,List.map_nil,ClockTree.slotProduct]
  ring

theorem native_six_connected_left_block {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (U : ℕ) (hU0 : 0 < U) (hU : U ≤ as.length) (K : ℕ→ℝ)
    (a z e f c d : T.Slot)
    (hcross : ∀ s∈[a,c,e,f],∀ t∈[z,d],T.splitIndex s t<U) :
    nativeSixConnectedKernel T U K a z e f c d=
      fullScalarCutConnected4 T U K a c e f*fullScalarCutGamma T U K z d := by
  have Had : T.splitIndex a d<U := hcross a (by simp) d (by simp)
  unfold nativeSixConnectedKernel
  rw [fullScalarCutMoment_six_reorder,fullScalarCutGamma_cross_zero T ho U K a d hU Had]
  simp only [zero_mul,add_zero]
  convert full_retained_six_connected_left T ho U hU0 hU K a c z d e f hcross using 1 <;> ring

theorem native_six_connected_right_block {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (U : ℕ) (hU0 : 0 < U) (hU : U ≤ as.length) (K : ℕ→ℝ)
    (a z e f c d : T.Slot)
    (hcross : ∀ s∈[a,c],∀ t∈[z,d,e,f],T.splitIndex s t<U) :
    nativeSixConnectedKernel T U K a z e f c d=
      fullScalarCutGamma T U K a c*fullScalarCutConnected4 T U K z d e f := by
  have Had : T.splitIndex a d<U := hcross a (by simp) d (by simp)
  unfold nativeSixConnectedKernel
  rw [fullScalarCutMoment_six_reorder,fullScalarCutGamma_cross_zero T ho U K a d hU Had]
  simp only [zero_mul,add_zero]
  convert full_retained_six_connected_right T ho U hU0 hU K a c z d e f hcross using 1 <;> ring

theorem native_six_connected_outside_blocks {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (U : ℕ) (hU0 : 0 < U) (hU : U ≤ as.length) (K : ℕ→ℝ)
    (a z e f c d : T.Slot)
    (hcross₁ : ∀ s∈[a,c],∀ t∈[z,d,e,f],T.splitIndex s t<U)
    (hcross₂ : ∀ s∈[z,d],∀ t∈[e,f],T.splitIndex s t<U) :
    nativeSixConnectedKernel T U K a z e f c d=0 := by
  have Had : T.splitIndex a d<U := hcross₁ a (by simp) d (by simp)
  unfold nativeSixConnectedKernel
  rw [fullScalarCutMoment_six_reorder,fullScalarCutGamma_cross_zero T ho U K a d hU Had]
  simp only [zero_mul,add_zero]
  convert full_retained_six_connected_outside T ho U hU0 hU K a c z d e f hcross₁ hcross₂ using 1 <;> ring

theorem native_six_connected_swap_low {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (U : ℕ) (K : ℕ→ℝ) (a z e f c d : T.Slot) :
    nativeSixConnectedKernel T U K a z e f c d=nativeSixConnectedKernel T U K a z e f d c := by
  have H : fullScalarCutMoment T U K [a,z,e,f,c,d]=fullScalarCutMoment T U K [a,z,e,f,d,c] := by
    unfold fullScalarCutMoment scalarCutMoment
    congr 1
    funext σ
    simp only [List.map_cons,List.map_nil,ClockTree.slotProduct]
    ring
  unfold nativeSixConnectedKernel
  rw [H]
  ring

theorem fullScalarCutMoment_cancel_pair {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (U : ℕ) (K : ℕ→ℝ)
    (a : T.Slot) (es : List T.Slot) :
    fullScalarCutMoment T U K (a::a::es)=fullScalarCutMoment T U K es := by
  unfold fullScalarCutMoment scalarCutMoment
  congr 1
  funext σ
  simp only [List.map_cons,ClockTree.slotProduct]
  rw [←mul_assoc,spinValue_sq,one_mul]

theorem fullScalarCutGamma_self {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (U : ℕ) (K : ℕ→ℝ) (a : T.Slot) : fullScalarCutGamma T U K a a=1 := by
  unfold fullScalarCutGamma
  rw [fullScalarCutMoment_cancel_pair,fullScalarCutMoment_nil T ho U K]

theorem fullScalarCutConnected4_target_self_zero {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (U : ℕ) (K : ℕ→ℝ) (a e f : T.Slot) :
    fullScalarCutConnected4 T U K a a e f=0 := by
  unfold fullScalarCutConnected4
  rw [fullScalarCutMoment_cancel_pair,fullScalarCutGamma_self T ho U K]
  change fullScalarCutGamma T U K e f-1*fullScalarCutGamma T U K e f=0
  ring

theorem native_six_connected_high_self_zero {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (U : ℕ) (K : ℕ→ℝ) (a z e c d : T.Slot)
    (hU : U ≤ as.length) (haz : T.splitIndex a z<U) (hcd : T.splitIndex c d<U) :
    nativeSixConnectedKernel T U K a z e e c d=0 := by
  have HM : fullScalarCutMoment T U K [a,z,e,e,c,d]=
      fullScalarCutMoment T U K [e,e,a,z,c,d] := by
    unfold fullScalarCutMoment scalarCutMoment
    congr 1
    funext σ
    simp only [List.map_cons,List.map_nil,ClockTree.slotProduct]
    ring
  unfold nativeSixConnectedKernel
  rw [HM,fullScalarCutMoment_cancel_pair,fullScalarCutGamma_self T ho U K,
    fullScalarCutMoment_low_pairing T ho U K a z c d hU haz hcd,one_mul,sub_self]

end OAI.SKFluctuations.Cavity
