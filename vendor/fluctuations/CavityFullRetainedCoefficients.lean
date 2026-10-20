module

public import CavityRetainedScalarCoefficients
public import CavityLowCoefficientSelection

@[expose] public section

noncomputable section
set_option maxHeartbeats 1500000
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S B : Type*}

theorem splitIndex_cavityRight {as : List PositiveMass} (T : ClockTree (S×B) as)
    (s t : T.Slot) :
    T.cavityRight.splitIndex (T.cavityRightSlot s) (T.cavityRightSlot t)=T.splitIndex s t := by
  induction T with
  | leaf => rfl
  | step a T ih => exact congrArg (1+·) (ih s t)
  | fork T V ihT ihV => cases s <;> cases t <;>
      first | rfl | exact ihT _ _ | exact ihV _ _

end OAI.SKFluctuations.Hierarchy.ClockTree

namespace OAI.SKFluctuations.Cavity
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped BigOperators Topology NNReal

def fullScalarCutMoment {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (U : ℕ) (K : ℕ→ℝ) (es : List T.Slot) : ℝ :=
  scalarCutMoment T.cavityRight U K (es.map T.cavityRightSlot)

def fullScalarCutGamma {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (U : ℕ) (K : ℕ→ℝ) (a c : T.Slot) : ℝ :=
  fullScalarCutMoment T U K [a,c]

def fullScalarCutConnected4 {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (U : ℕ) (K : ℕ→ℝ) (a c e f : T.Slot) : ℝ :=
  fullScalarCutMoment T U K [a,c,e,f]-fullScalarCutGamma T U K a c*fullScalarCutGamma T U K e f

theorem siteMonomial_eq_scalar {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (σ : T.Assignment) (es : List T.Slot) :
    siteMonomial T σ es=T.cavityRight.slotProduct spinValue (T.cavityAssignment σ).2
      (es.map T.cavityRightSlot) := by
  induction es with
  | nil => rfl
  | cons s es ih => simp only [siteMonomial,List.map_cons,ClockTree.slotProduct,
      T.atSlot_cavityRight,ih]

theorem cut_full_monomial_eq_retained (n : ℕ) (q : ℕ→RestCoordinate n→ℝ)
    (U : ℕ) (b h K : ℕ→ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (es : List T.Slot) :
    T.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U 0 0 b h K)
      (fun σ=>P (T.cavityAssignment σ).1*siteMonomial T σ es) 0 =
    T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q P 0*
      fullScalarCutMoment T U K es := by
  have he:=cutDisorderExpect_scalar_product n q U 0 b h K T ho P
    (fun σ=>T.cavityRight.slotProduct spinValue σ (es.map T.cavityRightSlot)) 0
  simp only [map_zero] at he
  simpa only [Pi.zero_def,siteMonomial_eq_scalar,fullScalarCutMoment,scalarCutMoment] using he

theorem fullScalarCutMoment_factor {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (U : ℕ) (hU0 : 0<U) (hU : U≤as.length) (K : ℕ→ℝ) (es fs : List T.Slot)
    (hcross : ∀ s∈es, ∀ t∈fs, T.splitIndex s t<U) :
    fullScalarCutMoment T U K (es++fs)=
      fullScalarCutMoment T U K es*fullScalarCutMoment T U K fs := by
  unfold fullScalarCutMoment
  rw [List.map_append]
  apply scalarCutMoment_factor T.cavityRight ho U hU0 hU K
  intro s hs t ht
  obtain ⟨s,hes,rfl⟩:=List.mem_map.mp hs
  obtain ⟨t,het,rfl⟩:=List.mem_map.mp ht
  simpa only [T.splitIndex_cavityRight] using hcross s hes t het

theorem cut_full_retained_four (n : ℕ) (q : ℕ→RestCoordinate n→ℝ)
    (U : ℕ) (hU0 : 0<U) (b h K : ℕ→ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as) (hU : U≤as.length)
    (P : T.cavityLeft.Assignment→ℝ) (a c z d : T.Slot)
    (hcross : ∀ s∈[a,c], ∀ t∈[z,d], T.splitIndex s t<U) :
    T.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U 0 0 b h K)
      (fun σ=>P (T.cavityAssignment σ).1*siteMonomial T σ [a,c,z,d]) 0 =
      fullScalarCutGamma T U K a c*fullScalarCutGamma T U K z d*
        T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q P 0 := by
  rw [cut_full_monomial_eq_retained n q U b h K T ho]
  have hf:=fullScalarCutMoment_factor T ho U hU0 hU K [a,c] [z,d] hcross
  simp only [List.cons_append,List.nil_append] at hf
  rw [hf]
  unfold fullScalarCutGamma
  ring

end OAI.SKFluctuations.Cavity
