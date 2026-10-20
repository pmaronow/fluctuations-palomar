module

public import ComparisonSignedCavitySecondLowParityPath
public import ComparisonSignedCavityActualSixConnectedClassification

@[expose] public section

noncomputable section
set_option maxHeartbeats 10000000
namespace OAI.SKFluctuations.Cavity
open MeasureTheory ProbabilityTheory Filter Set Hierarchy LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
attribute [local instance] Classical.propDecidable

theorem native_full_scalar_cut_nonzero_even_blocks
    {n : ℕ} {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (ho : MassOrdered 0 as) (U : ℕ) (hU0 : 0 < U) (hU : U ≤ as.length)
    (K : ℕ→ℝ) (es : List T.Slot) (H : fullScalarCutMoment T U K es≠0) :
    let : DecidableEq (T.CutBlock U hU):=Classical.decEq _
    ∀B,Even ((es.map (T.cutBlock U hU)).count B) := by
  classical
  have HF : T.disorderExpect (fullWeight n) (fullFeature n) 0
      (cutFullVariance n 0 U 0 0 0 0 K)
      (fun σ=>(1:ℝ)*siteMonomial T σ es) 0≠0 := by
    rw [cut_full_monomial_eq_retained n 0 U 0 0 K T ho (fun _=>1) es,
      T.cavityLeft.disorderExpect_one (restWeight_pos n) (restFeature n) ho,one_mul]
    exact H
  exact cutDisorderExpect_graph_nonzero_even n 0 U hU0 0 0 0 K T hU (fun _=>1) 0
    (by intro i;rfl) (by intro i;rfl) es HF

theorem native_second_low_scalar_nonzero_path
    {n : ℕ} {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (ho : MassOrdered 0 as) (U : ℕ) (hU : U ≤ as.length) (K : ℕ→ℝ)
    (a z f c e d : T.Slot)
    (haz : T.splitIndex a z < U) (hfc : T.splitIndex f c < U) (hed : T.splitIndex e d < U)
    (H : fullScalarCutMoment T U K [a,z,f,c,e,d]≠0) :
    (U ≤ T.splitIndex a f ∧ U ≤ T.splitIndex c e ∧ U ≤ T.splitIndex d z) ∨
    (U ≤ T.splitIndex a f ∧ U ≤ T.splitIndex c d ∧ U ≤ T.splitIndex e z) ∨
    (U ≤ T.splitIndex a c ∧ U ≤ T.splitIndex f e ∧ U ≤ T.splitIndex d z) ∨
    (U ≤ T.splitIndex a c ∧ U ≤ T.splitIndex f d ∧ U ≤ T.splitIndex e z) ∨
    (U ≤ T.splitIndex a e ∧ U ≤ T.splitIndex d f ∧ U ≤ T.splitIndex c z) ∨
    (U ≤ T.splitIndex a e ∧ U ≤ T.splitIndex d c ∧ U ≤ T.splitIndex f z) ∨
    (U ≤ T.splitIndex a d ∧ U ≤ T.splitIndex e f ∧ U ≤ T.splitIndex c z) ∨
    (U ≤ T.splitIndex a d ∧ U ≤ T.splitIndex e c ∧ U ≤ T.splitIndex f z) := by
  classical
  let : DecidableEq (T.CutBlock U hU):=Classical.decEq _
  let B:=T.cutBlock U hU
  have Hne (s t : T.Slot) (hst : T.splitIndex s t < U) : B s≠B t:=by
    intro HE
    have HR:=(T.cutBlock_eq_iff U hU s t).mp HE
    omega
  have HE:=native_full_scalar_cut_nonzero_even_blocks T ho U (by omega) hU K [a,z,f,c,e,d] H
  simp only [List.map_cons,List.map_nil] at HE
  have HR:=native_second_low_even_word_path (B a) (B z) (B f) (B c) (B e) (B d)
    (Hne a z haz) (Hne f c hfc) (Hne e d hed) HE
  dsimp only [B] at HR
  simp only [T.cutBlock_eq_iff] at HR
  exact HR

end OAI.SKFluctuations.Cavity
