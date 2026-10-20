module

public import CavityScalarBlockFactorization
public import CavityScalarRowBridge
public import SKFluctuationsOAI.Probability.SKFluctuations.CavityMixedInsertion

@[expose] public section

noncomputable section
set_option maxHeartbeats 1500000
namespace OAI.SKFluctuations.Cavity
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped BigOperators Topology NNReal

def scalarCutMoment {as : List PositiveMass} (T : ClockTree Bool as)
    (U : ℕ) (K : ℕ → ℝ) (es : List T.Slot) : ℝ :=
  T.disorderExpect (fun _=>(1/2:ℝ)) scalarFeature 0
    (fun j _=>relocatedClock U 0 K j)
    (fun σ=>T.slotProduct spinValue σ es) 0

def scalarCutGamma {as : List PositiveMass} (T : ClockTree Bool as)
    (U : ℕ) (K : ℕ → ℝ) (a c : T.Slot) : ℝ := scalarCutMoment T U K [a,c]

def scalarCutConnected4 {as : List PositiveMass} (T : ClockTree Bool as)
    (U : ℕ) (K : ℕ → ℝ) (a c e f : T.Slot) : ℝ :=
  scalarCutMoment T U K [a,c,e,f]-scalarCutGamma T U K a c*scalarCutGamma T U K e f

theorem scalarCutMoment_eq_expect {as : List PositiveMass} (T : ClockTree Bool as)
    (ho : MassOrdered 0 as) (U : ℕ) (hU0 : 0<U) (K : ℕ → ℝ) (es : List T.Slot) :
    scalarCutMoment T U K es =
      T.expect (fun _=>(1/2:ℝ)) scalarFeature
        (cumulativeIncrements (fun _=>relocatedClock U 0 K 0)
          (fun j _=>relocatedClock U 0 K (j+1)))
        (fun σ=>T.slotProduct spinValue σ es) 0 := by
  unfold scalarCutMoment
  rw [T.disorderExpect_integral (by intro σ; norm_num) scalarFeature ho]
  simp only [Pi.zero_apply,relocatedClock,hU0,ite_true,zero_mul,sub_zero,Real.toNNReal_zero,
    isotropicGaussian_zero,zeroContinuation,integral_dirac,add_zero]

theorem scalarCutMoment_factor {as : List PositiveMass} (T : ClockTree Bool as)
    (ho : MassOrdered 0 as) (U : ℕ) (hU0 : 0<U) (hU : U≤as.length)
    (K : ℕ → ℝ) (es fs : List T.Slot)
    (hcross : ∀ s∈es, ∀ t∈fs, T.splitIndex s t<U) :
    scalarCutMoment T U K (es++fs)=scalarCutMoment T U K es*scalarCutMoment T U K fs := by
  rw [scalarCutMoment_eq_expect T ho U hU0,scalarCutMoment_eq_expect T ho U hU0,
    scalarCutMoment_eq_expect T ho U hU0]
  apply T.expect_slotProduct_cut_factor (by intro σ; norm_num) scalarFeature ho _ U hU
    (f:=spinValue) (es:=es) (fs:=fs) (x:=0)
  · intro j hj
    funext i
    cases j with
    | zero => simp [cumulativeIncrements,relocatedClock,hU0,hj]
    | succ j =>
      have h1 : j+1<U := by omega
      simp [cumulativeIncrements,relocatedClock,h1,hj,Nat.succ_eq_add_one]
  · exact hcross

theorem scalar_retained_four (T : ClockTree Bool as) (ho : MassOrdered 0 as)
    (U : ℕ) (hU0 : 0<U) (hU : U≤as.length) (K : ℕ → ℝ)
    (a c b d : T.Slot)
    (hcross : ∀ s∈[a,c], ∀ t∈[b,d], T.splitIndex s t<U) :
    scalarCutMoment T U K [a,c,b,d]=scalarCutGamma T U K a c*scalarCutGamma T U K b d :=
  scalarCutMoment_factor T ho U hU0 hU K [a,c] [b,d] hcross

theorem scalar_retained_six_connected_left (T : ClockTree Bool as)
    (ho : MassOrdered 0 as) (U : ℕ) (hU0 : 0<U) (hU : U≤as.length) (K : ℕ → ℝ)
    (a c b d e f : T.Slot)
    (hcross : ∀ s∈[a,c,e,f], ∀ t∈[b,d], T.splitIndex s t<U) :
    scalarCutMoment T U K [a,c,b,d,e,f]-
      scalarCutGamma T U K a c*scalarCutGamma T U K b d*scalarCutGamma T U K e f =
      scalarCutConnected4 T U K a c e f*scalarCutGamma T U K b d := by
  have he : scalarCutMoment T U K [a,c,b,d,e,f]=scalarCutMoment T U K [a,c,e,f,b,d] := by
    unfold scalarCutMoment
    congr 1
    funext σ
    simp only [ClockTree.slotProduct]
    ring
  have hf:=scalarCutMoment_factor T ho U hU0 hU K [a,c,e,f] [b,d] hcross
  simp only [List.cons_append,List.nil_append] at hf
  rw [he,hf]
  unfold scalarCutConnected4 scalarCutGamma
  ring

theorem scalar_retained_six_connected_right (T : ClockTree Bool as)
    (ho : MassOrdered 0 as) (U : ℕ) (hU0 : 0<U) (hU : U≤as.length) (K : ℕ → ℝ)
    (a c b d e f : T.Slot)
    (hcross : ∀ s∈[a,c], ∀ t∈[b,d,e,f], T.splitIndex s t<U) :
    scalarCutMoment T U K [a,c,b,d,e,f]-
      scalarCutGamma T U K a c*scalarCutGamma T U K b d*scalarCutGamma T U K e f =
      scalarCutGamma T U K a c*scalarCutConnected4 T U K b d e f := by
  have hf:=scalarCutMoment_factor T ho U hU0 hU K [a,c] [b,d,e,f] hcross
  simp only [List.cons_append,List.nil_append] at hf
  rw [hf]
  unfold scalarCutConnected4 scalarCutGamma
  ring

theorem scalar_retained_six_connected_outside (T : ClockTree Bool as)
    (ho : MassOrdered 0 as) (U : ℕ) (hU0 : 0<U) (hU : U≤as.length) (K : ℕ → ℝ)
    (a c b d e f : T.Slot)
    (h1 : ∀ s∈[a,c], ∀ t∈[b,d,e,f], T.splitIndex s t<U)
    (h2 : ∀ s∈[b,d], ∀ t∈[e,f], T.splitIndex s t<U) :
    scalarCutMoment T U K [a,c,b,d,e,f]-
      scalarCutGamma T U K a c*scalarCutGamma T U K b d*scalarCutGamma T U K e f = 0 := by
  have hf1:=scalarCutMoment_factor T ho U hU0 hU K [a,c] [b,d,e,f] h1
  have hf2:=scalarCutMoment_factor T ho U hU0 hU K [b,d] [e,f] h2
  simp only [List.cons_append,List.nil_append] at hf1 hf2
  rw [hf1,hf2]
  unfold scalarCutGamma
  ring

end OAI.SKFluctuations.Cavity
