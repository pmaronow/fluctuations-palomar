module

public import ComparisonSignedCavityStarFieldForestClassification
public import ComparisonSignedCavityDynamicExteriorTransport
public import ComparisonSignedCavityTwinPrefixNativeLaw

@[expose] public section

noncomputable section
set_option maxHeartbeats 16000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]

theorem native_star_field_expect_smooth {as : List PositiveMass}
    (T : ClockTree S as) {w : S→ℝ} (hw : ∀σ,0<w σ)
    (φ : S→(ι→ℝ)→L[ℝ]ℝ) {a : ℝ} (ho : MassOrdered a as)
    (q : ℕ→ι→ℝ≥0) (J : (ι→ℝ)→T.Assignment→ℝ) (r : ℕ)
    (hJ : ∀σ,BddSmooth r (fun y=>J y σ)) :
    BddSmooth r (fun y=>T.expect w φ q (J y) y) := by
  unfold expect
  apply BddSmooth.sum Finset.univ
  intro σ _
  exact (T.weight_smooth hw φ ho q σ r).mul (hJ σ)

theorem native_prefixTest_dynamic_exterior_sum_swap {ias sas : List PositiveMass}
    {w : S→ℝ} (hw : ∀σ,0<w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (Ei : ClockTree S ias) (Es D : ClockTree S sas) {ast a : ℝ}
    (hos : MassOrdered ast sas) (qi qs : ℕ→ι→ℝ≥0)
    (mid tail : List (GaussianStep ι)) (ho : OrderedSteps a (mid++tail))
    (J : (ι→ℝ)→Ei.Assignment→Es.Assignment→D.Assignment→ℝ)
    (hJ : ∀η ζ δ,BddSmooth 0 (fun y=>J y η ζ δ)) (xi : ι→ℝ) :
    prefixTest mid (gaussianHierarchy w φ tail)
      (fun xs=>Cavity.nativeExteriorForestConditionalTest Ei Es D w φ qi qs (J xs) xi xs) xi=
      Ei.expect w φ qi (fun η=>prefixTest mid (gaussianHierarchy w φ tail)
        (fun xs=>(Es.fork D).expect w φ qs (fun σ=>J xs η σ.1 σ.2) xs) xi) xi := by
  simp_rw [Cavity.nativeExteriorForestConditionalTest_eq_joint]
  apply Cavity.prefixTest_native_expect_swap Ei hw φ qi mid tail ho
  intro η
  exact native_star_field_expect_smooth (Es.fork D) hw φ hos qs
    (fun y σ=>J y η σ.1 σ.2) 0 (fun σ=>hJ η σ.1 σ.2)

def nativeStarFieldDisorderMean (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {as : List PositiveMass} (T : ClockTree S as) (s : T.Slot) (star : ℕ)
    (v : ι→ℝ) (q : ℕ→ι→ℝ) (J : (ι→ℝ)→T.Assignment→ℝ) (x : ι→ℝ) : ℝ :=
  ∫y,nativeStarFieldTestMean w φ T s star
    (cumulativeIncrements (q 0) (fun j=>q (j+1))) J (x+y)
    ∂Measure.pi (fun i=>gaussianReal 0 (Real.toNNReal (q 0 i-v i)))

theorem native_star_field_disorder_field_independent
    {as : List PositiveMass} (T : ClockTree S as) (s : T.Slot) (star : ℕ)
    {w : S→ℝ} (hw : ∀σ,0<w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a as) (v : ι→ℝ) (q : ℕ→ι→ℝ)
    (Q : T.Assignment→ℝ) (x : ι→ℝ) :
    nativeStarFieldDisorderMean w φ T s star v q (fun _ σ=>Q σ) x=
      T.disorderExpect w φ v q Q x := by
  unfold nativeStarFieldDisorderMean
  rw [T.disorderExpect_integral hw φ ho]
  unfold zeroContinuation
  apply integral_congr_ae
  exact Eventually.of_forall (fun y=>
    native_star_field_test_field_independent T s star hw φ ho _ Q (x+y))

end OAI.SKFluctuations.Hierarchy.ClockTree

namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]

theorem native_two_level_star_field_joint_classification
    (pre mid tail : List PositiveMass) (T : ClockTree S (pre++(mid++tail))) (s : T.Slot)
    {U : ℕ} (hmid : 0 < mid.length) (hU : pre.length+mid.length<U)
    (hlen : U≤pre.length+mid.length+tail.length)
    (hT : NativePersistentLowForks pre.length (pre.length+mid.length) U T)
    {w : S→ℝ} (hw : ∀σ,0<w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a (pre++(mid++tail))) :
    ∃(Ei : ClockTree S (mid++tail)) (Es D : ClockTree S tail)
      (read : Ei.Assignment→Es.Assignment→D.Assignment→T.Assignment) (target : D.Slot),
      (∀η ζ δ,T.atSlot (read η ζ δ) s=D.atSlot δ target) ∧
      (∀c,T.splitIndex s c=pre.length → ∃e : Ei.Slot,
        ∀η ζ δ,T.atSlot (read η ζ δ) c=Ei.atSlot η e) ∧
      (∀c,T.splitIndex s c=pre.length+mid.length → ∃e : Es.Slot,
        ∀η ζ δ,T.atSlot (read η ζ δ) c=Es.atSlot ζ e) ∧
      (∀c,pre.length+mid.length<T.splitIndex s c → ∃d : D.Slot,
        (∀η ζ δ,T.atSlot (read η ζ δ) c=D.atSlot δ d) ∧
        pre.length+mid.length+D.splitIndex target d=T.splitIndex s c) ∧
      (∀(q : ℕ→ι→ℝ≥0) (Q : T.Assignment→ℝ) (x : ι→ℝ),
        T.expect w φ q Q x=(nativeExteriorForestTree pre mid Ei Es D).expect w φ q
          (nativeExteriorForestRead pre mid Ei Es D (fun η ζ δ=>Q (read η ζ δ))) x) ∧
      (∀(q : ℕ→ι→ℝ≥0) (J : (ι→ℝ)→T.Assignment→ℝ),
        (∀σ,BddSmooth 0 (fun y=>J y σ)) → ∀x : ι→ℝ,
        nativeStarFieldTestMean w φ T s (pre.length+mid.length) q J x=
          prefixTest (clockSteps pre q)
            (gaussianHierarchy w φ (clockSteps (mid++tail) (fun j=>q (pre.length+j))))
            (fun xi=>prefixTest (clockSteps mid (fun j=>q (pre.length+j)))
              (gaussianHierarchy w φ (clockSteps tail (fun j=>q (pre.length+(mid.length+j)))))
              (fun xs=>nativeExteriorForestConditionalTest Ei Es D w φ
                (fun j=>q (pre.length+j)) (fun j=>q (pre.length+(mid.length+j)))
                (fun η ζ δ=>J xs (read η ζ δ)) xi xs) xi) x) := by
  obtain ⟨Ei,Es,D,read,target,ht,hi,hs,hh,hl,hField⟩:=
    native_two_level_star_field_forest_classification pre mid tail T s hmid hU hlen hT hw φ ho
  refine ⟨Ei,Es,D,read,target,ht,hi,hs,hh,hl,?_⟩
  intro q J hJ x
  rw [hField]
  apply congrArg (fun L=>prefixTest (clockSteps pre q)
    (gaussianHierarchy w φ (clockSteps (mid++tail) (fun j=>q (pre.length+j)))) L x)
  funext xi
  exact (native_prefixTest_dynamic_exterior_sum_swap hw φ Ei Es D ho.suffix_end.suffix_end
    (fun j=>q (pre.length+j)) (fun j=>q (pre.length+(mid.length+j)))
    (clockSteps mid (fun j=>q (pre.length+j)))
    (clockSteps tail (fun j=>q (pre.length+(mid.length+j))))
    (by rw [←clockSteps_append];exact clockSteps_ordered ho.suffix_end _)
    (fun y η ζ δ=>J y (read η ζ δ)) (fun η ζ δ=>hJ (read η ζ δ)) xi).symm

variable [MeasurableSpace S] [StandardBorelSpace S]

theorem native_two_level_star_field_disorder_classification
    (pre mid tail : List PositiveMass) (T : ClockTree S (pre++(mid++tail))) (s : T.Slot)
    {U : ℕ} (hmid : 0 < mid.length) (hU : pre.length+mid.length<U)
    (hlen : U≤pre.length+mid.length+tail.length)
    (hT : NativePersistentLowForks pre.length (pre.length+mid.length) U T)
    {w : S→ℝ} (hw : ∀σ,0<w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a (pre++(mid++tail)))
    (v : ι→ℝ) (q : ℕ→ι→ℝ) (x : ι→ℝ) :
    ∃(Ei : ClockTree S (mid++tail)) (Es D : ClockTree S tail)
      (read : Ei.Assignment→Es.Assignment→D.Assignment→T.Assignment) (target : D.Slot),
      (∀η ζ δ,T.atSlot (read η ζ δ) s=D.atSlot δ target) ∧
      (∀c,T.splitIndex s c=pre.length → ∃e : Ei.Slot,
        ∀η ζ δ,T.atSlot (read η ζ δ) c=Ei.atSlot η e) ∧
      (∀c,T.splitIndex s c=pre.length+mid.length → ∃e : Es.Slot,
        ∀η ζ δ,T.atSlot (read η ζ δ) c=Es.atSlot ζ e) ∧
      (∀c,pre.length+mid.length<T.splitIndex s c → ∃d : D.Slot,
        (∀η ζ δ,T.atSlot (read η ζ δ) c=D.atSlot δ d) ∧
        pre.length+mid.length+D.splitIndex target d=T.splitIndex s c) ∧
      (∀(q₀ : ℕ→ι→ℝ≥0) (Q : T.Assignment→ℝ) (x₀ : ι→ℝ),
        T.expect w φ q₀ Q x₀=(nativeExteriorForestTree pre mid Ei Es D).expect w φ q₀
          (nativeExteriorForestRead pre mid Ei Es D (fun η ζ δ=>Q (read η ζ δ))) x₀) ∧
      (∀J : (ι→ℝ)→T.Assignment→ℝ,(∀σ,BddSmooth 0 (fun y=>J y σ)) →
        nativeStarFieldDisorderMean w φ T s (pre.length+mid.length) v q J x=
          ∫z,nativeExteriorForestConditionalTest Ei Es D w φ
            (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+j))
            (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+(mid.length+j)))
            (fun η ζ δ=>J (exteriorForestStarRoot z) (read η ζ δ))
            (exteriorForestIRoot z) (exteriorForestStarRoot z)
            ∂nativeExteriorForestDisorderRootLaw w φ pre mid tail v q x) := by
  obtain ⟨Ei,Es,D,read,target,ht,hi,hs,hh,hl,hField⟩:=
    native_two_level_star_field_joint_classification pre mid tail T s hmid hU hlen hT hw φ ho
  refine ⟨Ei,Es,D,read,target,ht,hi,hs,hh,hl,?_⟩
  intro J hJ
  have HM:=integral_native_dynamic_exterior_test hw φ pre mid tail ho Ei Es D v q x
    (fun z η ζ δ=>J z.2 (read η ζ δ))
    (fun η ζ δ=>(hJ (read η ζ δ)).compCLM
      (ContinuousLinearMap.snd ℝ (ι→ℝ) (ι→ℝ)))
  dsimp only at HM
  unfold nativeStarFieldDisorderMean
  refine (integral_congr_ae (Eventually.of_forall (fun y=>?_))).trans HM.symm
  simpa only [clockSteps_append] using hField _ J hJ (x+y)

end OAI.SKFluctuations.Cavity
