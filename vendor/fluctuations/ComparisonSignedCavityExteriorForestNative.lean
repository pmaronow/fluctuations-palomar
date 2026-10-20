module

public import ComparisonSignedCavityExteriorForestLaw

@[expose] public section

noncomputable section
set_option maxHeartbeats 6000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]
open Cavity

def exteriorPrepend (pre : List PositiveMass) {tail : List PositiveMass}
    (T : ClockTree S tail) : ClockTree S (pre++tail) :=
  match pre with
  | []=>T
  | b::pre=>(exteriorPrepend pre T).step b

def exteriorPrependAssignmentEquiv (pre : List PositiveMass) {tail : List PositiveMass}
    (T : ClockTree S tail) : (exteriorPrepend pre T).Assignment ≃ T.Assignment :=
  match pre with
  | []=>Equiv.refl _
  | _::pre=>exteriorPrependAssignmentEquiv pre T

theorem exteriorPrepend_expect (pre : List PositiveMass) {tail : List PositiveMass}
    {w : S→ℝ} (hw : ∀ σ,0<w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (T : ClockTree S tail) {a : ℝ} (ho : MassOrdered a (pre++tail))
    (q : ℕ→ι→ℝ≥0) (Q : T.Assignment→ℝ) (x : ι→ℝ) :
    (exteriorPrepend pre T).expect w φ q
      (fun σ=>Q (exteriorPrependAssignmentEquiv pre T σ)) x =
      prefixTest (clockSteps pre q)
        (gaussianHierarchy w φ (clockSteps tail (fun j=>q (pre.length+j))))
        (T.expect w φ (fun j=>q (pre.length+j)) Q) x := by
  induction pre generalizing a q x with
  | nil =>
    simp only [exteriorPrepend,exteriorPrependAssignmentEquiv,clockSteps,
      prefixTest,List.length_nil,Nat.zero_add]
    rfl
  | cons b pre ih =>
    change ((exteriorPrepend pre T).step b).expect w φ q
      (fun σ=>Q (exteriorPrependAssignmentEquiv pre T σ)) x = _
    rw [ClockTree.expect_step hw φ b _ ho.2.2]
    have he : (exteriorPrepend pre T).expect w φ (fun j=>q (j+1))
        (fun σ=>Q (exteriorPrependAssignmentEquiv pre T σ)) =
        prefixTest (clockSteps pre (fun j=>q (j+1)))
          (gaussianHierarchy w φ (clockSteps tail (fun j=>q (pre.length+j+1))))
          (T.expect w φ (fun j=>q (pre.length+j+1)) Q) :=
      funext fun y=>ih ho.2.2 (fun j=>q (j+1)) y
    rw [he]
    simp only [clockSteps,prefixTest,List.length_cons]
    have hq : (fun j=>q (pre.length+j+1))=(fun j=>q (pre.length+1+j)) := by
      funext j;congr 1;omega
    rw [hq,prefixContinuation_hierarchy]
    have hc : clockSteps (pre++tail) (fun j=>q (j+1)) =
        clockSteps pre (fun j=>q (j+1))++clockSteps tail (fun j=>q (pre.length+1+j)) := by
      rw [clockSteps_append,hq]
    exact congrArg (fun ls=>shiftedMean (Measure.pi fun i=>gaussianReal 0 (q 0 i)) b.val
      (gaussianHierarchy w φ ls)
      (prefixTest (clockSteps pre (fun j=>q (j+1)))
        (gaussianHierarchy w φ (clockSteps tail (fun j=>q (pre.length+1+j))))
        (T.expect w φ (fun j=>q (pre.length+1+j)) Q)) x) hc

def exteriorQuadNative {as : List PositiveMass} (T : ClockTree S as) : ClockTree S as :=
  (T.fork T).fork (T.fork T)

omit [Nonempty S] in
theorem exteriorForkNative_expect_product {as : List PositiveMass}
    (T V : ClockTree S as) (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (q : ℕ→ι→ℝ≥0) (A : T.Assignment→ℝ) (B : V.Assignment→ℝ) (x : ι→ℝ) :
    (T.fork V).expect w φ q (fun σ=>A σ.1*B σ.2) x =
      T.expect w φ q A x*V.expect w φ q B x := by
  unfold ClockTree.expect
  simp only [ClockTree.weight_fork,Fintype.sum_prod_type]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

omit [Nonempty S] in
theorem exteriorQuadNative_expect_product {as : List PositiveMass}
    (T : ClockTree S as) (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (q : ℕ→ι→ℝ≥0) (A B C D : T.Assignment→ℝ) (x : ι→ℝ) :
    (exteriorQuadNative T).expect w φ q
      (fun σ=>A σ.1.1*B σ.1.2*C σ.2.1*D σ.2.2) x =
      T.expect w φ q A x*T.expect w φ q B x*T.expect w φ q C x*T.expect w φ q D x := by
  unfold exteriorQuadNative
  have hf : (fun σ : ((T.fork T).fork (T.fork T)).Assignment=>
      A σ.1.1*B σ.1.2*C σ.2.1*D σ.2.2) =
      fun σ=>(A σ.1.1*B σ.1.2)*(C σ.2.1*D σ.2.2) := by funext σ;ring
  rw [hf]
  calc
    _ = (T.fork T).expect w φ q (fun η=>A η.1*B η.2) x*
        (T.fork T).expect w φ q (fun η=>C η.1*D η.2) x :=
      exteriorForkNative_expect_product (T.fork T) (T.fork T) w φ q _ _ x
    _ = _ := by
      rw [exteriorForkNative_expect_product,exteriorForkNative_expect_product]
      ring

end OAI.SKFluctuations.Hierarchy.ClockTree

namespace OAI.SKFluctuations.Cavity
open Hierarchy
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]

def nativeExteriorForestMean {ias sas : List PositiveMass}
    (Ei : ClockTree S ias) (Es : ClockTree S sas) (w : S→ℝ)
    (φ : S→(ι→ℝ)→L[ℝ]ℝ) (qi qs : ℕ→ι→ℝ≥0)
    (Q : Ei.Assignment→Es.Assignment→ℝ) (xi xs : ι→ℝ) : ℝ :=
  Ei.expect w φ qi (fun η=>Es.expect w φ qs (Q η) xs) xi

def nativeExteriorForestConditionalTest {ias sas : List PositiveMass}
    (Ei : ClockTree S ias) (Es D : ClockTree S sas) (w : S→ℝ)
    (φ : S→(ι→ℝ)→L[ℝ]ℝ) (qi qs : ℕ→ι→ℝ≥0)
    (Q : Ei.Assignment→Es.Assignment→D.Assignment→ℝ) (xi xs : ι→ℝ) : ℝ :=
  D.expect w φ qs (fun σ=>nativeExteriorForestMean Ei Es w φ qi qs (fun η ζ=>Q η ζ σ) xi xs) xs

omit [Nonempty S] in
theorem nativeExteriorForestConditionalTest_eq_joint {ias sas : List PositiveMass}
    (Ei : ClockTree S ias) (Es D : ClockTree S sas) (w : S→ℝ)
    (φ : S→(ι→ℝ)→L[ℝ]ℝ) (qi qs : ℕ→ι→ℝ≥0)
    (Q : Ei.Assignment→Es.Assignment→D.Assignment→ℝ) (xi xs : ι→ℝ) :
    nativeExteriorForestConditionalTest Ei Es D w φ qi qs Q xi xs =
      Ei.expect w φ qi (fun η=>(Es.fork D).expect w φ qs (fun σ=>Q η σ.1 σ.2) xs) xi := by
  unfold nativeExteriorForestConditionalTest nativeExteriorForestMean
  simp only [ClockTree.expect,ClockTree.weight_fork,Fintype.sum_prod_type,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro η _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ζ _
  apply Finset.sum_congr rfl
  intro σ _
  ring

def nativeExteriorForestTree (pre mid : List PositiveMass) {tail : List PositiveMass}
    (Ei : ClockTree S (mid++tail)) (Es D : ClockTree S tail) :
    ClockTree S (pre++(mid++tail)) :=
  ClockTree.exteriorPrepend pre (Ei.fork (ClockTree.exteriorPrepend mid (Es.fork D)))

def nativeExteriorForestRead (pre mid : List PositiveMass) {tail : List PositiveMass}
    (Ei : ClockTree S (mid++tail)) (Es D : ClockTree S tail)
    (Q : Ei.Assignment→Es.Assignment→D.Assignment→ℝ) :
    (nativeExteriorForestTree pre mid Ei Es D).Assignment→ℝ :=
  fun σ=>
    let z:=ClockTree.exteriorPrependAssignmentEquiv pre
      (Ei.fork (ClockTree.exteriorPrepend mid (Es.fork D))) σ
    let u:=ClockTree.exteriorPrependAssignmentEquiv mid (Es.fork D) z.2
    Q z.1 u.1 u.2

theorem nativeExteriorForestConditionalTest_smooth_joint {ias sas : List PositiveMass}
    {w : S→ℝ} (hw : ∀ σ,0<w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (Ei : ClockTree S ias) (Es D : ClockTree S sas) {ai ast : ℝ}
    (hoi : MassOrdered ai ias) (hos : MassOrdered ast sas)
    (qi qs : ℕ→ι→ℝ≥0) (Q : Ei.Assignment→Es.Assignment→D.Assignment→ℝ) (r : ℕ) :
    BddSmooth r (fun z : (ι→ℝ)×(ι→ℝ)=>nativeExteriorForestConditionalTest Ei Es D w φ qi qs Q z.1 z.2) := by
  have he : (fun z : (ι→ℝ)×(ι→ℝ)=>nativeExteriorForestConditionalTest Ei Es D w φ qi qs Q z.1 z.2) =
      fun z=>Ei.expect w φ qi (fun η=>(Es.fork D).expect w φ qs (fun σ=>Q η σ.1 σ.2) z.2) z.1 :=
    funext fun z=>nativeExteriorForestConditionalTest_eq_joint Ei Es D w φ qi qs Q z.1 z.2
  rw [he]
  unfold ClockTree.expect
  apply BddSmooth.sum Finset.univ
  intro η _
  exact ((Ei.weight_smooth hw φ hoi qi η r).compCLM
    (ContinuousLinearMap.fst ℝ (ι→ℝ) (ι→ℝ))).mul
      (((Es.fork D).nativeAnchor_expect_smooth hw φ hos qs (fun σ=>Q η σ.1 σ.2) r).compCLM
        (ContinuousLinearMap.snd ℝ (ι→ℝ) (ι→ℝ)))

theorem nativeExteriorForestConditionalTest_smooth_star {ias sas : List PositiveMass}
    {w : S→ℝ} (hw : ∀ σ,0<w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (Ei : ClockTree S ias) (Es D : ClockTree S sas) {ast : ℝ}
    (hos : MassOrdered ast sas) (qi qs : ℕ→ι→ℝ≥0)
    (Q : Ei.Assignment→Es.Assignment→D.Assignment→ℝ) (xi : ι→ℝ) (r : ℕ) :
    BddSmooth r (nativeExteriorForestConditionalTest Ei Es D w φ qi qs Q xi) := by
  have he : nativeExteriorForestConditionalTest Ei Es D w φ qi qs Q xi =
      fun xs=>Ei.expect w φ qi (fun η=>(Es.fork D).expect w φ qs (fun σ=>Q η σ.1 σ.2) xs) xi :=
    funext fun xs=>nativeExteriorForestConditionalTest_eq_joint Ei Es D w φ qi qs Q xi xs
  rw [he]
  unfold ClockTree.expect
  apply BddSmooth.sum Finset.univ
  intro η _
  exact ((Es.fork D).nativeAnchor_expect_smooth hw φ hos qs (fun σ=>Q η σ.1 σ.2) r).const_mul
    (Ei.weight w φ qi η xi)

theorem native_prefixTest_exterior_sum_swap {ias sas : List PositiveMass}
    {w : S→ℝ} (hw : ∀ σ,0<w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (Ei : ClockTree S ias) (Es D : ClockTree S sas) {ast a : ℝ}
    (hos : MassOrdered ast sas) (qi qs : ℕ→ι→ℝ≥0)
    (mid tail : List (GaussianStep ι)) (ho : OrderedSteps a (mid++tail))
    (Q : Ei.Assignment→Es.Assignment→D.Assignment→ℝ) (xi : ι→ℝ) :
    prefixTest mid (gaussianHierarchy w φ tail)
      (nativeExteriorForestConditionalTest Ei Es D w φ qi qs Q xi) xi =
    Ei.expect w φ qi (fun η=>prefixTest mid (gaussianHierarchy w φ tail)
      ((Es.fork D).expect w φ qs (fun σ=>Q η σ.1 σ.2)) xi) xi := by
  have he : nativeExteriorForestConditionalTest Ei Es D w φ qi qs Q xi =
      fun xs=>Ei.expect w φ qi (fun η=>(Es.fork D).expect w φ qs (fun σ=>Q η σ.1 σ.2) xs) xi :=
    funext fun xs=>nativeExteriorForestConditionalTest_eq_joint Ei Es D w φ qi qs Q xi xs
  rw [he]
  change prefixTest mid (gaussianHierarchy w φ tail)
    (fun y=>∑ η,Ei.weight w φ qi η xi*(Es.fork D).expect w φ qs (fun σ=>Q η σ.1 σ.2) y) xi =
    ∑ η,Ei.weight w φ qi η xi*prefixTest mid (gaussianHierarchy w φ tail)
      ((Es.fork D).expect w φ qs (fun σ=>Q η σ.1 σ.2)) xi
  rw [prefixTest_fintype_sum hw φ mid tail ho _ (fun η=>
    ((Es.fork D).nativeAnchor_expect_smooth hw φ hos qs (fun σ=>Q η σ.1 σ.2) 0).const_mul
      (Ei.weight w φ qi η xi)) xi]
  apply Finset.sum_congr rfl
  intro η _
  exact prefixTest_scalar_mul mid _ _ _ xi

theorem nativeExteriorForestTail_expect_eq_prefix (mid : List PositiveMass)
    {tail : List PositiveMass} {w : S→ℝ} (hw : ∀ σ,0<w σ)
    (φ : S→(ι→ℝ)→L[ℝ]ℝ) (Ei : ClockTree S (mid++tail))
    (Es D : ClockTree S tail) {a : ℝ} (ho : MassOrdered a (mid++tail))
    (q : ℕ→ι→ℝ≥0) (Q : Ei.Assignment→Es.Assignment→D.Assignment→ℝ) (xi : ι→ℝ) :
    (Ei.fork (ClockTree.exteriorPrepend mid (Es.fork D))).expect w φ q
      (fun z=>let u:=ClockTree.exteriorPrependAssignmentEquiv mid (Es.fork D) z.2;
        Q z.1 u.1 u.2) xi =
      prefixTest (clockSteps mid q)
        (gaussianHierarchy w φ (clockSteps tail (fun j=>q (mid.length+j))))
        (nativeExteriorForestConditionalTest Ei Es D w φ q (fun j=>q (mid.length+j)) Q xi) xi := by
  rw [ClockTree.expect_fork]
  have he (η : Ei.Assignment) := ClockTree.exteriorPrepend_expect mid hw φ (Es.fork D) ho q
    (fun σ=>Q η σ.1 σ.2) xi
  simp_rw [he]
  have hoG : OrderedSteps a (clockSteps mid q++clockSteps tail (fun j=>q (mid.length+j))) := by
    rw [←clockSteps_append]
    exact clockSteps_ordered ho q
  exact (native_prefixTest_exterior_sum_swap hw φ Ei Es D ho.suffix_end q
    (fun j=>q (mid.length+j)) (clockSteps mid q) _ hoG Q xi).symm

theorem nativeExteriorForestTree_expect_eq_prefix (pre mid : List PositiveMass)
    {tail : List PositiveMass} {w : S→ℝ} (hw : ∀ σ,0<w σ)
    (φ : S→(ι→ℝ)→L[ℝ]ℝ) (Ei : ClockTree S (mid++tail))
    (Es D : ClockTree S tail) {a : ℝ} (ho : MassOrdered a (pre++(mid++tail)))
    (q : ℕ→ι→ℝ≥0) (Q : Ei.Assignment→Es.Assignment→D.Assignment→ℝ) (x : ι→ℝ) :
    (nativeExteriorForestTree pre mid Ei Es D).expect w φ q
      (nativeExteriorForestRead pre mid Ei Es D Q) x =
    prefixTest (clockSteps pre q)
      (gaussianHierarchy w φ (clockSteps (mid++tail) (fun j=>q (pre.length+j))))
      (fun xi=>prefixTest (clockSteps mid (fun j=>q (pre.length+j)))
        (gaussianHierarchy w φ (clockSteps tail (fun j=>q (pre.length+(mid.length+j)))))
        (nativeExteriorForestConditionalTest Ei Es D w φ (fun j=>q (pre.length+j))
          (fun j=>q (pre.length+(mid.length+j))) Q xi) xi) x := by
  let T:=Ei.fork (ClockTree.exteriorPrepend mid (Es.fork D))
  let Q0 : T.Assignment→ℝ:=fun z=>
    let u:=ClockTree.exteriorPrependAssignmentEquiv mid (Es.fork D) z.2
    Q z.1 u.1 u.2
  have hcore := funext fun xi=>nativeExteriorForestTail_expect_eq_prefix mid hw φ Ei Es D
    ho.suffix_end (fun j=>q (pre.length+j)) Q xi
  have hpre:=ClockTree.exteriorPrepend_expect pre hw φ T ho q Q0 x
  change (ClockTree.exteriorPrepend pre T).expect w φ q
    (fun σ=>Q0 (ClockTree.exteriorPrependAssignmentEquiv pre T σ)) x = _
  rw [hpre]
  rw [hcore]

end OAI.SKFluctuations.Cavity
