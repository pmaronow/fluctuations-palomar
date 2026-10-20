module

public import ComparisonSignedCavityActualFiniteProfileMarginal
public import ComparisonSignedCavityActualFullMarkedProfileExchange

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Hierarchy.ClockTree
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
variable {S ι : Type} [Fintype S] [Nonempty S] [Fintype ι] [Nonempty ι]
set_option maxHeartbeats 18000000

omit [Nonempty ι] in
theorem native_disorder_row_transport_from_expect
    {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {as : List PositiveMass} (T : ClockTree S as) (ho : MassOrdered 0 as)
    (P Q : T.Assignment→ℝ)
    (hEq : ∀(q : ℕ→ι→ℝ≥0) x,T.expect w φ q P x=T.expect w φ q Q x)
    (v : ι→ℝ) (q : ℕ→ι→ℝ) (u x : ι→ℝ) :
    nativeMarkedDisorderRow w φ T v q P (fun σ=>φ σ u) x=
      nativeMarkedDisorderRow w φ T v q Q (fun σ=>φ σ u) x := by
  have Hrow (qc : ℕ→ι→ℝ≥0) (y : ι→ℝ) :
      nativeMarkedExpectRow w φ T qc P (fun σ=>φ σ u) y=
        nativeMarkedExpectRow w φ T qc Q (fun σ=>φ σ u) y := by
    have HL:=nativeMarkedExpectRow_hasDerivAt hw φ T ho qc P u y 0
    have HR:=nativeMarkedExpectRow_hasDerivAt hw φ T ho qc Q u y 0
    have Hfun : (fun t : ℝ=>T.expect w φ qc P (y+t • u))=
        (fun t : ℝ=>T.expect w φ qc Q (y+t • u)):=funext fun t=>hEq qc _
    rw [Hfun] at HL
    simpa only [zero_smul,add_zero] using HL.unique HR
  rw [nativeMarkedDisorderRow_eq_integral hw φ T ho,nativeMarkedDisorderRow_eq_integral hw φ T ho]
  apply integral_congr_ae
  exact Eventually.of_forall fun y=>Hrow _ _

theorem native_observed_covariance_transport_strict_from_expect
    {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {as : List PositiveMass} (T : ClockTree S as) (ho : MassOrdered 0 as)
    (P Q : T.Assignment→ℝ)
    (hEq : ∀(q : ℕ→ι→ℝ≥0) x,T.expect w φ q P x=T.expect w φ q Q x)
    (v u : ι→ℝ) (D : ℕ→ι→ℝ) {B : ℝ} (hB : 0 ≤ B) (hD : ∀j i,|D j i| ≤ B)
    (q : ℕ→ι→ℝ) {epsilon : ℝ} (he : 0 < epsilon)
    (hq : strictCumulativeClock v q epsilon) (x : ι→ℝ) :
    nativeMarkedProfileRow w φ T v q [ReplicaTree.coordinateProfile φ D] P (fun σ=>φ σ u) x=
      nativeMarkedProfileRow w φ T v q [ReplicaTree.coordinateProfile φ D] Q (fun σ=>φ σ u) x := by
  let radius:=epsilon/(2*(2*B+1))
  have hrpos : 0 < radius:=by dsimp [radius];positivity
  have hpert (t : ℝ) (ht : t∈Ioo (-radius) radius) :
      strictCumulativeClock v (fun j i=>q j i+t*D j i) (epsilon/2) := by
    apply strictCumulativeClock_perturb he hB hq hD
    have htabs : |t| ≤ radius:=(abs_le).2 ⟨ht.1.le,ht.2.le⟩
    have HH:=mul_le_mul_of_nonneg_right htabs (by positivity : 0 ≤ 2*B+1)
    have hrad : radius*(2*B+1)=epsilon/2:=by dsimp [radius];field_simp
    rwa [hrad] at HH
  have hmono : ∀t∈Ioo (-radius) radius,∀i,Monotone (fun j=>q j i+t*D j i) := by
    intro t ht i
    exact (hpert t ht).monotone (by positivity) i
  have hroot : ∀t∈Ioo (-radius) radius,∀i,v i ≤ q 0 i+t*D 0 i := by
    intro t ht i
    have H:=(hpert t ht).1 i
    linarith
  have hzero : (0:ℝ)∈Ioo (-radius) radius:=by constructor <;> linarith
  have HL:=nativeMarkedProfileRow_hasDerivAt hw φ T ho v q D hmono hroot [] P (fun σ=>φ σ u) x hzero
  have HR:=nativeMarkedProfileRow_hasDerivAt hw φ T ho v q D hmono hroot [] Q (fun σ=>φ σ u) x hzero
  have HF : (fun t=>nativeMarkedProfileRow w φ T v (fun j i=>q j i+t*D j i) [] P (fun σ=>φ σ u) x)=
      (fun t=>nativeMarkedProfileRow w φ T v (fun j i=>q j i+t*D j i) [] Q (fun σ=>φ σ u) x) := by
    funext t
    exact native_disorder_row_transport_from_expect hw φ T ho P Q hEq v _ u x
  rw [HF] at HL
  simpa only [List.nil_append,zero_mul,add_zero] using HL.unique HR

theorem native_observed_covariance_transport_from_expect
    {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {as : List PositiveMass} (T : ClockTree S as) (ho : MassOrdered 0 as)
    (P Q : T.Assignment→ℝ)
    (hEq : ∀(q : ℕ→ι→ℝ≥0) x,T.expect w φ q P x=T.expect w φ q Q x)
    (v : ι→ℝ) (q : ℕ→ι→ℝ) (hq : ∀i,Monotone (fun j=>q j i))
    (hq0 : ∀i,v i ≤ q 0 i) (D : ℕ→ι→ℝ) (u x : ι→ℝ) :
    nativeMarkedProfileRow w φ T v q [ReplicaTree.coordinateProfile φ D] P (fun σ=>φ σ u) x=
      nativeMarkedProfileRow w φ T v q [ReplicaTree.coordinateProfile φ D] Q (fun σ=>φ σ u) x := by
  obtain ⟨B,hB,hD⟩:=exists_single_direction_finite_bound as.length D
  let E:=clipDirection as.length D
  have hE : ∀j i,|E j i| ≤ B:=
    clipDirection_bounded as.length [D] hB hD E (by simp [E])
  let qr:=fun e : ℝ=>fun j i=>q j i+e*(j+1:ℕ)
  have HE : EqOn
      (fun e=>nativeMarkedProfileRow w φ T v (qr e) [ReplicaTree.coordinateProfile φ E] P (fun σ=>φ σ u) x)
      (fun e=>nativeMarkedProfileRow w φ T v (qr e) [ReplicaTree.coordinateProfile φ E] Q (fun σ=>φ σ u) x)
      (Ioi (0:ℝ)) := by
    intro e he
    exact native_observed_covariance_transport_strict_from_expect hw φ T ho P Q hEq v u E hB hE
      (qr e) he (strictCumulativeClock_regularize hq hq0 he.le) x
  have hc (j : ℕ) : Continuous (fun e=>qr e j):=by dsimp [qr];fun_prop
  have HL:=nativeMarkedProfileRow_continuous hw φ T ho v qr hc
    [ReplicaTree.coordinateProfile φ E] P (fun σ=>φ σ u) x
  have HR:=nativeMarkedProfileRow_continuous hw φ T ho v qr hc
    [ReplicaTree.coordinateProfile φ E] Q (fun σ=>φ σ u) x
  have h0 : (0:ℝ)∈closure (Ioi (0:ℝ)):=by
    simpa only [closure_Ioi,mem_Ici] using (le_rfl : (0:ℝ) ≤ 0)
  have H:=HE.closure HL HR h0
  simp only [qr,zero_mul,add_zero] at H
  change nativeMarkedProfileRow w φ T v q ([D].map (ReplicaTree.coordinateProfile φ)) P (fun σ=>φ σ u) x=
    nativeMarkedProfileRow w φ T v q ([D].map (ReplicaTree.coordinateProfile φ)) Q (fun σ=>φ σ u) x
  rw [nativeMarkedProfileRow_clip_directions w φ T v q [D] P (fun σ=>φ σ u) x,
    nativeMarkedProfileRow_clip_directions w φ T v q [D] Q (fun σ=>φ σ u) x]
  exact H

end OAI.SKFluctuations.Hierarchy.ClockTree
