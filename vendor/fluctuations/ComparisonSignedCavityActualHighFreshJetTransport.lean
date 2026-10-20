module

public import ComparisonSignedCavityHighFreshFullRowInterchange
public import ComparisonSignedCavityActualFiniteProfileMarginal

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Hierarchy.ClockTree
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 18000000
variable {S ι : Type} [Fintype S] [Nonempty S] [Fintype ι] [Nonempty ι]

omit [Nonempty ι] in
private theorem marked_disorder_row_transport
    {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {as : List PositiveMass} (T R : ClockTree S as) (ho : MassOrdered 0 as)
    (P : T.Assignment→ℝ) (Q : R.Assignment→ℝ)
    (hEq : ∀(q : ℕ→ι→ℝ≥0) x,T.expect w φ q P x=R.expect w φ q Q x)
    (v : ι→ℝ) (q : ℕ→ι→ℝ) (u x : ι→ℝ) :
    nativeMarkedDisorderRow w φ T v q P (fun σ=>φ σ u) x=
      nativeMarkedDisorderRow w φ R v q Q (fun σ=>φ σ u) x := by
  have Hrow (qc : ℕ→ι→ℝ≥0) (y : ι→ℝ) :
      nativeMarkedExpectRow w φ T qc P (fun σ=>φ σ u) y=
        nativeMarkedExpectRow w φ R qc Q (fun σ=>φ σ u) y := by
    have HL:=nativeMarkedExpectRow_hasDerivAt hw φ T ho qc P u y 0
    have HR:=nativeMarkedExpectRow_hasDerivAt hw φ R ho qc Q u y 0
    have Hfun : (fun t : ℝ=>T.expect w φ qc P (y+t • u))=
        (fun t : ℝ=>R.expect w φ qc Q (y+t • u)) := funext (fun t=>hEq qc _)
    rw [Hfun] at HL
    simpa only [zero_smul,add_zero] using HL.unique HR
  rw [nativeMarkedDisorderRow_eq_integral hw φ T ho,nativeMarkedDisorderRow_eq_integral hw φ R ho]
  apply integral_congr_ae
  exact Eventually.of_forall (fun y=>Hrow _ _)

private theorem covariance_transport_strict
    {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {as : List PositiveMass} (T R : ClockTree S as) (ho : MassOrdered 0 as)
    (P : T.Assignment→ℝ) (Q : R.Assignment→ℝ) (v : ι→ℝ)
    (hEq : ∀q x,T.disorderExpect w φ v q P x=R.disorderExpect w φ v q Q x)
    (D : ℕ→ι→ℝ) {B : ℝ} (hB : 0 ≤ B) (hD : ∀j i,|D j i| ≤ B)
    (q : ℕ→ι→ℝ) {epsilon : ℝ} (he : 0 < epsilon)
    (hq : strictCumulativeClock v q epsilon) (x : ι→ℝ) :
    disorderProfileJets w φ v q x [ReplicaTree.coordinateProfile φ D] T P=
      disorderProfileJets w φ v q x [ReplicaTree.coordinateProfile φ D] R Q := by
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
  have HL:=hasDerivAt_finiteProfileJets hw φ ho v q D hmono hroot [] T P x hzero
  have HR:=hasDerivAt_finiteProfileJets hw φ ho v q D hmono hroot [] R Q x hzero
  have HF : (fun t=>disorderProfileJets w φ v (fun j i=>q j i+t*D j i) x [] T P)=
      (fun t=>disorderProfileJets w φ v (fun j i=>q j i+t*D j i) x [] R Q) :=
    funext (fun t=>hEq _ x)
  rw [HF] at HL
  simpa only [List.nil_append,zero_mul,add_zero] using HL.unique HR

private theorem observed_covariance_transport_strict
    {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {as : List PositiveMass} (T R : ClockTree S as) (ho : MassOrdered 0 as)
    (P : T.Assignment→ℝ) (Q : R.Assignment→ℝ) (v : ι→ℝ) (u : ι→ℝ)
    (hEq : ∀q x,nativeMarkedDisorderRow w φ T v q P (fun σ=>φ σ u) x=
      nativeMarkedDisorderRow w φ R v q Q (fun σ=>φ σ u) x)
    (D : ℕ→ι→ℝ) {B : ℝ} (hB : 0 ≤ B) (hD : ∀j i,|D j i| ≤ B)
    (q : ℕ→ι→ℝ) {epsilon : ℝ} (he : 0 < epsilon)
    (hq : strictCumulativeClock v q epsilon) (x : ι→ℝ) :
    nativeMarkedProfileRow w φ T v q [ReplicaTree.coordinateProfile φ D] P (fun σ=>φ σ u) x=
      nativeMarkedProfileRow w φ R v q [ReplicaTree.coordinateProfile φ D] Q (fun σ=>φ σ u) x := by
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
  have HR:=nativeMarkedProfileRow_hasDerivAt hw φ R ho v q D hmono hroot [] Q (fun σ=>φ σ u) x hzero
  have HF : (fun t=>nativeMarkedProfileRow w φ T v (fun j i=>q j i+t*D j i) [] P (fun σ=>φ σ u) x)=
      (fun t=>nativeMarkedProfileRow w φ R v (fun j i=>q j i+t*D j i) [] Q (fun σ=>φ σ u) x) :=
    funext (fun t=>hEq _ x)
  rw [HF] at HL
  simpa only [List.nil_append,zero_mul,add_zero] using HL.unique HR

theorem NativeHighFreshFullRowRelation.covariance_eq {as : List PositiveMass}
    {w : S→ℝ} {φ : S→(ι→ℝ)→L[ℝ]ℝ} {T : ClockTree S as}
    {s : T.Slot} {star : ℕ} {aFresh : ℝ}
    {p : MarkedPlacement (nativeFreshAtSlot T aFresh s star).tree} {r : MarkedPlacement T}
    (h : NativeHighFreshFullRowRelation w φ T s star aFresh p r)
    (hw : ∀σ,0 < w σ) (ho : MassOrdered 0 as)
    (v : ι→ℝ) (q : ℕ→ι→ℝ) (hq : ∀i,Monotone (fun j=>q j i))
    (hq0 : ∀i,v i ≤ q 0 i) (D : ℕ→ι→ℝ) (Q : T.Assignment→S→S→ℝ) (x : ι→ℝ) :
    disorderProfileJets w φ v q x [ReplicaTree.coordinateProfile φ D] p.tree
      (fun σ=>Q ((nativeFreshAtSlot T aFresh s star).restrict (p.restrict σ))
        (p.spin σ) ((nativeFreshAtSlot T aFresh s star).spin (p.restrict σ)))=
    let g:=nativeFreshAtSlot r.tree aFresh (r.embed s) star
    disorderProfileJets w φ v q x [ReplicaTree.coordinateProfile φ D] g.tree
      (fun σ=>Q (r.restrict (g.restrict σ)) (r.spin (g.restrict σ)) (g.spin σ)) := by
  dsimp only
  let g:=nativeFreshAtSlot r.tree aFresh (r.embed s) star
  let PL:=fun σ=>Q ((nativeFreshAtSlot T aFresh s star).restrict (p.restrict σ))
    (p.spin σ) ((nativeFreshAtSlot T aFresh s star).spin (p.restrict σ))
  let PR:=fun σ=>Q (r.restrict (g.restrict σ)) (r.spin (g.restrict σ)) (g.spin σ)
  have HB:=exists_single_direction_finite_bound as.length D
  obtain ⟨B,hB,hD⟩:=HB
  let E:=clipDirection as.length D
  have hE : ∀j i,|E j i| ≤ B := clipDirection_bounded as.length [D] hB hD E (by simp [E])
  have HEq : ∀qc y,p.tree.disorderExpect w φ v qc PL y=g.tree.disorderExpect w φ v qc PR y :=
    fun qc y=>h.disorder_eq hw ho v qc Q y
  let qr:=fun e : ℝ=>fun j i=>q j i+e*(j+1:ℕ)
  have HE : EqOn
      (fun e=>disorderProfileJets w φ v (qr e) x [ReplicaTree.coordinateProfile φ E] p.tree PL)
      (fun e=>disorderProfileJets w φ v (qr e) x [ReplicaTree.coordinateProfile φ E] g.tree PR) (Ioi (0:ℝ)) := by
    intro e he
    exact covariance_transport_strict hw φ p.tree g.tree ho PL PR v HEq E hB hE (qr e) he
      (strictCumulativeClock_regularize hq hq0 he.le) x
  have hc (j : ℕ) : Continuous (fun e=>qr e j):=by dsimp [qr];fun_prop
  have HL:=disorderProfileJets_continuous hw φ ho v qr hc (fun _=>x) continuous_const
    [ReplicaTree.coordinateProfile φ E] p.tree PL
  have HR:=disorderProfileJets_continuous hw φ ho v qr hc (fun _=>x) continuous_const
    [ReplicaTree.coordinateProfile φ E] g.tree PR
  have h0 : (0:ℝ)∈closure (Ioi (0:ℝ)):=by
    simpa only [closure_Ioi,mem_Ici] using (le_rfl : (0:ℝ) ≤ 0)
  have H:=HE.closure HL HR h0
  change disorderProfileJets _ _ _ _ _ ([D].map (ReplicaTree.coordinateProfile φ)) _ _=
    disorderProfileJets _ _ _ _ _ ([D].map (ReplicaTree.coordinateProfile φ)) _ _
  rw [disorderProfileJets_eq_clipDirections w φ v q x [D] p.tree _,
    disorderProfileJets_eq_clipDirections w φ v q x [D] g.tree _]
  simpa only [qr,zero_mul,add_zero,List.map_cons,List.map_nil] using H

theorem NativeHighFreshFullRowRelation.observed_covariance_eq {as : List PositiveMass}
    {w : S→ℝ} {φ : S→(ι→ℝ)→L[ℝ]ℝ} {T : ClockTree S as}
    {s : T.Slot} {star : ℕ} {aFresh : ℝ}
    {p : MarkedPlacement (nativeFreshAtSlot T aFresh s star).tree} {r : MarkedPlacement T}
    (h : NativeHighFreshFullRowRelation w φ T s star aFresh p r)
    (hw : ∀σ,0 < w σ) (ho : MassOrdered 0 as)
    (v : ι→ℝ) (q : ℕ→ι→ℝ) (hq : ∀i,Monotone (fun j=>q j i))
    (hq0 : ∀i,v i ≤ q 0 i) (D : ℕ→ι→ℝ)
    (Q : T.Assignment→S→S→ℝ) (u x : ι→ℝ) :
    nativeMarkedProfileRow w φ p.tree v q [ReplicaTree.coordinateProfile φ D]
      (fun σ=>Q ((nativeFreshAtSlot T aFresh s star).restrict (p.restrict σ))
        (p.spin σ) ((nativeFreshAtSlot T aFresh s star).spin (p.restrict σ))) (fun σ=>φ σ u) x=
    let g:=nativeFreshAtSlot r.tree aFresh (r.embed s) star
    nativeMarkedProfileRow w φ g.tree v q [ReplicaTree.coordinateProfile φ D]
      (fun σ=>Q (r.restrict (g.restrict σ)) (r.spin (g.restrict σ)) (g.spin σ)) (fun σ=>φ σ u) x := by
  dsimp only
  let g:=nativeFreshAtSlot r.tree aFresh (r.embed s) star
  let PL:=fun σ=>Q ((nativeFreshAtSlot T aFresh s star).restrict (p.restrict σ))
    (p.spin σ) ((nativeFreshAtSlot T aFresh s star).spin (p.restrict σ))
  let PR:=fun σ=>Q (r.restrict (g.restrict σ)) (r.spin (g.restrict σ)) (g.spin σ)
  obtain ⟨B,hB,hD⟩:=exists_single_direction_finite_bound as.length D
  let E:=clipDirection as.length D
  have hE : ∀j i,|E j i| ≤ B := clipDirection_bounded as.length [D] hB hD E (by simp [E])
  have HEq : ∀qc y,nativeMarkedDisorderRow w φ p.tree v qc PL (fun σ=>φ σ u) y=
      nativeMarkedDisorderRow w φ g.tree v qc PR (fun σ=>φ σ u) y :=
    fun qc y=>marked_disorder_row_transport hw φ p.tree g.tree ho PL PR
      (fun qn yn=>h.expect_eq hw ho qn Q yn) v qc u y
  let qr:=fun e : ℝ=>fun j i=>q j i+e*(j+1:ℕ)
  have HE : EqOn
      (fun e=>nativeMarkedProfileRow w φ p.tree v (qr e) [ReplicaTree.coordinateProfile φ E] PL (fun σ=>φ σ u) x)
      (fun e=>nativeMarkedProfileRow w φ g.tree v (qr e) [ReplicaTree.coordinateProfile φ E] PR (fun σ=>φ σ u) x)
      (Ioi (0:ℝ)) := by
    intro e he
    exact observed_covariance_transport_strict hw φ p.tree g.tree ho PL PR v u HEq E hB hE (qr e) he
      (strictCumulativeClock_regularize hq hq0 he.le) x
  have hc (j : ℕ) : Continuous (fun e=>qr e j):=by dsimp [qr];fun_prop
  have HL:=nativeMarkedProfileRow_continuous hw φ p.tree ho v qr hc
    [ReplicaTree.coordinateProfile φ E] PL (fun σ=>φ σ u) x
  have HR:=nativeMarkedProfileRow_continuous hw φ g.tree ho v qr hc
    [ReplicaTree.coordinateProfile φ E] PR (fun σ=>φ σ u) x
  have h0 : (0:ℝ)∈closure (Ioi (0:ℝ)):=by
    simpa only [closure_Ioi,mem_Ici] using (le_rfl : (0:ℝ) ≤ 0)
  have H:=HE.closure HL HR h0
  change nativeMarkedProfileRow _ _ _ _ _ ([D].map (ReplicaTree.coordinateProfile φ)) _ _ _=
    nativeMarkedProfileRow _ _ _ _ _ ([D].map (ReplicaTree.coordinateProfile φ)) _ _ _
  rw [nativeMarkedProfileRow_clip_directions w φ p.tree v q [D],
    nativeMarkedProfileRow_clip_directions w φ g.tree v q [D]]
  simpa only [qr,zero_mul,add_zero,List.map_cons,List.map_nil] using H

end OAI.SKFluctuations.Hierarchy.ClockTree
