module

public import ComparisonSignedCavityActualFreshSourceMarginals
public import CavityMarginalProfileJets

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S ι : Type} [Fintype S] [Nonempty S] [Fintype ι]

def nativeMarkedExpectRow (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {as : List PositiveMass} (T : ClockTree S as) (q : ℕ→ι→ℝ≥0)
    (P : T.Assignment→ℝ) (B : S→ℝ) (x : ι→ℝ) : ℝ :=
  ((T.markedAttach 0).map (fun p=>p.coeff*p.tree.expect w φ q
    (fun σ=>P (p.restrict σ)*B (p.spin σ)) x)).sum

omit [Nonempty S] in
theorem nativeMarkedExpectRow_eq_realized (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {as : List PositiveMass} (T : ClockTree S as) (q : ℕ→ι→ℝ≥0)
    (P : T.Assignment→ℝ) (B : S→ℝ) (x : ι→ℝ) :
    nativeMarkedExpectRow w φ T q P B x=
      (T.realize q).row w φ 0 (fun σ=>P ((T.assignmentEquiv q).symm σ)) B x := by
  unfold ReplicaTree.row ReplicaTree.rowList
  rw [←(T.realize q).markedAttach_forget 0,←T.markedAttach_realize 0 q]
  simp only [List.map_map,Function.comp_def]
  unfold nativeMarkedExpectRow
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  rw [p.tree.expect_realize]
  simp only [MarkedPlacement.realize,ReplicaTree.Placement.eval,Equiv.symm_apply_apply]

theorem nativeMarkedExpectRow_hasDerivAt
    {w : S→ℝ} (hw : ∀σ,0<w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {as : List PositiveMass} (T : ClockTree S as) (ho : MassOrdered 0 as)
    (q : ℕ→ι→ℝ≥0) (P : T.Assignment→ℝ) (u x : ι→ℝ) (t : ℝ) :
    HasDerivAt (fun s=>T.expect w φ q P (x+s • u))
      (nativeMarkedExpectRow w φ T q P (fun σ=>φ σ u) (x+t • u)) t := by
  have H:=(T.realize q).hasDerivAt_expect hw φ u (clockSteps_ordered ho q)
    (fun σ=>P ((T.assignmentEquiv q).symm σ)) x t
  simpa only [←T.expect_realize,nativeMarkedExpectRow_eq_realized,zero_mul,sub_zero] using H

theorem native_marked_expect_row_marginal
    {w : S→ℝ} (hw : ∀σ,0<w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {as : List PositiveMass} (T : ClockTree S as) (ho : MassOrdered 0 as)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (q : ℕ→ι→ℝ≥0) (P : T.Assignment→ℝ) (u x : ι→ℝ) :
    nativeMarkedExpectRow w φ p.tree q (fun σ=>P (p.restrict σ)) (fun σ=>φ σ u) x=
      nativeMarkedExpectRow w φ T q P (fun σ=>φ σ u) x := by
  have HL:=nativeMarkedExpectRow_hasDerivAt hw φ p.tree ho q (fun σ=>P (p.restrict σ)) u x 0
  have HR:=nativeMarkedExpectRow_hasDerivAt hw φ T ho q P u x 0
  have HF : (fun s : ℝ=>p.tree.expect w φ q (fun σ=>P (p.restrict σ)) (x+s • u))=
      (fun s : ℝ=>T.expect w φ q P (x+s • u)) := by
    funext s
    exact native_marked_expect_marginal T ho p hp hw φ q P _
  rw [HF] at HL
  simpa only [zero_smul,add_zero] using HL.unique HR

def nativeMarkedDisorderRow (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {as : List PositiveMass} (T : ClockTree S as) (v : ι→ℝ) (q : ℕ→ι→ℝ)
    (P : T.Assignment→ℝ) (B : S→ℝ) (x : ι→ℝ) : ℝ :=
  ((T.markedAttach 0).map (fun p=>p.coeff*p.tree.disorderExpect w φ v q
    (fun σ=>P (p.restrict σ)*B (p.spin σ)) x)).sum

private theorem list_integral_sum {α Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (L : List α) (F : α→Ω→ℝ)
    (hi : ∀a∈L,Integrable (F a) μ) :
    (L.map (fun a=>∫x,F a x ∂μ)).sum=∫x,(L.map (fun a=>F a x)).sum ∂μ := by
  induction L with
  | nil=>simp
  | cons a L ih=>
    have ha:=hi a List.mem_cons_self
    have ht : ∀b∈L,Integrable (F b) μ:=fun b hb=>hi b (List.mem_cons_of_mem _ hb)
    have hs : Integrable (fun x=>(L.map (fun b=>F b x)).sum) μ := by
      clear ih hi ha
      induction L with
      | nil=>simp
      | cons b L ih=>
        change Integrable (F b+(fun x=>(L.map (fun c=>F c x)).sum)) μ
        exact (ht b List.mem_cons_self).add (ih (fun c hc=>ht c (List.mem_cons_of_mem _ hc)))
    simp only [List.map_cons,List.sum_cons]
    rw [ih ht,integral_add ha hs]

theorem nativeMarkedDisorderRow_eq_integral
    {w : S→ℝ} (hw : ∀σ,0<w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {as : List PositiveMass} (T : ClockTree S as) (ho : MassOrdered 0 as)
    (v : ι→ℝ) (q : ℕ→ι→ℝ) (P : T.Assignment→ℝ) (B : S→ℝ) (x : ι→ℝ) :
    nativeMarkedDisorderRow w φ T v q P B x=
      ∫y,nativeMarkedExpectRow w φ T (cumulativeIncrements (q 0) (fun j=>q (j+1)))
        P B (x+y) ∂(Measure.pi fun i=>gaussianReal 0 (Real.toNNReal (q 0 i-v i))) := by
  unfold nativeMarkedDisorderRow nativeMarkedExpectRow
  simp_rw [disorderExpect_integral hw φ _ ho,zeroContinuation,←integral_const_mul]
  exact list_integral_sum _ _ _ (fun p hp=>
    (p.tree.expect_zeroShift_integrable hw φ ho _ _ _ x).const_mul p.coeff)

theorem native_marked_disorder_row_marginal
    {w : S→ℝ} (hw : ∀σ,0<w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {as : List PositiveMass} (T : ClockTree S as) (ho : MassOrdered 0 as)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (v : ι→ℝ) (q : ℕ→ι→ℝ) (P : T.Assignment→ℝ) (u x : ι→ℝ) :
    nativeMarkedDisorderRow w φ p.tree v q (fun σ=>P (p.restrict σ)) (fun σ=>φ σ u) x=
      nativeMarkedDisorderRow w φ T v q P (fun σ=>φ σ u) x := by
  rw [nativeMarkedDisorderRow_eq_integral hw φ _ ho,nativeMarkedDisorderRow_eq_integral hw φ _ ho]
  apply integral_congr_ae
  exact Eventually.of_forall (fun y=>native_marked_expect_row_marginal hw φ T ho p hp _ P u _)

end OAI.SKFluctuations.Hierarchy.ClockTree
