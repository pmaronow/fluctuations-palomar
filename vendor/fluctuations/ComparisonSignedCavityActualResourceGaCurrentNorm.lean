module

public import ComparisonSignedCavityActualResourceGaReadout

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 18000000

theorem sourceMonomialScale_initial_scale_le {a degree : ℕ}
    (initial : Finset (Fin a)) {s x W B : ℝ} (hs : 0 ≤ s) (hx : 0 ≤ x)
    (hW : 0 ≤ W) (hB : 1 ≤ B) (hsx : s ≤ B*x) (ha : a ≤ degree) :
    sourceMonomialScale s W initial ≤ B^degree*sourceMonomialScale x W initial := by
  have hc : initial.card ≤ degree:=by
    have H:=Finset.card_le_univ initial
    simp only [Fintype.card_fin] at H
    omega
  unfold sourceMonomialScale
  calc
    _ ≤ (B*x)^initial.card*W^(a-initial.card):=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs hsx _) (pow_nonneg hW _)
    _ = B^initial.card*(x^initial.card*W^(a-initial.card)):=by rw [mul_pow];ring
    _ ≤ B^degree*(x^initial.card*W^(a-initial.card)):=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hB hc) (by positivity)

theorem actual_resource_current_Ga_normalized_bound
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {i star U k degree : ℕ} {seed : List NativeResourceMark} {P : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P) (ho : MassOrdered 0 as)
    (hi : i ≤ star) (hs : star < as.length) (hdegree : P.resources.length ≤ degree)
    {A x W Cmass price : ℝ} (hA : 1 ≤ A) (hx : M.xs ≤ x) (hxW : x ≤ W)
    (hCm : 0 ≤ Cmass) (hmi : partitionPoint 0 as i ≤ Cmass*x) (hprice : 0 ≤ price)
    (Hpair : P.PairMomentBudget (fullWeight n) (fullFeature n) 0
      (finitePhysicalCavitySquareVariance n U as
        (fun j=>(M.bf (partitionPoint 0 as j):ℝ)) (fun j=>(M.hf (partitionPoint 0 as j):ℝ)) 1 1)
      (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
      (nativePhysicalResourceCenter n M.bf M.hf as) 0 A x W 1)
    (Hlive : |nativeActualDecoupledGProjectedResampling T P.live.test star U M
      (fun j=>Sum.elim (fun _=>(M.bf (partitionPoint 0 as j):ℝ))
        (fun _=>(M.hf (partitionPoint 0 as j):ℝ)))| ≤
      price*sourceMonomialScale (M.xs+partitionPoint 0 as i) W
        (nativeGeneratedCompleteInitial P.live.test i)) :
    |(W⁻¹)^k*nativeActualResourceGaCurrent M U P| ≤
      |P.coefficient| *((1+Cmass)^degree*A^degree)*price*nativeResourceScale x W 1 seed := by
  have hx0:=M.hxs.trans_le hx
  have hW:=hx0.trans_le hxW
  have hlive : P.live.test.edges.length ≤ degree:=by
    have HH:=P.live.realizes.length_eq
    have HL : P.live.tags.length ≤ P.resources.length:=by
      simp only [NativeResourceTerm.resources,List.length_append]
      omega
    simp only [List.length_map,NativeResourceMonomial.tags] at HH HL
    omega
  have Hscale:=sourceMonomialScale_initial_scale_le (nativeGeneratedCompleteInitial P.live.test i)
    (M.hxs.le.trans (le_add_of_nonneg_right (partitionPoint_mem as ho i).1)) hx0.le hW.le
    (show 1 ≤ 1+Cmass by linarith) (show M.xs+partitionPoint 0 as i ≤ (1+Cmass)*x by nlinarith) hlive
  have HS:=P.scalar_mul_canonical_live_scale_le (fullWeight_pos n) (fullFeature n) ho 0
    (finitePhysicalCavitySquareVariance n U as
      (fun j=>(M.bf (partitionPoint 0 as j):ℝ)) (fun j=>(M.hf (partitionPoint 0 as j):ℝ)) 1 1)
    (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
    (nativePhysicalResourceCenter n M.bf M.hf as) 0 hA hx0 hxW hi hs Hpair
  let scalar:=nativeActualResourceOriginalScalar M U P
  let live:=nativeActualDecoupledGProjectedResampling T P.live.test star U M
    (fun j=>Sum.elim (fun _=>(M.bf (partitionPoint 0 as j):ℝ))
      (fun _=>(M.hf (partitionPoint 0 as j):ℝ)))
  have Hp : 0 ≤ price*(1+Cmass)^degree:=mul_nonneg hprice (pow_nonneg (by linarith) _)
  have HL : |live| ≤ (price*(1+Cmass)^degree)*sourceMonomialScale x W
      (nativeGeneratedCompleteInitial P.live.test i):=by
    exact Hlive.trans ((mul_le_mul_of_nonneg_left Hscale hprice).trans_eq (by ring))
  have Hprod : |scalar*live| ≤
      |P.coefficient| *nativeResourceEnvelope A x W 1 P.resources*(price*(1+Cmass)^degree):=by
    rw [abs_mul]
    apply (mul_le_mul_of_nonneg_left HL (abs_nonneg scalar)).trans
    convert mul_le_mul_of_nonneg_right HS Hp using 1
    dsimp only [scalar,nativeActualResourceOriginalScalar]
    ring
  have Hnorm:=mul_le_mul_of_nonneg_left Hprod (show 0 ≤ (W⁻¹)^k by positivity)
  have HE : (W⁻¹)^k*(|P.coefficient| *nativeResourceEnvelope A x W 1 P.resources*(price*(1+Cmass)^degree))=
      |P.coefficient| *A^P.resources.length*nativeResourceScale x W 1 seed*(price*(1+Cmass)^degree) := by
    rw [nativeResourceEnvelope_scale]
    calc
      _=|P.coefficient| *A^P.resources.length*((W⁻¹)^k*nativeResourceScale x W 1 P.resources)*
          (price*(1+Cmass)^degree):=by ring
      _=_:=by rw [hP.normalized_saved_scale x W 1 hW.ne',one_pow,mul_one]
  rw [HE] at Hnorm
  have hseed : 0 ≤ nativeResourceScale x W 1 seed:=by
    unfold nativeResourceScale
    apply List.prod_nonneg
    intro z hz
    obtain ⟨mark,hm,rfl⟩:=List.mem_map.mp hz
    exact (mark.savedScale_pos hx0 hW zero_lt_one).le
  have Hfinal:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hA hdegree) (abs_nonneg P.coefficient)) hseed) Hp
  rw [←abs_of_nonneg (show 0 ≤ (W⁻¹)^k by positivity),←abs_mul] at Hnorm
  change |(W⁻¹)^k*nativeActualResourceGaCurrent M U P| ≤ _ at Hnorm
  apply (Hnorm.trans Hfinal).trans_eq
  ring

end OAI.SKFluctuations.Cavity
