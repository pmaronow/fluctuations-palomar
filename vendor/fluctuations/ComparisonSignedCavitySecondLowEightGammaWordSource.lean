module

public import ComparisonSignedCavitySecondLowEightGammaFactors
public import ComparisonSignedCavitySecondLowJointWordBudget

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open MeasureTheory ProbabilityTheory Set Hierarchy Hierarchy.ClockTree
open scoped BigOperators
set_option maxHeartbeats 28000000
attribute [local instance] Classical.propDecidable

theorem native_second_low_gamma_zero_off_path {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as) (U : ℕ) (hU : U≤as.length)
    (K : ℕ→ℝ) (a z f c e d : T.Slot) (j : Fin 8)
    (H : ¬nativeSecondLowBlockPath j (T.cutBlock U hU a) (T.cutBlock U hU z)
      (T.cutBlock U hU f) (T.cutBlock U hU c) (T.cutBlock U hU e) (T.cutBlock U hU d)) :
    nativeSecondLowPathGamma T U K a z f c e d j=0 := by
  have HB (u v : T.Slot) (HΓ : fullScalarCutGamma T U K u v≠0) :
      T.cutBlock U hU u=T.cutBlock U hU v := by
    apply (T.cutBlock_eq_iff U hU u v).mpr
    by_contra HH
    exact HΓ (fullScalarCutGamma_cross_zero T ho U K u v hU (lt_of_not_ge HH))
  by_contra HΓ
  fin_cases j
  all_goals dsimp only [nativeSecondLowPathGamma,nativeSecondLowBlockPath] at HΓ H
  all_goals simp only [mul_ne_zero_iff] at HΓ
  all_goals exact H ⟨HB _ _ HΓ.1.1,HB _ _ HΓ.1.2,HB _ _ HΓ.2⟩

def nativeSecondLowGammaWordValue (n : ℕ) (q : ℕ→RestCoordinate n→ℝ)
    (U : ℕ) (b h K : ℕ→ℝ) {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot) (j : Fin 8)
    (p : MarkedPlacement T) (r : MarkedPlacement p.tree)
    (s : MarkedPlacement r.tree) (t : MarkedPlacement s.tree) : ℝ :=
  t.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
    (nativeSecondLowJointRestTest n U b h K P p r s t) 0*
    nativeSecondLowPathGamma t.tree U K (t.embed (s.embed (r.embed (p.embed a))))
      (t.embed (s.embed (r.embed (p.embed z)))) (t.embed (s.embed (r.embed p.mark)))
      (t.embed (s.embed r.mark)) (t.embed s.mark) t.mark j

theorem native_second_low_masked_word_eq_gamma_source (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (hU : U≤as.length) (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot) (haz : T.splitIndex a z<U)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (r : MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0)
    (s : MarkedPlacement r.tree) (hs : s∈r.tree.markedAttach 0)
    (t : MarkedPlacement s.tree) (ht : t∈s.tree.markedAttach 0) (j : Fin 8) :
    (if nativeSecondLowWordPath U hU a z p r s t j
      then nativeSecondLowWordValue n q U b h K P a z p r s t else 0)=
      nativeSecondLowGammaWordValue n q U b h K P a z j p r s t := by
  by_cases Hpath : nativeSecondLowWordPath U hU a z p r s t j
  · simp only [Hpath,ite_true]
    by_cases Hfc : r.tree.splitIndex (r.embed p.mark) r.mark<U
    · by_cases Hed : t.tree.splitIndex (t.embed s.mark) t.mark<U
      · have Ha : t.tree.splitIndex (t.embed (s.embed (r.embed (p.embed a))))
            (t.embed (s.embed (r.embed (p.embed z))))<U := by
          rw [(s.tree.markedAttach_embed_preserves 0 t ht).2,
            (r.tree.markedAttach_embed_preserves 0 s hs).2,
            (p.tree.markedAttach_embed_preserves 0 r hr).2,
            (T.markedAttach_embed_preserves 0 p hp).2]
          exact haz
        have Hf : t.tree.splitIndex (t.embed (s.embed (r.embed p.mark)))
            (t.embed (s.embed r.mark))<U := by
          rw [(s.tree.markedAttach_embed_preserves 0 t ht).2,
            (r.tree.markedAttach_embed_preserves 0 s hs).2]
          exact Hfc
        unfold nativeSecondLowWordValue nativeSecondLowGammaWordValue
        change _*fullScalarCutMoment t.tree U K
          [t.embed (s.embed (r.embed (p.embed a))),t.embed (s.embed (r.embed (p.embed z))),
            t.embed (s.embed (r.embed p.mark)),t.embed (s.embed r.mark),t.embed s.mark,t.mark]=_
        rw [native_second_low_scalar_factor_all_paths t.tree ho U hU K _ _ _ _ _ _ Ha Hf Hed j Hpath]
      · have HZ:=native_second_low_joint_rest_test_zero_of_second_high n U b h K P p r s t (not_lt.mp Hed)
        unfold nativeSecondLowWordValue nativeSecondLowGammaWordValue
        rw [HZ]
        simp [disorderExpect]
    · have HZ:=native_second_low_joint_rest_test_zero_of_first_high n U b h K P p r s t (not_lt.mp Hfc)
      unfold nativeSecondLowWordValue nativeSecondLowGammaWordValue
      rw [HZ]
      simp [disorderExpect]
  · simp only [Hpath,ite_false]
    unfold nativeSecondLowGammaWordValue
    rw [native_second_low_gamma_zero_off_path t.tree ho U hU K _ _ _ _ _ _ j Hpath,mul_zero]

def nativeSecondLowGammaPathLedger (n : ℕ) (q : ℕ→RestCoordinate n→ℝ)
    (U : ℕ) (b h K : ℕ→ℝ) {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot) (j : Fin 8) : ℝ :=
  nativeSecondLowDoubleAverage T (fun p r=>nativeSecondLowDoubleAverage r.tree (fun s t=>
    nativeSecondLowGammaWordValue n q U b h K P a z j p r s t))

theorem native_second_low_path_ledger_eq_gamma_source (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (hU : U≤as.length) (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot) (haz : T.splitIndex a z<U)
    (j : Fin 8) : nativeSecondLowPathLedger n q U b h K T hU P a z j=
      nativeSecondLowGammaPathLedger n q U b h K T P a z j := by
  unfold nativeSecondLowPathLedger nativeSecondLowGammaPathLedger
  apply native_second_low_double_average_congr
  intro p hp r hr
  apply native_second_low_double_average_congr
  intro s hs t ht
  exact native_second_low_masked_word_eq_gamma_source n q U b h K T ho hU P a z haz p hp r hr s hs t ht j

theorem native_second_low_joint_ledger_half_eq_eight_gamma_sources (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (hU : U≤as.length) (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot) (haz : T.splitIndex a z<U) :
    nativeSecondLowJointLedger n q U b h K T P [a,z]/2=
      ∑j : Fin 8,nativeSecondLowGammaPathLedger n q U b h K T P a z j/2 := by
  rw [native_second_low_joint_ledger_half_eq_eight_paths n q U b h K T ho hU P a z haz]
  simp_rw [native_second_low_path_ledger_eq_gamma_source n q U b h K T ho hU P a z haz]

end OAI.SKFluctuations.Cavity
