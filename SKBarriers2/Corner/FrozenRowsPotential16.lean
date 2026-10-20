module

public import SKBarriers2.Corner.FrozenRowsPotential14
public import SKBarriers2.Corner.FrozenRowsPotential15
public import SKBarriers2.Corner.FrozenRowsAffineGeometry3

@[expose] public section

noncomputable section
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory ProbabilityTheory OAI.SK.Analytic

open SKOptimized.Overshoot

namespace SKBarriers2.Corner
open StepCalculus

def frozenCompletedHeadLogInput (β : ℝ) (α : ℝ → ℝ) (a s h z ε : ℝ)
    (q : Fin 12) (k t : ℝ) (y : Vec3) : ℝ :=
  let u := frozenRowsHead β a h q.val k
  let tail := (frozenSchedule β a (1 / 2) h k).drop (q.val + 1)
  let Q := terminalTaylorQuadratic β α s h z
  let P := riccatiRecursion tail (Q.scale (1 - ε))
  let w := (Real.sqrt (P.precision u.1 u.2)⁻¹) • u.2
  u.1 * epsilonFrameResidual tail Q (frozenTerminal β α s h) ε
    (quadraticMeanLinear P u.1 u.2 ((Real.sqrt h) • y + (fun _ => z)) +
      quadraticNoiseConstant P u.1 u.2 + t • w)

theorem frozenSchedule_drop_cons (β a h k : ℝ) (q : Fin 12) :
    (frozenSchedule β a (1 / 2) h k).drop q.val =
      frozenRowsHead β a h q.val k ::
        (frozenSchedule β a (1 / 2) h k).drop (q.val + 1) := by
  fin_cases q <;> rfl

theorem frozenCompletedDirection_eq_head (β a u χ h k : ℝ) (hh : 0 ≤ h) (q : Fin 12) :
    let tail := (frozenSchedule β a (1 / 2) h k).drop (q.val + 1)
    let v := frozenRowsHead β a h q.val k
    let Q := separableTaylorQuadratic 0 u χ 0
    gaussianPathLinear tail Q
      ((Real.sqrt ((riccatiRecursion tail Q).precision v.1 v.2)⁻¹) • v.2) =
        frozenCompletedDirection β a χ h q k := by
  dsimp only
  have H := congrArg List.head? (completedSquareSchedule_drop
    (frozenSchedule β a (1 / 2) h k) (separableTaylorQuadratic 0 u χ 0) q.val)
  rw [frozenSchedule_drop_cons, completedSquareSchedule,
    completedSquareSchedule_frozen β a 0 u χ h 0 k hh] at H
  rw [List.head?_cons,List.head?_drop,List.getElem?_ofFn,dite_eq_left q.isLt] at H
  exact congrArg Prod.snd (Option.some.inj H)

theorem scalarData_frozenCompletedHeadLogInput_eq_pureChain {β l u : ℝ} (D : ScalarData β)
    (hl : 0 < l) (hu : u < D.q) :
    ∃ h₀ : ℝ, 0 < h₀ ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ z : ℝ,
      ∀ ε ∈ Icc (0 : ℝ) 1, ∀ q : Fin 12, ∀ k : ℝ, |k| ≤ 1 / 2 → ∀ t : ℝ, ∀ y : Vec3,
      let α := cdf (D.μ : Measure ℝ)
      let a := α (r - h)
      let R := centeredFrozenRowsQuadratic β α (r - h) h z ε
      let χ := (1 - ε) * jet β α 2 ((r - h) + 4 * h) z
      let f := centeredFrozenRowsTerminal β α (r - h) h z ε
      let X := gaussianPathMean ((frozenSchedule β a (1 / 2) h k).drop q.val) R
        ((Real.sqrt h) • y) + t • frozenCompletedDirection β a χ h q k
      frozenCompletedHeadLogInput β α a (r - h) h z ε q k t y =
        (frozenRowsHead β a h q.val k).1 * frozenCompletedSuffixChain β a χ h f q k X := by
  obtain ⟨h₀, hh₀, H⟩ := scalarData_frozen_suffix_completedSquareChain D hl hu
  refine ⟨h₀, hh₀, ?_⟩
  intro r hr h hh hhsmall z ε hε q k hk t y
  let α := cdf (D.μ : Measure ℝ)
  let a := α (r - h)
  let tail := (frozenSchedule β a (1 / 2) h k).drop (q.val + 1)
  let v := frozenRowsHead β a h q.val k
  let Q := terminalTaylorQuadratic β α (r - h) h z
  let P := Q.scale (1 - ε)
  let R := centeredFrozenRowsQuadratic β α (r - h) h z ε
  let c : Vec3 := fun _ => z
  let C := 3 * (1 - ε) * Phi β α ((r - h) + 4 * h) z
  let χ := (1 - ε) * jet β α 2 ((r - h) + 4 * h) z
  let w := (Real.sqrt ((riccatiRecursion tail P).precision v.1 v.2)⁻¹) • v.2
  let x := (Real.sqrt h) • y
  have hPR : P.translate c = R.addConstant C := separableTaylorQuadratic_scale_translate _ _ _ _ _
  have hp : (riccatiRecursion tail P).precision v.1 v.2 =
      (riccatiRecursion tail R).precision v.1 v.2 := by
    rw [← QuadraticTerminal.translate_precision (riccatiRecursion tail P) c,
      ← riccatiRecursion_translate, hPR, riccatiRecursion_addConstant]
    rfl
  have hd : gaussianPathLinear tail P w = frozenCompletedDirection β a χ h q k := by
    rw [← gaussianPathLinear_translate tail P c, hPR, gaussianPathLinear_addConstant]
    dsimp only [w]
    rw [hp]
    exact frozenCompletedDirection_eq_head β a _ χ h k hh.le q
  have hm : gaussianPathMean ((frozenSchedule β a (1 / 2) h k).drop q.val) P (x + c) =
      gaussianPathMean ((frozenSchedule β a (1 / 2) h k).drop q.val) R x + c := by
    rw [gaussianPathMean_translate, hPR, gaussianPathMean_addConstant]
  have hmean : gaussianPathMean tail P
      (quadraticMeanLinear (riccatiRecursion tail P) v.1 v.2 (x + c) +
        quadraticNoiseConstant (riccatiRecursion tail P) v.1 v.2 + t • w) =
      (gaussianPathMean ((frozenSchedule β a (1 / 2) h k).drop q.val) R x +
        t • frozenCompletedDirection β a χ h q k) + c := by
    rw [← quadraticMeanTransition_eq_affine, gaussianPathMean_shift, hd]
    have he : gaussianPathMean tail P
        (quadraticMeanTransition (riccatiRecursion tail P) v.1 v.2 (x + c)) =
        gaussianPathMean ((frozenSchedule β a (1 / 2) h k).drop q.val) P (x + c) := by
      rw [frozenSchedule_drop_cons]
      rfl
    rw [he, hm]
    module
  have hs : completedSquareSchedule tail P = completedSquareSchedule tail R := by
    rw [← completedSquareSchedule_translate tail P c, hPR, completedSquareSchedule_addConstant]
  have hres (Y : Vec3) : epsilonFrameResidual tail Q (frozenTerminal β α (r - h) h) ε Y =
      vectorIncrementChain (completedSquareSchedule tail P)
        (fun Y => ε * frozenTerminal β α (r - h) h Y) (gaussianPathMean tail P Y) := by
    rw [epsilonFrameResidual_eq_actual]
    have HE := H r hr h hh hhsmall k hk z ε
      ⟨by linarith [hε.1], by linarith [hε.2]⟩ tail (List.drop_suffix _ _) Y
    change epsilonChain tail Q (terminalResidual β α (r - h) h z) ε Y = _ at HE
    change epsilonChain tail Q (terminalResidual β α (r - h) h z) ε Y -
      (riccatiRecursion tail P).value Y = _
    rw [HE]
    ring
  dsimp only
  change v.1 * epsilonFrameResidual tail Q (frozenTerminal β α (r - h) h) ε
    (quadraticMeanLinear (riccatiRecursion tail P) v.1 v.2 (x + c) +
      quadraticNoiseConstant (riccatiRecursion tail P) v.1 v.2 + t • w) = _
  rw [hres, hmean, hs, vectorIncrementChain_translate_argument]
  congr 1
  exact frozenCompletedSuffixChain_eq_actual β a 0 _ χ h 0 k hh.le _ q _

end SKBarriers2.Corner
