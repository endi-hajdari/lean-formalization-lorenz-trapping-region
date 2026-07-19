/-
Copyright (c) 2026 ICARM Summer School. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdullah Ahmed, Endi Hajdari, Pankaj Singh, and Swati
-/

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Basic
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Order.Filter.Basic

/-!
# Lorenz system trapping region

Theorems and results to be used later in the main theorem and pushed to Mathlib.
-/

open Set
open Filter Topology

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {s E : Set α}

/-- A preconnected set meets a frontier iff it meets the closures of the set and its complement. -/
theorem IsPreconnected.inter_frontier_nonempty_iff (hs : IsPreconnected s) :
    (s ∩ frontier E).Nonempty ↔
      (s ∩ closure E).Nonempty ∧ (s ∩ closure Eᶜ).Nonempty := by
  rw [frontier_eq_closure_inter_closure]
  refine ⟨fun ⟨x, hx, hxc, hxc'⟩ => ⟨⟨x, hx, hxc⟩, ⟨x, hx, hxc'⟩⟩, fun ⟨hE, hEc⟩ => ?_⟩
  exact isPreconnected_closed_iff.1 hs _ _ isClosed_closure isClosed_closure
    (fun x _ => (em (x ∈ E)).imp (fun h => subset_closure h) (fun h => subset_closure h)) hE hEc

/-- A preconnected set meeting both `E` and its complement meets the frontier of `E`. -/
theorem IsPreconnected.inter_frontier_nonempty (hs : IsPreconnected s)
    (hse : (s ∩ E).Nonempty) (hsec : (s ∩ Eᶜ).Nonempty) :
    (s ∩ frontier E).Nonempty :=
  hs.inter_frontier_nonempty_iff.2
    ⟨hse.mono (Set.inter_subset_inter subset_rfl subset_closure),
     hsec.mono (Set.inter_subset_inter subset_rfl subset_closure)⟩

/-- A continuous image of a preconnected set crosses a frontier if it crosses the set. -/
theorem IsPreconnected.exists_image_mem_frontier {s : Set α}
    (hs : IsPreconnected s) {f : α → β} (hf : ContinuousOn f s) {E : Set β} {a b : α}
    (ha : a ∈ s) (hb : b ∈ s) (hfa : f a ∈ E) (hfb : f b ∉ E) :
    ∃ c ∈ s, f c ∈ frontier E := by
  obtain ⟨y, ⟨c, hc, rfl⟩, hy⟩ :=
    (hs.image f hf).inter_frontier_nonempty ⟨f a, ⟨a, ha, rfl⟩, hfa⟩ ⟨f b, ⟨b, hb, rfl⟩, hfb⟩
  exact ⟨c, hc, hy⟩

theorem RightContinuous.firstExit_mem_closure [ConditionallyCompleteLinearOrder α]
    [OrderTopology α] {f : α → β} (hf : ∀ x, ContinuousWithinAt f (Ioi x) x)
    {s : Set α} (hs : s.Nonempty) (hbs : BddBelow s) {E : Set β} (hfs : MapsTo f s E) :
    f (sInf s) ∈ closure E := by
  have hglb : IsGLB s (sInf s) := isGLB_csInf hs hbs
  have hmem : sInf s ∈ closure s := hglb.mem_closure hs
  have hci : ContinuousWithinAt f (Ici (sInf s)) (sInf s) :=
    continuousWithinAt_Ioi_iff_Ici.1 (hf _)
  exact (hci.mono fun x hx => hglb.1 hx).mem_closure hmem hfs

theorem Continuous.firstExit_mem_frontier [ConditionallyCompleteLinearOrder α]
    [DenselyOrdered α] [OrderTopology α] {f : α → β} (hf : Continuous f) {E : Set β}
    {a b : α} (hab : a ≤ b) (hfa : f a ∈ E) (hfb : f b ∉ E) :
    f (sInf {x | a ≤ x ∧ f x ∉ E}) ∈ frontier E := by
  set S : Set α := {x | a ≤ x ∧ f x ∉ E} with hSdef
  have hSne : S.Nonempty := ⟨b, hab, hfb⟩
  have hSbdd : BddBelow S := ⟨a, fun x hx => hx.1⟩
  set c := sInf S with hc
  have hac : a ≤ c := le_csInf hSne fun x hx => hx.1
  have hclc : f c ∈ closure Eᶜ :=
    RightContinuous.firstExit_mem_closure (fun x => hf.continuousWithinAt) hSne hSbdd
      fun x hx => hx.2
  have hcE : f c ∈ closure E := by
    rcases eq_or_lt_of_le hac with hEq | hLt
    · rw [← hEq]; exact subset_closure hfa
    · refine hf.continuousWithinAt.mem_closure (s := Ico a c) ?_ ?_
      · rw [closure_Ico hLt.ne]; exact right_mem_Icc.2 hLt.le
      · rintro x hx
        by_contra hxE
        exact absurd (csInf_le hSbdd ⟨hx.1, hxE⟩) (not_le.2 hx.2)
  rw [frontier_eq_closure_inter_closure]
  exact ⟨hcE, hclc⟩


/-! Open scoped ContDiff -/
set_option linter.style.longLine false
open scoped ContDiff

/-! Defining the three coordinate functions of the Lorenz trajectory -/
structure LorenzTrajectory where
  total : ℝ → ℝ × ℝ × ℝ


def LorenzTrajectoryx (φ : LorenzTrajectory) : ℝ → ℝ := fun t => (φ.total t).1
def LorenzTrajectoryy (φ : LorenzTrajectory) : ℝ → ℝ := fun t => (φ.total t).2.1
def LorenzTrajectoryz (φ : LorenzTrajectory) : ℝ → ℝ := fun t => (φ.total t).2.2

/-! Defining the three parameters that comprise the Lorenz system -/
structure LorenzParams where
  (σ r b : ℝ)
  σ_pos: 0<σ
  r_pos: 0<r
  b_pos: 0<b

/-! Defining what it means for a trajectory φ to satisfy the Lorenz system
with parameters p -/
def IsSolution (p : LorenzParams) (φ : LorenzTrajectory) : Prop :=
  (∀ t : ℝ, HasDerivAt (LorenzTrajectoryx φ) (p.σ * (LorenzTrajectoryy φ t
  - LorenzTrajectoryx φ t)) t)  ∧
  (∀ t : ℝ, HasDerivAt (LorenzTrajectoryy φ) (p.r * LorenzTrajectoryx φ t - LorenzTrajectoryy φ t
  - LorenzTrajectoryx φ t * LorenzTrajectoryz φ t) t) ∧
  (∀ t : ℝ, HasDerivAt (LorenzTrajectoryz φ) (LorenzTrajectoryx φ t * LorenzTrajectoryy φ t
  - p.b * LorenzTrajectoryz φ t) t)∧
  (∀ t: ℝ, DifferentiableAt ℝ (LorenzTrajectory.total φ) t)

/-! Defining Lyapunov function as a function of a point (x, y, z) -/
def Lyapunov (p : LorenzParams) (u : ℝ × ℝ × ℝ) : ℝ :=
  let (x, y, z) := u
  p.r * x^2 + p.σ * y^2 + p.σ * (z - 2 * p.r)^2

/-! Showing that all derivatives for the Lyapunov function exist and are continuous -/
lemma Lyapunov_ContDiff (p : LorenzParams) : ContDiff ℝ ∞ (Lyapunov p) := by
  unfold Lyapunov
  fun_prop

lemma Lyapunov_Continuous (p : LorenzParams) : Continuous (Lyapunov p) := by
  exact (Lyapunov_ContDiff p).continuous

/-! Defining Lyapunov function along a trajectory -/
def LyapunovAlongTrajectory (p : LorenzParams) (φ : LorenzTrajectory) (t : ℝ) : ℝ :=
  Lyapunov p (φ.total t)

/-! Defining the simplified derivative expression -/
def LyapunovTilde (p : LorenzParams) (u : ℝ × ℝ × ℝ) : ℝ :=
  let (x, y, z) := u
  (-2) * p.σ * (p.r * x^2 + y^2 + p.b *(z - p.r)^2)+2*p.σ *p.b * p.r^2

/-! Showing that all derivatives for the LyapunovTilde function exist and are continuous -/
lemma LyapunovTilde_ContDiff (p : LorenzParams) : ContDiff ℝ ∞ (LyapunovTilde p) := by
  unfold LyapunovTilde
  fun_prop

lemma LyapunovTilde_Continuous (p : LorenzParams) : Continuous (LyapunovTilde p) := by
  exact (LyapunovTilde_ContDiff p).continuous

/-! Defining the simplified derivative expression -/
lemma Lyapunov_Derivative_Algebra (p : LorenzParams) (v : ℝ × ℝ × ℝ) :
  p.r * (2 * v.1 * (p.σ * (v.2.1 - v.1))) + p.σ * (2 * v.2.1 * (p.r * v.1 - v.2.1 - v.1* v.2.2))
  + p.σ * (2 * (v.2.2 - 2 * p.r) * (v.1 * v.2.1 - p.b * v.2.2)) =
  LyapunovTilde p v := by
    simp [LyapunovTilde]
    ring

/-! Showing that along a Lorenz solution, the derivative of Lyapunov is LyapunovTilde -/
lemma LyapunovAlongTrajectory_Deriv (p : LorenzParams) (φ : LorenzTrajectory)
(hφ : IsSolution p φ) (t : ℝ) :
  HasDerivAt (LyapunovAlongTrajectory p φ) (LyapunovTilde p (φ.total t)) t := by
  rcases hφ with ⟨hx, hy, hz, -⟩
  have hx_sq := (hx t).pow 2
  have hy_sq := (hy t).pow 2
  have hz_shift_sq := ((hz t).sub_const (2 * p.r)).pow 2
  have hV :=
    (hx_sq.const_mul p.r).add ((hy_sq.const_mul p.σ).add (hz_shift_sq.const_mul p.σ))
  have hfun : LyapunovAlongTrajectory p φ =
    (fun s => p.r * (LorenzTrajectoryx φ ^ 2) s) + ((fun s => p.σ * (LorenzTrajectoryy φ ^ 2) s)
    + fun s => p.σ * ((fun x => LorenzTrajectoryz φ x - 2 * p.r) ^ 2) s) := by
    unfold LorenzTrajectoryx LorenzTrajectoryy LorenzTrajectoryz
    funext s
    simp [LyapunovAlongTrajectory, Lyapunov]
    ring_nf
  rw [hfun]
  refine hV.congr_deriv ?_
  rw [← Lyapunov_Derivative_Algebra p (φ.total t)]
  push_cast
  unfold LorenzTrajectoryx LorenzTrajectoryy LorenzTrajectoryz
  ring
--
/-! Defining the region where the derivative of LyapunovTilde is non-negative -/
def D (p : LorenzParams) : Set (ℝ × ℝ × ℝ) :=
  {u | 0 ≤ LyapunovTilde p u}


/-! Calculations on compactness of D, F and related properties -/
private lemma abs_le_max_one_of_sq_le {x K : ℝ} (h : x ^ 2 ≤ K) : |x| ≤ max K 1 := by
  rcases le_or_gt |x| 1 with h1 | h1
  · exact h1.trans (le_max_right _ _)
  · calc |x| ≤ |x| ^ 2 := by nlinarith
      _ = x ^ 2 := sq_abs x
      _ ≤ K := h
      _ ≤ max K 1 := le_max_left _ _

/-! The defining inequality of D, with the positive factor 2 * σ divided out. -/
lemma D_quadratic_le (p : LorenzParams) {x y z : ℝ} (hu : (x, y, z) ∈ D p) :
    p.r * x ^ 2 + y ^ 2 + p.b * (z - p.r) ^ 2 ≤ p.b * p.r ^ 2 := by
  simp only [D, Set.mem_ofPred_eq, LyapunovTilde] at hu
  nlinarith [p.σ_pos]

/-! D is closed: it is the preimage of [0, ∞) under the continuous LyapunovTilde. -/
lemma D_isClosed (p : LorenzParams) : IsClosed (D p) :=
  isClosed_Ici.preimage (LyapunovTilde_Continuous p)

/-! D is bounded: on D the positive definite quadratic form r x² + y² + b (z - r)²
is at most b r², which bounds each coordinate separately. -/
lemma D_isBounded (p : LorenzParams) : Bornology.IsBounded (D p) := by
  rw[Metric.isBounded_iff_subset_closedBall (0, 0, p.r)]
  refine ⟨max (max (p.b * p.r) 1) (max (max (p.b * p.r ^ 2) 1) (max (p.r ^ 2) 1)), ?_⟩
  rintro ⟨x, y, z⟩ hu
  have hQ := D_quadratic_le p hu
  have hx : x ^ 2 ≤ p.b * p.r := by nlinarith [p.r_pos, p.b_pos, sq_nonneg y, sq_nonneg (z - p.r)]
  have hy : y ^ 2 ≤ p.b * p.r ^ 2 := by
    nlinarith [p.r_pos, p.b_pos, sq_nonneg x, sq_nonneg (z - p.r)]
  have hz : (z - p.r) ^ 2 ≤ p.r ^ 2 := by nlinarith [p.b_pos, p.r_pos, sq_nonneg x, sq_nonneg y]
  simp only [Metric.mem_closedBall, Prod.dist_eq, Real.dist_eq, sub_zero, max_le_iff]
  exact ⟨(abs_le_max_one_of_sq_le hx).trans (le_max_left _ _),
    (abs_le_max_one_of_sq_le hy).trans ((le_max_left _ _).trans (le_max_right _ _)),
    (abs_le_max_one_of_sq_le hz).trans ((le_max_right _ _).trans (le_max_right _ _))⟩

/-! D is nonempty: it contains the center (0, 0, r), where LyapunovTilde = 2 σ b r² > 0. -/
lemma D_nonempty (p : LorenzParams) : (D p).Nonempty := by
  refine ⟨(0, 0, p.r), ?_⟩
  have h : LyapunovTilde p (0, 0, p.r) = 2 * p.σ * p.b * p.r ^ 2 := by
    simp only [LyapunovTilde]; ring
  have hpos : 0 < p.σ * p.b * p.r ^ 2 :=
    mul_pos (mul_pos p.σ_pos p.b_pos) (pow_pos p.r_pos 2)
  simp only [D, Set.mem_ofPred_eq, h]
  linarith


lemma D_isCompact (p : LorenzParams) :
    IsCompact (D p) := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · exact isClosed_le continuous_const (LyapunovTilde_Continuous p)
  · exact D_isBounded p

-- derive contradiction from hnonneg and dist > r



lemma V_attainsMaximum_onD (p : LorenzParams) :
    ∃ u ∈ D p, ∀ v ∈ D p, Lyapunov p u ≥ Lyapunov p v := by
  have hcompact : IsCompact (D p) := D_isCompact p
  have cont : ContinuousOn (Lyapunov p) (D p) :=
    (Lyapunov_Continuous p).continuousOn
  have hD : (D p).Nonempty := by
    refine ⟨(0, 0, p.r), ?_⟩
    have hσ_nonneg : 0 ≤ p.σ := le_of_lt p.σ_pos
    have hb_nonneg : 0 ≤ p.b := le_of_lt p.b_pos
    have hr_sq_nonneg : 0 ≤ p.r ^ 2 := sq_nonneg p.r
    have hnonneg : 0 ≤ 2 * p.σ * p.b * p.r ^ 2 := by
      exact
        mul_nonneg
          (mul_nonneg
            (mul_nonneg (by norm_num : 0 ≤ (2 : ℝ)) hσ_nonneg) hb_nonneg)
          hr_sq_nonneg
    simpa [D, LyapunovTilde] using hnonneg
  obtain ⟨u, hu, hmax⟩ := hcompact.exists_isMaxOn hD cont
  exact ⟨u, hu, fun _ hv => hmax hv⟩



noncomputable def c (p : LorenzParams) : ℝ :=
  Lyapunov p (Classical.choose (V_attainsMaximum_onD p))

def F (p : LorenzParams) : Set (ℝ × ℝ × ℝ) :=
  {u | Lyapunov p u  ≤ c p +1}

lemma F_isCompact (p : LorenzParams)
    : IsCompact (F p) := by
  let A := Real.sqrt (|c p + 1| / p.r)
  let B := Real.sqrt (|c p + 1| / p.σ)
  let K := Icc (-A) A ×ˢ
    (Icc (-B) B ×ˢ Icc (2 * p.r - B) (2 * p.r + B))
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  refine hK.of_isClosed_subset
    (isClosed_le (Lyapunov_Continuous p) continuous_const) ?_
  rintro ⟨x, y, z⟩ hu
  simp only [F, Set.mem_ofPred_eq] at hu
  change p.r * x ^ 2 + p.σ * y ^ 2 + p.σ * (z - 2 * p.r) ^ 2 ≤
    c p + 1 at hu
  have hxterm : p.r * x ^ 2 ≤ |c p + 1| := by
    nlinarith [hu, le_abs_self (c p + 1),
      mul_nonneg p.σ_pos.le (sq_nonneg y),
      mul_nonneg p.σ_pos.le (sq_nonneg (z - 2 * p.r))]
  have hyterm : p.σ * y ^ 2 ≤ |c p + 1| := by
    nlinarith [hu, le_abs_self (c p + 1),
      mul_nonneg p.r_pos.le (sq_nonneg x),
      mul_nonneg p.σ_pos.le (sq_nonneg (z - 2 * p.r))]
  have hzterm : p.σ * (z - 2 * p.r) ^ 2 ≤ |c p + 1| := by
    nlinarith [hu, le_abs_self (c p + 1),
      mul_nonneg p.r_pos.le (sq_nonneg x),
      mul_nonneg p.σ_pos.le (sq_nonneg y)]
  have hx2 : x ^ 2 ≤ |c p + 1| / p.r :=
    (le_div_iff₀ p.r_pos).2 (by simpa [mul_comm] using hxterm)
  have hy2 : y ^ 2 ≤ |c p + 1| / p.σ :=
    (le_div_iff₀ p.σ_pos).2 (by simpa [mul_comm] using hyterm)
  have hz2 : (z - 2 * p.r) ^ 2 ≤ |c p + 1| / p.σ :=
    (le_div_iff₀ p.σ_pos).2 (by simpa [mul_comm] using hzterm)
  have hx : |x| ≤ A := by
    apply abs_le_of_sq_le_sq
    · rw [show A ^ 2 = |c p + 1| / p.r by
        exact Real.sq_sqrt (div_nonneg (abs_nonneg _) p.r_pos.le)]
      exact hx2
    · exact Real.sqrt_nonneg _
  have hy : |y| ≤ B := by
    apply abs_le_of_sq_le_sq
    · rw [show B ^ 2 = |c p + 1| / p.σ by
        exact Real.sq_sqrt (div_nonneg (abs_nonneg _) p.σ_pos.le)]
      exact hy2
    · exact Real.sqrt_nonneg _
  have hz : |z - 2 * p.r| ≤ B := by
    apply abs_le_of_sq_le_sq
    · rw [show B ^ 2 = |c p + 1| / p.σ by
        exact Real.sq_sqrt (div_nonneg (abs_nonneg _) p.σ_pos.le)]
      exact hz2
    · exact Real.sqrt_nonneg _
  rcases abs_le.mp hx with ⟨hxlo, hxhi⟩
  rcases abs_le.mp hy with ⟨hylo, hyhi⟩
  rcases abs_le.mp hz with ⟨hzlo, hzhi⟩
  exact ⟨⟨hxlo, hxhi⟩, ⟨⟨hylo, hyhi⟩, ⟨by linarith, by linarith⟩⟩⟩

lemma dF_in_levelset (p : LorenzParams) :
  ∀ u ∈ frontier (F p), Lyapunov p u = c p +1 := by
  intro u hu
  exact frontier_le_subset_eq (Lyapunov_Continuous p) continuous_const
    (by simpa [F] using hu)


lemma dF_disjoint_from_D (p : LorenzParams) :
  ∀ u ∈ frontier (F p), u ∉ D p := by
  intro u hu huD
  have hmax := Classical.choose_spec (V_attainsMaximum_onD p)
  have hlevel : Lyapunov p u = c p + 1 := dF_in_levelset p u hu
  have hmaxc : Lyapunov p (Classical.choose (V_attainsMaximum_onD p)) = c p := rfl
  have hcontra : False := by
    have hle : Lyapunov p (Classical.choose (V_attainsMaximum_onD p)) ≥ Lyapunov p u :=
      hmax.2 u huD
    linarith [hle, hlevel, hmaxc]
  exact hcontra.elim

lemma LyapunovTilde_negative_on_dF (p : LorenzParams) :
  ∀ u ∈ frontier (F p), LyapunovTilde p u < 0 := by
  intro u hu
  have hnot : ¬ 0 ≤ LyapunovTilde p u := by
    simpa [D] using (dF_disjoint_from_D p u hu)
  exact lt_of_not_ge hnot

lemma FequalBdunionInt (p : LorenzParams) :
  F p = interior (F p) ∪ frontier (F p) := by
  have h : IsClosed (F p) := (F_isCompact p).isClosed
  conv_lhs=>rw [← h.closure_eq]
  apply closure_eq_interior_union_frontier


/-! Main theorem -/
theorem Lorenz_trapping_region_case1 (p : LorenzParams) (φ : LorenzTrajectory)
(hφ : IsSolution p φ) (t0 : ℝ) (hφ_t0 : φ.total t0 ∈ interior (F p)) :
  ∀ t > t0, φ.total t ∈ interior (F p) := by
  by_contra hnot
  have h : ∃ t > t0, φ.total t ∉ interior (F p) := by
    simpa using not_forall.mp hnot
  let S : Set ℝ := {t : ℝ | t ≥  t0 ∧ φ.total t ∉ interior (F p)}
  let hS_nonempty: S.Nonempty := by
    use Classical.choose h
    unfold S
    grind
  let lowerbound : ∀ t ∈ S, t0 ≤ t := by
    unfold S
    grind
  let τ : ℝ := sInf S
  have hhτ : t0 ≤ τ := by
    rw [show τ = sInf S by rfl]
    exact le_csInf hS_nonempty lowerbound
  let φτ : ℝ × ℝ × ℝ := φ.total τ
  let t' : ℝ := Classical.choose h
  have hf : Continuous φ.total := by
   exact continuous_iff_continuousAt.mpr (by
    intro t
    exact (hφ.2.2.2 t).continuousAt)
  have htt: t0 ≤ t' := by grind
  have hφt' : φ.total t' ∉ interior (F p) := by grind
  have hφτ : φτ∈ (frontier (interior (F p))) := by
    rw [show φτ = φ.total τ from rfl]
    rw [show τ = sInf S from rfl]
    unfold S
    apply Continuous.firstExit_mem_frontier hf htt hφ_t0 hφt'
  have hφτ' : φτ∈ (frontier (F p)) := by
    grind [frontier_interior_subset]
  let hhhτ: τ≠ t0:= by
     by_contra hc
     have hcc: φ.total t0 ∈ frontier (F p) := by grind
     have hccc: φ.total t0 ∉ frontier (F p) := by
      exact Set.disjoint_left.mp disjoint_interior_frontier hφ_t0
     grind
  let hhhhτ: τ> t0:= by grind
  have hφτ'' : Lyapunov p (φ.total τ) = c p + 1 := by
      rw [dF_in_levelset p φτ hφτ']
  have hφt: ∀ t∈{t | t ≥ t0 ∧ t < τ}, φ.total t ∈ interior (F p) := by
    by_contra hh
    simp only [not_forall, exists_prop] at hh
    let t'' :ℝ := Classical.choose hh
    have hφt'' : t'' ∈ S := by grind
    have hhτ : τ ≤ t'' := by
      rw [show τ = sInf S from rfl]
      exact csInf_le ⟨t0, lowerbound⟩ hφt''
    grind
  have hVφt : ∀ t∈{t | t ≥ t0 ∧ t < τ}, Lyapunov p (φ.total t) ≤ c p + 1 := by
    intro t hyt
    have hhhh: φ.total t ∈ interior (F p) :=by grind
    have hhh : φ.total t ∈ F p := by apply interior_subset hhhh
    rw[F] at hhh
    assumption
  ---Leftlimit derivative argument at τ using hVφt and hφτ''
  let hneg : (LyapunovTilde p (φ.total τ))<0:= by
    apply LyapunovTilde_negative_on_dF p φτ hφτ'
  let hderiv := LyapunovAlongTrajectory_Deriv p φ hφ τ
  have hleft := (hasDerivAt_iff_tendsto_slope_left_right.mp hderiv).1
  have h_slope_nonneg : ∀ᶠ t in 𝓝[<] τ, 0 ≤ slope (LyapunovAlongTrajectory p φ) τ t := by
    have hIco : Ioo t0 τ ∈ 𝓝[<] τ := by
       apply Ioo_mem_nhdsLT
       exact hhhhτ
    filter_upwards [hIco] with t ht
    unfold slope
    unfold Ioo at ht
    rw [show LyapunovAlongTrajectory p φ t = Lyapunov p (φ.total t) from rfl]
    rw [show LyapunovAlongTrajectory p φ τ = Lyapunov p (φ.total τ) from rfl]
    have denomneg : (t - τ)⁻¹ < 0 := by simpa [sub_lt_zero] using ht.2;
    have numerneg : Lyapunov p (φ.total t) - Lyapunov p (φ.total τ) ≤ 0 := by
      have hVφt' : Lyapunov p (φ.total t) ≤ c p + 1 := by grind
      have hVφτ' : Lyapunov p (φ.total τ) = c p + 1 := by grind
      linarith
    have denomneg' : (t - τ)⁻¹ ≤ 0 := le_of_lt denomneg
    exact mul_nonneg_of_nonpos_of_nonpos denomneg' numerneg
  have h_derivative_nonneg : 0 ≤ LyapunovTilde p (φ.total τ) :=
    ge_of_tendsto hleft h_slope_nonneg
  grind

theorem Lorenz_trapping_region_case2 (p : LorenzParams) (φ : LorenzTrajectory)
(hφ : IsSolution p φ) (t0 : ℝ) (hφ_t0 : φ.total t0 ∈ frontier (F p)) :
  ∀ t > t0, φ.total t ∈ interior (F p) := by
  by_contra h
  push Not at h
  --simp at h
  let t' :ℝ := Classical.choose h
  let S : Set ℝ := {t : ℝ | t > t0 ∧ t<t'}
  have ht' : (∃ t''∈ S, φ.total t'' ∈ (interior (F p))) ∨ (∀ t''∈ S, φ.total t'' ∉ (interior (F p))):= by
    grind
  rcases ht' with h1 | h2
  ----First case
  · let t'': ℝ := Classical.choose h1
    have hφ_t'' : φ.total t'' ∈ (interior (F p)) := by grind
    have prop : ∀ t > t'', φ.total t ∈ interior (F p):= Lorenz_trapping_region_case1 p φ hφ t'' hφ_t''
    grind
  ----Second case
  · have h3 : ∀ t'' ∈ S, Lyapunov p (φ.total t'') ≥ c p + 1 := by
      intro t ht
      have ht_not_int : φ.total t ∉ interior (F p) := h2 t ht
      by_cases htF : φ.total t ∈ F p
      · rw [FequalBdunionInt p] at htF
        rcases htF with ht_int | ht_frontier
        · exact (ht_not_int ht_int).elim
        · exact (dF_in_levelset p (φ.total t) ht_frontier).ge
      · have hnotle : ¬ Lyapunov p (φ.total t) ≤ c p + 1 := by
          simpa [F] using htF
        exact (lt_of_not_ge hnotle).le
    let φt0 : ℝ × ℝ × ℝ := φ.total t0
    have hφt0 : Lyapunov p (φ.total t0) = c p + 1 := by
      rw [dF_in_levelset p φt0 hφ_t0]
    ---Right limit derivative argument at t_0 left using h3 and hφt0
    let hneg : (LyapunovTilde p (φ.total t0))<0:= by
      apply LyapunovTilde_negative_on_dF p φt0 hφ_t0
    let hderiv := LyapunovAlongTrajectory_Deriv p φ hφ t0
    have hright := (hasDerivAt_iff_tendsto_slope_left_right.mp hderiv).2
    have h_slope_nonneg : ∀ᶠ t in 𝓝[>] t0, 0 ≤ slope (LyapunovAlongTrajectory p φ) t0 t := by
      have ht0t' : t0 < t' := (Classical.choose_spec h).1
      have hIco : Ioo t0 t' ∈ 𝓝[>] t0 := Ioo_mem_nhdsGT ht0t'
      filter_upwards [hIco] with t ht
      unfold slope
      unfold Ioo at ht
      rw [show LyapunovAlongTrajectory p φ t = Lyapunov p (φ.total t) from rfl]
      rw [show LyapunovAlongTrajectory p φ t0 = Lyapunov p (φ.total t0) from rfl]
      have denompos : (t - t0)⁻¹ > 0 := by simpa [sub_lt_zero] using ht.1
      have hVφt' : Lyapunov p (φ.total t) ≥ c p + 1 := by
        have htS : t ∈ S := by
          constructor
          · exact ht.1
          · exact ht.2
        exact h3 t htS
      have hVφt0' : Lyapunov p (φ.total t0) = c p + 1 := hφt0
      have numer_nonneg : Lyapunov p (φ.total t) - Lyapunov p (φ.total t0) ≥ 0 := by
        linarith
      have denom_nonneg : (t - t0)⁻¹ ≥ 0 := le_of_lt denompos
      exact mul_nonneg denom_nonneg numer_nonneg
    have h_derivative_nonneg : 0 ≤ LyapunovTilde p (φ.total t0) :=
       ge_of_tendsto hright h_slope_nonneg
    exact not_lt_of_ge h_derivative_nonneg hneg


theorem Lorenz_trapping_region (p : LorenzParams) (φ : LorenzTrajectory)
(hφ : IsSolution p φ) : ∃ F : Set (ℝ × ℝ × ℝ), Bornology.IsBounded F ∧  ∀t0 : ℝ, φ.total t0 ∈ F →
 (∀ t > t0, φ.total t ∈ interior (F)):= by
  use F p
  rw [and_iff_left ?_]
  · refine IsCompact.isBounded ?_
    apply F_isCompact
  · intro t0 h1
    let φt0 : ℝ × ℝ × ℝ := φ.total t0
    have hφt0 : φt0∈ (interior (F p)) ∪ (frontier (F p)):= by
      rw [← FequalBdunionInt p]
      assumption
    rcases hφt0 with hφt0_interior | hφt0_frontier
    · exact Lorenz_trapping_region_case1 p φ hφ t0 hφt0_interior
    · exact Lorenz_trapping_region_case2 p φ hφ t0 hφt0_frontier
