/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Ordinals.Tree.Rec

/-!
# Ordinal arithmetic on trees

Addition, multiplication and exponentiation of trees, by transfinite recursion (`orec`) on the
second argument:

- `add s t := orec s succ t`: start at `s` and apply `succ` (snu-sf: `OrdArith.add`).
- `mul s t := orec zero (fun r => add r s) t`: start at `zero` and add `s` (snu-sf:
  `OrdArith.mult`).
- `pow s t := orec (succ zero) (fun r => mul r s) t`: start at `1` and multiply by `s` (snu-sf:
  `OrdArith.expn`).

Each operation has monotonicity lemmas and a congruence lemma for `≈`. The main results are
`add_assoc`, `mul_add` (left distributivity), `mul_assoc`, `pow_add` and `pow_mul`, the
equations for `zero`, `succ`, `sup`, `mk` and `max`, and the compatibility with `ofNat`.
`trec_add` and `orec_add` (snu-sf: sections `RECAPP`, `ORECAPP`) give the recursion along a
sum: the recursion along `add s t` is the recursion along `t` from the result along `s`.

This file follows snu-sf/Ordinal (`src/Arithmetic.v`, module `OrdArith`). The names of the Rocq
lemmas are in the docstrings. The lemmas take only the hypotheses that their proofs need. For
example, `pow_le_pow_right` and `pow_sup` do not need `zero < s`: with this definition,
`pow zero t ≈ succ zero` for each `t` (`pow_zero_left`).

Lemmas with the name of a general algebraic law (`add_assoc`, `mul_add`, ...) are protected.

The results of this file use no axioms.
-/

@[expose] public section

namespace Ordinals

universe u v

namespace OTree

/-! ## Addition -/

/-- Ordinal addition: `add s t` applies `succ` to `s` along `t` (snu-sf: `OrdArith.add`). -/
def add (s : OTree.{u}) : OTree.{u} → OTree.{u} :=
  orec s succ

/-- snu-sf: `OrdArith.add_base_l`. -/
protected theorem le_add_right (s t : OTree.{u}) : s ≤ add s t :=
  base_le_orec t

/-- snu-sf: `OrdArith.add_O_r`. -/
protected theorem add_zero (s : OTree.{u}) : add s zero ≈ s :=
  orec_zero

/-- snu-sf: `OrdArith.add_S`. -/
theorem add_succ (s t : OTree.{u}) : add s (succ t) ≈ succ (add s t) :=
  orec_succ le_succ t

/-- snu-sf: `OrdArith.add_join`. -/
theorem add_sup (s : OTree.{u}) {ι : Type u} (f : ι → OTree.{u}) :
    add s (sup f) ≈ max s (sup fun i => add s (f i)) :=
  orec_sup succ_le_succ f

/-- snu-sf: `OrdArith.add_join_inhabited`. -/
theorem add_sup_of_nonempty (s : OTree.{u}) {ι : Type u} [Nonempty ι] (f : ι → OTree.{u}) :
    add s (sup f) ≈ sup fun i => add s (f i) :=
  orec_sup_of_nonempty succ_le_succ f

/-- snu-sf: `OrdArith.add_build`. -/
theorem add_mk (s : OTree.{u}) (ι : Type u) (f : ι → OTree.{u}) :
    add s (mk ι f) ≈ max s (sup fun i => succ (add s (f i))) :=
  orec_mk ι f

/-- snu-sf: `OrdArith.add_union`. -/
theorem add_max (r s t : OTree.{u}) : add r (max s t) ≈ max (add r s) (add r t) :=
  orec_max succ_le_succ s t

/-- snu-sf: `OrdArith.le_add_r`. -/
protected theorem add_le_add_left {s t : OTree.{u}} (h : s ≤ t) (r : OTree.{u}) :
    add r s ≤ add r t :=
  orec_le_orec succ_le_succ h

/-- snu-sf: `OrdArith.lt_add_r`. -/
protected theorem add_lt_add_left {s t : OTree.{u}} (h : s < t) (r : OTree.{u}) :
    add r s < add r t :=
  OTree.lt_of_lt_of_le (lt_succ _) (next_orec_le_orec succ_le_succ h)

/-- snu-sf: `OrdArith.eq_add_r`. -/
theorem add_congr_right {s t : OTree.{u}} (h : s ≈ t) (r : OTree.{u}) : add r s ≈ add r t :=
  orec_congr succ_le_succ h

/-- snu-sf: `OrdArith.le_add_l`. -/
protected theorem add_le_add_right {s t : OTree.{u}} (h : s ≤ t) (r : OTree.{u}) :
    add s r ≤ add t r :=
  orec_mono h succ_le_succ r

/-- snu-sf: `OrdArith.eq_add_l`. -/
theorem add_congr_left {s t : OTree.{u}} (h : s ≈ t) (r : OTree.{u}) : add s r ≈ add t r :=
  ⟨OTree.add_le_add_right h.le r, OTree.add_le_add_right h.ge r⟩

/-- snu-sf: `OrdArith.add_le_proper`. -/
protected theorem add_le_add {s s' t t' : OTree.{u}} (hs : s ≤ s') (ht : t ≤ t') :
    add s t ≤ add s' t' :=
  OTree.le_trans (OTree.add_le_add_right hs t) (OTree.add_le_add_left ht s')

/-- snu-sf: `OrdArith.add_eq_proper`. -/
theorem add_congr {s s' t t' : OTree.{u}} (hs : s ≈ s') (ht : t ≈ t') : add s t ≈ add s' t' :=
  ⟨OTree.add_le_add hs.le ht.le, OTree.add_le_add hs.ge ht.ge⟩

/-- snu-sf: `OrdArith.add_base_r`. -/
protected theorem le_add_left (s t : OTree.{u}) : t ≤ add s t :=
  OTree.le_trans (orec_zero_succ t).ge (orec_mono (zero_le s) succ_le_succ t)

/-- snu-sf: `OrdArith.add_O_l`. -/
protected theorem zero_add (s : OTree.{u}) : add zero s ≈ s :=
  orec_zero_succ s

/-- snu-sf: `OrdArith.add_lt_l`. -/
protected theorem lt_add_of_pos_right (s : OTree.{u}) {t : OTree.{u}} (h : zero < t) :
    s < add s t :=
  OTree.lt_of_le_of_lt (OTree.add_zero s).ge (OTree.add_lt_add_left h s)

/-! ## Recursion along a sum -/

section Trec

variable {D : Type v} {dle : D → D → Prop} {wf : D → Prop} {djoin : (A : Type u) → (A → D) → D}
  {base : D} {next : D → D}

/-- Recursion along `add s t` is recursion along `t`, from the result of the recursion along `s`
(snu-sf: `OrdArith.rec_app`). -/
theorem trec_add (hJ : JoinLaws dle wf djoin) (hS : StepLaws wf base next)
    (hm : NextMono dle wf next) (hl : ∀ {d}, wf d → dle d (next d)) (s : OTree.{u}) :
    ∀ t : OTree.{u},
      dle (trec base next djoin (add s t)) (trec (trec base next djoin s) next djoin t) ∧
        dle (trec (trec base next djoin s) next djoin t) (trec base next djoin (add s t))
  | mk ι f => by
    have wT := trec_wf hJ hS
    have wT' := trec_wf hJ (base := trec base next djoin s) ⟨wT s, hS.next_wf⟩
    have ih := fun i => trec_add hJ hS hm hl s (f i)
    have wn' : ∀ i, wf (next (trec (trec base next djoin s) next djoin (f i))) :=
      fun i => hS.next_wf (wT' (f i))
    have wg : ∀ i, wf (trec base next djoin (succ (add s (f i)))) := fun i => wT _
    have wY := hJ.join_wf wg
    have wY' := hJ.join_wf wn'
    have wB := hJ.dunion_wf hS.base_wf wY
    -- `trec (succ (add s (f i)))` is `next (trec' (f i))`.
    have e₄ : ∀ i, dle (trec base next djoin (succ (add s (f i))))
          (next (trec (trec base next djoin s) next djoin (f i))) ∧
        dle (next (trec (trec base next djoin s) next djoin (f i)))
          (trec base next djoin (succ (add s (f i)))) := fun i =>
      hJ.equiv_trans (wT _) (hS.next_wf (wT _)) (wn' i) (trec_succ hJ hS hl _)
        ⟨hm (wT _) (wT' _) (ih i).1, hm (wT' _) (wT _) (ih i).2⟩
    have e₅ := hJ.join_congr wg wn' e₄
    -- The member `base` is below `trec s`.
    have hb := base_le_trec hJ hS s
    have wR := hJ.dunion_wf (wT s) wY'
    have e₆ : dle (dunion djoin (trec base next djoin s)
            (dunion djoin base (djoin ι fun i => trec base next djoin (succ (add s (f i))))))
          (dunion djoin (trec base next djoin s)
            (djoin ι fun i => next (trec (trec base next djoin s) next djoin (f i)))) ∧
        dle (dunion djoin (trec base next djoin s)
            (djoin ι fun i => next (trec (trec base next djoin s) next djoin (f i))))
          (dunion djoin (trec base next djoin s)
            (dunion djoin base (djoin ι fun i => trec base next djoin (succ (add s (f i)))))) := by
      refine ⟨hJ.dunion_le (wT s) wB wR (hJ.le_dunion_left (wT s) wY') ?_, ?_⟩
      · refine hJ.dunion_le hS.base_wf wY wR
          (hJ.le_trans hS.base_wf (wT s) wR hb (hJ.le_dunion_left (wT s) wY')) ?_
        exact hJ.le_trans wY wY' wR e₅.1 (hJ.le_dunion_right (wT s) wY')
      · exact hJ.dunion_mono (wT s) wY' (wT s) wB (hJ.le_refl (wT s))
          (hJ.le_trans wY' wY wB e₅.2 (hJ.le_dunion_right hS.base_wf wY))
    have e₁ := trec_congr hJ hS hm (add_mk s ι f)
    have e₂ := trec_max hJ hS hm s (sup fun i => succ (add s (f i)))
    have e₃ := trec_sup hJ hS hm fun i => succ (add s (f i))
    have e₂₃ := hJ.equiv_trans (wT _) (hJ.dunion_wf (wT s) (wT _)) (hJ.dunion_wf (wT s) wB) e₂
      (hJ.dunion_congr (wT s) (wT _) (wT s) wB
        ⟨hJ.le_refl (wT s), hJ.le_refl (wT s)⟩ e₃)
    exact hJ.equiv_trans (wT _) (wT _) wR e₁
      (hJ.equiv_trans (wT _) (hJ.dunion_wf (wT s) wB) wR e₂₃ e₆)

end Trec

/-- Recursion along `add s t` into the trees (snu-sf: `OrdArith.orec_app`). -/
theorem orec_add {next : OTree.{u} → OTree.{u}}
    (hm : ∀ {s t : OTree.{u}}, s ≤ t → next s ≤ next t) (hl : ∀ s, s ≤ next s)
    (base s t : OTree.{u}) :
    orec base next (add s t) ≈ orec (orec base next s) next t :=
  trec_add sup_joinLaws (stepLaws_true base next) (nextMono_of_mono hm) (fun _ => hl _) s t

/-- snu-sf: `OrdArith.add_assoc`. -/
protected theorem add_assoc (r s t : OTree.{u}) : add (add r s) t ≈ add r (add s t) :=
  (orec_add succ_le_succ le_succ r s t).symm

/-! ## Multiplication -/

/-- Ordinal multiplication: `mul s t` adds `s` along `t`, from `zero`
(snu-sf: `OrdArith.mult`). -/
def mul (s : OTree.{u}) : OTree.{u} → OTree.{u} :=
  orec zero fun r => add r s

/-- `add · s` is monotone: the step of `mul` (snu-sf: `OrdArith.mult_gen_mon`; the lemma
`OrdArith.mult_gen_le` is `le_add_right`). -/
theorem add_right_mono (s : OTree.{u}) {r r' : OTree.{u}} (h : r ≤ r') : add r s ≤ add r' s :=
  OTree.add_le_add_right h s

/-- snu-sf: `OrdArith.mult_O_r`. -/
protected theorem mul_zero (s : OTree.{u}) : mul s zero ≈ zero :=
  orec_zero

/-- snu-sf: `OrdArith.mult_S`. -/
theorem mul_succ (s t : OTree.{u}) : mul s (succ t) ≈ add (mul s t) s :=
  orec_succ (fun r => OTree.le_add_right r s) t

/-- snu-sf: `OrdArith.mult_join`. -/
theorem mul_sup (s : OTree.{u}) {ι : Type u} (f : ι → OTree.{u}) :
    mul s (sup f) ≈ sup fun i => mul s (f i) :=
  Equiv.trans (orec_sup (add_right_mono s) f) (max_equiv_of_le (zero_le _))

/-- snu-sf: `OrdArith.mult_build`. -/
theorem mul_mk (s : OTree.{u}) (ι : Type u) (f : ι → OTree.{u}) :
    mul s (mk ι f) ≈ sup fun i => add (mul s (f i)) s :=
  Equiv.trans (orec_mk ι f) (max_equiv_of_le (zero_le _))

/-- snu-sf: `OrdArith.mult_union`. -/
theorem mul_max (r s t : OTree.{u}) : mul r (max s t) ≈ max (mul r s) (mul r t) :=
  orec_max (add_right_mono r) s t

/-- snu-sf: `OrdArith.le_mult_r`. -/
protected theorem mul_le_mul_left {s t : OTree.{u}} (h : s ≤ t) (r : OTree.{u}) :
    mul r s ≤ mul r t :=
  orec_le_orec (add_right_mono r) h

/-- snu-sf: `OrdArith.eq_mult_r`. -/
theorem mul_congr_right {s t : OTree.{u}} (h : s ≈ t) (r : OTree.{u}) : mul r s ≈ mul r t :=
  orec_congr (add_right_mono r) h

/-- snu-sf: `OrdArith.le_mult_l`. -/
protected theorem mul_le_mul_right {s t : OTree.{u}} (h : s ≤ t) (r : OTree.{u}) :
    mul s r ≤ mul t r :=
  orec_mono OTree.le_rfl (fun h' => OTree.add_le_add h' h) r

/-- snu-sf: `OrdArith.eq_mult_l`. -/
theorem mul_congr_left {s t : OTree.{u}} (h : s ≈ t) (r : OTree.{u}) : mul s r ≈ mul t r :=
  ⟨OTree.mul_le_mul_right h.le r, OTree.mul_le_mul_right h.ge r⟩

/-- snu-sf: `OrdArith.mult_le_proper`. -/
protected theorem mul_le_mul {s s' t t' : OTree.{u}} (hs : s ≤ s') (ht : t ≤ t') :
    mul s t ≤ mul s' t' :=
  OTree.le_trans (OTree.mul_le_mul_right hs t) (OTree.mul_le_mul_left ht s')

/-- snu-sf: `OrdArith.mult_eq_proper`. -/
theorem mul_congr {s s' t t' : OTree.{u}} (hs : s ≈ s') (ht : t ≈ t') : mul s t ≈ mul s' t' :=
  ⟨OTree.mul_le_mul hs.le ht.le, OTree.mul_le_mul hs.ge ht.ge⟩

/-- snu-sf: `OrdArith.lt_mult_r`. -/
protected theorem mul_lt_mul_of_pos_left {r s t : OTree.{u}} (h : s < t) (hr : zero < r) :
    mul r s < mul r t :=
  OTree.lt_of_lt_of_le (OTree.lt_add_of_pos_right _ hr) (next_orec_le_orec (add_right_mono r) h)

/-- snu-sf: `OrdArith.mult_O_l`. -/
protected theorem zero_mul : ∀ s : OTree.{u}, mul zero s ≈ zero
  | mk ι f =>
    ⟨OTree.le_trans (mul_mk zero ι f).le
        (sup_le fun i => OTree.le_trans (OTree.add_zero _).le (OTree.zero_mul (f i)).le),
      zero_le _⟩

/-- snu-sf: `OrdArith.mult_1_r`. -/
protected theorem mul_one (s : OTree.{u}) : mul s (succ zero) ≈ s :=
  Equiv.trans (mul_succ s zero)
    (Equiv.trans (add_congr_left (OTree.mul_zero s) s) (OTree.zero_add s))

/-- snu-sf: `OrdArith.mult_1_l`. -/
protected theorem one_mul (s : OTree.{u}) : mul (succ zero) s ≈ s := by
  refine Equiv.trans ⟨?_, ?_⟩ (orec_zero_succ s)
  · exact orec_mono OTree.le_rfl (fun h => OTree.le_trans (add_succ _ zero).le
      (succ_le_succ (OTree.le_trans (OTree.add_zero _).le h))) s
  · exact orec_mono OTree.le_rfl (fun h => OTree.le_trans
      (succ_le_succ (OTree.le_trans h (OTree.add_zero _).ge)) (add_succ _ zero).ge) s

/-- Left distributivity (snu-sf: `OrdArith.mult_dist`). -/
protected theorem mul_add (r : OTree.{u}) (s : OTree.{u}) :
    ∀ t : OTree.{u}, mul r (add s t) ≈ add (mul r s) (mul r t)
  | mk ι f => by
    have ih := fun i => OTree.mul_add r s (f i)
    -- Left side.
    have e₁ : mul r (add s (mk ι f)) ≈
        max (mul r s) (sup fun i => add (add (mul r s) (mul r (f i))) r) :=
      Equiv.trans (mul_congr_right (add_mk s ι f) r)
        (Equiv.trans (mul_max r s _)
          (max_congr (Equiv.refl _)
            (Equiv.trans (mul_sup r _)
              (sup_congr fun i => Equiv.trans (mul_succ r _) (add_congr_left (ih i) r)))))
    -- Right side.
    have e₂ : add (mul r s) (mul r (mk ι f)) ≈
        max (mul r s) (sup fun i => add (mul r s) (add (mul r (f i)) r)) :=
      Equiv.trans (add_congr_right (mul_mk r ι f) _) (add_sup _ _)
    exact Equiv.trans e₁ (Equiv.trans
      (max_congr (Equiv.refl _) (sup_congr fun i => OTree.add_assoc _ _ _)) e₂.symm)

/-- snu-sf: `OrdArith.mult_assoc`. -/
protected theorem mul_assoc (r s : OTree.{u}) :
    ∀ t : OTree.{u}, mul (mul r s) t ≈ mul r (mul s t)
  | mk ι f => by
    have ih := fun i => OTree.mul_assoc r s (f i)
    refine Equiv.trans (mul_mk _ ι f) (Equiv.trans ?_ (mul_congr_right (mul_mk s ι f) r).symm)
    refine Equiv.trans ?_ (mul_sup r _).symm
    exact sup_congr fun i =>
      Equiv.trans (add_congr_left (ih i) _) (OTree.mul_add r _ s).symm

/-- snu-sf: `OrdArith.mult_le_l`. -/
protected theorem le_mul_of_pos_right (s : OTree.{u}) {t : OTree.{u}} (h : zero < t) :
    s ≤ mul s t :=
  OTree.le_trans (OTree.mul_one s).ge (OTree.mul_le_mul_left (succ_le_of_lt h) s)

/-- snu-sf: `OrdArith.mult_lt_l`. -/
protected theorem lt_mul_of_one_lt_right {s t : OTree.{u}} (hs : zero < s) (ht : succ zero < t) :
    s < mul s t := by
  have h₁ : add s s ≈ mul s (succ (succ zero)) :=
    Equiv.trans (add_congr_left (OTree.mul_one s) s).symm (mul_succ s (succ zero)).symm
  exact OTree.lt_of_lt_of_le (OTree.lt_add_of_pos_right s hs)
    (OTree.le_trans h₁.le (OTree.mul_le_mul_left (succ_le_of_lt ht) s))

/-! ## Exponentiation -/

/-- Ordinal exponentiation: `pow s t` multiplies by `s` along `t`, from `succ zero`
(snu-sf: `OrdArith.expn`). -/
def pow (s : OTree.{u}) : OTree.{u} → OTree.{u} :=
  orec (succ zero) fun r => mul r s

/-- `mul · s` is monotone: the step of `pow` (snu-sf: the local `expn_gen_mon` of section
`EXPN`). -/
theorem mul_right_mono (s : OTree.{u}) {r r' : OTree.{u}} (h : r ≤ r') : mul r s ≤ mul r' s :=
  OTree.mul_le_mul_right h s

/-- snu-sf: `OrdArith.expn_O`. -/
protected theorem pow_zero (s : OTree.{u}) : pow s zero ≈ succ zero :=
  orec_zero

/-- snu-sf: `OrdArith.expn_pos`. -/
protected theorem zero_lt_pow (s t : OTree.{u}) : zero < pow s t :=
  OTree.lt_of_lt_of_le (zero_lt_succ zero) (base_le_orec t)

/-- snu-sf: `OrdArith.expn_S`. -/
protected theorem pow_succ {s : OTree.{u}} (hs : zero < s) (t : OTree.{u}) :
    pow s (succ t) ≈ mul (pow s t) s :=
  orec_succ (fun r => OTree.le_mul_of_pos_right r hs) t

/-- snu-sf: `OrdArith.le_expn_r`. The hypothesis `zero < s` of snu-sf is not necessary. -/
protected theorem pow_le_pow_right (s : OTree.{u}) {t t' : OTree.{u}} (h : t ≤ t') :
    pow s t ≤ pow s t' :=
  orec_le_orec (mul_right_mono s) h

/-- snu-sf: `OrdArith.eq_expn_r`. -/
theorem pow_congr_right (s : OTree.{u}) {t t' : OTree.{u}} (h : t ≈ t') : pow s t ≈ pow s t' :=
  orec_congr (mul_right_mono s) h

/-- snu-sf: `OrdArith.expn_join`. -/
theorem pow_sup (s : OTree.{u}) {ι : Type u} (f : ι → OTree.{u}) :
    pow s (sup f) ≈ max (succ zero) (sup fun i => pow s (f i)) :=
  orec_sup (mul_right_mono s) f

/-- snu-sf: `OrdArith.expn_join_inhabited`. -/
theorem pow_sup_of_nonempty (s : OTree.{u}) {ι : Type u} [Nonempty ι] (f : ι → OTree.{u}) :
    pow s (sup f) ≈ sup fun i => pow s (f i) :=
  orec_sup_of_nonempty (mul_right_mono s) f

/-- snu-sf: `OrdArith.expn_build`. -/
theorem pow_mk (s : OTree.{u}) (ι : Type u) (f : ι → OTree.{u}) :
    pow s (mk ι f) ≈ max (succ zero) (sup fun i => mul (pow s (f i)) s) :=
  orec_mk ι f

/-- snu-sf: `OrdArith.expn_union`. -/
theorem pow_max (r s t : OTree.{u}) : pow r (max s t) ≈ max (pow r s) (pow r t) :=
  orec_max (mul_right_mono r) s t

/-- With this definition, `pow zero t` is `succ zero` for each `t`. -/
theorem pow_zero_left (t : OTree.{u}) : pow zero t ≈ succ zero := by
  cases t with
  | mk ι f =>
    exact ⟨OTree.le_trans (pow_mk zero ι f).le (max_le OTree.le_rfl
        (sup_le fun _ => OTree.le_trans (OTree.mul_zero _).le (zero_le _))),
      base_le_orec _⟩

/-- snu-sf: `OrdArith.expn_1_r`. -/
protected theorem pow_one {s : OTree.{u}} (hs : zero < s) : pow s (succ zero) ≈ s :=
  Equiv.trans (OTree.pow_succ hs zero)
    (Equiv.trans (mul_congr_left (OTree.pow_zero s) s) (OTree.one_mul s))

/-- snu-sf: `OrdArith.expn_add`. -/
protected theorem pow_add {s : OTree.{u}} (hs : zero < s) (t : OTree.{u}) :
    ∀ t' : OTree.{u}, pow s (add t t') ≈ mul (pow s t) (pow s t')
  | mk ι f => by
    have ih := fun i => OTree.pow_add hs t (f i)
    have h₁ : succ zero ≤ pow s t := succ_le_of_lt (OTree.zero_lt_pow s t)
    -- Left side.
    have e₁ : pow s (add t (mk ι f)) ≈
        max (pow s t) (sup fun i => mul (mul (pow s t) (pow s (f i))) s) := by
      refine Equiv.trans (pow_congr_right s (add_mk t ι f)) (Equiv.trans (pow_max s _ _) ?_)
      refine Equiv.trans (max_congr (Equiv.refl _) (pow_sup s _)) ?_
      refine Equiv.trans (max_assoc _ _ _).symm (max_congr ?_ ?_)
      · exact Equiv.trans (max_comm _ _) (max_equiv_of_le h₁)
      · exact sup_congr fun i =>
          Equiv.trans (OTree.pow_succ hs _) (mul_congr_left (ih i) s)
    -- Right side.
    have e₂ : mul (pow s t) (pow s (mk ι f)) ≈
        max (pow s t) (sup fun i => mul (pow s t) (mul (pow s (f i)) s)) := by
      refine Equiv.trans (mul_congr_right (pow_mk s ι f) _) (Equiv.trans (mul_max _ _ _) ?_)
      exact max_congr (OTree.mul_one _) (mul_sup _ _)
    exact Equiv.trans e₁ (Equiv.trans
      (max_congr (Equiv.refl _) (sup_congr fun i => OTree.mul_assoc _ _ _)) e₂.symm)

/-- snu-sf: `OrdArith.lt_expn_r`. -/
protected theorem pow_lt_pow_right {s : OTree.{u}} (hs : succ zero < s) {t t' : OTree.{u}}
    (h : t < t') : pow s t < pow s t' :=
  OTree.lt_of_lt_of_le (OTree.lt_mul_of_one_lt_right (OTree.zero_lt_pow s t) hs)
    (next_orec_le_orec (mul_right_mono s) h)

/-- snu-sf: `OrdArith.expn_1_l`. -/
protected theorem one_pow : ∀ t : OTree.{u}, pow (succ zero) t ≈ succ zero
  | mk ι f =>
    ⟨OTree.le_trans (pow_mk _ ι f).le (max_le OTree.le_rfl (sup_le fun i =>
        OTree.le_trans (OTree.mul_one _).le (OTree.one_pow (f i)).le)),
      base_le_orec _⟩

/-- snu-sf: `OrdArith.le_expn_l`. -/
protected theorem pow_le_pow_left {s s' : OTree.{u}} (h : s ≤ s') (t : OTree.{u}) :
    pow s t ≤ pow s' t :=
  orec_mono OTree.le_rfl (fun h' => OTree.mul_le_mul h' h) t

/-- snu-sf: `OrdArith.eq_expn_l`. -/
theorem pow_congr_left {s s' : OTree.{u}} (h : s ≈ s') (t : OTree.{u}) : pow s t ≈ pow s' t :=
  ⟨OTree.pow_le_pow_left h.le t, OTree.pow_le_pow_left h.ge t⟩

/-- snu-sf: `OrdArith.expn_le_proper`. -/
protected theorem pow_le_pow {s s' t t' : OTree.{u}} (hs : s ≤ s') (ht : t ≤ t') :
    pow s t ≤ pow s' t' :=
  OTree.le_trans (OTree.pow_le_pow_left hs t) (OTree.pow_le_pow_right s' ht)

/-- snu-sf: `OrdArith.expn_eq_proper`. -/
theorem pow_congr {s s' t t' : OTree.{u}} (hs : s ≈ s') (ht : t ≈ t') : pow s t ≈ pow s' t' :=
  ⟨OTree.pow_le_pow hs.le ht.le, OTree.pow_le_pow hs.ge ht.ge⟩

/-- snu-sf: `OrdArith.expn_mult`. -/
protected theorem pow_mul {s : OTree.{u}} (hs : zero < s) (t : OTree.{u}) :
    ∀ t' : OTree.{u}, pow s (mul t t') ≈ pow (pow s t) t'
  | mk ι f => by
    have ih := fun i => OTree.pow_mul hs t (f i)
    refine Equiv.trans (pow_congr_right s (mul_mk t ι f))
      (Equiv.trans (pow_sup s _) (Equiv.trans ?_ (pow_mk _ ι f).symm))
    exact max_congr (Equiv.refl _) (sup_congr fun i =>
      Equiv.trans (OTree.pow_add hs _ t) (mul_congr_left (ih i) _))

/-! ## Natural numbers

snu-sf `OrdArith.le_from_nat` and `OrdArith.lt_from_nat` are `ofNat_le_ofNat_iff` and
`ofNat_lt_ofNat_iff` (file `Ordinals.Tree.Constructions`). -/

/-- snu-sf: `OrdArith.add_from_nat`. -/
theorem ofNat_add (m : Nat) : ∀ n : Nat, ofNat.{u} (m + n) ≈ add (ofNat m) (ofNat n)
  | 0 => (OTree.add_zero _).symm
  | n + 1 => Equiv.trans (succ_congr (ofNat_add m n)) (add_succ _ _).symm

/-- snu-sf: `OrdArith.mult_from_nat`. -/
theorem ofNat_mul (m : Nat) : ∀ n : Nat, ofNat.{u} (m * n) ≈ mul (ofNat m) (ofNat n)
  | 0 => (OTree.mul_zero _).symm
  | n + 1 => Equiv.trans (ofNat_add (m * n) m)
      (Equiv.trans (add_congr_left (ofNat_mul m n) _) (mul_succ _ _).symm)

/-- snu-sf: `OrdArith.expn_from_nat`. -/
theorem ofNat_pow {m : Nat} (hm : 0 < m) : ∀ n : Nat, ofNat.{u} (m ^ n) ≈ pow (ofNat m) (ofNat n)
  | 0 => (OTree.pow_zero _).symm
  | n + 1 => Equiv.trans (ofNat_mul (m ^ n) m)
      (Equiv.trans (mul_congr_left (ofNat_pow hm n) _)
        (OTree.pow_succ (ofNat_lt_ofNat_iff.mpr hm) _).symm)

end OTree

end Ordinals
