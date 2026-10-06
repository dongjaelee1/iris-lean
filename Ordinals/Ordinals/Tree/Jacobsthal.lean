/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Ordinals.Tree.HessenbergArith

/-!
# The Jacobsthal product and power of trees

The Jacobsthal product and power are the analogues of the standard product and power, with the
natural sum `nadd` in place of the standard sum `add`. They use transfinite recursion (`orec`) on
the second argument:

- `jmul s t := orec zero (nadd s) t`: start at `zero` and add `s` on the left with the natural
  sum (snu-sf: `Jacobsthal.mult`).
- `jpow s t := orec (succ zero) (fun r => jmul r s) t`: start at `1` and multiply by `s` with the
  Jacobsthal product (snu-sf: `Jacobsthal.expn`).

The Jacobsthal product is at least the standard product (`mul_le_jmul`), and the Jacobsthal
power is at least the standard power (`pow_le_jpow`). Each operation has monotonicity lemmas, a
congruence lemma for `≈`, and the equations for `zero`, `succ`, `sup`, `mk` and `max`. The
Jacobsthal product distributes over the natural sum on the left (`jmul_nadd`) and is associative
(`jmul_assoc`). The Jacobsthal power changes a standard sum into a Jacobsthal product
(`jpow_add`) and a standard product into a power of a power (`jpow_mul`).

This file follows snu-sf/Ordinal (`src/Hessenberg.v`, module `Jacobsthal`, sections `MULT`,
`EXPN`, `BASE`, `POSITIVE`; and `src/ClassicalHessenberg.v`, module `ClassicJacobsthal`). The
names of the Rocq lemmas are in the docstrings. The lemmas take only the hypotheses that their
proofs need.

## Implementation notes

snu-sf proves `ClassicJacobsthal.mult_dist` (`jmul_nadd` here) with classical logic: a case
analysis on `o0 == 0` and on "successor or limit" for the two other arguments. Here the proof is
constructive: an induction on two trees (`induction₂`) with the characterization of `<` below
a natural sum (`lt_nadd_iff`) and below a Jacobsthal product (`lt_jmul_iff`). Thus
`jmul_assoc`, `jpow_add` and `jpow_mul` are also constructive, and the results of
`ClassicalHessenberg.v` are in this file. The results of this file use no axioms.
-/

@[expose] public section

namespace Ordinals

universe u

namespace OTree

/-! ## Jacobsthal product -/

/-- The Jacobsthal product: `jmul s t` adds `s` on the left with the natural sum along `t`, from
`zero` (snu-sf: `Jacobsthal.mult`). -/
def jmul (s : OTree.{u}) : OTree.{u} → OTree.{u} :=
  orec zero (nadd s)

/-- snu-sf: `Jacobsthal.mult_O_r`. -/
theorem jmul_zero (s : OTree.{u}) : jmul s zero ≈ zero :=
  orec_zero

/-- snu-sf: `Jacobsthal.mult_S`. -/
theorem jmul_succ (s t : OTree.{u}) : jmul s (succ t) ≈ nadd s (jmul s t) :=
  orec_succ (le_nadd_self s) t

/-- snu-sf: `Jacobsthal.mult_join`. -/
theorem jmul_sup (s : OTree.{u}) {ι : Type u} (f : ι → OTree.{u}) :
    jmul s (sup f) ≈ sup fun i => jmul s (f i) :=
  Equiv.trans (orec_sup (nadd_le_nadd_left · s) f) (max_equiv_of_le (zero_le _))

/-- snu-sf: `Jacobsthal.mult_build`. -/
theorem jmul_mk (s : OTree.{u}) (ι : Type u) (f : ι → OTree.{u}) :
    jmul s (mk ι f) ≈ sup fun i => nadd s (jmul s (f i)) :=
  Equiv.trans (orec_mk ι f) (max_equiv_of_le (zero_le _))

/-- snu-sf: `Jacobsthal.mult_union`. -/
theorem jmul_max (r s t : OTree.{u}) : jmul r (max s t) ≈ max (jmul r s) (jmul r t) :=
  orec_max (nadd_le_nadd_left · r) s t

/-- snu-sf: `Jacobsthal.le_mult_r`. -/
theorem jmul_le_jmul_left {s t : OTree.{u}} (h : s ≤ t) (r : OTree.{u}) :
    jmul r s ≤ jmul r t :=
  orec_le_orec (nadd_le_nadd_left · r) h

/-- snu-sf: `Jacobsthal.eq_mult_r`. -/
theorem jmul_congr_right {s t : OTree.{u}} (h : s ≈ t) (r : OTree.{u}) : jmul r s ≈ jmul r t :=
  orec_congr (nadd_le_nadd_left · r) h

/-- snu-sf: `Jacobsthal.le_mult_l`. -/
theorem jmul_le_jmul_right {s t : OTree.{u}} (h : s ≤ t) (r : OTree.{u}) :
    jmul s r ≤ jmul t r :=
  orec_mono OTree.le_rfl (fun h' => nadd_mono h h') r

/-- snu-sf: `Jacobsthal.eq_mult_l`. -/
theorem jmul_congr_left {s t : OTree.{u}} (h : s ≈ t) (r : OTree.{u}) : jmul s r ≈ jmul t r :=
  ⟨jmul_le_jmul_right h.le r, jmul_le_jmul_right h.ge r⟩

/-- snu-sf: `Jacobsthal.mult_le_proper`. -/
theorem jmul_le_jmul {s s' t t' : OTree.{u}} (hs : s ≤ s') (ht : t ≤ t') :
    jmul s t ≤ jmul s' t' :=
  OTree.le_trans (jmul_le_jmul_right hs t) (jmul_le_jmul_left ht s')

/-- `jmul` respects `≈` (snu-sf: `Jacobsthal.mult_eq_proper`). -/
theorem jmul_congr {s s' t t' : OTree.{u}} (hs : s ≈ s') (ht : t ≈ t') :
    jmul s t ≈ jmul s' t' :=
  ⟨jmul_le_jmul hs.le ht.le, jmul_le_jmul hs.ge ht.ge⟩

/-- The step below a larger tree (snu-sf: `Ord.lt_rec` for `jmul`). -/
theorem nadd_jmul_le_jmul {r s t : OTree.{u}} (h : s < t) : nadd r (jmul r s) ≤ jmul r t :=
  next_orec_le_orec (nadd_le_nadd_left · r) h

/-- An upper bound of `jmul` (snu-sf: `Ord.orec_build_supremum` for `jmul`). -/
theorem jmul_le {r t x : OTree.{u}} (h : ∀ t', t' < t → nadd r (jmul r t') ≤ x) :
    jmul r t ≤ x :=
  orec_le (zero_le x) h

/-- The trees below a Jacobsthal product. -/
theorem lt_jmul_iff {x r t : OTree.{u}} :
    x < jmul r t ↔ ∃ t', t' < t ∧ x < nadd r (jmul r t') := by
  constructor
  · intro h
    cases t with
    | mk ι f =>
      obtain ⟨i, hi⟩ := lt_sup_iff.mp ((lt_congr (Equiv.refl x) (jmul_mk r ι f)).mp h)
      exact ⟨f i, child_lt (mk ι f) i, hi⟩
  · exact fun ⟨_, ht', hx⟩ => OTree.lt_of_lt_of_le hx (nadd_jmul_le_jmul ht')

/-- snu-sf: `Jacobsthal.lt_mult_r`. -/
theorem jmul_lt_jmul_of_pos_left {r s t : OTree.{u}} (h : s < t) (hr : zero < r) :
    jmul r s < jmul r t :=
  OTree.lt_of_lt_of_le (lt_nadd_of_pos_left _ hr) (nadd_jmul_le_jmul h)

/-- The standard product is at most the Jacobsthal product
(snu-sf: `Jacobsthal.arith_mult_larger`). -/
theorem mul_le_jmul (s t : OTree.{u}) : mul s t ≤ jmul s t :=
  orec_mono OTree.le_rfl (fun h => OTree.le_trans (add_le_nadd _ s)
    (OTree.le_trans (nadd_comm _ s).le (nadd_le_nadd_left h s))) t

/-- snu-sf: `Jacobsthal.mult_O_l`. -/
theorem zero_jmul : ∀ s : OTree.{u}, jmul zero s ≈ zero
  | mk ι f =>
    ⟨OTree.le_trans (jmul_mk zero ι f).le
        (sup_le fun i => OTree.le_trans (zero_nadd _).le (zero_jmul (f i)).le),
      zero_le _⟩

/-- snu-sf: `Jacobsthal.mult_1_r`. -/
theorem jmul_one (s : OTree.{u}) : jmul s (succ zero) ≈ s :=
  Equiv.trans (jmul_succ s zero) (Equiv.trans (nadd_congr_left (jmul_zero s) s) (nadd_zero s))

/-- snu-sf: `Jacobsthal.mult_1_l`. -/
theorem one_jmul (s : OTree.{u}) : jmul (succ zero) s ≈ s := by
  refine Equiv.trans ⟨?_, ?_⟩ (orec_zero_succ s)
  · exact orec_mono OTree.le_rfl (fun h => OTree.le_trans (succ_nadd _ _).le
      (succ_le_succ (OTree.le_trans (zero_nadd _).le h))) s
  · exact orec_mono OTree.le_rfl (fun h => OTree.le_trans
      (succ_le_succ (OTree.le_trans h (zero_nadd _).ge)) (succ_nadd _ _).ge) s

/-- A Jacobsthal product with a positive right factor is at least the left factor
(snu-sf: the local `expn_gen_le` of section `POSITIVE`). -/
theorem le_jmul_of_pos_right (s : OTree.{u}) {t : OTree.{u}} (h : zero < t) : s ≤ jmul s t :=
  OTree.le_trans (jmul_one s).ge (jmul_le_jmul_left (succ_le_of_lt h) s)

/-- A Jacobsthal product with a positive left factor is at least the right factor. -/
theorem le_jmul_of_pos_left {s : OTree.{u}} (t : OTree.{u}) (h : zero < s) : t ≤ jmul s t :=
  OTree.le_trans (one_jmul t).ge (jmul_le_jmul_right (succ_le_of_lt h) t)

/-- snu-sf: `Jacobsthal.mult_from_nat`. -/
theorem ofNat_jmul (m : Nat) : ∀ n : Nat, ofNat.{u} (m * n) ≈ jmul (ofNat m) (ofNat n)
  | 0 => (jmul_zero _).symm
  | n + 1 => Equiv.trans (nadd_ofNat (m * n) m).symm
      (Equiv.trans (nadd_comm _ _)
        (Equiv.trans (nadd_congr_left (ofNat_jmul m n) _) (jmul_succ _ _).symm))

/-! ## Distributivity and associativity -/

/-- The Jacobsthal product distributes over the natural sum on the left
(snu-sf: `ClassicJacobsthal.mult_dist`). snu-sf uses classical logic. This proof is
constructive. -/
theorem jmul_nadd (r s t : OTree.{u}) : jmul r (nadd s t) ≈ nadd (jmul r s) (jmul r t) := by
  induction s, t using induction₂ with
  | _ s t ihs iht =>
    constructor
    · refine jmul_le fun x hx => ?_
      rcases lt_nadd_iff.mp hx with ⟨s', hs', hx'⟩ | ⟨t', ht', hx'⟩
      · exact OTree.le_trans
          (nadd_le_nadd_left (OTree.le_trans (jmul_le_jmul_left hx' r) (ihs s' hs').le) r)
          (OTree.le_trans (nadd_assoc _ _ _).ge (nadd_le_nadd_right (nadd_jmul_le_jmul hs') _))
      · exact OTree.le_trans
          (nadd_le_nadd_left (OTree.le_trans (jmul_le_jmul_left hx' r) (iht t' ht').le) r)
          (OTree.le_trans (nadd_left_comm _ _ _).le (nadd_le_nadd_left (nadd_jmul_le_jmul ht') _))
    · refine nadd_le_of_forall_lt (fun y hy => ?_) (fun y hy => ?_)
      · obtain ⟨s', hs', hy'⟩ := lt_jmul_iff.mp hy
        exact OTree.lt_of_lt_of_le (nadd_lt_nadd_right hy' _)
          (OTree.le_trans (nadd_assoc _ _ _).le (OTree.le_trans
            (nadd_le_nadd_left (ihs s' hs').ge r) (nadd_jmul_le_jmul (nadd_lt_nadd_right hs' t))))
      · obtain ⟨t', ht', hy'⟩ := lt_jmul_iff.mp hy
        exact OTree.lt_of_lt_of_le (nadd_lt_nadd_left hy' _)
          (OTree.le_trans (nadd_left_comm _ _ _).le (OTree.le_trans
            (nadd_le_nadd_left (iht t' ht').ge r) (nadd_jmul_le_jmul (nadd_lt_nadd_left ht' s))))

/-- snu-sf: `ClassicJacobsthal.mult_assoc`. -/
theorem jmul_assoc (r s : OTree.{u}) : ∀ t : OTree.{u}, jmul (jmul r s) t ≈ jmul r (jmul s t)
  | mk ι f => by
    have ih := fun i => jmul_assoc r s (f i)
    refine Equiv.trans (jmul_mk _ ι f) (Equiv.trans ?_ (jmul_congr_right (jmul_mk s ι f) r).symm)
    refine Equiv.trans ?_ (jmul_sup r _).symm
    exact sup_congr fun i => Equiv.trans (nadd_congr_left (ih i) _) (jmul_nadd r _ _).symm

/-! ## Jacobsthal power -/

/-- The Jacobsthal power: `jpow s t` multiplies by `s` on the right with the Jacobsthal product
along `t`, from `succ zero` (snu-sf: `Jacobsthal.expn`). -/
def jpow (s : OTree.{u}) : OTree.{u} → OTree.{u} :=
  orec (succ zero) fun r => jmul r s

/-- The standard power is at most the Jacobsthal power
(snu-sf: `Jacobsthal.arith_expn_larger`). -/
theorem pow_le_jpow (s t : OTree.{u}) : pow s t ≤ jpow s t :=
  orec_mono OTree.le_rfl (fun h => OTree.le_trans (mul_le_jmul _ s) (jmul_le_jmul_right h s)) t

/-- snu-sf: `Jacobsthal.expn_O`. -/
theorem jpow_zero (s : OTree.{u}) : jpow s zero ≈ succ zero :=
  orec_zero

/-- snu-sf: `Jacobsthal.expn_pos`. -/
theorem zero_lt_jpow (s t : OTree.{u}) : zero < jpow s t :=
  OTree.lt_of_lt_of_le (zero_lt_succ zero) (base_le_orec t)

/-- snu-sf: `Jacobsthal.expn_S`. -/
theorem jpow_succ {s : OTree.{u}} (hs : zero < s) (t : OTree.{u}) :
    jpow s (succ t) ≈ jmul (jpow s t) s :=
  orec_succ (fun r => le_jmul_of_pos_right r hs) t

/-- snu-sf: `Jacobsthal.le_expn_r`. The hypothesis `zero < s` of snu-sf is not necessary. -/
theorem jpow_le_jpow_right (s : OTree.{u}) {t t' : OTree.{u}} (h : t ≤ t') :
    jpow s t ≤ jpow s t' :=
  orec_le_orec (jmul_le_jmul_right · s) h

/-- snu-sf: `Jacobsthal.eq_expn_r`. The hypothesis `zero < s` of snu-sf is not necessary. -/
theorem jpow_congr_right (s : OTree.{u}) {t t' : OTree.{u}} (h : t ≈ t') :
    jpow s t ≈ jpow s t' :=
  orec_congr (jmul_le_jmul_right · s) h

/-- snu-sf: `Jacobsthal.expn_join`. The hypothesis `zero < s` of snu-sf is not necessary. -/
theorem jpow_sup (s : OTree.{u}) {ι : Type u} (f : ι → OTree.{u}) :
    jpow s (sup f) ≈ max (succ zero) (sup fun i => jpow s (f i)) :=
  orec_sup (jmul_le_jmul_right · s) f

/-- snu-sf: `Jacobsthal.expn_join_inhabited`. The hypothesis `zero < s` of snu-sf is not
necessary. -/
theorem jpow_sup_of_nonempty (s : OTree.{u}) {ι : Type u} [Nonempty ι] (f : ι → OTree.{u}) :
    jpow s (sup f) ≈ sup fun i => jpow s (f i) :=
  orec_sup_of_nonempty (jmul_le_jmul_right · s) f

/-- snu-sf: `Jacobsthal.expn_build`. -/
theorem jpow_mk (s : OTree.{u}) (ι : Type u) (f : ι → OTree.{u}) :
    jpow s (mk ι f) ≈ max (succ zero) (sup fun i => jmul (jpow s (f i)) s) :=
  orec_mk ι f

/-- snu-sf: `Jacobsthal.expn_union`. The hypothesis `zero < s` of snu-sf is not necessary. -/
theorem jpow_max (r s t : OTree.{u}) : jpow r (max s t) ≈ max (jpow r s) (jpow r t) :=
  orec_max (jmul_le_jmul_right · r) s t

/-- With this definition, `jpow zero t` is `succ zero` for each `t`. -/
theorem jpow_zero_left (t : OTree.{u}) : jpow zero t ≈ succ zero := by
  cases t with
  | mk ι f =>
    exact ⟨OTree.le_trans (jpow_mk zero ι f).le (max_le OTree.le_rfl
        (sup_le fun _ => OTree.le_trans (jmul_zero _).le (zero_le _))),
      base_le_orec _⟩

/-- snu-sf: `Jacobsthal.expn_1_r`. -/
theorem jpow_one {s : OTree.{u}} (hs : zero < s) : jpow s (succ zero) ≈ s :=
  Equiv.trans (jpow_succ hs zero) (Equiv.trans (jmul_congr_left (jpow_zero s) s) (one_jmul s))

/-- snu-sf: `Jacobsthal.lt_expn_r`. -/
theorem jpow_lt_jpow_right {s : OTree.{u}} (hs : succ zero < s) {t t' : OTree.{u}}
    (h : t < t') : jpow s t < jpow s t' :=
  OTree.lt_of_le_of_lt (jmul_one _).ge (OTree.lt_of_lt_of_le
    (jmul_lt_jmul_of_pos_left hs (zero_lt_jpow s t))
    (next_orec_le_orec (jmul_le_jmul_right · s) h))

/-- snu-sf: `Jacobsthal.expn_1_l`. -/
theorem one_jpow : ∀ t : OTree.{u}, jpow (succ zero) t ≈ succ zero
  | mk ι f =>
    ⟨OTree.le_trans (jpow_mk _ ι f).le (max_le OTree.le_rfl (sup_le fun i =>
        OTree.le_trans (jmul_one _).le (one_jpow (f i)).le)),
      base_le_orec _⟩

/-- snu-sf: `Jacobsthal.le_expn_l`. -/
theorem jpow_le_jpow_left {s s' : OTree.{u}} (h : s ≤ s') (t : OTree.{u}) :
    jpow s t ≤ jpow s' t :=
  orec_mono OTree.le_rfl (fun h' => jmul_le_jmul h' h) t

/-- snu-sf: `Jacobsthal.eq_expn_l`. -/
theorem jpow_congr_left {s s' : OTree.{u}} (h : s ≈ s') (t : OTree.{u}) :
    jpow s t ≈ jpow s' t :=
  ⟨jpow_le_jpow_left h.le t, jpow_le_jpow_left h.ge t⟩

/-- snu-sf: `Jacobsthal.expn_le_proper`. -/
theorem jpow_le_jpow {s s' t t' : OTree.{u}} (hs : s ≤ s') (ht : t ≤ t') :
    jpow s t ≤ jpow s' t' :=
  OTree.le_trans (jpow_le_jpow_left hs t) (jpow_le_jpow_right s' ht)

/-- `jpow` respects `≈` (snu-sf: `Jacobsthal.expn_eq_proper`). -/
theorem jpow_congr {s s' t t' : OTree.{u}} (hs : s ≈ s') (ht : t ≈ t') :
    jpow s t ≈ jpow s' t' :=
  ⟨jpow_le_jpow hs.le ht.le, jpow_le_jpow hs.ge ht.ge⟩

/-- snu-sf: `Jacobsthal.expn_from_nat`. -/
theorem ofNat_jpow {m : Nat} (hm : 0 < m) :
    ∀ n : Nat, ofNat.{u} (m ^ n) ≈ jpow (ofNat m) (ofNat n)
  | 0 => (jpow_zero _).symm
  | n + 1 => Equiv.trans (ofNat_jmul (m ^ n) m)
      (Equiv.trans (jmul_congr_left (ofNat_jpow hm n) _)
        (jpow_succ (ofNat_lt_ofNat_iff.mpr hm) _).symm)

/-! ## Power of a sum and of a product -/

/-- The Jacobsthal power of a standard sum is the Jacobsthal product of the powers
(snu-sf: `ClassicJacobsthal.expn_add`). -/
theorem jpow_add {s : OTree.{u}} (hs : zero < s) (t : OTree.{u}) :
    ∀ t' : OTree.{u}, jpow s (add t t') ≈ jmul (jpow s t) (jpow s t')
  | mk ι f => by
    have ih := fun i => jpow_add hs t (f i)
    have h₁ : succ zero ≤ jpow s t := succ_le_of_lt (zero_lt_jpow s t)
    -- Left side.
    have e₁ : jpow s (add t (mk ι f)) ≈
        max (jpow s t) (sup fun i => jmul (jmul (jpow s t) (jpow s (f i))) s) := by
      refine Equiv.trans (jpow_congr_right s (add_mk t ι f)) (Equiv.trans (jpow_max s _ _) ?_)
      refine Equiv.trans (max_congr (Equiv.refl _) (jpow_sup s _)) ?_
      refine Equiv.trans (max_assoc _ _ _).symm (max_congr ?_ ?_)
      · exact Equiv.trans (max_comm _ _) (max_equiv_of_le h₁)
      · exact sup_congr fun i => Equiv.trans (jpow_succ hs _) (jmul_congr_left (ih i) s)
    -- Right side.
    have e₂ : jmul (jpow s t) (jpow s (mk ι f)) ≈
        max (jpow s t) (sup fun i => jmul (jpow s t) (jmul (jpow s (f i)) s)) := by
      refine Equiv.trans (jmul_congr_right (jpow_mk s ι f) _) (Equiv.trans (jmul_max _ _ _) ?_)
      exact max_congr (jmul_one _) (jmul_sup _ _)
    exact Equiv.trans e₁ (Equiv.trans
      (max_congr (Equiv.refl _) (sup_congr fun i => jmul_assoc _ _ _)) e₂.symm)

/-- The Jacobsthal power of a standard product is a power of a power
(snu-sf: `ClassicJacobsthal.expn_mult`). -/
theorem jpow_mul {s : OTree.{u}} (hs : zero < s) (t : OTree.{u}) :
    ∀ t' : OTree.{u}, jpow s (mul t t') ≈ jpow (jpow s t) t'
  | mk ι f => by
    have ih := fun i => jpow_mul hs t (f i)
    refine Equiv.trans (jpow_congr_right s (mul_mk t ι f))
      (Equiv.trans (jpow_sup s _) (Equiv.trans ?_ (jpow_mk _ ι f).symm))
    exact max_congr (Equiv.refl _) (sup_congr fun i =>
      Equiv.trans (jpow_add hs _ t) (jmul_congr_left (ih i) _))

end OTree

end Ordinals
