/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Ordinals.Ordinal.Constructions

/-!
# Ordinals in different universes

Lean has no cumulative universes, so `Ordinal.{u}` is not a part of `Ordinal.{u+1}`. `lift`
moves an ordinal to a larger universe, and `univ.{u} : Ordinal.{u+1}` is the order type of
`Ordinal.{u}`.
-/

@[expose] public section

namespace Ordinals

universe u v w

namespace Ordinal

/-! ## The lift -/

/-- The same ordinal in the universe `max u v`. -/
def lift : Ordinal.{u} → Ordinal.{max u v} :=
  Quotient.lift (fun t => mk (OTree.lift.{u, v} t)) fun _ _ h => sound (OTree.lift_congr h)

@[simp] theorem lift_mk (t : OTree.{u}) : lift.{u, v} (mk t) = mk (OTree.lift.{u, v} t) :=
  rfl

@[simp] theorem lift_le_lift_iff {a b : Ordinal.{u}} : lift.{u, v} a ≤ lift.{u, v} b ↔ a ≤ b :=
  Ordinal.inductionOn₂ a b fun _ _ => OTree.lift_le_lift_iff

@[simp] theorem lift_lt_lift_iff {a b : Ordinal.{u}} : lift.{u, v} a < lift.{u, v} b ↔ a < b :=
  Ordinal.inductionOn₂ a b fun _ _ => OTree.lift_lt_lift_iff

@[simp] theorem lift_inj {a b : Ordinal.{u}} : lift.{u, v} a = lift.{u, v} b ↔ a = b :=
  ⟨fun h => Ordinal.le_antisymm (lift_le_lift_iff.mp (Ordinal.le_of_eq h))
      (lift_le_lift_iff.mp (Ordinal.le_of_eq h.symm)),
   fun h => h ▸ rfl⟩

@[simp] theorem lift_zero : lift.{u, v} (0 : Ordinal.{u}) = 0 :=
  sound OTree.lift_zero

@[simp] theorem lift_succ (a : Ordinal.{u}) : lift.{u, v} (succ a) = succ (lift.{u, v} a) :=
  Ordinal.inductionOn a fun t => sound (OTree.lift_succ t)

@[simp] theorem lift_ofNat (n : Nat) : lift.{u, v} (ofNat n) = ofNat n := by
  induction n with
  | zero => exact lift_zero
  | succ n ih => rw [ofNat_succ, lift_succ, ih, ofNat_succ]

@[simp] theorem lift_max (a b : Ordinal.{u}) : lift.{u, v} (max a b) = max (lift a) (lift b) := by
  rcases Ordinal.le_total a b with h | h
  · rw [Ordinal.max_eq_right h, Ordinal.max_eq_right (lift_le_lift_iff.mpr h)]
  · rw [Ordinal.max_eq_left h, Ordinal.max_eq_left (lift_le_lift_iff.mpr h)]

/-- Each ordinal at most a lifted ordinal is a lifted ordinal. -/
theorem exists_eq_lift_of_le {a : Ordinal.{max u v}} {b : Ordinal.{u}} (h : a ≤ lift.{u, v} b) :
    ∃ c, a = lift.{u, v} c := by
  induction b using Ordinal.ind with
  | _ t =>
    induction t generalizing a with
    | mk κ g ih =>
      by_cases hj : ∃ j, a ≤ lift.{u, v} (mk (g j))
      · obtain ⟨j, hj⟩ := hj
        exact ih j hj
      · refine ⟨mk (OTree.mk κ g), Ordinal.le_antisymm h ?_⟩
        induction a using Ordinal.ind with
        | _ s =>
          show OTree.mk (ULift.{v} κ) (fun j => OTree.lift.{u, v} (g j.down)) ≤ s
          exact OTree.mk_le.mpr fun j => Ordinal.not_le.mp fun h' => hj ⟨j.down, h'⟩

/-- The image of the lift is an initial segment. -/
theorem lt_lift_iff {a : Ordinal.{max u v}} {b : Ordinal.{u}} :
    a < lift.{u, v} b ↔ ∃ c, c < b ∧ a = lift.{u, v} c := by
  constructor
  · intro h
    obtain ⟨c, rfl⟩ := exists_eq_lift_of_le (Ordinal.le_of_lt h)
    exact ⟨c, lift_lt_lift_iff.mp h, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact lift_lt_lift_iff.mpr hc

theorem le_lift_iff {a : Ordinal.{max u v}} {b : Ordinal.{u}} :
    a ≤ lift.{u, v} b ↔ ∃ c, c ≤ b ∧ a = lift.{u, v} c := by
  constructor
  · intro h
    obtain ⟨c, rfl⟩ := exists_eq_lift_of_le h
    exact ⟨c, lift_le_lift_iff.mp h, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact lift_le_lift_iff.mpr hc

theorem lift_sup {ι : Type u} (f : ι → Ordinal.{u}) :
    lift.{u, v} (sup f) = sup fun i : ULift.{v} ι => lift.{u, v} (f i.down) := by
  refine Ordinal.le_antisymm ?_ (sup_le fun i => lift_le_lift_iff.mpr (le_sup f i.down))
  refine le_of_forall_lt fun c hc => ?_
  obtain ⟨d, hd, rfl⟩ := lt_lift_iff.mp hc
  obtain ⟨i, hi⟩ := lt_sup_iff.mp hd
  exact lt_sup_iff.mpr ⟨⟨i⟩, lift_lt_lift_iff.mpr hi⟩

theorem lift_ssup {ι : Type u} (f : ι → Ordinal.{u}) :
    lift.{u, v} (ssup f) = ssup fun i : ULift.{v} ι => lift.{u, v} (f i.down) := by
  rw [ssup_eq_sup_succ, ssup_eq_sup_succ, lift_sup]
  simp only [lift_succ]

theorem lift_omega : lift.{u, v} (ω : Ordinal.{u}) = ω := by
  refine Ordinal.le_antisymm ?_ (omega_le fun n => ?_)
  · refine le_of_forall_lt fun c hc => ?_
    obtain ⟨d, hd, rfl⟩ := lt_lift_iff.mp hc
    obtain ⟨n, rfl⟩ := lt_omega_iff.mp hd
    rw [lift_ofNat]
    exact ofNat_lt_omega n
  · rw [← lift_ofNat.{u, v} n]
    exact lift_le_lift_iff.mpr (Ordinal.le_of_lt (ofNat_lt_omega n))

@[simp] theorem lift_lift (a : Ordinal.{u}) :
    lift.{max u v, w} (lift.{u, v} a) = lift.{u, max v w} a := by
  induction a using Ordinal.induction with
  | _ a ih =>
    refine Ordinal.ext fun c => ⟨fun hc => ?_, fun hc => ?_⟩
    · obtain ⟨d, hd, rfl⟩ := lt_lift_iff.mp hc
      obtain ⟨e, he, rfl⟩ := lt_lift_iff.mp hd
      rw [ih e he]
      exact lift_lt_lift_iff.mpr he
    · obtain ⟨d, hd, rfl⟩ := lt_lift_iff.mp hc
      rw [← ih d hd]
      exact lift_lt_lift_iff.mpr (lift_lt_lift_iff.mpr hd)

@[simp] theorem lift_id (a : Ordinal.{u}) : lift.{u, u} a = a := by
  induction a using Ordinal.induction with
  | _ a ih =>
    refine Ordinal.ext fun c => ⟨fun hc => ?_, fun hc => ?_⟩
    · obtain ⟨d, hd, rfl⟩ := lt_lift_iff.mp hc
      rw [ih d hd]
      exact hd
    · rw [← ih c hc]
      exact lift_lt_lift_iff.mpr hc

/-! ## An ordinal above all ordinals of a universe -/

/-- The order type of `Ordinal.{u}`: the strict supremum of all its lifted ordinals. -/
noncomputable def univ : Ordinal.{u + 1} :=
  ssup fun a : Ordinal.{u} => lift.{u, u + 1} a

theorem lift_lt_univ (a : Ordinal.{u}) : lift.{u, u + 1} a < univ.{u} :=
  lt_ssup (fun a : Ordinal.{u} => lift.{u, u + 1} a) a

theorem lt_univ_iff {a : Ordinal.{u + 1}} : a < univ.{u} ↔ ∃ c : Ordinal.{u}, a = lift.{u, u + 1} c := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := lt_ssup_iff.mp h
    obtain ⟨d, -, rfl⟩ := le_lift_iff.mp hc
    exact ⟨d, rfl⟩
  · rintro ⟨c, rfl⟩
    exact lift_lt_univ c

theorem univ_isLimit : IsLimit univ.{u} := by
  refine ⟨fun h => ?_, fun b hb => ?_⟩
  · have := lift_lt_univ (0 : Ordinal.{u})
    rw [h] at this
    exact Ordinal.not_lt_zero _ this
  · obtain ⟨c, rfl⟩ := lt_univ_iff.mp hb
    rw [← lift_succ]
    exact lift_lt_univ (succ c)

end Ordinal

end Ordinals
