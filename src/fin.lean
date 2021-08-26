import data.fin
import data.equiv.fin

namespace fin

@[elab_as_eliminator]
def reverse_induction {n : ℕ}
  {C : fin (n + 1) → Sort*}
  (h0 : C (fin.last n))
  (hs : ∀ i : fin n, C i.succ → C i.cast_succ) :
  Π (i : fin (n + 1)), C i
| i :=
if hi : i = fin.last n
then _root_.cast (by rw hi) h0
else
  let j : fin n :=  ⟨i, lt_of_le_of_ne (nat.le_of_lt_succ i.2) (λ h, hi (fin.ext h))⟩ in
  have wf : n + 1 - j.succ < n + 1 - i, begin
    cases i,
    rw [nat.sub_lt_sub_left_iff];
    simp [*, nat.succ_le_iff],
  end,
  have hi : i = fin.cast_succ j, from fin.ext rfl,
_root_.cast (by rw hi) (hs _ (reverse_induction j.succ))
using_well_founded { rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ i : fin (n+1), n + 1 - i)⟩],
  dec_tac := `[assumption] }

lemma reverse_induction_last {n : ℕ}
  {C : fin (n + 1) → Sort*}
  (h0 : C (fin.last n))
  (hs : ∀ i : fin n, C i.succ → C i.cast_succ) :
  (reverse_induction h0 hs (fin.last n) : C (fin.last n)) = h0 :=
by rw [reverse_induction]; simp

lemma reverse_induction_cast_succ {n : ℕ}
  {C : fin (n + 1) → Sort*}
  (h0 : C (fin.last n))
  (hs : ∀ i : fin n, C i.succ → C i.cast_succ) (i : fin n):
  (reverse_induction h0 hs i.cast_succ : C i.cast_succ) =
    hs i (reverse_induction h0 hs i.succ) :=
begin
  rw [reverse_induction, dif_neg (ne_of_lt (fin.cast_succ_lt_last i))],
  cases i,
  refl
end

@[elab_as_eliminator, elab_strategy]
def last_cases {n : ℕ} {C : fin (n + 1) → Sort*}
  (hlast : C (fin.last n)) (hcast : (Π (i : fin n), C i.cast_succ)) (i : fin (n + 1)) : C i :=
reverse_induction hlast (λ i _, hcast i) i

@[simp] lemma last_cases_last {n : ℕ} {C : fin (n + 1) → Sort*}
  (hlast : C (fin.last n)) (hcast : (Π (i : fin n), C i.cast_succ)) :
  (fin.last_cases hlast hcast (fin.last n): C (fin.last n)) = hlast :=
reverse_induction_last _ _

@[simp] lemma last_cases_cast_succ {n : ℕ} {C : fin (n + 1) → Sort*}
  (hlast : C (fin.last n)) (hcast : (Π (i : fin n), C i.cast_succ)) (i : fin n) :
  (fin.last_cases hlast hcast (fin.cast_succ i): C (fin.cast_succ i)) = hcast i :=
reverse_induction_cast_succ _ _ _

@[elab_as_eliminator, elab_strategy]
def add_cases {m n : ℕ} {C : fin (m + n) → Sort*}
  (hleft : Π i, C (fin.cast_add n i))
  (hright : Π i, C (fin.cast_add_right m i)) (i : fin (m + n)) : C i :=
if hi : (i : ℕ) < m
then have hi' : i = fin.cast_add _ ⟨i, hi⟩, from fin.ext rfl,
  _root_.cast (congr_arg C hi'.symm) (hleft _)
else have hi' : i = fin.cast_add_right m
  ⟨i - m, show (i : ℕ) - m < n,
      from (nat.sub_lt_left_iff_lt_add (le_of_not_gt hi)).2 i.2⟩,
    from fin.ext $ by simp [nat.add_sub_cancel' (le_of_not_gt hi)],
  _root_.cast (congr_arg C hi'.symm) (hright _)

@[simp] lemma add_cases_left {m n : ℕ} {C : fin (m + n) → Sort*}
  (hleft : Π i, C (fin.cast_add n i))
  (hright : Π i, C (fin.cast_add_right m i))
  (i : fin m) :
  (fin.add_cases hleft hright (fin.cast_add n i) : C (fin.cast_add n i)) =
  hleft i :=
begin
  cases i,
  simp only [add_cases, *, dif_pos, coe_mk, cast_eq, cast_add_mk],
  refl
end

@[simp] lemma add_cases_right {m n : ℕ} {C : fin (m + n) → Sort*}
  (hleft : Π i, C (fin.cast_add n i))
  (hright : Π i, C (fin.cast_add_right m i))
  (i : fin n) :
  (fin.add_cases hleft hright (fin.cast_add_right m i) : C (fin.cast_add_right m i)) =
  hright i :=
begin
  have : ¬ (cast_add_right m i : ℕ) < m, from not_lt_of_ge (le_cast_add_right _ _),
  cases i with i hi,
  simp only [add_cases, this, dif_neg, not_false_iff, cast_eq, not_false_iff],
  rw [cast_eq_iff_heq],
  congr,
  simp
end

@[simp] lemma fin_sum_fin_equiv_symm_apply_cast_add {m n : ℕ} (i : fin m) :
  fin_sum_fin_equiv.symm (cast_add n i) = sum.inl i :=
begin
  rw [fin_sum_fin_equiv_symm_apply_left _ (cast_add_lt _ _)],
  simp
end

@[simp] lemma fin_sum_fin_equiv_symm_apply_cast_add_right {m n : ℕ} (i : fin m) :
  fin_sum_fin_equiv.symm (cast_add_right n i) = sum.inr i :=
begin
  rw [fin_sum_fin_equiv_symm_apply_right _ (le_cast_add_right _ _)],
  simp
end

@[simp] lemma fin_sum_fin_equiv_apply_left' {m : ℕ} (n : ℕ) (i : fin m) :
  (fin_sum_fin_equiv (sum.inl i) : fin (m + n)) = fin.cast_add n i := rfl

@[simp] lemma fin_sum_fin_equiv_apply_right' (m : ℕ) {n : ℕ} (i : fin n) :
  (fin_sum_fin_equiv (sum.inr i) : fin (m + n)) = fin.cast_add_right m i := rfl

end fin
