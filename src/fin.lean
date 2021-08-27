import data.fin
import data.equiv.fin

namespace fin

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
