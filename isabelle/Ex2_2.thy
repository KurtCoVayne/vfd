theory Ex2_2
  imports Main
begin

datatype nat = zero | Succ nat
fun add :: "nat => nat => nat" where
  "add zero n = n" |
  "add (Succ m) n = Succ (add m n)"

lemma add_02: "add m zero = m"
apply(induction m)
apply(auto)
done

fun double :: "nat => nat" where
  "double zero = zero" |
  "double (Succ n) = Succ (Succ (double n))"

lemma plus_n_Sm: "add n (Succ m) = Succ (add n m)"
apply(induction n)
apply(auto)
done

lemma double_eq_add: "double n = add n n"
  apply(induction n)
  apply(auto)
  apply(auto simp: plus_n_Sm)
  done
end