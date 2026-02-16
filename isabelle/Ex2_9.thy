theory Ex2_9
  imports Main
begin

fun itadd :: "nat => nat => nat" where
  "itadd n 0 = n" |
  "itadd n (Suc m) = itadd (Suc n) m"

lemma itadd_correct: "itadd n m = n + m"
  apply(induction m arbitrary: n)
  apply(auto)
done

end
