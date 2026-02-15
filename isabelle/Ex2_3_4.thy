theory Ex2_3_4
  imports Main
begin
datatype natlist = Nil0 | Cons0 nat natlist


fun len:: "natlist => nat" where
  "len Nil0 = 0" |
  "len (Cons0 h t) = Suc (len t)"

fun count:: "nat => natlist => nat" where
  "count n Nil0 = 0" |
  "count n (Cons0 h t) = (if n = h then Suc (count n t) else count n t)"



lemma count_le_length[simp]: "count n l <= len l"
  apply(induction l)
  apply(auto)
 done


fun snoc:: "natlist => nat => natlist" where
  "snoc Nil0 n = Cons0 n Nil0" |
  "snoc (Cons0 h t) n = Cons0 h (snoc t n)"

value "snoc (Cons0 1 (Cons0 2 Nil0)) 3"


fun rev:: "natlist => natlist" where
  "rev Nil0 = Nil0" |
  "rev (Cons0 h t) = snoc (rev t) h"
 
lemma rev_snoc: "rev (snoc l n) = Cons0 n (rev l)"
    apply(induction l)
    apply(auto)
  done

lemma rev_involutive: "rev (rev l) = l"
  apply(induction l)
  apply(auto simp: rev_snoc)
  done

print_syntax
end