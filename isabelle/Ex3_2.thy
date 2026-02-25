theory Ex3_2
  imports Main
begin

inductive palindrome :: "'a list \<Rightarrow> bool" where
  palindrome_empty:   "palindrome []"  
| palindrome_one:     "palindrome [x]"
| palindrome_step:    "palindrome xs \<Longrightarrow> palindrome (x # xs @ [x])"

theorem palindrome_rev: "palindrome xs \<Longrightarrow> rev xs = xs"
  apply(induction rule: palindrome.induct)
  apply(auto)
done

end
