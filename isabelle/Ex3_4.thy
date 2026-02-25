theory Ex3_4
  imports Main
begin


inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
  refl_star: "star r x x"
| step_star: "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

inductive iter :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
  iter_refl: "iter r 0 x x"
| iter_step: "r x y \<Longrightarrow> iter r n y z \<Longrightarrow> iter r (Suc n) x z"

theorem star_implies_iter: "star r x y \<Longrightarrow> \<exists>n. iter r n x y"
  apply(induction rule: star.induct)
  apply(auto intro: iter.intros)
done

theorem iter_implies_star: "iter r n x y \<Longrightarrow> star r x y"
  apply(induction rule: iter.induct)
  apply(auto intro: star.intros)
done

end
