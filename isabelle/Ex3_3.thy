theory Ex3_3
  imports Main
begin


inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
  refl_star: "star r x x"
| step_star: "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

inductive star' :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
  refl_star': "star' r x x"
| step_star': "star' r x y \<Longrightarrow> r y z \<Longrightarrow> star' r x z"

lemma star_trans_step: "star r x y \<Longrightarrow> r y z \<Longrightarrow> star r x z"
  apply(induction rule: star.induct)
  apply(auto intro: star.intros)
done

lemma star'_step_trans: "star' r y z \<Longrightarrow> r x y \<Longrightarrow> star' r x z"
  apply(induction rule: star'.induct)
  apply(auto intro: star'.intros)
done

theorem star'_implies_star: "star' r x y \<Longrightarrow> star r x y"
  apply(induction rule: star'.induct)
  apply(auto intro: star.intros star_trans_step)
done

theorem star_implies_star': "star r x y \<Longrightarrow> star' r x y"
  apply(induction rule: star.induct)
  apply(auto intro: star'.intros star'_step_trans)
done

theorem star_iff_star': "star r x y \<longleftrightarrow> star' r x y"
  apply(auto intro: star_implies_star' star'_implies_star)
done

end
