theory Ex2_6_7_8
  imports Main
begin

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun preorder:: "'a tree => 'a list" where
  "preorder Tip = []" |
  "preorder (Node l x r) = x # preorder l @ preorder r"

abbreviation contents:: "'a tree => 'a list" where "contents\<equiv> preorder"

fun inorder:: "'a tree => 'a list" where
    "inorder Tip = []" |
    "inorder (Node l x r) = inorder l @ [x] @ inorder r"

fun postorder:: "'a tree => 'a list" where
    "postorder Tip = []" |
    "postorder (Node l x r) = postorder l @ postorder r @ [x]"

fun mirror:: "'a tree => 'a tree" where
  "mirror Tip = Tip" |
  "mirror (Node l x r) = Node (mirror r) x (mirror l)"

fun sum_tree:: "nat tree => nat" where
  "sum_tree Tip = 0" |
  "sum_tree (Node l x r) = x + sum_tree l + sum_tree r"

lemma sum_tree_equiv: "sum_tree t = sum_list (contents t)"
  apply(induction t)
  apply(auto)
done

lemma mirror_of_preorder_is_reverse_postorder: "preorder (mirror t) = rev (postorder t)"
  apply(induction t)
    apply simp
    apply simp
  done

fun intersperse:: "'a => 'a list => 'a list" where
  "intersperse _ [] = []" |
  "intersperse sep (x # xs) = x # (case xs of [] => [] | _ => sep # intersperse sep xs)"

lemma intersperse_map: "map f (intersperse a xs) = intersperse (f a) (map f xs)"
  apply (induction xs)
   apply auto
  apply (case_tac xs)
   apply auto
  done

value "cons 1 (nil)"

end