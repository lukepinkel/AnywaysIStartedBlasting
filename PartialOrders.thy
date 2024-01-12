theory PartialOrders
  imports Main
begin

hide_const(open) List.list.Nil
no_notation List.list.Nil ("[]")  
no_notation Cons (infixr "#" 65) 


declare [[show_types]]
declare [[show_sorts]]
declare [[show_consts]]

(*
Organization - the duals can be taken as implicit

 1. Add complete_semilattice_inf 
   1.1 Add it as an semilattice_inf
   1.2 Add complete_boolean_algebra and complete_lattice as complete_semilattice_inf
2. First extend semilattice_inf to finitary fInf using fold
3. Up
  3.1  Sets of upper bounds
    3.1.1 ub_set is all the upper bounds of the type
    3.1.2 ub_set_in is all the upper bounds restricted to a set
  3.2 max (greatest)
    3.2.1 is_max predicate
    3.2.2 has_max existential
    3.2.3 choice operator
  3.3 sup
    3.3.1 is_sup_in

*)

section CompleteSemilatticeClass

(*
  complete_semilattice_inf will have a bot element and dually for complete_semilattice_sup and a top
  but this element need not be the Inf or Sup of the empty set
*)
class complete_semilattice_inf = semilattice_inf + Inf +
    assumes CInf_lower: "A \<noteq> {} \<Longrightarrow> x \<in> A \<Longrightarrow> Inf A \<le> x"
    and CInf_greatest: "A \<noteq> {} \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> z \<le> x) \<Longrightarrow> z \<le> Inf A"

class complete_semilattice_sup = semilattice_sup + Sup +
   assumes CSup_upper: "A \<noteq> {} \<Longrightarrow> x \<in> A \<Longrightarrow> x \<le>  Sup A"
    and CSup_least: "A \<noteq> {} \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> x \<le> z) \<Longrightarrow> Sup A \<le> z"


class complete_semilattice_inf_top = complete_semilattice_inf + top +
   assumes top_greatest: "a \<le> top"

class complete_semilattice_sup_bot = complete_semilattice_sup + bot +
   assumes bot_least: "bot \<le> a"


sublocale complete_semilattice_inf \<subseteq> semilattice_inf inf "(\<le>)" "(<)" ..

sublocale complete_semilattice_sup \<subseteq> semilattice_sup sup "(\<le>)" "(<)" ..

sublocale complete_lattice \<subseteq> semilattice_inf inf  "(\<le>)" "(<)" ..

sublocale complete_lattice \<subseteq> semilattice_sup sup  "(\<le>)" "(<)" ..

sublocale complete_boolean_algebra  \<subseteq> semilattice_inf inf  "(\<le>)" "(<)" ..

sublocale complete_boolean_algebra  \<subseteq> semilattice_sup sup "(\<le>)" "(<)" ..

sublocale complete_lattice \<subseteq> csls:complete_semilattice_sup
  apply unfold_locales
  apply (simp add: local.Sup_upper)
  using local.Sup_least by blast


sublocale complete_lattice \<subseteq> csli:complete_semilattice_inf
  apply unfold_locales
  apply (simp add: local.Inf_lower)
  using local.Inf_greatest by blast

sublocale complete_semilattice_inf_top \<subseteq> complete_semilattice_inf ..

sublocale complete_semilattice_sup_bot \<subseteq> complete_semilattice_sup ..

sublocale complete_lattice \<subseteq> complete_semilattice_inf_top
  apply unfold_locales
  by simp

sublocale complete_lattice \<subseteq> complete_semilattice_sup_bot
  apply unfold_locales
  by simp


section SemilatticeInfFinitaryOperator
(*

  Adapted from  https://isabelle.in.tum.de/library/HOL/HOL/Lattices_Big.html 

  and

  T. Nipkow, L.C. Paulson (2005), "Proof Pearl: Defining Functions over Finite Sets", 
  in J. Hurd, T. Melham (Eds.), Theorem Proving in Higher Order Logics, TPHOLs 2005, 
  LNCS, Vol. 3603, Springer, Berlin, Heidelberg. 
  Available at: https://doi.org/10.1007/11541868_25

*)

context semilattice_inf
begin


definition fInf::"'a set \<Rightarrow> 'a" where
  eq_fold1:"fInf A = the (Finite_Set.fold (\<lambda>x y. Some (case y of None \<Rightarrow> x | Some z \<Rightarrow> inf x z)) None A)"


lemma eq_fold2:
  assumes "finite A"
  shows "fInf (insert x A) = Finite_Set.fold inf x A"
  using assms eq_fold1 local.Inf_fin.eq_fold local.Inf_fin.eq_fold' by auto


lemma singleton [simp]:
  "fInf {x} = x"
  using eq_fold1 local.Inf_fin.eq_fold' local.Inf_fin.singleton by presburger

lemma insert_not_elem:
  assumes "finite A" and "x \<notin> A" and "A \<noteq> {}"
  shows "fInf (insert x A) = inf x (fInf A)"
  using assms(1) assms(3) eq_fold1 local.Inf_fin.eq_fold' local.Inf_fin.insert by presburger

lemma in_idem:
  assumes "finite A" and "x \<in> A"
  shows "inf x (fInf A) = fInf A"
  using assms(1) assms(2) eq_fold1 local.Inf_fin.eq_fold' local.Inf_fin.in_idem by presburger

lemma insert [simp]:
  assumes "finite A" and "A \<noteq> {}"
  shows "fInf (insert x A) = inf x (fInf A)"
  using assms by (cases "x \<in> A") (simp_all add: insert_absorb in_idem insert_not_elem)

lemma union:
  assumes "finite A" "A \<noteq> {}" and "finite B" "B \<noteq> {}"
  shows "fInf(A \<union> B) = inf (fInf A) (fInf B)"
  using assms by (induct A rule: finite_ne_induct) (simp_all add: ac_simps)

lemma remove:
  assumes "finite A" and "x \<in> A"
  shows "fInf A = (if A - {x} = {} then x else inf x (fInf(A - {x})))"
proof -
  from assms obtain B where "A = insert x B" and "x \<notin> B" by (blast dest: mk_disjoint_insert)
  with assms show ?thesis by simp
qed

lemma insert_remove:
  assumes "finite A"
  shows "fInf (insert x A) = (if A - {x} = {} then x else inf x (fInf(A - {x})))"
  using assms by (cases "x \<in> A") (simp_all add: insert_absorb remove)

lemma subset:
  assumes "finite A" "B \<noteq> {}" and "B \<subseteq> A"
  shows "inf (fInf B) (fInf A) = fInf A"
proof -
  from assms have "A \<noteq> {}" and "finite B" by (auto dest: finite_subset)
  with assms show ?thesis by (simp add: union [symmetric] Un_absorb1)
qed

lemma closed:
  assumes "finite A" "A \<noteq> {}" and elem: "\<And>x y. inf x y \<in> {x, y}"
  shows "fInf A \<in> A"
using \<open>finite A\<close> \<open>A \<noteq> {}\<close> proof (induct rule: finite_ne_induct)
  case singleton then show ?case by simp
next
  case insert with elem show ?case by force
qed

lemma hom_commute:
  assumes hom: "\<And>x y. h (inf x y) = inf (h x) (h y)"
  and N: "finite N" "N \<noteq> {}"
  shows "h (fInf N) = fInf (h ` N)"
using N proof (induct rule: finite_ne_induct)
  case singleton thus ?case by simp
next
  case (insert n N)
  then have "h (fInf (insert n N)) = h (inf n (fInf N))" by simp
  also have "\<dots> = inf (h n) (h (fInf N))" by (rule hom)
  also have "h (fInf N) = fInf (h ` N)" by (rule insert)
  also have "inf (h n) \<dots> = fInf (insert (h n) (h ` N))"
    using insert by simp
  also have "insert (h n) (h ` N) = h ` insert n N" by simp
  finally show ?case .
qed

lemma infinite: "\<not> finite A \<Longrightarrow> fInf A = the None"
  unfolding eq_fold1 by (cases "finite (UNIV::'a set)") (auto intro: finite_subset fold_infinite)

lemma lower_bounded_iff:
  assumes "finite A" and "A \<noteq> {}"
  shows "x \<le> fInf A \<longleftrightarrow> (\<forall>a\<in>A. x \<le> a)"
  using assms by (induct rule: finite_ne_induct) simp_all

lemma boundedI:
  assumes "finite A"
  assumes "A \<noteq> {}"
  assumes "\<And>a. a \<in> A \<Longrightarrow> x \<le> a"
  shows "x \<le> fInf A"
  using assms by (simp add: lower_bounded_iff)

lemma boundedE:
  assumes "finite A" and "A \<noteq> {}" and "x \<le> fInf A"
  obtains "\<And>a. a \<in> A \<Longrightarrow> x \<le> a"
  using assms by (simp add: lower_bounded_iff)

lemma coboundedI:
  assumes "finite A"
    and "a \<in> A"
  shows "fInf A \<le> a"
proof -
  from assms have "A \<noteq> {}" by auto
  from \<open>finite A\<close> \<open>A \<noteq> {}\<close> \<open>a \<in> A\<close> show ?thesis
  proof (induct rule: finite_ne_induct)
    case singleton thus ?case by (simp add: refl)
  next
    case (insert x B)
    from insert have "a = x \<or> a \<in> B" by simp
    then show ?case
      by (simp add: in_idem insert.hyps(1) local.inf.absorb_iff2)
  qed
qed

lemma subset_imp:
  assumes "A \<subseteq> B" and "A \<noteq> {}" and "finite B"
  shows "fInf B \<le> fInf A"
proof (cases "A = B")
  case True then show ?thesis by (simp add: refl)
next
  case False
  have B: "B = A \<union> (B - A)" using \<open>A \<subseteq> B\<close> by blast
  then have "fInf B = fInf (A \<union> (B - A))" by simp
  also have "\<dots> = inf (fInf A) (fInf (B - A))" using False assms by (subst union) (auto intro: finite_subset)
  also have "\<dots> \<le> fInf A" by simp
  finally show ?thesis .
qed

lemma finite_inf_greatest:
  "\<And>z A. A \<noteq> {} \<Longrightarrow> finite A \<Longrightarrow> ((\<And>x. x \<in> A \<Longrightarrow> z \<le> x) \<Longrightarrow> z \<le> fInf A)"
  by (simp add: lower_bounded_iff)
end

section SemilatticeSupFinitaryOperator
context semilattice_sup
begin

definition fSup::"'a set \<Rightarrow> 'a" where
  eq_fold1:"fSup A = the (Finite_Set.fold (\<lambda>x y. Some (case y of None \<Rightarrow> x | Some z \<Rightarrow> sup x z)) None A)"


lemma eq_fold2:
  assumes "finite A"
  shows "fSup (insert x A) = Finite_Set.fold sup x A"
  using assms local.Sup_fin.eq_fold local.Sup_fin.eq_fold' local.eq_fold1 by auto

lemma singleton [simp]:
  "fSup {x} = x"
  using local.Sup_fin.eq_fold' local.Sup_fin.singleton local.eq_fold1 by presburger


lemma insert_not_elem:
  assumes "finite A" and "x \<notin> A" and "A \<noteq> {}"
  shows "fSup (insert x A) = sup x (fSup A)"
  using assms(1) assms(3) local.Sup_fin.eq_fold' local.Sup_fin.insert local.eq_fold1 by presburger


lemma in_idem:
  assumes "finite A" and "x \<in> A"
  shows "sup x (fSup A) = fSup A"
  using assms(1) assms(2) local.Sup_fin.eq_fold' local.Sup_fin.in_idem local.eq_fold1 by presburger


lemma insert [simp]:
  assumes "finite A" and "A \<noteq> {}"
  shows "fSup (insert x A) = sup x (fSup A)"
  using assms by (cases "x \<in> A") (simp_all add: insert_absorb in_idem insert_not_elem)

lemma union:
  assumes "finite A" "A \<noteq> {}" and "finite B" "B \<noteq> {}"
  shows "fSup(A \<union> B) = sup (fSup A) (fSup B)"
  using assms by (induct A rule: finite_ne_induct) (simp_all add: ac_simps)

lemma remove:
  assumes "finite A" and "x \<in> A"
  shows "fSup A = (if A - {x} = {} then x else sup x (fSup(A - {x})))"
proof -
  from assms obtain B where "A = insert x B" and "x \<notin> B" by (blast dest: mk_disjoint_insert)
  with assms show ?thesis by simp
qed

lemma insert_remove:
  assumes "finite A"
  shows "fSup (insert x A) = (if A - {x} = {} then x else sup x (fSup(A - {x})))"
  using assms by (cases "x \<in> A") (simp_all add: insert_absorb remove)

lemma subset:
  assumes "finite A" "B \<noteq> {}" and "B \<subseteq> A"
  shows "sup (fSup B) (fSup A) = fSup A"
proof -
  from assms have "A \<noteq> {}" and "finite B" by (auto dest: finite_subset)
  with assms show ?thesis by (simp add: union [symmetric] Un_absorb1)
qed

lemma closed:
  assumes "finite A" "A \<noteq> {}" and elem: "\<And>x y. sup x y \<in> {x, y}"
  shows "fSup A \<in> A"
using \<open>finite A\<close> \<open>A \<noteq> {}\<close> proof (induct rule: finite_ne_induct)
  case singleton then show ?case by simp
next
  case insert with elem show ?case by force
qed

lemma hom_commute:
  assumes hom: "\<And>x y. h (sup x y) = sup (h x) (h y)"
  and N: "finite N" "N \<noteq> {}"
  shows "h (fSup N) = fSup (h ` N)"
using N proof (induct rule: finite_ne_induct)
  case singleton thus ?case by simp
next
  case (insert n N)
  then have "h (fSup (insert n N)) = h (sup n (fSup N))" by simp
  also have "\<dots> = sup (h n) (h (fSup N))" by (rule hom)
  also have "h (fSup N) = fSup (h ` N)" by (rule insert)
  also have "sup (h n) \<dots> = fSup (insert (h n) (h ` N))"
    using insert by simp
  also have "insert (h n) (h ` N) = h ` insert n N" by simp
  finally show ?case .
qed

lemma infinite: "\<not> finite A \<Longrightarrow> fSup A = the None"
  unfolding eq_fold1 by (cases "finite (UNIV::'a set)") (auto intro: finite_subset fold_infinite)

lemma upper_bounded_iff:
  assumes "finite A" and "A \<noteq> {}"
  shows "fSup A \<le> x \<longleftrightarrow> (\<forall>a\<in>A. a \<le> x)"
  using assms by (induct rule: finite_ne_induct) simp_all

lemma boundedI:
  assumes "finite A"
  assumes "A \<noteq> {}"
  assumes "\<And>a. a \<in> A \<Longrightarrow> a \<le> x"
  shows "fSup A \<le> x"
  using assms(1) assms(2) assms(3) upper_bounded_iff by auto

lemma boundedE:
  assumes "finite A" and "A \<noteq> {}" and "fSup A \<le> x"
  obtains "\<And>a. a \<in> A \<Longrightarrow> a \<le> x"
  using assms by (simp add: upper_bounded_iff)

lemma coboundedI:
  assumes "finite A"
    and "a \<in> A"
  shows "a \<le> fSup A"
proof -
  from assms have "A \<noteq> {}" by auto
  from \<open>finite A\<close> \<open>A \<noteq> {}\<close> \<open>a \<in> A\<close> show ?thesis
  proof (induct rule: finite_ne_induct)
    case singleton thus ?case by (simp add: refl)
  next
    case (insert x B)
    from insert have "a = x \<or> a \<in> B" by simp
    then show ?case
      by (simp add: insert.hyps(1) local.in_idem local.le_iff_sup)
  qed
qed

lemma subset_imp:
  assumes "A \<subseteq> B" and "A \<noteq> {}" and "finite B"
  shows "fSup A \<le> fSup B"
proof (cases "A = B")
  case True then show ?thesis by (simp add: refl)
next
  case False
  have B: "B = A \<union> (B - A)" using \<open>A \<subseteq> B\<close> by blast
  then have "fSup B = fSup (A \<union> (B - A))" by simp
  also have "\<dots> = sup (fSup A) (fSup (B - A))" using False assms by (subst union) (auto intro: finite_subset)
  also have "\<dots> \<ge> fSup A" by simp
  finally show ?thesis .
qed

lemma finite_sup_greatest:
  "\<And>z A. A \<noteq> {} \<Longrightarrow> finite A \<Longrightarrow> ((\<And>x. x \<in> A \<Longrightarrow> x \<le> z) \<Longrightarrow> fSup A \<le> z)"
  by (simp add: upper_bounded_iff)

end


abbreviation Fpow_ne::"'a set \<Rightarrow> 'a set set" where
  "Fpow_ne A \<equiv> (Fpow A)-{{}}"

abbreviation Dpow::"'a set \<Rightarrow> 'a set set set" where
  "Dpow A \<equiv> (Pow (Pow A))"

abbreviation Pow_ne::"'a set \<Rightarrow> 'a set set" where
  "Pow_ne A \<equiv> (Pow A) - {{}}"

lemma in_dpow_iff:
  "a \<in> Dpow A \<longleftrightarrow> (\<forall>x  \<in> a. x \<in> Pow A)"
  by blast

section Definitions
subsection Bounds
definition ub_set_in::"'a::ord set \<Rightarrow> 'a::ord set  \<Rightarrow> 'a::ord set" where
  "ub_set_in A B \<equiv> {u. (\<forall>x. x \<in> A \<longrightarrow> x \<le> u) \<and> u \<in> B}"

definition ub_set::"'a::ord set  \<Rightarrow> 'a::ord set" where
  "ub_set A \<equiv> {u. (\<forall>x. x \<in> A \<longrightarrow> x \<le> u)}"


(*
 an alternative definition would be to have (\<forall>x. x \<in> A \<inter> B \<longrightarrow> x \<le> u) which is equivalent
  if A \<subseteq> B. 

definition ub_set_inr1::"'a::ord set \<Rightarrow> 'a::ord set  \<Rightarrow> 'a::ord set" where
  "ub_set_inr1 A B \<equiv> {u. (\<forall>x. x \<in> A \<inter> B \<longrightarrow> x \<le> u) \<and> u \<in> B}"

lemma ub_set_inr1_elem_iff:
   "\<forall>x. x \<in> ub_set_inr1 A B \<longleftrightarrow> (x \<in> B) \<and> (\<forall>a. a \<in> A \<and> a \<in> B \<longrightarrow> a \<le> x)"
   using ub_set_inr1_def by auto

lemma ub_set_in_eq_ub_set_inr1:
  fixes A B::"'a::order set"
  assumes A0:"A \<subseteq> B"
  shows "ub_set_in A B = ub_set_inr1 A B"
  apply(simp add:set_eq_iff  ub_set_inr1_elem_iff ub_set_in_mem_iff)
  using assms by blast
 *)

definition lb_set_in::"'a::ord set \<Rightarrow> 'a::ord set  \<Rightarrow> 'a::ord set" where
  "lb_set_in A B \<equiv> {l. (\<forall>x. x \<in> A \<longrightarrow> l \<le> x) \<and> l \<in> B}"

definition lb_set::"'a::ord set  \<Rightarrow> 'a::ord set" where
  "lb_set A \<equiv> {l. (\<forall>x. x \<in> A \<longrightarrow> l \<le> x)}"


subsection Predicates
subsubsection GreatestLeastPredicates
definition is_max::"'a::ord \<Rightarrow> 'a::ord set \<Rightarrow> bool" where
  "is_max m A \<equiv> (m \<in> A \<inter> (ub_set_in A UNIV))"

definition is_min::"'a::ord \<Rightarrow> 'a::ord set \<Rightarrow> bool" where
  "is_min m A \<equiv> (m \<in> A \<inter> (lb_set_in A UNIV))"

definition has_max::"'a::ord set \<Rightarrow> bool" where
  "has_max A \<equiv> (\<exists>m. is_max m A)"

definition has_min::"'a::ord set \<Rightarrow> bool" where
  "has_min A \<equiv> (\<exists>m. is_min m A)"

subsubsection SupInfPredicates
definition is_sup_in::"'a::ord \<Rightarrow> 'a::ord set \<Rightarrow> 'a::ord set \<Rightarrow> bool" where
  "is_sup_in s A X \<equiv>  (is_min s (ub_set_in A X))"

definition is_inf_in::"'a::ord \<Rightarrow> 'a::ord set \<Rightarrow> 'a::ord set \<Rightarrow> bool" where
  "is_inf_in i A X \<equiv>  (is_max i (lb_set_in A X))"

definition is_sup::"'a::order \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "is_sup s A \<equiv>  (is_min s (ub_set A))"

definition is_inf::"'a::order \<Rightarrow>  'a::order set \<Rightarrow> bool" where
  "is_inf i A \<equiv>  (is_max i (lb_set A))"

definition has_sup_in::" 'a::ord set \<Rightarrow> 'a::ord set \<Rightarrow> bool" where
  "has_sup_in A X \<equiv>  (has_min (ub_set_in A X))"

definition has_inf_in::" 'a::ord set \<Rightarrow> 'a::ord set \<Rightarrow> bool" where
  "has_inf_in A X \<equiv>  (has_max (lb_set_in A X))"

definition has_sup::" 'a::order set \<Rightarrow> bool" where
  "has_sup A \<equiv>  (has_min (ub_set A))"

definition has_inf::" 'a::order set  \<Rightarrow> bool" where
  "has_inf A \<equiv>  (has_max (lb_set A))"

subsection Operators
subsubsection GreatestLeastOperators
definition max::"'a::ord set \<Rightarrow> 'a::ord" where
  "max A \<equiv> (THE m. is_max m A)"

definition min::"'a::ord set \<Rightarrow> 'a::ord" where
  "min A \<equiv> (THE m. is_min m A)"

subsubsection SupInfOperators
definition SupIn::"'a::ord set \<Rightarrow>'a::ord set \<Rightarrow> 'a::ord" where
  "SupIn A X = (THE s. is_sup_in s A X)"

definition InfIn::"'a::ord set \<Rightarrow>'a::ord set \<Rightarrow> 'a::ord" where
  "InfIn A X = (THE i. is_inf_in i A X)"

definition SupUn::"'a::order set \<Rightarrow> 'a::order" where
  "SupUn A = (THE s. is_sup s A)"

definition InfUn::"'a::order set \<Rightarrow> 'a::order" where
  "InfUn A = (THE i. is_inf i A)"

subsection PropertiesOfFunctions
definition is_extensive::"('a::ord \<Rightarrow> 'a::ord) \<Rightarrow> bool" where
  "is_extensive f \<equiv> (\<forall>x. (x \<le> (f x)))"

definition is_isotone::"('a::ord \<Rightarrow> 'b::ord) \<Rightarrow> bool" where
  "is_isotone f \<equiv> (\<forall>x1 x2. x1 \<le> x2 \<longrightarrow> (f x1) \<le> (f x2))"

definition is_idempotent::"('a::ord \<Rightarrow> 'a::ord) \<Rightarrow> bool" where
  "is_idempotent f \<equiv> (\<forall>x.  (f x)= f (f x))"

definition is_closure::"('a::ord \<Rightarrow> 'a::ord) \<Rightarrow> bool" where
  "is_closure f \<equiv> (is_extensive f) \<and> (is_isotone f) \<and> (is_idempotent f)"

definition pointwise_less_eq::"('a::ord \<Rightarrow> 'b::ord) \<Rightarrow>('a::ord \<Rightarrow> 'b::ord) \<Rightarrow> bool" where
  "pointwise_less_eq f g \<equiv> (\<forall>x. (f x) \<le> (g x))"

definition pointwise_less::"('a::ord \<Rightarrow> 'b::ord) \<Rightarrow>('a::ord \<Rightarrow> 'b::ord) \<Rightarrow> bool" where
  "pointwise_less f g \<equiv> (pointwise_less_eq f g) \<and> (f \<noteq> g)"

definition antitone :: "('a::ord \<Rightarrow> 'b::ord) \<Rightarrow> bool" where
"antitone f \<longleftrightarrow> (\<forall>x y. x \<le> y \<longrightarrow> f y \<le> f x)"

definition comp_extensive :: "('a::ord \<Rightarrow> 'b::ord) \<Rightarrow> ('b::ord \<Rightarrow> 'a::ord) \<Rightarrow> bool" where
"comp_extensive f g \<longleftrightarrow> (\<forall>x. x \<le> g (f x)) \<and> (\<forall>y. y \<le> f (g y))"

subsection GaloisConnections
definition relation_to_fgc::"('a \<times> 'b) set \<Rightarrow> (('a set) \<Rightarrow> ('b set))" where
  "relation_to_fgc R = (\<lambda>(A::('a set)). {(y::'b). \<forall>x \<in> A. (x, y) \<in> R}) "

definition relation_to_ggc::"('a \<times> 'b) set \<Rightarrow> (('b set) \<Rightarrow> ('a set))" where
  "relation_to_ggc R = (\<lambda>(B::('b set)). {(x::'a). \<forall>y \<in> B. (x, y) \<in> R}) "

definition fgc_to_relation::"(('a set) \<Rightarrow> ('b set)) \<Rightarrow> ('a \<times> 'b) set" where
  "fgc_to_relation f = {(x, y). y \<in> f({x}) }"

definition ggc_to_relation::"(('b set) \<Rightarrow> ('a set)) \<Rightarrow> ('a \<times> 'b) set" where
  "ggc_to_relation g = {(x, y). x \<in> g({y}) }"

definition is_gc2::"('a::ord \<Rightarrow> 'b::ord) \<Rightarrow> ('b::ord \<Rightarrow> 'a::ord) \<Rightarrow> bool" where
  "is_gc2 f g \<equiv> (comp_extensive f g) \<and> (antitone f) \<and> (antitone g)"

definition is_gc4::"('a::ord \<Rightarrow> 'b::ord) \<Rightarrow> ('b::ord \<Rightarrow> 'a::ord) \<Rightarrow> bool" where
  "is_gc4 f g \<equiv> \<forall>(x::('a::ord)). \<forall>(y::('b::ord)). y \<le> (f x) \<longleftrightarrow> x \<le> (g y)"

definition binf::"'a::order  \<Rightarrow> 'a::order \<Rightarrow> 'a::order" where
  "binf a b \<equiv> InfUn {a,b}"

definition bsup::"'a::order \<Rightarrow> 'a::order \<Rightarrow> 'a::order" where
  "bsup a b \<equiv> SupUn {a, b}"

definition is_join_dual::"('a::order \<Rightarrow> 'b::order) \<Rightarrow> bool" where
  "is_join_dual f \<equiv> (\<forall>A. ( (f (SupUn A)) = (InfUn (f`(A))) ))"

definition join_dual_partner::"('a::order \<Rightarrow> 'b::order) \<Rightarrow> ('b::order \<Rightarrow> 'a::order)" where
  "join_dual_partner f = (\<lambda>y::('b::order). SupUn {x::'a::order. y \<le> (f x)})"

subsection SpecialSets

definition is_cofinal_in::"'a::ord set \<Rightarrow> 'a::ord set \<Rightarrow> bool" (infix "is'_cofinal'_in" 50) where
  "A is_cofinal_in B \<equiv> (\<forall>a. a \<in> A \<longrightarrow> (\<exists>b \<in> B. b \<ge> a))"

definition is_inf_complete::"'a::ord set \<Rightarrow> bool" where 
  "is_inf_complete X \<equiv> (\<forall>A. A \<in> Pow_ne X \<longrightarrow> has_inf_in A X)"

definition is_sup_complete::"'a::ord set \<Rightarrow> bool" where 
  "is_sup_complete X \<equiv> (\<forall>A. A \<in> Pow_ne X \<longrightarrow> has_sup_in A X)"

definition is_inf_closed::"'a::ord set \<Rightarrow> bool" where 
  "is_inf_closed X \<equiv> (\<forall>A. A \<in> Pow_ne X \<longrightarrow> InfIn A X \<in> X)"

definition is_sup_closed::"'a::ord set \<Rightarrow> bool" where 
  "is_sup_closed X \<equiv> (\<forall>A. A \<in> Pow_ne X  \<longrightarrow> SupIn A X \<in> X)"

definition is_inhabited::"'a set  \<Rightarrow> bool" where
   "is_inhabited X \<equiv> (X \<noteq> {})"

definition is_downdir::"'a::ord set \<Rightarrow> bool" where
   "is_downdir X \<equiv> (\<forall>a b. (a \<in> X) \<longrightarrow> ( b \<in> X) \<longrightarrow> (\<exists>c  \<in> X. (c \<le> a) \<and>  (c \<le> b)))"

definition is_upclosed::"'a::ord set \<Rightarrow> bool" where
   "is_upclosed X \<equiv> (\<forall>a b. a \<le> b \<longrightarrow>  a \<in> X \<longrightarrow>  b \<in> X)"

definition is_upclosed_in::"'a::ord set \<Rightarrow> 'a::ord \<Rightarrow> bool" where
   "is_upclosed_in A x \<equiv> (\<forall>a b. a \<le> b \<and>  b \<le> x  \<and>  a \<in> A \<longrightarrow>  b \<in> A)"

definition is_pisystem::"'a::order set \<Rightarrow> bool" where
   "is_pisystem X \<equiv> (\<forall>a b. a \<in> X  \<longrightarrow> b \<in> X \<longrightarrow> (binf a b)  \<in> X)"

definition is_filter::"'a::ord set \<Rightarrow> bool" where 
  "is_filter F \<equiv> (is_downdir F \<and> is_upclosed F \<and> is_inhabited F)"

definition is_filter_in::"'a::ord set \<Rightarrow> 'a::ord \<Rightarrow> bool" where 
  "is_filter_in F x \<equiv> (is_downdir F \<and> is_upclosed_in F x \<and> is_inhabited F \<and> (\<forall>f. f \<in> F \<longrightarrow> f \<le> x))"

definition covers::"'a::ord set \<Rightarrow> 'a::ord \<Rightarrow> bool" where
  "covers A b \<equiv> (b \<in> lb_set A) \<and> (A \<noteq> {}) "

definition is_finite_subcover::"'a::ord set \<Rightarrow> 'a::ord set \<Rightarrow>   'a::ord \<Rightarrow>  bool" where
 "is_finite_subcover S A b \<equiv> (S \<in> Fpow_ne A)  \<and> (b \<in> lb_set S)"

definition is_compact::"'a::ord \<Rightarrow> bool" where
  "is_compact b \<equiv> (\<forall>A. (covers A b) \<longrightarrow> (\<exists>S. is_finite_subcover S A b))"

definition is_directed::"'a::ord set \<Rightarrow> bool" where 
  "is_directed D \<equiv> (D \<noteq> {}) \<and> (\<forall>A. A  \<in> Fpow_ne D \<longrightarrow> (\<exists>u \<in> D. u \<in> ub_set A))"

definition directed_covering::"'a::ord \<Rightarrow> 'a::ord set \<Rightarrow> bool" where
  "directed_covering a D \<equiv> (covers D a) \<and> is_directed D"

definition is_compactly_generated::"'a::order set  \<Rightarrow> bool" where
  "is_compactly_generated X \<equiv> (\<forall>x \<in> X. (\<exists>Cx. (\<forall>c \<in> Cx. is_compact c) \<and> (is_sup x Cx)))"

definition is_meet_reducible::"'a::order \<Rightarrow> bool" where
  "is_meet_reducible x \<equiv> (\<exists>A. (A \<noteq> {}) \<and> (x \<notin> A) \<and> (is_inf x A))"

definition is_join_reducible::"'a::order \<Rightarrow> bool" where
  "is_join_reducible x \<equiv> (\<exists>A. (A \<noteq> {}) \<and> (x \<notin> A) \<and> (is_sup x A))"

definition is_moore_family::"'a::order set \<Rightarrow> bool" where
  "is_moore_family C \<equiv> (C \<noteq> {}) \<and> (\<forall>(a::'a). has_min (ub_set_in {a} C))"

definition moore_to_closure::"'a::order set \<Rightarrow> ('a::order \<Rightarrow> 'a::order)" where
  "moore_to_closure C \<equiv> (\<lambda>x. InfUn(ub_set_in {x} C))"

definition filter_closure::"'a::order set \<Rightarrow> 'a::order set" where
  "filter_closure A \<equiv> {a. \<exists>S\<in>Fpow_ne(A). InfUn S \<le> a}"

definition filter_closure_in::"'a::order set \<Rightarrow>'a::order \<Rightarrow> 'a::order set" where
  "filter_closure_in A x \<equiv> {a. a \<le> x \<and> (\<exists>S\<in>Fpow_ne(A). InfUn S \<le> a)}"


definition up_closure::"'a::order set \<Rightarrow> 'a::order set" where
  "up_closure A \<equiv> {x. \<exists>a \<in> A. a \<le> x}"

definition up_closure_in::"'a::order set \<Rightarrow> 'a::order \<Rightarrow>  'a::order set" where
  "up_closure_in A x \<equiv> {y. \<exists>a \<in> A. a \<le> y \<and> y \<le> x}"

definition is_prime::"'a::{order, sup} set \<Rightarrow> bool" where
  "is_prime A \<equiv> (\<forall>a. \<forall>b. (sup a b) \<in> A \<longrightarrow> (a \<in> A \<or> b \<in> A))"

definition is_prime_alt::"'a::{boolean_algebra,order_bot} set \<Rightarrow> bool" where
  "is_prime_alt U \<equiv> (\<forall>a. ((a \<in> U) \<and> \<not>((-a) \<in> U)) \<or> (\<not>(a \<in> U) \<and> ((-a) \<in> U)))"

definition binary_filter_sup::"'a::semilattice_inf set \<Rightarrow> 'a::semilattice_inf set \<Rightarrow> 'a::semilattice_inf set" where
  "binary_filter_sup A B = {x. \<exists>a \<in> A. \<exists>b \<in> B. inf a b \<le> x}"

definition filter_sup::"'a::order set set \<Rightarrow> 'a::order set" where
  "filter_sup EF \<equiv> filter_closure(Sup(EF))"

definition filter_inf::"'a::bounded_semilattice_inf_top set set \<Rightarrow> 'a::bounded_semilattice_inf_top set" where
  "filter_inf EF \<equiv> (if EF={} then {top} else \<Inter>EF)"

definition is_proper::"'a::order set \<Rightarrow> bool" where
  "is_proper F \<equiv> F \<noteq> UNIV"

definition is_proper_in::"'a::order set \<Rightarrow> 'a::order \<Rightarrow> bool" where
  "is_proper_in F x \<equiv> (F \<noteq> {y. y \<le> x})"

definition is_pfilter::"'a::order set \<Rightarrow>  bool" where
  "is_pfilter F \<equiv> (is_filter F) \<and> (is_proper F)"

definition is_pfilter_in::"'a::order set \<Rightarrow> 'a::order \<Rightarrow> bool" where
  "is_pfilter_in F x \<equiv>  (is_filter_in F x) \<and> (is_proper_in F x)"

definition is_ultrafilter::"'a::order set  \<Rightarrow> bool" where
  "is_ultrafilter U \<equiv> (is_pfilter U  \<and> (\<forall>F .  (is_pfilter F \<and> U \<subseteq> F) \<longrightarrow> U=F))"

definition upsets_in::"'a::order set \<Rightarrow> 'a::order set set" where
  "upsets_in A = {U. (is_upclosed U) \<and> (U \<in> (Pow A))}"

abbreviation upset_family::"'a::order set set" where
  "upset_family \<equiv> upsets_in UNIV" 

definition filters_in::"'a::order set \<Rightarrow> 'a::order set set" where
  "filters_in A = {F. (is_filter F) \<and> (F \<in> (Pow A))}"

definition pfilters_in::"'a::order set \<Rightarrow> 'a::order set set" where
  "pfilters_in A = {F. (is_pfilter F) \<and> (F \<in> (Pow A))}"

definition ultrafilters_in::"'a::order set \<Rightarrow> 'a::order set set" where
  "ultrafilters_in A = {U. (is_ultrafilter U) \<and> (U \<in> (Pow A))}"

definition finer_pfilters::"'a::order set \<Rightarrow> 'a::order set set" where
  "finer_pfilters F = {U. is_pfilter U \<and> (F \<subseteq> U)}"
    
definition finer_ultrafilters::"'a::order set \<Rightarrow> 'a::order set set" where
  "finer_ultrafilters F = {U. is_ultrafilter U \<and> (F \<subseteq> U)}"

definition coarser_ultrafilters::"'a::order set \<Rightarrow> 'a::order set set" where
  "coarser_ultrafilters F = {U. is_ultrafilter U \<and> (F \<supseteq> U)}"

definition finer_upsets::"'a::order set \<Rightarrow> 'a::order set set" where
  "finer_upsets A = {U. is_upclosed U \<and> (A \<subseteq> U)}"

definition is_chain::"'X::order set \<Rightarrow> bool" where
  "is_chain A \<equiv> (\<forall>a1 \<in> A. \<forall>a2 \<in> A. (a1 \<le> a2 \<or> a2 \<le> a1))"

definition meshes::"('a::{lattice,order_bot} set) \<Rightarrow> ('a::{lattice,order_bot} set) \<Rightarrow> bool"  (infixl "#" 50)  where
   "(A # B) \<equiv> (\<forall>a \<in> A. \<forall>b \<in> B.  ((inf a b) \<noteq> bot))"

definition grill::"'a::{lattice,order_bot} set \<Rightarrow> 'a::{lattice,order_bot} set" where
  "grill A = {x::('a::{lattice,order_bot}). {x}#A}"  

abbreviation principal_filter_in::"'a::order \<Rightarrow> 'a::order set \<Rightarrow> 'a::order set" where
  "principal_filter_in x A \<equiv> ub_set_in {x} A"


section FiniteExtrema
subsection Lattices
context lattice
begin
(*Existence of finite inf and sup in lattice*)
lemma finf_lattice:
  "\<And>A. (finite A \<and> A \<noteq> {}) \<longrightarrow> (\<exists>i. fInf A=i)"
  by simp
lemma fsup_lattice:
  "\<And>A. (finite A \<and> A \<noteq> {}) \<longrightarrow> (\<exists>s. fSup A=s)"
  by simp
end

subsubsection CompleteSemilattices
context complete_semilattice_sup
begin
(*finite inf and sup agree with inf and sup in complete lattice*)
lemma fsup_complete_lattice:
  "\<And>A. (finite A \<and> A \<noteq> {}) \<longrightarrow> (fSup A = Sup A)"
  using local.CSup_least local.CSup_upper local.Sup_fin.boundedI local.Sup_fin.coboundedI
         local.Sup_fin.eq_fold' local.dual_order.antisym local.eq_fold1 by auto

end

context complete_semilattice_inf
begin
(*finite inf and sup agree with inf and sup in complete lattice*)
lemma finf_complete_lattice:
  "\<And>A. (finite A \<and> A \<noteq> {}) \<longrightarrow> (fInf A = Inf A)"
  using local.CInf_greatest local.CInf_lower local.Inf_fin.bounded_iff 
          local.Inf_fin.coboundedI local.Inf_fin.eq_fold' local.dual_order.antisym local.eq_fold1
           by auto
end

subsubsection CompleteLattices
context complete_lattice
begin
(*finite inf and sup agree with inf and sup in complete lattice*)
lemma finf_complete_lattice:
  "\<And>A. (finite A \<and> A \<noteq> {}) \<longrightarrow> (fInf A = Inf A)"
  by (simp add: local.csli.finf_complete_lattice)


lemma fsup_complete_lattice:
  "\<And>A. (finite A \<and> A \<noteq> {}) \<longrightarrow> (fSup A = Sup A)"
  using local.csls.fsup_complete_lattice by blast

end
section Bounds
subsection UpperBounds
subsubsection Relative

lemma ub_set_in_mem:
  "\<And>(A::'a::order set) X x u. (u \<in> ub_set_in A X  \<and> x \<in> A) \<Longrightarrow> (x \<le> u \<and> u \<in> X) "
  by (simp add: ub_set_in_def)

lemma ub_set_in_subset:
  "ub_set_in A X \<subseteq> X"
  by (simp add: Collect_conj_eq ub_set_in_def)

lemma ub_set_in_imp:
  "\<And>(A::'a::order set) X u. (u \<in> ub_set_in A X) \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> x \<le> u)"
  by (simp add: ub_set_in_def)


lemma ub_set_in_elm:
  "\<And>(A::'a::order set) X u. (\<And>a. a \<in> A \<Longrightarrow> a \<le> u) \<Longrightarrow> u \<in> X \<Longrightarrow> u \<in> ub_set_in A X"
  by (simp add: ub_set_in_def)

lemma ub_set_in_mem_iff:
  "\<forall>x. x \<in> ub_set_in A B \<longleftrightarrow> (x \<in> B) \<and> (\<forall>a. a \<in> A \<longrightarrow> a \<le> x )"
  using ub_set_in_def by auto


lemma ub_set_in_antitone1:
  "\<And>A B X. A \<subseteq> B \<Longrightarrow>  ub_set_in B X \<subseteq> ub_set_in A X"
  by (simp add: subset_eq ub_set_in_def)

lemma ub_set_in_isotone2:
  "\<And>A  B X. B \<subseteq> X \<Longrightarrow>  ub_set_in A B \<subseteq> ub_set_in A X"
  by (simp add: subset_eq ub_set_in_def)

lemma ub_set_in_degenerate:
  "ub_set_in {} X = X"
  by (simp add: ub_set_in_def)

lemma ub_set_in_ub_inter:
  "(ub_set A) \<inter> B = ub_set_in A B"
  by (simp add: Collect_conj_eq ub_set_def ub_set_in_def)

lemma ub_set_in_ub_univ:
  "ub_set A = ub_set_in A UNIV"
  using ub_set_in_ub_inter by auto

lemma ub_set_in_univ_absorb:
  "ub_set_in A UNIV = ub_set A"
  using ub_set_in_ub_univ by blast

lemma ub_set_in_singleton:
  "ub_set_in {x} C  = {y \<in> C. x \<le> y}"
  by (simp add: set_eq_iff ub_set_in_mem_iff)

subsubsection Absolute

lemma ub_set_mem:
  "\<And>(A::'a::order set) x u. (u \<in> ub_set A  \<and> x \<in> A) \<Longrightarrow> (x \<le> u) "
  by (simp add: ub_set_def)

lemma ub_set_imp:
  "\<And>(A::'a::order set) u. (u \<in> ub_set A) \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> x \<le> u) "
  by (simp add: ub_set_def)

lemma ub_set_if:
  "\<And>(A::'a::order set) u. (\<And>x. x \<in> A \<Longrightarrow> x \<le> u) \<Longrightarrow> u \<in> ub_set A"
  by (simp add: ub_set_def)



lemma ub_set_elm:
  "\<And>(A::'a::order set) u. (\<And>a. a \<in> A \<Longrightarrow> a \<le> u)  \<Longrightarrow> u \<in> ub_set A"
  by (simp add: ub_set_def)

lemma ub_set_mem_iff:
  "\<forall>x. x \<in> ub_set A \<longleftrightarrow> (\<forall>a. a \<in> A \<longrightarrow> a \<le> x )"
  using ub_set_def by auto

lemma imp_in_upper_bounds:
  "\<And>u A.  (\<forall>a \<in> A. a \<le> u) \<Longrightarrow> u \<in> ub_set A"
  using ub_set_mem_iff by blast


lemma ub_set_antitone1:
  "\<And>A B. A \<subseteq> B \<Longrightarrow>  ub_set B \<subseteq> ub_set A"
  by (simp add: subset_eq ub_set_def)

lemma ub_set_degenerate:
  "ub_set {} = UNIV"
  by (simp add: ub_set_def)

lemma ub_set_singleton:
  "ub_set {x}  = {y. x \<le> y}"
  by (simp add: set_eq_iff ub_set_mem_iff)



subsection LowerBounds
subsubsection Relative
lemma lb_set_in_mem:
  "\<And>(A::'a::order set) X x l. (l \<in> lb_set_in A X  \<and> x \<in> A) \<Longrightarrow> (l \<le> x \<and> l \<in> X) "
  by (simp add: lb_set_in_def)

lemma lb_set_in_imp:
  "\<And>(A::'a::order set) X l. (l \<in> lb_set_in A X) \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> l \<le> x)"
  by (simp add: lb_set_in_def)

lemma lb_set_in_subset:
  "lb_set_in A X \<subseteq> X"
  by (simp add: Collect_conj_eq lb_set_in_def)

lemma lb_set_in_elm:
  "\<And>(A::'a::order set) X l. (\<And>a. a \<in> A \<Longrightarrow> l \<le> a) \<Longrightarrow> l \<in> X \<Longrightarrow> l \<in> lb_set_in A X"
  by (simp add: lb_set_in_def)

lemma lb_set_in_mem_iff:
  "\<forall>x. x \<in> lb_set_in A B \<longleftrightarrow> (x \<in> B) \<and> (\<forall>a. a \<in> A \<longrightarrow> x \<le> a )"
  using lb_set_in_def by auto

lemma lb_set_in_antitone1:
  "\<And>A  B X. A \<subseteq> B \<Longrightarrow>  lb_set_in B X \<subseteq> lb_set_in A X"
  by (simp add: subset_eq lb_set_in_def)
                                 
lemma lb_set_in_isotone2:
  "\<And>A B X. B \<subseteq> X \<Longrightarrow>  lb_set_in A B \<subseteq> lb_set_in A X"
  by (simp add: subset_eq lb_set_in_def)

lemma lb_set_in_degenerate:
  "lb_set_in {} X = X"
  by (simp add: lb_set_in_def)
  
lemma lb_set_in_lb_inter:
  "(lb_set A) \<inter> B = lb_set_in A B"
  by (simp add: Collect_conj_eq lb_set_def lb_set_in_def)

lemma lb_set_in_lb_univ:
  "lb_set A = lb_set_in A UNIV"
  using lb_set_in_lb_inter by auto

lemma lb_set_in_univ_absorb:
  "lb_set_in A UNIV = lb_set A"
  using lb_set_in_lb_univ by blast

lemma lb_set_in_singleton:
  "lb_set_in {x} C  = {y \<in> C. x \<ge> y}"
  by (simp add: set_eq_iff lb_set_in_mem_iff)


subsubsection Absolute

lemma lb_set_mem:
  "\<And>(A::'a::order set) x l. (l \<in> lb_set A  \<and> x \<in> A) \<Longrightarrow> (l \<le> x) "
  by (simp add: lb_set_def)

lemma lb_set_imp:
  "\<And>(A::'a::order set) l. (l \<in> lb_set A) \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> l \<le> x)"
  by (simp add: lb_set_def)

lemma lb_set_if:
  "\<And>(A::'a::order set) l. (\<And>x. x \<in> A \<Longrightarrow> l \<le> x) \<Longrightarrow> l \<in> lb_set A"
  by (simp add: lb_set_def)

lemma lb_set_elm:
  "\<And>(A::'a::order set) l. (\<And>a. a \<in> A \<Longrightarrow> l \<le> a)  \<Longrightarrow> l \<in> lb_set A"
  by (simp add: lb_set_def)

lemma lb_set_mem_iff:
  "\<forall>x. x \<in> lb_set A \<longleftrightarrow> (\<forall>a. a \<in> A \<longrightarrow> x \<le> a )"
  using lb_set_def by auto

lemma imp_in_lower_bounds:
  "\<And>l A.  (\<forall>a \<in> A. l \<le> a) \<Longrightarrow> l \<in> lb_set A"
  using lb_set_mem_iff by blast

lemma lb_set_antitone1:
  "\<And>A B. A \<subseteq> B \<Longrightarrow>  lb_set B \<subseteq> lb_set A"
  by (simp add: subset_eq lb_set_def)
      
lemma lb_set_degenerate:
  "lb_set {} = UNIV"
  by (simp add: lb_set_def)
         
lemma lb_set_singleton:
  "lb_set {x} = {y. x \<ge> y}"
  by (simp add: set_eq_iff lb_set_mem_iff)

subsection Misc

lemma ub_lb_extensive:
  fixes A X::"'a::ord set"
  assumes "A \<subseteq> X"
  shows "A \<subseteq> (ub_set_in (lb_set_in A X) X)"
  by (meson assms lb_set_in_mem_iff subset_iff ub_set_in_mem_iff)

lemma lb_ub_extensive:
  fixes A X::"'a::ord set"
  assumes "A \<subseteq> X"
  shows "A \<subseteq> (lb_set_in (ub_set_in A X) X)"
  by (meson assms ub_set_in_mem_iff subset_iff lb_set_in_mem_iff)


section MaxMin      
subsection Max
subsubsection Predicate                                  
lemma is_max_imp:
  "\<And>A x. is_max x A \<Longrightarrow> (x \<in> A \<and> x \<in> ub_set A)"
  by (simp add: is_max_def ub_set_in_ub_univ)

lemma is_max_if1:
  "\<And>A x.  (x \<in> A \<and> x \<in> ub_set A) \<Longrightarrow> is_max x A"
  by (simp add: is_max_def ub_set_in_ub_univ)
                                   
lemma is_max_if2:
  "\<And>A x.  x \<in> A \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> a \<le> x) \<Longrightarrow> is_max x A"
  by (simp add: is_max_if1 ub_set_mem_iff)
           
lemma is_max_imp_has_max:
  "\<And>A m. is_max m A \<Longrightarrow> has_max A"
  using has_max_def by auto
     
lemma is_max_iff:
  "is_max m A \<longleftrightarrow> m \<in> A \<and> (\<forall>a. a \<in> A \<longrightarrow> a \<le> m )"
  by (simp add: is_max_def ub_set_in_mem_iff)

lemma max_imp_ne:
  assumes "\<exists>m. is_max m A"
  shows "A \<noteq> {}"
  using assms is_max_def by auto

lemma max_isotone1:
  "\<And>A B ma mb. A \<subseteq> B \<and> (is_max ma A) \<and> ( is_max mb B) \<longrightarrow>  ma \<le> mb"
  using is_max_iff by blast

lemma is_max_top:
  fixes top::"'a::ord"
  assumes is_top:"\<forall>x. x \<le> top"
  shows "is_max top UNIV"
  by (simp add: is_max_iff is_top)
     

lemma is_max_singleton:
  "is_max (x::'a::order) {x}"
  by (simp add: is_max_iff)

subsubsection Existential                                  

lemma has_max_iff:
  "has_max A \<longleftrightarrow> (\<exists>m.  m \<in> A \<and> (\<forall>a. a \<in> A \<longrightarrow> a \<le> m ))"
  by (simp add: has_max_def is_max_iff)

lemma has_max_iff2:
  "has_max A \<longleftrightarrow> (\<exists>m. is_max m A)"
  by (simp add: has_max_def is_max_iff)

lemma max_unique:
  "\<And>(A::'a::order set) m1 m2. is_max m1 A \<Longrightarrow> is_max m2 A \<Longrightarrow> m1=m2"
  by (meson Orderings.order_eq_iff is_max_iff)  


lemma if_has_max_max_unique:
  assumes "has_max (A::'a::order set)"
  shows "\<exists>!m. is_max m A"
  using assms has_max_iff2 max_unique by blast

lemma has_max_singleton:
  "has_max {x::'a::order}"
  using has_max_def is_max_singleton by auto

lemma max_top:
  fixes top::"'a::ord"
  assumes is_top:"\<forall>x. x \<le> top"
  shows "has_max (UNIV::'a::ord set)"
proof-
  have B0:"is_max top UNIV"
    by (simp add: is_max_top is_top)
  have B1:"\<exists>(m::'a::ord). is_max m UNIV"
    using B0 by auto
  show ?thesis
    by (simp add: B1 has_max_def)
qed

subsubsection Operator        

lemma max_if:
  "\<And>(A::'a::order set) m. is_max m A \<Longrightarrow> m = max A"
  by (simp add: max_def max_unique the_equality)
 
lemma max_if2:
  "\<And>(A::'a::order set) x.  x \<in> A \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> a \<le> x) \<Longrightarrow>  x = max A"
  by (simp add: is_max_if2 max_if)
           
lemma max_isotone2:
  "\<And>(A::'a::order set) B. A \<subseteq> B \<and> (has_max A) \<and> ( has_max B) \<longrightarrow>  max A \<le> max B"
  by (metis if_has_max_max_unique max_if max_isotone1)

lemma max_singleton:
  "max {x::'a::order} = x"
  by(simp add: max_def is_max_def ub_set_in_def)

subsection Min
subsubsection Predicate
lemma is_min_imp:
  "\<And>A x. is_min x A \<Longrightarrow> (x \<in> A \<and> x \<in> lb_set A)"
  by (simp add: is_min_def lb_set_in_lb_univ)  
                                         
lemma is_min_if1:
  "\<And>A x.  (x \<in> A \<and> x \<in> lb_set A) \<Longrightarrow> is_min x A "
  by (simp add: is_min_def lb_set_in_lb_univ)  
       
lemma is_min_if2:
  "\<And>A x.  x \<in> A \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> x \<le> a) \<Longrightarrow> is_min x A"
  by (simp add: is_min_if1 lb_set_mem_iff)
  
lemma is_min_imp_has_min:
  "\<And>A m. is_min m A \<Longrightarrow> has_min A"
  using has_min_def by auto

lemma is_min_iff:
  "is_min m A \<longleftrightarrow> m \<in> A \<and> (\<forall>a. a \<in> A \<longrightarrow> m \<le> a )"
  by (simp add: is_min_def lb_set_in_mem_iff)

lemma min_imp_ne:
  assumes "\<exists>m. is_min m A"
  shows "A \<noteq> {}"
  using assms is_min_def by auto

lemma min_antitone1:
  "\<And>A B ma mb. A \<subseteq> B \<and> (is_min ma A) \<and> ( is_min mb B) \<longrightarrow>  mb \<le> ma"
  using is_min_iff by blast

lemma is_min_bot:
  fixes bot::"'a::ord"
  assumes is_bot:"\<forall>x. bot \<le> x"
  shows "is_min bot UNIV"
  by (simp add: is_min_iff is_bot)

lemma is_min_singleton:
  "is_min (x::'a::order) {x}"
  by (simp add: is_min_iff)

subsubsection Existential

lemma has_min_iff:
  "has_min A \<longleftrightarrow> (\<exists>m.  m \<in> A \<and> (\<forall>a. a \<in> A \<longrightarrow> m \<le> a ))"
  by (simp add: has_min_def is_min_iff)

lemma has_min_iff2:
  "has_min A \<longleftrightarrow> (\<exists>m. is_min m A)"
  by (simp add: has_min_def)

lemma min_unique:
  "\<And>(A::'a::order set) m1 m2. is_min m1 A \<Longrightarrow> is_min m2 A \<Longrightarrow> m1=m2"
  by (meson Orderings.order_eq_iff is_min_iff)  

lemma if_has_min_min_unique:
  assumes "has_min (A::'a::order set)"
  shows "\<exists>!m. is_min m A"
  using assms has_min_iff2 min_unique by blast

lemma min_bot:
  fixes bot::"'a::ord"
  assumes is_bot:"\<forall>x. bot \<le> x"
  shows "has_min (UNIV::'a::ord set)"
proof-
  have B0:"is_min bot UNIV"
    by (simp add: is_min_bot is_bot)
  have B1:"\<exists>(m::'a::ord). is_min m UNIV"
    using B0 by auto
  show ?thesis
    by (simp add: B1 has_min_def)
qed

lemma has_min_singleton:
  "has_min {x::'a::order}"
  using has_min_def is_min_singleton by auto

subsubsection Operator

lemma min_if:
  "\<And>(A::'a::order set) m. is_min m A \<Longrightarrow> m = min A"
  by (simp add: min_def min_unique the_equality)
          
lemma min_if2:
  "\<And>(A::'a::order set) x.  x \<in> A \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> x \<le> a) \<Longrightarrow>  x = min A"
  by (simp add: is_min_if2 min_if)
  
lemma min_antitone2:
  "\<And>(A::'a::order set) B. A \<subseteq> B \<and> (has_min A) \<and> ( has_min B) \<longrightarrow>  min B \<le> min A"
  by (metis has_min_def is_min_iff min_if subset_iff)

lemma min_singleton:
  "min {x::'a::order} = x"  
  by(simp add: min_def is_min_def lb_set_in_def)


section RelativeExtrema
subsection Suprema

lemma is_sup_in_iff:
  "is_sup_in m A X \<longleftrightarrow> (is_min m ( ub_set_in A X))"
  by (simp add: is_sup_in_def)

lemma is_sup_in_imp1:
  "\<And>m A X. is_sup_in m A X  \<Longrightarrow>  (m \<in>( ub_set_in A X) \<and> is_min m (ub_set_in A X))"
  by (simp add: is_min_imp is_sup_in_iff)

lemma is_sup_in_imp2:
  "\<And>m A X. is_sup_in m A X  \<Longrightarrow>   (\<And>a. a \<in> A \<Longrightarrow> a \<le> m)"
  by (simp add:  is_sup_in_def is_min_def ub_set_in_def)

lemma is_sup_in_imp3:
  "\<And>m A X. is_sup_in m A X  \<Longrightarrow>  (\<And>u. u \<in> X \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> a \<le> u) \<Longrightarrow> m \<le> u)"
  by (simp add: is_min_iff is_sup_in_def ub_set_in_mem_iff)

lemma is_sup_in_in_set:
  "\<And>m A X. is_sup_in m A X \<Longrightarrow> m \<in> X"
  by (simp add: is_sup_in_def is_sup_in_imp1 is_min_iff ub_set_in_mem_iff)

lemma is_sup_in_if1:
  "\<And>m A X. m \<in> X \<Longrightarrow>  (m \<in>( ub_set_in A X) \<and> is_min m (ub_set_in A X)) \<Longrightarrow> is_sup_in m A X "
  by (simp add: is_sup_in_def)

lemma is_sup_in_if2:
  "\<And>m A X. m \<in> X \<Longrightarrow>  (\<And>a. a \<in> A \<Longrightarrow> a \<le> m) \<Longrightarrow> is_min m (ub_set_in A X) \<Longrightarrow> is_sup_in m A X "
  by (simp add: is_sup_in_def)

lemma is_sup_in_if3:
  "\<And>m A X. m \<in> X \<Longrightarrow>  (\<And>a. a \<in> A \<Longrightarrow> a \<le> m) \<Longrightarrow>  (\<And>u. u \<in> X \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> a \<le> u) \<Longrightarrow> m \<le> u) \<Longrightarrow> is_sup_in m A X "
  by (simp add: is_min_iff is_sup_in_def ub_set_in_mem_iff)

lemma sup_in_unique:
  "\<And>(A::'a::order set) X m1 m2. is_sup_in m1 A X \<Longrightarrow> is_sup_in m2 A X \<Longrightarrow> m1=m2"
  by (simp add: is_sup_in_def min_unique)

lemma if_has_sup_in_unique:
  assumes "has_sup_in (A::'a::order set) X"
  shows "\<exists>!m. is_sup_in m A X"
  using assms has_sup_in_def if_has_min_min_unique is_sup_in_def by blast

lemma has_sup_in_has_lub:
  "\<And>A B.  has_sup_in A B \<Longrightarrow> has_min(ub_set_in A B)"
  by (simp add: has_sup_in_def)

lemma supin_is_sup:
  assumes A0:"has_sup_in (A::'a::order set) B"
  shows "is_sup_in (SupIn A B) A B"
proof-
  obtain m where A1:"m = SupIn A B"
    by simp
  have B0:"is_sup_in m A B"
    by (metis A0 A1 SupIn_def if_has_sup_in_unique the_equality)
  show ?thesis
    using A1 B0 by blast
qed

lemma has_sup_in_imp1:
  "\<And>(A::'a::order set) X. has_sup_in A X  \<Longrightarrow>  ((SupIn A X) \<in>( ub_set_in A X) \<and> is_min (SupIn A X) (ub_set_in A X))"
  using is_sup_in_imp1 supin_is_sup by blast

lemma has_sup_in_imp2:
  "\<And>(A::'a::order set) X. has_sup_in A X  \<Longrightarrow>  (\<And>a. a \<in> A \<Longrightarrow> a \<le> (SupIn A X))"
  using is_sup_in_imp2 supin_is_sup by blast

lemma has_sup_in_imp3:
  "\<And>(A::'a::order set) X. has_sup_in A X  \<Longrightarrow> (\<And>u. u \<in> X \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> a \<le> u) \<Longrightarrow> (SupIn A X) \<le> u)"
  using is_sup_in_imp3 supin_is_sup by blast

lemma has_sup_in_in_set:
  "\<And>(A::'a::order set) X. has_sup_in A X \<Longrightarrow> (SupIn A X) \<in> X"
  using is_sup_in_in_set supin_is_sup by blast

lemma sup_in_degenerate:  
  assumes A0:"has_min (X::'a::order set)"
  shows "SupIn {} X = min X"
  by (simp add: min_def SupIn_def is_sup_in_iff ub_set_in_degenerate)

lemma is_supin_singleton:
  "is_sup_in (x::'a::order) {x} UNIV"
  by(simp add:is_sup_in_def ub_set_in_def is_min_def lb_set_in_def)

lemma supin_singleton:
  "SupIn {x::'a::order} UNIV = x"
  apply(simp add: SupIn_def)
  using is_supin_singleton sup_in_unique by blast

lemma sup_in_max:
  fixes X::"'a::order set"
  assumes "has_sup_in X X"
  shows "is_max (SupIn X X) X"
  by (simp add: assms has_sup_in_imp2 has_sup_in_in_set is_max_if2)

lemma sup_in_isotone1:
  "\<And>(A::'a::order set) B X. has_sup_in A X \<Longrightarrow> has_sup_in B X \<Longrightarrow> A \<subseteq> B \<Longrightarrow> SupIn A X \<le> SupIn B X"
  by (meson  supin_is_sup is_sup_in_imp1 is_min_iff ub_set_in_antitone1 subsetD)

lemma sup_in_antitone2:
  "\<And>(A::'a::order set) B X. has_sup_in A X \<Longrightarrow> has_sup_in A B \<Longrightarrow> B \<subseteq> X \<Longrightarrow> SupIn A X \<le> SupIn A B"
  by (meson is_sup_in_def min_antitone1 supin_is_sup ub_set_in_isotone2)

lemma is_sup_in_sup_eq:
  "\<And>(s::'a::order) A X. is_sup_in s A X \<Longrightarrow> (s = SupIn A X)"
  by (simp add: SupIn_def sup_in_unique the_equality)

lemma sup_geq_rsup:
  fixes A B C::"'a::order set"
  assumes A0:"A \<noteq> {} \<and> A \<subseteq> B \<and> B \<subseteq> C" and
          A1:"has_sup_in A C" and
          A2:"has_sup_in A B"
  shows "SupIn A C \<le> SupIn A B"
  by (simp add: A0 A1 A2 sup_in_antitone2)

lemma sup_leq_rsup_if:
  fixes A B C::"'a::order set"
  assumes A0:"A \<noteq> {} \<and> A \<subseteq> B \<and> B \<subseteq> C" and
          A1:"has_sup_in A C" and
          A2:"has_sup_in A B"
  shows "SupIn A C \<ge> SupIn A B \<longleftrightarrow> (SupIn A C \<in> B)" (is "?L \<longleftrightarrow> ?R")
proof
  assume L:?L show ?R
    by (metis A0 A1 A2 L dual_order.antisym has_sup_in_in_set sup_in_antitone2)
  next
  assume R:?R show ?L
    by (simp add: A1 A2 R has_sup_in_imp2 has_sup_in_imp3)
qed


(*
  this is more familiar if we take B=Y and C=UNIV so that 
  Sup A \<in> Y then Sup_{Y} A exists and equals Sup A
*)
lemma sup_subset_eq:
  fixes A B C::"'a::order set"
  assumes A0:"A \<subseteq> B" and A1:"B \<subseteq> C" and A2:"has_sup_in A C" and A3:"SupIn A C \<in> B"
  shows "has_sup_in A B \<and> SupIn A B = SupIn A C"
proof-
  define sc where "sc =SupIn A C"
  have B0:"is_sup_in sc A C"
    by (simp add: A2 sc_def supin_is_sup)
  have B1:"sc \<in> ub_set_in A B"
    by (metis A3 B0 is_sup_in_imp1 sc_def ub_set_in_mem_iff)
  have B2:"ub_set_in A B \<subseteq> ub_set_in A C"
    by (simp add: A1 ub_set_in_isotone2)
  have B3:"is_min sc (ub_set_in A B)"
    by (meson B0 B1 B2 is_min_iff is_sup_in_def subset_eq)
  have B4:"is_sup_in sc A B"
    by (simp add: B3 is_sup_in_def)
  show ?thesis
    by (metis B3 B4 has_sup_in_def is_min_imp_has_min is_sup_in_sup_eq sc_def)
qed

lemma sup_in_expression:
  "is_sup_in m A X \<longleftrightarrow> m \<in> (lb_set_in (ub_set_in A X) X) \<inter> (ub_set_in A X)" (is "?L \<longleftrightarrow> ?R")
proof
  assume L:"?L" show "?R"
  by (metis IntI L is_min_imp is_sup_in_imp1 lb_set_in_lb_inter ub_set_in_mem_iff)
  next
  assume R:"?R" show "?L"
    by (metis IntD2 R inf_commute is_min_if1 is_sup_in_def lb_set_in_lb_inter)
qed


lemma sup_complete_has_max:
  "\<And>(X::'a::order set). X \<noteq> {} \<Longrightarrow> is_sup_complete X \<Longrightarrow> (is_max (SupIn X X) X)"
  by (simp add: is_sup_complete_def sup_in_max)

lemma sup_complete_bounded_inf:
  fixes X::"'a::order set"
  assumes A0:"is_sup_complete X"
  shows "\<And>A. (A \<subseteq> X \<and>  lb_set_in A X \<noteq> {}) \<longrightarrow> (has_inf_in A X)"
proof
  fix A
  assume  A1:"A \<subseteq> X \<and>  (lb_set_in A X \<noteq> {})" 
  let ?L="lb_set_in A X"
  have B0:"?L \<subseteq> X"
    by (simp add: lb_set_in_subset)
  have B1:"has_sup_in ?L X"
    using A1 B0 assms is_sup_complete_def by blast
  have B2:"(SupIn ?L X) \<in> ?L"
    by (meson A1 B1 has_sup_in_imp3 has_sup_in_in_set lb_set_in_elm lb_set_in_imp subsetD)
  show "has_inf_in A X"
  proof(cases "A = {}")
    case True
    then show ?thesis
      by (metis B1 has_inf_in_def has_max_iff2 lb_set_in_degenerate sup_in_max)
  next
    case False
    then show ?thesis
      by (meson B1 B2 has_inf_in_def has_max_iff has_sup_in_imp2)
  qed
qed


subsection Infima

lemma is_inf_in_iff:
  "is_inf_in m A X \<longleftrightarrow> (is_max m (lb_set_in A X))"
  by (simp add: is_inf_in_def)

lemma is_inf_in_imp1:
  "\<And>m A X. is_inf_in m A X  \<Longrightarrow>  (m \<in>(lb_set_in A X) \<and> is_max m (lb_set_in A X))"
  by (simp add: is_max_imp is_inf_in_iff)

lemma is_inf_in_imp2:
  "\<And>m A X. is_inf_in m A X  \<Longrightarrow>   (\<And>a. a \<in> A \<Longrightarrow> m \<le> a)"
  by (simp add:  is_inf_in_def is_max_def lb_set_in_def)

lemma is_inf_in_imp3:
  "\<And>m A X. is_inf_in m A X  \<Longrightarrow>  (\<And>l. l \<in> X \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> l \<le> a) \<Longrightarrow> l \<le> m)"
  by (simp add: is_max_iff is_inf_in_def lb_set_in_mem_iff)

lemma is_inf_in_in_set:
  "\<And>m A X. is_inf_in m A X \<Longrightarrow> m \<in> X"
  by (simp add: is_inf_in_def is_inf_in_imp1 is_max_iff lb_set_in_mem_iff)


lemma is_inf_in_if1:
  "\<And>m A X. m \<in> X \<Longrightarrow>  (m \<in>( lb_set_in A X) \<and> is_max m (lb_set_in A X)) \<Longrightarrow> is_inf_in m A X "
  by (simp add: is_inf_in_def)

lemma is_inf_in_if2:
  "\<And>m A X. m \<in> X \<Longrightarrow>  (\<And>a. a \<in> A \<Longrightarrow> m \<le> a) \<Longrightarrow> is_max m (lb_set_in A X) \<Longrightarrow> is_inf_in m A X "
  by (simp add: is_inf_in_def)

lemma is_inf_in_if3:
  "\<And>m A X. m \<in> X \<Longrightarrow>  (\<And>a. a \<in> A \<Longrightarrow> m \<le> a) \<Longrightarrow>  (\<And>l. l \<in> X \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> l \<le> a) \<Longrightarrow> l \<le> m) \<Longrightarrow> is_inf_in m A X "
  by (simp add: is_max_iff is_inf_in_def lb_set_in_mem_iff)

lemma inf_in_unique:
  "\<And>(A::'a::order set) X m1 m2. is_inf_in m1 A X \<Longrightarrow> is_inf_in m2 A X \<Longrightarrow> m1=m2"  
  by (simp add: is_inf_in_def max_unique)

lemma if_has_inf_in_unique:
  assumes "has_inf_in (A::'a::order set) X"
  shows "\<exists>!m. is_inf_in m A X"
  using assms has_inf_in_def if_has_max_max_unique is_inf_in_def by blast

lemma has_inf_in_has_glb:
  "\<And>A B.  has_inf_in A B \<Longrightarrow> has_max (lb_set_in A B)"
  by (simp add: has_inf_in_def)

lemma infin_is_inf:
  assumes A0:"has_inf_in (A::'a::order set) B"
  shows "is_inf_in (InfIn A B) A B"
proof-
  obtain m where A1:"m = InfIn A B"
    by simp
  have B0:"is_inf_in m A B"
    by (metis A1 InfIn_def assms if_has_inf_in_unique the_equality)
  show ?thesis
    using A1 B0 by blast
qed

lemma has_inf_in_imp1:
  "\<And>(A::'a::order set) X. has_inf_in A X  \<Longrightarrow>  ((InfIn A X) \<in>(lb_set_in A X) \<and> is_max (InfIn A X) (lb_set_in A X))"
  using is_inf_in_imp1 infin_is_inf by blast

lemma has_inf_in_imp2:
  "\<And>(A::'a::order set) X. has_inf_in A X  \<Longrightarrow>  (\<And>a. a \<in> A \<Longrightarrow> a \<ge> (InfIn A X))"
  using is_inf_in_imp2 infin_is_inf by blast

lemma has_inf_in_imp3:
  "\<And>(A::'a::order set) X. has_inf_in A X  \<Longrightarrow> (\<And>u. u \<in> X \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> a \<ge> u) \<Longrightarrow> (InfIn A X) \<ge> u)"
  using is_inf_in_imp3 infin_is_inf by blast

lemma has_inf_in_in_set:
  "\<And>(A::'a::order set) X. has_inf_in A X \<Longrightarrow> (InfIn A X) \<in> X"
  using is_inf_in_in_set infin_is_inf by blast


lemma inf_in_degenerate:  
  assumes A0:"has_max (X::'a::order set)"
  shows "InfIn {} X = max X"
  by (simp add: max_def InfIn_def is_inf_in_iff lb_set_in_degenerate)

lemma is_infin_singleton:
  "is_inf_in (x::'a::order) {x} UNIV"
  by(simp add: is_inf_in_def lb_set_in_def is_max_def ub_set_in_def)

lemma infin_singleton:
  "InfIn {x::'a::order} UNIV = x"
  apply(simp add: InfIn_def)
  using is_infin_singleton inf_in_unique by blast

lemma infin_eq_infun:
  assumes A0:"has_inf_in (A::'a::order set) UNIV"
  shows "InfIn A UNIV = InfUn A"
  by (simp add: InfIn_def InfUn_def is_inf_in_def is_inf_def lb_set_in_univ_absorb)

lemma inf_in_min:
  fixes X::"'a::order set"
  assumes "has_inf_in X X"
  shows "is_min (InfIn X X) X"
  by (simp add: assms has_inf_in_imp2 has_inf_in_in_set is_min_if2)

lemma inf_in_antitone1:
  "\<And>(A::'a::order set) B X. has_inf_in A X \<Longrightarrow> has_inf_in B X \<Longrightarrow> A \<subseteq> B \<Longrightarrow> InfIn B X \<le> InfIn A X"
  by (meson  infin_is_inf is_inf_in_imp1 is_max_iff lb_set_in_antitone1 subsetD)

lemma inf_in_isotone2:
  "\<And>(A::'a::order set) B X. has_inf_in A X \<Longrightarrow> has_inf_in A B \<Longrightarrow> B \<subseteq> X \<Longrightarrow> InfIn A B \<le> InfIn A X"
  by (meson in_mono infin_is_inf is_inf_in_imp1 is_max_iff lb_set_in_isotone2)

lemma is_inf_in_inf_eq:
  "\<And>(i::'a::order) A X. is_inf_in i A X \<Longrightarrow> (i = InfIn A X)"
  by (simp add: InfIn_def Uniq_def inf_in_unique the1_equality')

lemma inf_leq_rinf:
  fixes A B C::"'a::order set"
  assumes A0:"A \<noteq> {} \<and> A \<subseteq> B \<and> B \<subseteq> C" and
          A1:"has_inf_in A C" and
          A2:"has_inf_in A B"
  shows "InfIn A B \<le> InfIn A C"
  by (simp add: A0 A1 A2 inf_in_isotone2)

lemma inf_leq_rinf_if:
  fixes A B C::"'a::order set"
  assumes A0:"A \<noteq> {} \<and> A \<subseteq> B \<and> B \<subseteq> C" and
          A1:"has_inf_in A C" and
          A2:"has_inf_in A B"
  shows "InfIn A B \<ge> InfIn A C \<longleftrightarrow> (InfIn A C \<in> B)" (is "?L \<longleftrightarrow> ?R")
proof
  assume L:?L show ?R
    by (metis A0 A1 A2 L dual_order.antisym has_inf_in_in_set inf_in_isotone2)
  next
  assume R:?R show ?L
    by (simp add: A1 A2 R has_inf_in_imp2 has_inf_in_imp3)
qed

lemma inf_subset_eq:
  fixes A B C::"'a::order set"
  assumes A0:"A \<subseteq> B" and A1:"B \<subseteq> C" and A2:"has_inf_in A C" and A3:"InfIn A C \<in> B"
  shows "InfIn A B = InfIn A C"
proof-
  define ic where "ic =InfIn A C"
  have B0:"is_inf_in ic A C"
    by (simp add: A2 ic_def infin_is_inf)
  have B1:"ic \<in> lb_set_in A B"
    by (metis A3 B0 is_inf_in_imp1 ic_def lb_set_in_mem_iff)
  have B2:"lb_set_in A B \<subseteq> lb_set_in A C"
    by (simp add: A1 lb_set_in_isotone2)
  have B3:"is_max ic (lb_set_in A B)"
    by (meson B0 B1 B2 is_max_iff is_inf_in_def subset_eq)
  have B4:"is_inf_in ic A B"
    by (simp add: B3 is_inf_in_def)
  show ?thesis
    using B4 is_inf_in_inf_eq ic_def by force
qed

lemma inf_in_expression:
  "is_inf_in m A X \<longleftrightarrow> m \<in> (ub_set_in (lb_set_in A X) X) \<inter> (lb_set_in A X)" (is "?L \<longleftrightarrow> ?R")
proof
  assume L:"?L" show "?R"
  by (metis IntI L is_max_imp is_inf_in_imp1 ub_set_in_ub_inter lb_set_in_mem_iff)
  next
  assume R:"?R" show "?L"
    by (metis IntD2 R inf_commute is_inf_in_def is_max_if1 ub_set_in_ub_inter)
qed

lemma inf_complete_has_min:
  "\<And>(X::'a::order set). X \<noteq> {} \<Longrightarrow> is_inf_complete X \<Longrightarrow> (is_min (InfIn X X) X)"
  by (simp add: is_inf_complete_def inf_in_min)


lemma inf_complete_bounded_sup:
  fixes X::"'a::order set"
  assumes A0:"is_inf_complete X"
  shows "\<And>A. (A \<subseteq> X \<and>  ub_set_in A X \<noteq> {}) \<longrightarrow> (has_sup_in A X)"
proof
  fix A
  assume  A1:"A \<subseteq> X \<and>  (ub_set_in A X \<noteq> {})" 
  let ?U="ub_set_in A X"
  have B0:"?U \<subseteq> X"
    by (simp add: ub_set_in_subset)
  have B1:"has_inf_in ?U X"
    using A1 B0 assms is_inf_complete_def by blast
  have B2:"(InfIn ?U X) \<in> ?U"
    by (meson A1 B1 has_inf_in_imp3 has_inf_in_in_set ub_set_in_elm ub_set_in_imp subsetD)
  show "has_sup_in A X"
  proof(cases "A = {}")
    case True
    then show ?thesis
      by (metis B1 has_sup_in_def has_min_iff2 ub_set_in_degenerate inf_in_min)
  next
    case False
    then show ?thesis
      by (meson B1 B2 has_inf_in_imp2 has_min_iff has_sup_in_def)
  qed
qed

lemma sup_in_eq_inf_in_ub:
  fixes A X::"'a::order set"
  assumes A0:"A \<subseteq> X" and A1:"has_inf_in (ub_set_in A X) X"
  shows "has_sup_in A X \<and> SupIn A X = InfIn(ub_set_in A X) X"
proof-
  let ?U="ub_set_in A X"
  let ?i="InfIn ?U X"
  have B0:"A \<subseteq> lb_set_in ?U X"
    by (simp add: A0 lb_ub_extensive)
  have B1:"\<forall>a. a \<in> A \<longrightarrow> a \<le> ?i"
    by (meson A0 A1 has_inf_in_imp3 subsetD ub_set_in_imp)
  have B2:"?i \<in> ?U"
    by (simp add: A1 B1 has_inf_in_in_set ub_set_in_elm)
  have B3:"is_min ?i ?U"
    by (simp add: A1 B2 has_inf_in_imp2 is_min_if2)
  show ?thesis
    using B3 has_sup_in_def has_sup_in_imp1 is_min_imp_has_min min_unique by blast
qed

lemma inf_in_eq_sup_in_lb:
  fixes A X::"'a::order set"
  assumes A0:"A \<subseteq> X" and A1:"has_sup_in (lb_set_in A X) X"
  shows "has_inf_in A X \<and> InfIn A X = SupIn(lb_set_in A X) X"
proof-
  let ?L="lb_set_in A X"
  let ?s="SupIn ?L X"
  have B0:"A \<subseteq> ub_set_in ?L X"
    by (meson A0 lb_set_in_imp subset_eq ub_set_in_elm)
  have B1:"?s \<in> lb_set_in A X"
    by (meson A1 B0 has_sup_in_imp1 has_sup_in_in_set is_min_iff lb_set_in_elm subset_eq)
  have B2:"is_max ?s ?L"
    by (simp add: A1 B1 has_sup_in_imp2 is_max_if2)
  show ?thesis
    by (metis B2 has_inf_in_def has_max_iff2 is_inf_in_iff is_inf_in_inf_eq)
qed



section AbsoluteExtrema
subsection Suprema

lemma is_sup_iff:
  "is_sup m A \<longleftrightarrow> (is_min m ( ub_set A))"
  by (simp add: is_sup_def)


lemma is_sup_imp1:
  "\<And>m A. is_sup m A  \<Longrightarrow>  (m \<in>( ub_set A) \<and> is_min m (ub_set A))"
  by (simp add: is_min_imp is_sup_iff)

lemma is_sup_imp2:
  "\<And>m A. is_sup m A  \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> a \<le> m)"
  by (simp add: is_sup_def is_min_def ub_set_def)

lemma is_sup_imp3:
  "\<And>m A. is_sup m A  \<Longrightarrow>  (\<And>u. (\<And>a. a \<in> A \<Longrightarrow> a \<le> u) \<Longrightarrow> m \<le> u)"
  by (simp add: is_min_iff is_sup_def ub_set_mem_iff)

lemma is_sup_if1:
  "\<And>m A. (m \<in>( ub_set A) \<and> is_min m (ub_set A)) \<Longrightarrow> is_sup m A"
  by (simp add: is_sup_def)

lemma is_sup_if2:
  "\<And>m A. (\<And>a. a \<in> A \<Longrightarrow> a \<le> m) \<Longrightarrow>  is_min m (ub_set A) \<Longrightarrow> is_sup m A"
  by (simp add: is_sup_def)

lemma is_sup_if3:
  "\<And>m A. (\<And>a. a \<in> A \<Longrightarrow> a \<le> m) \<Longrightarrow>  (\<And>u. (\<And>a. a \<in> A \<Longrightarrow> a \<le> u) \<Longrightarrow> m \<le> u) \<Longrightarrow> is_sup m A"
  by (simp add: is_min_iff is_sup_def ub_set_mem_iff)


lemma is_sup_unique:
  "\<And>(A::'a::order set)m1 m2. is_sup m1 A \<Longrightarrow> is_sup m2 A \<Longrightarrow> m1=m2"
  by (simp add: is_sup_def min_unique)


lemma if_has_sup_unique:
  assumes "has_sup (A::'a::order set)"
  shows "\<exists>!m. is_sup m A"
  using assms has_sup_def if_has_min_min_unique is_sup_def by blast

lemma is_max_is_sup:
  "\<And>A m.  is_max m A \<Longrightarrow> is_sup m A"
  by (simp add: is_max_iff is_sup_if3)

lemma has_max_has_sup:
  "\<And>A.  has_max A \<Longrightarrow> has_sup A"
  by (meson has_min_def has_sup_def if_has_max_max_unique is_max_is_sup is_sup_def)
lemma sup_is_sup:
  assumes A0:"has_sup (A::'a::order set)"
  shows "is_sup (SupUn A) A"
proof-
  obtain m where A1:"m = SupUn A"
    by simp
  have B0:"is_sup m A"
    by (metis A1 SupUn_def assms if_has_sup_unique the_equality)
  show ?thesis
    using A1 B0 by blast
qed


lemma sup_degenerate: 
  "SupUn {} =( bot::'a::order_bot)"
  by (metis min_bot SupUn_def bot.extremum has_sup_def
      if_has_sup_unique is_min_bot is_sup_def
       the_equality ub_set_in_degenerate ub_set_in_ub_univ)

lemma has_sup_in_imp_sup:
  assumes "has_sup_in A UNIV"
  shows "has_sup A"
  by (metis assms has_sup_def has_sup_in_def ub_set_in_ub_univ)

lemma has_sup_imp_sup_in:
  assumes "has_sup A"
  shows "has_sup_in A UNIV"
  by (metis assms has_sup_def has_sup_in_def ub_set_in_ub_univ)

lemma has_min_ub:
  assumes A0:"has_min (ub_set_in (A::'a::order set) B)"
  shows "is_sup_in (SupIn A B) A B"
  by (simp add: assms has_sup_in_def supin_is_sup)

lemma supin_eq_supun:
  assumes A0:"has_sup_in(A::'a::order set) UNIV"
  shows "SupIn A UNIV = SupUn A"
  by(simp add:SupIn_def SupUn_def is_sup_in_def is_sup_def ub_set_in_univ_absorb)

lemma complete_semilattice_sup_is_sup:
  "\<And>(A::'a::complete_semilattice_sup set). A \<noteq> {} \<Longrightarrow> (is_sup (Sup A) A)"
  by (simp add: CSup_least CSup_upper is_sup_if3)

lemma complete_semilattice_sup_is_sup_in:
  "\<And>(A::'a::complete_semilattice_sup set). A \<noteq> {} \<Longrightarrow> (is_sup_in (Sup A) A UNIV)"
  by (simp add: CSup_least CSup_upper is_sup_in_if3)

lemma complete_semilattice_supun_is_sup:
  "\<And>(A::'a::complete_semilattice_sup set). A \<noteq> {} \<Longrightarrow> (is_sup (SupUn A) A)"
  by (meson complete_semilattice_sup_is_sup has_min_def has_sup_def is_sup_def sup_is_sup)

lemma complete_semilattice_supin_is_sup:
  "\<And>(A::'a::complete_semilattice_sup set). A \<noteq> {} \<Longrightarrow> (is_sup (SupIn A UNIV) A)"
  by (metis complete_semilattice_sup_is_sup complete_semilattice_sup_is_sup_in is_sup_in_sup_eq)

lemma complete_semilattice_supin_is_supin:
  "\<And>(A::'a::complete_semilattice_sup set). A \<noteq> {} \<Longrightarrow> (is_sup_in (SupIn A UNIV) A UNIV)"
  by (simp add: complete_semilattice_supin_is_sup is_sup_imp1 is_sup_in_iff ub_set_in_univ_absorb)

lemma complete_semilattice_supin_existence:
  "\<And>(A::'a::complete_semilattice_sup set). A \<noteq> {} \<Longrightarrow> has_sup_in A UNIV"
  by (metis complete_semilattice_supin_is_sup has_sup_in_def is_min_imp_has_min is_sup_iff ub_set_in_univ_absorb)

lemma complete_semilattice_sup_existence:
  "\<And>(A::'a::complete_semilattice_sup set). A \<noteq> {} \<Longrightarrow> has_sup A"
  by (simp add: complete_semilattice_supin_existence has_sup_in_imp_sup)


lemma complete_semilattice_sup_least:
  fixes A::"'a::complete_semilattice_sup set"
  shows "\<forall>u \<in> ub_set A. A \<noteq> {} \<longrightarrow>  Sup A \<le> u"
  by (simp add: CSup_least ub_set_imp)

lemma complete_semilattice_supun_eq_sup:
  fixes A::"'a::complete_semilattice_sup set" 
  assumes "A \<noteq> {}"
  shows "SupUn A = Sup A"
  by (meson assms complete_semilattice_sup_is_sup complete_semilattice_supun_is_sup is_sup_unique)

lemma complete_semilattice_sup_is_sup2:
  "\<forall>(A::'X::complete_semilattice_sup set). A \<noteq> {} \<longrightarrow> SupUn A = Sup A"
  by (simp add: complete_semilattice_supun_eq_sup)

lemma has_supin_singleton:
  "has_sup_in {x::'a::order} UNIV"
  by (simp add: has_max_has_sup has_max_singleton has_sup_imp_sup_in)


lemma is_sup_singleton:
  "is_sup (x::'a::order) {x}"
  by (simp add: is_max_is_sup is_max_singleton)

lemma has_sup_singleton:
  "has_sup {x::'a::order}"
  by (simp add: has_sup_in_imp_sup has_supin_singleton)

lemma sup_singleton:
  "SupUn {x::'a::order} = x"
  using has_sup_singleton is_sup_singleton is_sup_unique sup_is_sup by blast

lemma sup_monotone1:
  "\<And>A B. has_sup A \<Longrightarrow> has_sup B \<Longrightarrow> A \<subseteq> B \<Longrightarrow> SupUn A \<le> SupUn B"
  by (meson is_sup_imp2 is_sup_imp3 subsetD sup_is_sup)

lemma is_sup_sup_eq:
  "\<And>(s::'a::order) A. has_sup A \<Longrightarrow> is_sup s A \<Longrightarrow> (s = SupUn A)"
  by (simp add: is_sup_unique sup_is_sup)

lemma complete_lattice_sup_is_sup:
  fixes A::"'a::complete_lattice set"
  assumes "A \<noteq> {}"
  shows "(is_sup (Sup A) A)"
  by (simp add: Sup_least Sup_upper is_sup_if3)

lemma has_max_imp_sup_eq_max:
  fixes A::"'a::order set"
  assumes A0:"has_max A"
  shows "SupUn A = max A"
  by (metis assms has_max_has_sup if_has_max_max_unique is_max_is_sup is_sup_unique max_if sup_is_sup)

lemma complete_lattice_sup_least:
  fixes A::"'a::complete_lattice set"
  shows "\<forall>u \<in> ub_set A. A \<noteq> {} \<longrightarrow> Sup A \<le> u"
  by (simp add: csls.CSup_least ub_set_mem)

lemma is_sup_imp_lub:
  "\<And>s A. is_sup s A \<Longrightarrow> is_min s (ub_set A)"
  by (simp add: is_sup_iff)

subsection Infima

lemma is_inf_iff:
  "is_inf m A \<longleftrightarrow> (is_max m (lb_set A))"
  by (simp add: is_inf_def)

lemma is_inf_imp1:
  "\<And>m A. is_inf m A  \<Longrightarrow>  (m \<in>( lb_set A) \<and> is_max m (lb_set A))"
  by (simp add: is_max_imp is_inf_iff)

lemma is_inf_imp2:
  "\<And>m A. is_inf m A  \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> m \<le> a)"
  by (simp add: is_inf_def is_max_def lb_set_def)

lemma is_inf_imp3:
  "\<And>m A. is_inf m A  \<Longrightarrow>  (\<And>l. (\<And>a. a \<in> A \<Longrightarrow> l \<le> a) \<Longrightarrow> l \<le> m)"
  by (simp add: is_max_iff is_inf_def lb_set_mem_iff)

lemma is_inf_if1:
  "\<And>m A. (is_max m (lb_set A)) \<Longrightarrow> is_inf m A"
  by (simp add: is_inf_def)

lemma is_inf_if2:
  "\<And>m A.  m \<in> (lb_set A) \<Longrightarrow>  (\<And>l. (\<And>a. a \<in> A \<Longrightarrow> l \<le> a) \<Longrightarrow> l \<le> m) \<Longrightarrow> is_inf m A"
  by (simp add: is_inf_if1 is_max_iff lb_set_mem_iff)

lemma is_inf_if3:
  "\<And>m A. (\<And>a. a \<in> A \<Longrightarrow> m \<le> a) \<Longrightarrow>  (\<And>l. (\<And>a. a \<in> A \<Longrightarrow> l \<le> a) \<Longrightarrow> l \<le> m) \<Longrightarrow> is_inf m A"
  by (simp add: is_inf_if2 lb_set_elm)

lemma is_inf_unique:
  "\<And>(A::'a::order set) m1 m2. is_inf m1 A \<Longrightarrow> is_inf m2 A \<Longrightarrow> m1=m2"  
  by (simp add: is_inf_def max_unique)

lemma if_has_inf_unique:
  assumes "has_inf (A::'a::order set)"
  shows "\<exists>!m. is_inf m A"
  using assms has_inf_def if_has_max_max_unique is_inf_def by blast

lemma is_min_is_inf:
  "\<And>A m.  is_min m A \<Longrightarrow> is_inf m A"
  by (simp add: is_inf_if2 is_min_imp)

lemma has_min_has_inf:
  "\<And>A.  has_min A \<Longrightarrow> has_inf A"
  by (meson has_inf_def has_max_iff2 if_has_min_min_unique is_inf_def is_min_is_inf)

lemma has_inf_in_imp_inf:
  assumes "has_inf_in A UNIV"
  shows "has_inf A"
  by (metis assms has_inf_def has_inf_in_def lb_set_in_lb_univ)

lemma has_inf_imp_inf_in:
  assumes "has_inf A"
  shows "has_inf_in A UNIV"
  by (metis assms has_inf_def has_inf_in_def lb_set_in_lb_univ)

lemma has_max_lb:
  assumes A0:"has_max (lb_set_in (A::'a::order set) B)"
  shows "is_inf_in (InfIn A B) A B"
  by (simp add: assms has_inf_in_def infin_is_inf)

lemma inf_is_inf:
  assumes A0:"has_inf (A::'a::order set)"
  shows "is_inf (InfUn A) A"
proof-
  obtain m where A1:"m = InfUn A"
    by simp
  have B0:"is_inf m A"
    by (metis A1 InfUn_def assms if_has_inf_unique the_equality)
  show ?thesis
    using A1 B0 by blast
qed

lemma complete_semilattice_inf_has_min:
  fixes X::"'a::order set"
  assumes "X \<noteq> {} \<and> is_inf_complete X"
  shows "has_min X \<and> (is_min (InfIn X X) X)"
  using assms inf_complete_has_min is_min_imp_has_min by blast

lemma complete_semilattice_sup_has_max:
  fixes X::"'a::order set"
  assumes "X \<noteq> {} \<and> is_sup_complete X"
  shows "has_max X \<and> (is_max (SupIn X X) X)"
  using assms is_max_imp_has_max sup_complete_has_max by blast


lemma complete_semilattice_inf_has_min2:
  "has_min (UNIV::'a::complete_semilattice_inf set)"
  by (metis CInf_lower PartialOrders.min_bot UNIV_I empty_not_UNIV)

lemma complete_semilattice_sup_has_max2:
  "has_max (UNIV::'a::complete_semilattice_sup set)"
  by (metis CSup_upper PartialOrders.max_top UNIV_I ex_in_conv)


lemma complete_semilattice_inf_is_inf:
  "\<And>(A::'a::complete_semilattice_inf set). A \<noteq> {} \<Longrightarrow> (is_inf (Inf A) A)"
  by (simp add: CInf_greatest CInf_lower is_inf_if3)

lemma complete_semilattice_inf_is_inf_in:
  "\<And>(A::'a::complete_semilattice_inf set). A \<noteq> {} \<Longrightarrow> (is_inf_in (Inf A) A UNIV)"
  by (simp add: CInf_greatest CInf_lower is_inf_in_if3)

lemma complete_semilattice_infun_is_inf:
  "\<And>(A::'a::complete_semilattice_inf set). A \<noteq> {} \<Longrightarrow> (is_inf (InfUn A) A)"
  by (meson complete_semilattice_inf_is_inf has_inf_def inf_is_inf is_inf_def is_max_imp_has_max)

lemma complete_semilattice_infin_is_inf:
  "\<And>(A::'a::complete_semilattice_inf set). A \<noteq> {} \<Longrightarrow> (is_inf (InfIn A UNIV) A)"
  by (metis complete_semilattice_inf_is_inf complete_semilattice_inf_is_inf_in is_inf_in_inf_eq)

lemma complete_semilattice_infin_is_infin:
  "\<And>(A::'a::complete_semilattice_inf set). A \<noteq> {} \<Longrightarrow> (is_inf_in (InfIn A UNIV) A UNIV)"
  by (simp add: complete_semilattice_infin_is_inf is_inf_imp1 is_inf_in_iff lb_set_in_univ_absorb)

lemma complete_semilattice_infin_existence:
  "\<And>(A::'a::complete_semilattice_inf set). A \<noteq> {} \<Longrightarrow> has_inf_in A UNIV"
  by (metis complete_semilattice_infun_is_inf has_inf_in_def has_max_def is_inf_def lb_set_in_lb_univ)

lemma complete_semilattice_inf_existence:
  "\<And>(A::'a::complete_semilattice_inf set). A \<noteq> {} \<Longrightarrow> has_inf A"
  by (simp add: complete_semilattice_infin_existence has_inf_in_imp_inf)

lemma complete_semilattice_inf_greatest:
  fixes A::"'a::complete_semilattice_inf set"
  shows "\<forall>l \<in> lb_set A. A \<noteq> {} \<longrightarrow> l \<le> Inf A"
  by (simp add: CInf_greatest lb_set_mem)

lemma complete_lattice_inf_is_inf:
  fixes A::"'a::complete_lattice set"
  assumes "A \<noteq> {}"
  shows "(is_inf (Inf A) A)"
  by (simp add: Inf_greatest Inf_lower is_inf_if3)

lemma complete_semilattice_infun_eq_inf:
  fixes A::"'a::complete_semilattice_inf set"
  assumes "A \<noteq> {}"
  shows "InfUn A = Inf A"
  by (meson assms complete_semilattice_inf_is_inf complete_semilattice_infun_is_inf is_inf_unique)

lemma complete_semilattice_inf_is_inf2:
  "\<forall>(A::'X::complete_semilattice_inf set). A \<noteq> {} \<longrightarrow> InfUn A = Inf A"
  using complete_semilattice_infun_eq_inf by blast


lemma has_infin_singleton:
  "has_inf_in {x::'a::order} UNIV"
  by (simp add: has_min_has_inf has_min_singleton has_inf_imp_inf_in)


lemma inf_degenerate:  
  "InfUn {} =( top::'a::order_top)"
  apply(simp add:InfUn_def is_inf_def lb_set_degenerate ub_set_in_def is_max_def)
  using top.extremum_unique by force

lemma is_inf_singleton:
  "is_inf (x::'a::order) {x}"
  by (simp add: is_min_is_inf is_min_singleton)

lemma has_inf_singleton:
  "has_inf {x::'a::order}"
  by (simp add: has_inf_in_imp_inf has_infin_singleton)

lemma inf_singleton:
  "InfUn {x::'a::order} = x"
  using has_inf_singleton is_inf_singleton is_inf_unique inf_is_inf by blast

lemma inf_antitone1:
  "\<And>A B. has_inf A \<Longrightarrow> has_inf B \<Longrightarrow> A \<subseteq> B \<Longrightarrow> InfUn B \<le> InfUn A"
  by (meson inf_is_inf is_inf_imp2 is_inf_imp3 subset_eq)

lemma is_inf_inf_eq:
  "\<And>(i::'a::order) A. has_inf A \<Longrightarrow> is_inf i A \<Longrightarrow> (i = InfUn A)"
  by (simp add: inf_is_inf is_inf_unique)

lemma sup_eq_inf_ub:
  fixes A::"'a::order set"
  assumes "has_inf (ub_set A)"
  shows "has_sup A \<and> SupUn A = InfUn(ub_set A)"
proof-
  let ?U="ub_set A"
  let ?i="InfUn ?U"
  have B0:"A \<subseteq> lb_set ?U"
    by (simp add: lb_set_elm subset_eq ub_set_imp)
  have B1:"?i \<in> ub_set A"
    by (meson B0 assms inf_is_inf is_inf_def is_max_iff subset_eq ub_set_mem_iff)
  have B2:"is_min ?i (ub_set A)"
    by (simp add: B1 assms inf_is_inf is_inf_imp1 is_min_if1)
  show ?thesis
    by (metis B2 has_min_def has_sup_def is_sup_def is_sup_sup_eq)
qed

lemma inf_eq_sup_lb:
  fixes A::"'a::order set"
  assumes "has_sup (lb_set A)"
  shows "has_inf A \<and> InfUn A = SupUn(lb_set A)"
proof-
  let ?L="lb_set A"
  let ?s="SupUn ?L"
  have B0:"A \<subseteq> ub_set ?L"
    by (simp add: ub_set_elm subset_eq lb_set_imp)
  have B1:"?s \<in> lb_set A"
    by (meson B0 assms sup_is_sup is_sup_def is_min_iff subset_eq lb_set_mem_iff)
  have B2:"is_max ?s (lb_set A)"
    by (simp add: B1 assms sup_is_sup  is_sup_imp1 is_max_if1)
  show ?thesis
    by (metis B2 has_inf_def has_max_iff2 is_inf_def is_inf_inf_eq)
qed

lemma has_least_imp_inf_eq_least:
  fixes A::"'a::order set"
  assumes A0:"has_min A"
  shows "InfUn A = min A"
  by (metis assms has_min_has_inf if_has_min_min_unique inf_is_inf is_inf_unique is_min_is_inf min_if)


lemma complete_lattice_inf_greatest:
  fixes A::"'a::complete_lattice set"
  shows "\<forall>l \<in> lb_set A. A \<noteq> {} \<longrightarrow> l \<le> Inf A"
  by (simp add: csli.CInf_greatest lb_set_imp)

lemma complete_semilattice_inf_exists_inf:
  "\<And>(A::'a::complete_semilattice_inf set). A \<noteq> {} \<Longrightarrow> has_inf A"
  by (metis complete_semilattice_infun_is_inf has_inf_def has_max_def is_inf_def)

lemma is_inf_imp_glb1:
  "\<And>i A. is_inf i A \<Longrightarrow> is_max i (lb_set A)"
  by (simp add: is_inf_iff)



lemma inf_complete_bounded_sup_eq1:
  fixes A X::"'a::order set"
  assumes A0:"(A \<subseteq> X \<and> ub_set_in A X \<noteq> {})" and
          A1:"has_inf_in (ub_set_in A X) X"
  shows "SupIn A X = InfIn (ub_set_in A X) X"
proof(cases "A = {}")
  case True
  then show ?thesis
    by (metis A1 has_min_iff2 inf_in_min min_if sup_in_degenerate ub_set_in_degenerate)
next
  case False
  define U where "U=ub_set_in A X"
  define I where "I=InfIn U X"
  have B0:"I \<in> U"
  proof-
    have B00:"I \<in> X"
      by (simp add: A1 I_def U_def has_inf_in_in_set)
    have B01:"\<forall>a. a \<in> A \<longrightarrow> a \<le> I"
      by (metis A0 A1 I_def U_def has_inf_in_imp3 subsetD ub_set_in_imp)
    show ?thesis
      by (simp add: B00 B01 U_def ub_set_in_elm)
  qed
  have B1:"\<forall>u. u \<in> U \<longrightarrow> I \<le> u"
    by (simp add: A1 I_def U_def has_inf_in_imp2)
  have B2:"is_sup_in I A X"
    by (metis B0 B1 U_def is_min_if2 is_sup_in_def)
  then show ?thesis
    using I_def U_def is_sup_in_sup_eq by fastforce
qed

lemma sup_complete_bounded_inf_eq1:
  fixes A X::"'a::order set"
  assumes A0:"(A \<subseteq> X \<and>  lb_set_in A X \<noteq> {})" and
          A1:"has_sup_in (lb_set_in A X) X"
  shows "InfIn A X = SupIn (lb_set_in A X) X"
proof(cases "A = {}")
  case True
  then show ?thesis
    by (metis A1 has_max_iff2 inf_in_degenerate lb_set_in_degenerate max_if sup_in_max)
next
  case False
  define L where "L=lb_set_in A X" 
  define S where "S=SupIn L X"
  have B0:"S \<in> L"
  proof-
    have B00:"S \<in> X"
      by (simp add: A1 L_def S_def has_sup_in_in_set)
    have B01:"\<forall>a. a \<in> A \<longrightarrow> S \<le> a"
      using A0 A1 L_def S_def has_sup_in_imp3 lb_set_in_imp by blast
    show ?thesis
      by (simp add: B00 B01 L_def lb_set_in_elm)
  qed
  have B1:"\<forall>l. l \<in> L \<longrightarrow> l \<le> S"
    by (simp add: A1 L_def S_def has_sup_in_imp2)
  have B2:"is_inf_in S A X"
    using B0 B1 L_def is_inf_in_def is_max_if2 by blast
  then show ?thesis
    using L_def S_def is_inf_in_inf_eq by force
qed
  

lemma sup_complete_bounded_inf_eq2:
  fixes X::"'a::order set"
  assumes A0:"is_sup_complete X"
  shows "\<And>A. (A \<subseteq> X \<and>  lb_set_in A X \<noteq> {}) \<longrightarrow> (InfIn A X = SupIn (lb_set_in A X) X)"
  by (metis assms bot.extremum_uniqueI lb_set_in_subset lb_ub_extensive sup_complete_bounded_inf sup_complete_bounded_inf_eq1 sup_in_eq_inf_in_ub ub_set_in_subset)


lemma inf_complete_bounded_sup_eq2:
  fixes X::"'a::order set"
  assumes A0:"is_inf_complete X"
  shows "\<And>A. (A \<subseteq> X \<and>  ub_set_in A X \<noteq> {}) \<longrightarrow> (SupIn A X = InfIn (ub_set_in A X) X)"
  by (metis assms bot.extremum_uniqueI inf_complete_bounded_sup inf_complete_bounded_sup_eq1 inf_in_eq_sup_in_lb lb_set_in_subset ub_lb_extensive ub_set_in_subset)



section MiscResults
(*de Morgans for finite sup and inf in complete boolean algebra*)

context complete_boolean_algebra
begin
lemma finf_complete_lattice_set:
  "\<And>A. (finite A \<and> A \<noteq> {}) \<longrightarrow> -(fInf A) = fSup (uminus ` A)"
  by (simp add: local.finf_complete_lattice local.fsup_complete_lattice local.uminus_Inf)


lemma fsup_complete_lattice_set:
  "\<And>A. (finite A \<and> A \<noteq> {}) \<longrightarrow> -(fSup A) = fInf (uminus ` A)"
  by (simp add: local.finf_complete_lattice local.fsup_complete_lattice local.uminus_Sup)

end




lemma complete_semilattice_sup_lb_imp_inf:
  fixes A::"'a::complete_semilattice_sup set"
  assumes "lb_set A \<noteq> {}"
  shows "has_inf A \<and> InfUn A = Sup(lb_set A)"
  by (simp add: assms complete_semilattice_sup_existence complete_semilattice_supun_eq_sup inf_eq_sup_lb)

lemma complete_semilattice_sup_lb_imp_inf2:
  fixes A::"'a::complete_semilattice_sup set"
  assumes "lb_set A \<noteq> {}"
  shows "has_inf A \<and> InfUn A = SupUn(lb_set A)"
  by (simp add: assms complete_semilattice_sup_is_sup2 complete_semilattice_sup_lb_imp_inf)

lemma ub_set_in_ne_iff:
  "(ub_set_in {a} B) \<noteq> {} \<longleftrightarrow> (\<exists>b \<in> B. a \<le> b)"
  using ub_set_in_singleton by fastforce

lemma lb_set_in_ne_iff:
  "(lb_set_in {a} B) \<noteq> {} \<longleftrightarrow> (\<exists>b \<in> B. a \<ge> b)"
  using lb_set_in_singleton by fastforce

lemma is_cofinal_in_imp:
  "\<And>A B. A is_cofinal_in B \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> (\<exists>b \<in> B. a \<le> b))"
  by (simp add: is_cofinal_in_def)

lemma is_cofinal_in_imp_ub_in_ne:
  "\<And>A B. A is_cofinal_in B \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> (ub_set_in {a} B) \<noteq> {})"
  by (simp add: is_cofinal_in_imp ub_set_in_ne_iff)


lemma is_cofinal_in_if:
  "\<And>A B. (\<And>a. a \<in> A \<Longrightarrow> (\<exists>b \<in> B. a \<le> b)) \<Longrightarrow> A is_cofinal_in B "
  by (simp add: is_cofinal_in_def)

lemma is_cofinal_in_if_ub_in_ne:
  "\<And>A B. (\<And>a. a \<in> A \<Longrightarrow> (ub_set_in {a} B) \<noteq> {}) \<Longrightarrow> A is_cofinal_in B "
  by (simp add: is_cofinal_in_if ub_set_in_ne_iff)



lemma is_inhabited_imp:
  "\<And>X. is_inhabited X \<Longrightarrow> \<exists>x. x \<in> X"
  by (simp add: ex_in_conv is_inhabited_def)

lemma is_downdir_imp:
  assumes "is_downdir X"
  shows "\<And>a b. (a \<in> X \<and> b \<in> X) \<Longrightarrow> (\<exists>c  \<in> X. (c \<le> a) \<and>  (c \<le> b))"
  using assms is_downdir_def by blast

lemma is_upclosed_imp:
  assumes "is_upclosed X"
  shows "\<And>a b. (a \<le> b \<and> a \<in> X) \<Longrightarrow> b \<in> X"
  using assms is_upclosed_def by blast

lemma is_upclosed_in_imp:
  assumes "is_upclosed_in A x"
  shows "(\<And>a b. a \<le> b \<and>  b \<le> x  \<and>  a \<in> A \<longrightarrow>  b \<in> A)"
  using assms is_upclosed_in_def by blast

lemma is_pisystem_imp:
  assumes "is_pisystem X"
  shows "\<And>a b. (a \<in> X \<and> b \<in> X) \<Longrightarrow> (binf a b) \<in> X"
  using assms is_pisystem_def by blast

lemma semilattice_inf_exists_inf:
  fixes a::"'a::semilattice_inf" and b::"'a::semilattice_inf"
  shows "has_inf {a, b}"
proof-
  define c1 where "c1=inf a b"
  have B0:"c1 \<in> lb_set {a, b}"
    by (simp add: c1_def lb_set_mem_iff)
  have B1:"\<forall>l \<in> lb_set {a, b}. l \<le> c1"
    by (simp add: c1_def lb_set_mem_iff)
  have B2:"is_max  c1 (lb_set {a, b})"
    apply (simp add: B0 B1 is_max_def ub_set_mem_iff)
    by (simp add: B1 ub_set_in_elm)
  have B3:"is_inf c1 {a, b}"
    by (simp add: B2 is_inf_iff)
  have B4:"has_inf {a, b}"
    using B2 has_inf_def has_max_iff2 by auto
  show ?thesis
    by (simp add: B4)
qed


lemma semilattice_inf_has_inf:
  fixes A::"'a::semilattice_inf set"
  assumes A0:"finite A" and
          A1:"A \<noteq> {}"
  shows "has_inf A"
proof-
  define i where "i=fInf A"
  have B0:"i \<in> lb_set A"
    by (simp add: A0 i_def lb_set_mem_iff semilattice_inf_class.coboundedI)
  have B1:"\<forall>l. l \<in> lb_set A \<longrightarrow> l \<le> i"
    by (simp add: A0 A1 finite_inf_greatest i_def lb_set_mem_iff)
  have B0:"is_inf i A"
    by (simp add: B0 B1 is_inf_def is_max_iff)
  show "has_inf A"
    using B0 has_inf_def has_max_iff2 is_inf_def by blast
qed


lemma semilattice_sup_has_sup:
  fixes A::"'a::semilattice_sup set"
  assumes A0:"finite A" and
          A1:"A \<noteq> {}"
  shows "has_sup A"
proof-
  define s where "s=fSup A"
  have B0:"s \<in> ub_set A"
    by (simp add: A0 s_def semilattice_sup_class.coboundedI ub_set_elm)
  have B1:"\<forall>u. u \<in> ub_set A \<longrightarrow> s \<le> u"
    by (simp add: A0 A1 s_def ub_set_mem_iff upper_bounded_iff)
  have B0:"is_sup s A"
    by (simp add: B0 B1 is_min_if2 is_sup_if1)
  show "has_sup A"
    using B0 has_sup_def is_min_imp_has_min is_sup_imp_lub by blast
qed

lemma semilattice_inf_finf_eq:
  fixes A::"'a::semilattice_inf set"
  assumes A0:"finite A" and
          A1:"A \<noteq> {}"
  shows " InfUn A = fInf A"
proof-
  have B0:"is_inf (InfUn A) A"
    by (simp add: A0 A1 inf_is_inf semilattice_inf_has_inf)
  have B1:"is_inf (fInf A) A"
    by (simp add: A0 A1 is_inf_if3 semilattice_inf_class.boundedI semilattice_inf_class.coboundedI)
  show "InfUn A = fInf A"
    using B0 B1 is_inf_unique by blast
qed


lemma semilattice_sup_fsup_eq:
  fixes A::"'a::semilattice_sup set"
  assumes A0:"finite A" and
          A1:"A \<noteq> {}"
  shows " SupUn A = fSup A"
proof-
  have B0:"is_sup (SupUn A) A"
    by (simp add: A0 A1 semilattice_sup_has_sup sup_is_sup)
  have B1:"is_sup (fSup A) A"
    by (simp add: A0 A1 finite_sup_greatest is_sup_if3 semilattice_sup_class.coboundedI)
  show "SupUn A = fSup A"
    using B0 B1 is_sup_unique by blast
qed
  


lemma semilattice_inf_finf_eq_small_inf:
  fixes a::"'a::semilattice_inf" and b::"'a::semilattice_inf"
  shows "inf a b = InfUn {a, b}"
  by (simp add: semilattice_inf_finf_eq)

lemma semilattice_inf_binf_eq_inf:
  fixes a::"'a::semilattice_inf" and b::"'a::semilattice_inf"
  shows "inf a b = binf a b"
  by (simp add: binf_def semilattice_inf_finf_eq)


lemma semilattice_sup_fsup_eq_small_inf:
  fixes a::"'a::semilattice_sup" and b::"'a::semilattice_sup"
  shows "sup a b = SupUn {a, b}"
  by (simp add: semilattice_sup_fsup_eq)

lemma semilattice_sup_bsup_eq_sup:
  fixes a::"'a::semilattice_sup" and b::"'a::semilattice_sup"
  shows "sup a b = bsup a b"
  by (simp add: bsup_def semilattice_sup_fsup_eq)

lemma fpow_ne_imp:
  "A \<in> Fpow_ne X \<Longrightarrow> (finite A) \<and> (A \<noteq> {}) \<and> (A \<subseteq> X)"
  by (simp add: Fpow_Pow_finite)


lemma fpow_ne_if:
  " (finite A) \<and> (A \<noteq> {}) \<and> (A \<subseteq> X) \<Longrightarrow> A \<in> Fpow_ne X "
  by (simp add: Fpow_Pow_finite)

lemma finite_subcover_imp:
  "is_finite_subcover S A x \<Longrightarrow> (S \<subseteq> A) \<and> (S \<noteq> {}) \<and> (finite S)"
  using fpow_ne_imp is_finite_subcover_def by blast

lemma finite_subcover_imp2:
  "is_finite_subcover S A x \<Longrightarrow> S \<in> Fpow_ne A"
  using fpow_ne_imp is_finite_subcover_def by blast


lemma is_pi_system_imp:
  fixes X::"'a::semilattice_inf set"
  shows "is_pisystem X \<longleftrightarrow> (\<forall>a b. a \<in> X  \<longrightarrow> b \<in> X \<longrightarrow> (inf a b)  \<in> X)"
  by (simp add: is_pisystem_def semilattice_inf_binf_eq_inf)

lemma downdir_inf:
  fixes X::"'X::semilattice_inf set"
  assumes A0:"is_downdir X" and A1:"is_upclosed X"
  shows "\<And>(a::'X) b. (a \<in> X \<and> b \<in> X) \<longrightarrow> ((inf a b) \<in> X)"
proof
  fix a b assume A2:"(a \<in> X \<and> b \<in> X)"
  obtain c where A3:"c \<in> X \<and> (c \<le> a) \<and> (c \<le> b)"
    using A0 A2 is_downdir_imp by blast
  have B0:"c \<le> (inf a b)"
     by (simp add: A3)
  show "(inf a b) \<in> X"
    using A1 A3 B0 is_upclosed_imp by blast
qed

lemma downdir_up_pisystem:
  fixes X::"'X::semilattice_inf set"
  assumes "is_upclosed X"
  shows "(is_downdir X) \<longleftrightarrow> (is_pisystem X)"
proof
  let ?L="(is_downdir X)" let ?R="(is_pisystem X)"
  assume AL:"?L"
  show "?R"
    by (simp add: AL assms downdir_inf is_pi_system_imp)
  next
  let ?L="(is_downdir X)" let ?R="(is_pisystem X)"
  assume AR:"?R"
  show "?L"
  proof-
    have ARB0:"\<And>a b. (a \<in> X \<and> b \<in> X) \<longrightarrow> (\<exists>c  \<in> X. (c \<le> a) \<and>  (c \<le> b))"
    proof
      fix a b assume ARA0:"(a \<in> X \<and> b \<in> X)"
      have ARB1:"(inf a b) \<in> X"
        using AR ARA0 is_pi_system_imp by auto
      have ARB2:"(inf a b) \<le> a \<and> (inf a b) \<le> b"
        by simp 
      show "(\<exists>c  \<in> X. (c \<le> a) \<and>  (c \<le> b))"
        using ARB1 ARB2 by blast
    qed
    show ?thesis
      by (simp add: ARB0 is_downdir_def)
  qed
qed

lemma infs_eq:
  assumes A0:"finite F"
  shows "inf x (fInf F) = fInf {x, fInf F}"
proof-
  let ?R="fInf {x, fInf F}"
  let ?L="inf x (fInf F)"
  have B0:"?R \<le> x \<and> ?R \<le> fInf F"
    by simp
  have B1:"?L \<le> ?R"
    by simp
  have B2:"?L \<le> x \<and> ?L \<le> fInf F"
    by simp
  have B3:"?R \<le> ?L"
    by (simp add: B0)
  have B4:"?L = ?R"
    by simp
  show ?thesis
    using B4 by blast
qed

lemma infs_insert:
  assumes "finite F \<and> F \<noteq> {}"
  shows "fInf {x, fInf F} = fInf (insert x F)"
proof-
  have B0:"\<forall>y \<in> (insert x F). fInf {x, fInf F} \<le> y"
    by (metis assms finite.insertI infs_eq semilattice_inf_class.coboundedI semilattice_inf_class.insert)
  have B1:"\<forall>y \<in>  (insert x F).  fInf (insert x F) \<le> y"
    using B0 assms by auto
  have B2:"fInf {x, fInf F} \<le> fInf (insert x F)"
    using assms semilattice_inf_class.insert by fastforce
  have B3:"finite (insert x F) \<and> (insert x F) \<noteq> {}"
    by (simp add: assms)
  have B4:" finite {x, fInf F} \<and>  {x, fInf F} \<noteq> {}"
    by simp
  have B5:"\<forall>y \<in> {x, fInf F}. (fInf (insert x F)) \<le> y"
    by (simp add: B1 assms semilattice_inf_class.finite_inf_greatest)
  have B6:"fInf (insert x F) \<le> fInf {x, fInf F}"
    by (simp add: B5)
  show ?thesis
    using B2 B6 order_antisym_conv by blast
qed
  

lemma finite_meet_in_set:
  fixes C::"'a::semilattice_inf set"
  assumes A0: "\<And>a1 a2. a1 \<in> C \<Longrightarrow> a2 \<in> C \<Longrightarrow> (inf a1 a2) \<in> C" and 
          A1:"finite E" and
          A2:"E \<noteq> {}" and
          A3:"E \<subseteq> C"
  shows "(fInf E) \<in> C"
  using A1 A2 A3 
  proof (induct E rule: finite_ne_induct)
    case (singleton x)
    then show ?case
    proof-
      have S0:"fInf {x} \<le> x"
        by simp
      have S1:"x \<le> x"
        by simp
      have S2:"x \<le> fInf {x}"
        by simp
      have S3:"fInf {x} = x"
        by simp
      show S4:"fInf {x} \<in> C"
        using S3 singleton by force
    qed
  next
    case (insert x F)
    have P0:"x \<in> C"
      using insert.prems by auto
    have P1: "F \<subseteq> C" 
      using insert.prems by auto
    have P2:"inf x (fInf F) \<in> C"
      by (simp add: A0 P0 P1 insert.hyps(4))
    have P4:"fInf (insert x F) = inf x (fInf F)"
      by (simp add: insert.hyps(1) insert.hyps(2))
    then show ?case
      by (simp add: P2 P4)
qed



lemma pi_system_then_fc:
  fixes X::"'X::semilattice_inf set"
  assumes A0:"is_pisystem X"
  shows "(\<forall>F. F \<noteq> {} \<longrightarrow> finite F \<longrightarrow> F  \<subseteq> X \<longrightarrow> (fInf F) \<in> X)"
proof-
  have B0:"\<And>a1 a2. a1 \<in> X \<Longrightarrow> a2 \<in> X \<Longrightarrow> (inf a1 a2) \<in> X"
    by (simp add: assms is_pisystem_imp semilattice_inf_binf_eq_inf)
  have B1:"\<And>F. (F \<noteq> {}) \<and> (finite F) \<and> (F \<subseteq> X) \<longrightarrow> (fInf F) \<in> X"
  proof
    fix F assume A1:"(F \<noteq> {}) \<and> (finite F) \<and> (F \<subseteq> X) "
    show "(fInf F) \<in> X"
      by (simp add: A1 B0 finite_meet_in_set)
  qed
  show ?thesis
    using B1 by presburger
qed


lemma upclosed_in_lattice_iff:
   fixes X::"'X::lattice set"
  assumes "X \<noteq> {}"
  shows "is_upclosed X \<longleftrightarrow> (\<forall>x z. x \<in> X \<longrightarrow> (sup x z) \<in> X)"
  by (metis inf_sup_ord(3) is_upclosed_def sup.commute sup.orderE)

lemma fpow_ne_singleton:
  "x \<in> A \<Longrightarrow> {x} \<in> Fpow_ne A"
  by (meson empty_subsetI finite.emptyI finite_insert fpow_ne_if insert_not_empty insert_subset)

lemma fpow_ne_union:
  assumes "X \<noteq> {}" and "EF \<noteq> {}" and "finite EF" and "\<forall>F \<in> EF. F \<in> Fpow_ne X"
  shows "(\<Union>EF) \<in> Fpow_ne X"
  by (metis Sup_le_iff all_not_in_conv assms(2) assms(3) assms(4) empty_Union_conv finite_Union fpow_ne_if fpow_ne_imp) 

lemma covers_imp:
  "\<And>A b. covers A b \<Longrightarrow> A \<noteq> {} \<and> (\<forall>a. a \<in> A \<longrightarrow> b \<le> a)"
  by (simp add: covers_def lb_set_mem_iff)

lemma covers_if:
  "\<And>A b.  A \<noteq> {} \<and> (\<forall>a. a \<in> A \<longrightarrow> b \<le> a) \<Longrightarrow> covers A b"
  by (simp add: covers_def lb_set_mem_iff)


lemma is_finite_subcover_imp1:
  "\<And>S A b. is_finite_subcover S A b \<Longrightarrow> (\<forall>s. s \<in> S \<longrightarrow> b \<le> s)"
  by (simp add: is_finite_subcover_def lb_set_mem_iff)

lemma is_finite_subcover_imp2:
  "\<And>S A b. is_finite_subcover S A b \<Longrightarrow> (S \<subseteq> A \<and> S \<noteq> {} \<and> finite S)"
  by (simp add: finite_subcover_imp)

lemma is_finite_subcover_if:
  "\<And>S A b. (S \<subseteq> A \<and> S \<noteq> {} \<and> finite S) \<and>  (\<forall>s. s \<in> S \<longrightarrow> b \<le> s) \<Longrightarrow>  is_finite_subcover S A b"
  by (metis fpow_ne_if imp_in_lower_bounds is_finite_subcover_def)

lemma is_compact_imp:
  "\<And>A b.  is_compact b \<Longrightarrow> (covers A b) \<Longrightarrow>  (\<exists>S. is_finite_subcover S A b)"
  using is_compact_def by auto

lemma is_compact_if:
  "\<And>b.  (\<And>A.  (covers A b) \<Longrightarrow>  (\<exists>S. is_finite_subcover S A b))  \<Longrightarrow>  is_compact b"
  using is_compact_def by auto

lemma directed_imp1:
  "is_directed D \<Longrightarrow> D \<noteq> {}"
  by (simp add: is_directed_def)

lemma directed_imp2:
  "\<And>D A. is_directed D \<Longrightarrow> A \<in> Fpow_ne D \<Longrightarrow>  (\<exists>u \<in> D. u \<in> ub_set A)"
  by (simp add: is_directed_def)

lemma directed_if:
  "\<And>D. (\<And>A.  A \<in> Fpow_ne D \<Longrightarrow>  (\<exists>u \<in> D. u \<in> ub_set A)) \<Longrightarrow> D \<noteq> {} \<Longrightarrow> is_directed D"
  by (simp add: is_directed_def)


lemma directed_covering_imp:
  "\<And>a D. directed_covering a D \<Longrightarrow> (covers D a) \<and> is_directed D"
  by (simp add: directed_covering_def)

lemma directed_covering_if:
  "\<And>a D. (covers D a) \<and> is_directed D \<Longrightarrow> directed_covering a D "
  by (simp add: directed_covering_def)

lemma is_compactly_generated_imp:
  "\<And>X. is_compactly_generated  X \<Longrightarrow>  x \<in> X \<Longrightarrow> (\<exists>Cx. (\<forall>c \<in> Cx. is_compact c) \<and> (is_sup x Cx))"
  using is_compactly_generated_def by blast

lemma is_compactly_generated_if:
  "\<And>X. (\<And>x.  x \<in> X \<Longrightarrow> (\<exists>Cx. (\<forall>c \<in> Cx. is_compact c) \<and> (is_sup x Cx))) \<Longrightarrow>  is_compactly_generated  X "
  using is_compactly_generated_def by blast


lemma compact_lattice_imp:
  fixes c::"'a::order"
  assumes A0:"is_compact c"
  shows "\<And>D. directed_covering c D \<longrightarrow> (\<exists>d \<in> D. c \<le> d)"
proof
  fix D assume A1:"directed_covering c D"
  have B0:"(covers D c) "
    using A1 directed_covering_def by auto
  obtain S where A2:"is_finite_subcover S D c"
    using B0 assms is_compact_def by blast
  have B1:"(S \<subseteq> D) \<and> (S \<noteq> {}) \<and> (finite S)"
    using A2 is_finite_subcover_imp2 by blast
  obtain d where A3:"d \<in> D \<and>  d \<in> ub_set S"
    by (meson A1 A2 directed_covering_imp directed_imp2 is_finite_subcover_def)
  show "(\<exists>d \<in> D. c \<le> d)"
    by (meson A3 B0 covers_def lb_set_mem)
qed


lemma compact_lattice_if:
  fixes c::"'a::complete_lattice"
  assumes A0:"\<And>D. directed_covering c D \<longrightarrow> (\<exists>d \<in> D. c \<le> d)"
  shows "is_compact c"
proof-
  have B0:"(\<And>A. (covers A c) \<longrightarrow> (\<exists>S. is_finite_subcover S A c))"
  proof
    fix A assume A1:"covers A c"
    define B where A2:"B \<equiv> {x. (\<exists>S \<in> Fpow_ne A. (x=fSup S))}"
    have B1:"is_directed B"
    proof-
      have B2:"B \<noteq> {}"
      proof-
        have A3:"A \<noteq> {}"
          using A1 covers_def by blast
        obtain S where A4:"S \<in> Fpow_ne A"
          by (metis A3 empty_subsetI ex_in_conv finite.intros(1) finite_insert fpow_ne_if insert_subset)
        show ?thesis
          using A2 A4 by blast
      qed
      have B3:"\<And>S. (S \<in> Fpow_ne B) \<longrightarrow> (\<exists>u \<in> B.  u \<in> ub_set S)"
      proof
        fix S assume A5:"S \<in> Fpow_ne B"
        have B4:"\<forall>s \<in> S. \<exists>F. F \<in> Fpow_ne A \<and> s=fSup F"
          using A2 A5 fpow_ne_imp by auto
        define f where "f=(\<lambda>s. SOME F. (F \<in> Fpow_ne A  \<and> s=fSup F) )"
        define fS where "fS=\<Union>(f`S)"
        have B5:"\<forall>s \<in> S.  (f s) \<in> Fpow_ne A \<and> s=fSup (f s)"
          by (metis (mono_tags, lifting) B4 f_def someI_ex)
        have B50:"finite (f`S) \<and> (f`S \<noteq> {})"
          using A5 fpow_ne_imp by blast
        have B6:"fS \<in> Fpow_ne A"
          by (metis A1 B5 B50 covers_def fS_def fpow_ne_union imageE)
        have B7:"fSup fS \<in> B"
          using A2 B6 by blast
        have B8:"\<forall>s \<in> S. f s \<subseteq> fS"
          by (simp add: SUP_upper fS_def)
        have B9:"\<forall>s \<in> S. (fSup fS) \<ge> fSup (f s)"
          by (metis B5 B6 B8 fpow_ne_imp semilattice_sup_class.subset_imp)
        have B10:"\<forall>s \<in> S. s \<le> fSup fS"
        proof
          fix s assume A6:"s \<in> S"
          have B100:"(fSup fS) \<ge> fSup (f s)"
            by (simp add: A6 B9)
          have B101:"fSup (f s) = s"
            using A6 B5 by auto
           show "s \<le> fSup fS"
             using B100 B101 by auto
        qed
        show "\<exists>u \<in> B.  u \<in> ub_set S"
          by (meson B10 B7 ub_set_elm)
      qed
      show ?thesis
        by (simp add: B2 B3 is_directed_def)
    qed
    have B11:"A \<subseteq> B"
    proof
      fix x assume A7:"x \<in> A"
      have B12:"{x} \<in> Fpow_ne A  \<and> fSup {x} = x"
        using A7 fpow_ne_singleton by force
      show "x \<in> B"
        by (metis (mono_tags, lifting) A2 B12 CollectI) 
    qed
    have B13:"Sup A \<le> Sup B"
      by (simp add: B11 Sup_subset_mono)
    have B14:"c \<le> Sup B"
      by (metis A1 B13 Inf_le_Sup complete_lattice_inf_greatest covers_def dual_order.trans)
    obtain b where A8:"b \<in> B \<and> c \<le> b"
      by (metis A1 B11 covers_def lb_set_mem_iff subset_empty subset_eq)
    obtain S where A9:"S \<in> Fpow_ne A \<and>  fSup S = b"
      using A2 A8 by blast
    have B15:"c \<le> fSup S"
      by (simp add: A8 A9)
    have B16:"fSup S = Sup S"
      by (metis A9 complete_lattice_class.fsup_complete_lattice fpow_ne_imp)
    have B16:"is_finite_subcover S A c"
      by (metis A1 A9 Int_iff covers_def fpow_ne_imp inf.absorb_iff2 is_finite_subcover_if lb_set_mem_iff)
    show "(\<exists>S. is_finite_subcover S A c)"
      using B16 by blast
  qed
  show ?thesis
    by (simp add: B0 is_compact_def)
qed


lemma top_is_meet_irreducible:
  assumes A0:"\<forall>(x::'a::{order,top}). x \<le> top"
  shows "\<not>(is_meet_reducible (top::'a::{order, top}))"
proof(rule ccontr)
  assume A1:"\<not>\<not>((is_meet_reducible (top::'a::{order, top})))"
  have B1:"(\<exists>(A::('a::{order, top} set)). (A \<noteq> {}) \<and> (top \<notin> A) \<and> (is_inf top A))"
    using A1 is_meet_reducible_def by auto
  obtain A where A2:"((A::('a::{order, top} set)) \<noteq> {}) \<and> (top \<notin> A) \<and> (is_inf top A)"
    using B1 by force
  have B2:"top \<in> lb_set A"
    using A2 is_inf_def is_max_iff by auto
  show False
    by (metis A2 B2 assms dual_order.eq_iff ex_in_conv lb_set_mem_iff)
qed


lemma bot_is_meet_irreducible:
  assumes A0:"\<forall>(x::'a::{order,bot}). bot \<le> x"
  shows "\<not>(is_join_reducible (bot::'a::{order, bot}))"
proof(rule ccontr)
  assume A1:"\<not>\<not>((is_join_reducible (bot::'a::{order, bot})))"
  have B1:"(\<exists>(A::('a::{order, bot} set)). (A \<noteq> {}) \<and> (bot \<notin> A) \<and> (is_sup bot A))"
    using A1 is_join_reducible_def by auto
  obtain A where A2:"((A::('a::{order, bot} set)) \<noteq> {}) \<and> (bot \<notin> A) \<and> (is_sup bot A)"
    using B1 by force
  have B2:"bot \<in> ub_set A"
    by (meson A2 is_min_iff is_sup_iff)
  show False
    by (metis A2 B2 assms dual_order.eq_iff ex_in_conv ub_set_mem_iff)
qed

lemma meet_irreducible_in_complete_lattice_iff:
  fixes m::"'a::complete_lattice"
  assumes A0:"m \<noteq> top"
  shows "\<not>(is_meet_reducible m) \<longleftrightarrow> (m < Inf {x. m < x})"
proof
  assume A1:"\<not>(is_meet_reducible m)"
  have B0:"{x. m < x} \<noteq> {}"
    using assms top.not_eq_extremum by auto
  have B1:"m \<le> Inf {x. m < x}"
    using le_Inf_iff order_le_less by auto
  show "(m < Inf {x. m < x})"
  proof-
    let ?L="{x. m <x}"
    have B5:"\<not>(m < Inf {x. m < x}) \<longrightarrow> \<not>\<not>(is_meet_reducible m)"
    proof
    assume A2:"\<not>(m < Inf {x. m < x})"
      have B2:"m \<ge> Inf {x. m <x}"
        using A2 B1 by auto
      have B3:"m = Inf {x. m <x}"
        using A2 B1 by auto
      have B4:"m \<notin> {x. m < x}"
        by simp
      have B5:"is_inf (Inf ?L) ?L"
      proof-
        have B50:"Inf ?L \<in> lb_set ?L"
          by (meson Inf_lower imp_in_lower_bounds)
        have B51:"is_max (Inf ?L) (lb_set ?L)"
          by (meson B0 B50 complete_lattice_inf_greatest is_max_iff)
        show ?thesis
          by (simp add: B51 is_inf_if1)
      qed
      have B3:"(is_meet_reducible m)"
        by (metis B0 B3 B4 B5 is_meet_reducible_def)
      show "\<not>\<not>(is_meet_reducible m)"
        by (simp add: B3)
      qed
    show ?thesis
      using A1 B5 by auto
  qed
  next
  assume A3:"(m < Inf {x. m < x})"
  show "\<not>(is_meet_reducible m)"
  proof-
     have B6:"(is_meet_reducible m) \<longrightarrow> \<not>(m < Inf {x. m < x})"
     proof
      assume A4:"is_meet_reducible m"
      obtain A where A5:"A \<noteq> {} \<and> m \<notin> A \<and> is_inf m A"
        using A4 is_meet_reducible_def by auto
      have B7:"\<forall>x \<in> A. m < x"
        by (metis A5 complete_lattice_inf_is_inf csli.CInf_lower is_inf_unique order_le_less)
      show " \<not>(m < Inf {x. m < x})"
        by (metis A5 B7 Inf_superset_mono complete_lattice_inf_is_inf is_inf_unique leD mem_Collect_eq subsetI)
      qed
    show ?thesis
      using A3 B6 by auto
  qed 
qed




lemma kt_fixed:
  fixes f::"'a::complete_lattice \<Rightarrow> 'a::complete_lattice"
  assumes A0:"is_isotone f"
  defines "A \<equiv> {x. (f x) \<le> x}" and "P \<equiv> {x. f x = x}"
  shows "(\<exists>a. f a = a) \<and> (\<exists>l. is_min l P) "
proof-
  define a where "a = Inf A"
  have B0:"top \<in> A"
    by (simp add: A_def)
  have B1:"A \<noteq> {}"
    using B0 by auto
  have B2:"\<forall>x \<in> A. a \<le> x"
    by (simp add: Inf_lower a_def)
  have B3:"\<forall>x \<in> A. f a \<le> f x"
    using A0 B2 is_isotone_def by auto
  have B4:"\<forall>x \<in> A. f x \<le> x"
    by (simp add: A_def)
  have B5:"\<forall>x \<in> A. f a \<le> x"
    by (metis B3 B4 order_trans)
  have B6:"f a \<le> a"
    by (metis B5 Inf_greatest a_def)
  have B7:"(f \<circ> f)(a) \<le> f a"
    using A0 B6 is_isotone_def by auto
  have B8:"(f a) \<in> A"
    using A_def B7 by auto
  have B9:"a \<le> f a"
    by (simp add: B2 B8)
  have B10:"f a = a"
    by (simp add: B6 B9 dual_order.antisym)
  have B11:"P \<subseteq> A"
    by (simp add: A_def Collect_mono_iff P_def)
  have B12:"\<forall>x \<in> P. a \<le> x"
    using B11 B2 by blast
  have B13:"a \<in> A"
    using B10 B8 by auto
  show ?thesis
    by (metis (mono_tags, lifting) B10 B12 P_def is_min_iff mem_Collect_eq)
qed

lemma isotone_inf_leq_inf_isotone:
  fixes A::"'a::order set" and
        f::"'a::order \<Rightarrow> 'b::order"
  assumes A0:"is_isotone f" and
          A1:"has_inf A" and
          A2:"has_inf (f`A)"
  shows "f (InfUn A) \<le> InfUn (f`A)"
proof-
  have B0:"\<forall>x. x \<in> A \<longrightarrow> f (InfUn A) \<le> (f x)"
    using A0 A1 inf_is_inf is_inf_imp2 is_isotone_def by blast
  show ?thesis
    by (metis (mono_tags, lifting) A2 B0 image_iff inf_is_inf is_inf_imp3)
qed
    
lemma principle_filter_anti1:
  "\<And>(x1::'a::order) x2 X. x1 \<le> x2 \<Longrightarrow> (principal_filter_in x2 X) \<subseteq>  (principal_filter_in x1 X)"
  by (simp add: order_trans subset_eq ub_set_in_mem_iff)

lemma principle_filter_anti2:
  "\<And>(x1::'a::order) x2. (principal_filter_in x2 UNIV) \<subseteq>  (principal_filter_in x1 UNIV) \<Longrightarrow>  x1 \<le> x2"
  by (simp add: order_trans subset_eq ub_set_in_mem_iff)


lemma sup_equiv1:
  "is_sup_in (s::'a::order) A X \<longleftrightarrow> (s \<in> X \<and> (\<forall>u \<in> X. ((\<forall>a \<in> A. a \<le> u) \<longleftrightarrow> (s \<le> u))))" (is "?L \<longleftrightarrow> ?R")
proof
  assume L:?L  show ?R
    by (meson L is_sup_in_imp2 is_sup_in_imp3 is_sup_in_in_set order.trans)
  next
  assume R:?R  show ?L
     by (metis R dual_order.refl is_sup_in_if3)
qed
  
lemma inf_equiv1:
  "is_inf_in (i::'a::order) A X \<longleftrightarrow> (i \<in> X \<and> (\<forall>l \<in> X. ((\<forall>a \<in> A. l \<le> a) \<longleftrightarrow> (l \<le> i))))" (is "?L \<longleftrightarrow> ?R")
proof
  assume L:?L  show ?R
    by (meson L dual_order.trans is_inf_in_imp2 is_inf_in_imp3 is_inf_in_in_set)
  next
  assume R:?R  show ?L
     by (metis R dual_order.refl is_inf_in_if3)
qed



lemma inf_from_sup:
  "(InfUn A)  = (SupUn (lb_set A))"
  by (metis (full_types) Collect_empty_eq Collect_empty_eq_bot InfUn_def SupUn_def has_max_def 
      has_max_has_sup has_min_def has_sup_def inf_eq_sup_lb is_inf_def is_sup_def)

lemma sup_from_inf:
  "(SupUn A)  = (InfUn (ub_set A))"
  by (metis (no_types, lifting) Collect_empty_eq Collect_empty_eq_bot InfUn_def SupUn_def has_inf_def
       has_min_has_inf is_inf_def is_max_imp_has_max is_min_imp_has_min is_sup_iff sup_eq_inf_ub)

lemma inter_complete_lat:
  fixes A::"'a set set" and X::"'a set"
  assumes A0:"A \<subseteq> (Pow X)"
  shows "InfIn A (Pow X) = X \<inter> (\<Inter> A)"
proof-
  define I where "I=X \<inter> (\<Inter> A)"
  have B0:"I \<in> lb_set_in A (Pow X)"
    using I_def lb_set_in_mem_iff by auto
  have B1:"\<forall>l. l \<in> (lb_set_in A (Pow X)) \<longrightarrow> l \<le> I"
    by (simp add: I_def Inf_greatest lb_set_in_mem_iff)
  have B2:"is_inf_in I A (Pow X)"
    by (simp add: B0 B1 is_inf_in_def is_max_if2)
  show ?thesis
    using B2 I_def is_inf_in_inf_eq by blast
qed


lemma empty_inter_is_carrier:
  fixes X::"'a set"
  shows "InfIn {} (Pow X) = X"
  by (simp add: inter_complete_lat)



lemma inf_comp_un_ind:
  fixes F::"'b \<Rightarrow> 'a::order set" and I::"'b set"
  assumes A0:"I \<noteq> {}" and A1:"\<And>i. i \<in> I  \<Longrightarrow> has_inf (F i)" and A2:"has_inf (InfUn`(F`I))"
  shows "(has_inf (\<Union>i \<in> I. F i)) \<and> InfUn (InfUn`(F`I)) = InfUn (\<Union>i \<in> I. F i)"
proof-
  define A where A3:"A=(\<Union>i \<in> I. F i)"
  define G where A4:"G= InfUn`(F`I)"
  have B0:"\<And>i. i \<in> I \<longrightarrow> (F i) \<subseteq> A"
    by (simp add: A3 SUP_upper)
  have B1:"\<And>i. i \<in> I \<longrightarrow> (\<forall>l. l \<in>(lb_set A) \<longrightarrow> l \<le> InfUn (F i))"
    by (meson A1 B0 inf_is_inf is_inf_imp1 is_max_iff lb_set_antitone1 subsetD)
  have B2:"\<And>i. i \<in> I \<longrightarrow> lb_set A \<subseteq> lb_set {(InfUn (F i))}"
    by (simp add: B1 lb_set_mem_iff subset_eq)
  have B3:"lb_set A \<subseteq> lb_set G"
    by (simp add: A4 B1 imp_in_lower_bounds subsetI)
  have B4:"\<And>l. l \<in> lb_set A \<longrightarrow> l  \<le> InfUn G"
    using A2 A4 B3 inf_is_inf is_inf_imp3 lb_set_imp by blast
  have B5:"\<And>a. a \<in> A \<longrightarrow> InfUn G \<le> a"
  proof
    fix a assume A5:"a \<in> A"
    obtain i where A6:"i \<in> I \<and> a \<in> F i"
      using A3 A5 by blast
    have B6:"InfUn (F i) \<le> a"
      using A1 A6 inf_is_inf is_inf_imp2 by blast
    show "InfUn G \<le> a"
      by (metis A2 A4 A6 B6 imageI inf_is_inf is_inf_imp1 lb_set_mem order_trans)
  qed
  have B8:"is_inf (InfUn G) A"
    by (simp add: B4 B5 imp_in_lower_bounds is_inf_if3)
  have B9:"has_inf A"
    using B8 has_inf_def has_max_def is_inf_def by blast
  have B10:"InfUn G = InfUn A"
    by (simp add: B8 B9 is_inf_inf_eq)
  show ?thesis
    using A3 A4 B9 B10 by blast
qed
  
lemma inf_comp_un:
  fixes F::"'a::order set set"
  assumes A0:"F \<noteq> {}" and A1:"\<And>A. A \<in> F \<Longrightarrow> has_inf A" and A2:"has_inf (InfUn`(F))"
  shows "(has_inf (\<Union>F)) \<and> (InfUn (InfUn`(F)) = InfUn (\<Union>F))"
proof-
  define A where A3:"A=\<Union>F"
  define G where A4:"G=InfUn`(F)"
  have B0:"\<And>E. E \<in> F \<Longrightarrow> E \<subseteq> A"
    by (simp add: A3 Union_upper)
  have B1:"\<And>E. E \<in> F \<Longrightarrow> (\<forall>l. l \<in>(lb_set A) \<longrightarrow> l \<le> InfUn (E))"
    by (meson A1 B0 inf_is_inf is_inf_imp1 is_max_iff lb_set_antitone1 subsetD)
  have B2:"\<And>E. E \<in> F \<Longrightarrow> lb_set A \<subseteq> lb_set {(InfUn E)}"
    by (simp add: B1 lb_set_mem_iff subset_eq)
  have B3:"lb_set A \<subseteq> lb_set G"
    by (simp add: A4 B1 imp_in_lower_bounds subsetI)
  have B4:"\<And>l. l \<in> lb_set A \<longrightarrow> l  \<le> InfUn G"
    using A2 A4 B3 inf_is_inf is_inf_imp3 lb_set_imp by blast
  have B5:"\<And>a. a \<in> A \<longrightarrow> InfUn G \<le> a"
  proof
    fix a assume A5:"a \<in> A"
    obtain E  where A6:"E \<in> F \<and> a \<in> E"
      using A3 A5 by blast
    have B6:"InfUn E \<le> a"
      using A1 A6 inf_is_inf is_inf_imp2 by blast
    show "InfUn G \<le> a"
      by (metis A2 A4 A6 B6 imageI inf_is_inf is_inf_imp1 lb_set_mem order_trans)
  qed
  have B8:"is_inf (InfUn G) A"
    by (simp add: B4 B5 imp_in_lower_bounds is_inf_if3)
  have B9:"has_inf A"
    using B8 has_inf_def has_max_def is_inf_def by blast
  have B10:"InfUn G = InfUn A"
    by (simp add: B8 B9 is_inf_inf_eq)
  show ?thesis
    using A3 A4 B9 B10 by blast
qed

lemma sup_comp_un_ind:
  fixes F::"'b \<Rightarrow> 'a::order set" and I::"'b set"
  assumes A0:"I \<noteq> {}" and A1:"\<And>i. i \<in> I  \<Longrightarrow> has_sup (F i)" and A2:"has_sup (SupUn`(F`I))"
  shows "(has_sup (\<Union>i \<in> I. F i)) \<and> SupUn (SupUn`(F`I)) = SupUn (\<Union>i \<in> I. F i)"
proof-
  define A where A3:"A=(\<Union>i \<in> I. F i)"
  define G where A4:"G= SupUn`(F`I)"
  have B0:"\<And>i. i \<in> I \<longrightarrow> (F i) \<subseteq> A"
    by (simp add: A3 SUP_upper)
  have B1:"\<And>i. i \<in> I \<longrightarrow> (\<forall>u. u \<in>(ub_set A) \<longrightarrow> SupUn (F i) \<le> u)"
    by (meson A1 B0 in_mono is_sup_imp3 sup_is_sup ub_set_mem_iff)
  have B2:"\<And>i. i \<in> I \<longrightarrow> ub_set A \<subseteq> ub_set {(SupUn (F i))}"
    by (simp add: B1 ub_set_mem_iff subset_eq)
  have B3:"ub_set A \<subseteq> ub_set G"
    by (simp add: A4 B1 imp_in_upper_bounds subsetI)
  have B4:"\<And>u. u \<in> ub_set A \<longrightarrow> SupUn G \<le> u"
    using A2 A4 B3 sup_is_sup is_sup_imp3 ub_set_imp by blast
  have B5:"\<And>a. a \<in> A \<longrightarrow> a \<le> SupUn G"
  proof
    fix a assume A5:"a \<in> A"
    obtain i where A6:"i \<in> I \<and> a \<in> F i"
      using A3 A5 by blast
    have B6:"a \<le> SupUn (F i)"
      using A1 A6 is_sup_imp2 sup_is_sup by blast
    show "a \<le> SupUn G"
      by (metis A2 A4 A6 B6 dual_order.trans imageI is_sup_imp2 sup_is_sup)
  qed
  have B8:"is_sup (SupUn G) A"
    by (simp add: B4 B5 imp_in_upper_bounds is_sup_if3)
  have B9:"has_sup A"
    using B8 has_sup_def has_min_def is_sup_def by blast
  have B10:"SupUn G = SupUn A"
    by (simp add: B8 B9 is_sup_sup_eq)
  show ?thesis
    using A3 A4 B9 B10 by blast
qed

lemma sup_comp_un:
  fixes F::"'a::order set set"
  assumes A0:"F \<noteq> {}" and A1:"\<And>A. A \<in> F \<Longrightarrow> has_sup A" and A2:"has_sup (SupUn`(F))"
  shows "(has_sup (\<Union>F)) \<and> (SupUn (SupUn`(F)) = SupUn (\<Union>F))"
proof-
  define A where A3:"A=\<Union>F"
  define G where A4:"G=SupUn`(F)"
  have B0:"\<And>E. E \<in> F \<Longrightarrow> E \<subseteq> A"
    by (simp add: A3 Union_upper)
  have B1:"\<And>E. E \<in> F \<Longrightarrow> (\<forall>u. u \<in>(ub_set A) \<longrightarrow> SupUn (E) \<le> u)"
    by (meson A1 B0 in_mono is_sup_imp3 sup_is_sup ub_set_mem_iff)
  have B2:"\<And>E. E \<in> F \<Longrightarrow> ub_set A \<subseteq> ub_set {(SupUn E)}"
    by (simp add: B1 ub_set_mem_iff subset_eq)
  have B3:"ub_set A \<subseteq> ub_set G"
    by (simp add: A4 B1 imp_in_upper_bounds subsetI)
  have B4:"\<And>u. u \<in> ub_set A \<longrightarrow> SupUn G \<le> u"
    using A2 A4 B3 sup_is_sup is_sup_imp3 ub_set_imp by blast
  have B5:"\<And>a. a \<in> A \<longrightarrow> a \<le> SupUn G"
  proof
    fix a assume A5:"a \<in> A"
    obtain E  where A6:"E \<in> F \<and> a \<in> E"
      using A3 A5 by blast
    have B6:"a \<le> SupUn E"
      using A1 A6 is_sup_imp2 sup_is_sup by blast
    show "a \<le> SupUn G"
      by (metis A2 A4 A6 B6 dual_order.trans imageI is_sup_imp2 sup_is_sup)
  qed
  have B8:"is_sup (SupUn G) A"
    by (simp add: B4 B5 imp_in_upper_bounds is_sup_if3)
  have B9:"has_sup A"
    using B8 has_sup_def has_min_def is_sup_def by blast
  have B10:"SupUn G = SupUn A"
    by (simp add: B8 B9 is_sup_sup_eq)
  show ?thesis
    using A3 A4 B9 B10 by blast
qed

end