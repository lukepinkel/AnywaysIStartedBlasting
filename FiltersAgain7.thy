theory FiltersAgain7
  imports Main "./Closures"
begin

(*\strikethrough{6th}7th times the charm*)

(*
TODO

(1). The upclosed set of a topped poset
   (1.1) form a moore collection (dually for ideals) DONE (upsets_moore_family)
   (1.2) form a complete join subsemilattice in the powerset by inclusion - uncertain best way to
         implement the whole "sub" part
   (1.3) The upclosure of E is merely Union of principal filters for each x in E if E is nonempty or
         the singleton containing the top otherwise DONE (up_closure_expression)


(2). The filters on a topped semilattice inf form a moore collection 
  DONE (filter_moore_family)
  (2.1) The closure of a family of filters is described in filter_closure_is_closure
        filter_closure_is_filter 
  (2.2) The supremum of  a family is described in filter_sup_is_ub filter_sup_is_lub
        and via definition in terms of closure by filter_closure_is_filter
  (2.3) The infimum is described in filter_inf_is_filter
(3). The filters on a lattice
  (3.1) form a lattice 
        DONE (instantiation filter:: (lattice) lattice)
  (3.2)complete semilattice sup 
      TODO - the issue is with the definition involving finitary inf for
      arbitrary A
      Sup A = {x. exists S in Pow A.  finite S and S neq {} and Inf S leq x }
      So the finite Inf needed can maybe be constructed using Finite_Set.fold
      or something - maybe extending semilattice_inf? 
      Otherwise the bozo move is with the semilattice_inf_finiteInf defined below
  (3.3)the finite sup is just finite intersection of filters whose elements are finite joins
  (3.4) the arbitrary sup is the upclosure of finite meets for all finite collections  of the union

modularity and distributivity is inherited and in fact the filter lattice is modular iff the 
underlying lattice is and ditto for distributivity
distributivity  means 
  -finite sups are meets of elements from each filter
  -arbitrary sups are  the infs of finitely many elements from the union
  - ultrafilters are prime filters

Every proper filter in a topped distributive lattice is the inf of finer ultrafilters


*)

section Settings
hide_const(open) List.list.Nil
no_notation List.list.Nil ("[]")  
no_notation Cons (infixr "#" 65)

declare [[show_types]]
declare [[show_sorts]]
declare [[show_consts]]

section Definitions
definition is_inhabited::"'a set  \<Rightarrow> bool" where
   "is_inhabited X \<equiv> (X \<noteq> {})"

definition is_downdir::"'a::order set \<Rightarrow> bool" where
   "is_downdir X \<equiv> (\<forall>a b. (a \<in> X) \<longrightarrow> ( b \<in> X) \<longrightarrow> (\<exists>c  \<in> X. (c \<le> a) \<and>  (c \<le> b)))"

definition is_upclosed::"'a::order set \<Rightarrow> bool" where
   "is_upclosed X \<equiv> (\<forall>a b. a \<le> b \<longrightarrow>  a \<in> X \<longrightarrow>  b \<in> X)"

definition is_pisystem::"'a::{order,inf} set \<Rightarrow> bool" where
   "is_pisystem X \<equiv> (\<forall>a b. a \<in> X  \<longrightarrow> b \<in> X \<longrightarrow> (inf a b)  \<in> X)"

definition is_filter::"'a::order set \<Rightarrow> bool" where 
  "is_filter F \<equiv> (is_downdir F \<and> is_upclosed F \<and> is_inhabited F)"

(*this is valid even without top element which is only needed for the degenerate case*)

definition is_lb_set::"'a::order set \<Rightarrow> 'a::order \<Rightarrow> bool"
  where "is_lb_set L a \<equiv> (\<forall>x \<in> L. x \<le>a)"


(*
  this is probably a stupid move here - its likely trivial to reduce finite shit to pairs but
  this should work too lol
 *)
class semilattice_inf_Inf=semilattice_inf+Inf+
  assumes  Finite_Inf_lower: "\<And>x A. finite A \<Longrightarrow>  x \<in> A \<Longrightarrow> Inf A \<le> x" and
           Finite_Inf_greatest: "\<And>z A. finite A \<Longrightarrow> ((\<And>x. x \<in> A \<Longrightarrow> z \<le> x) \<Longrightarrow> z \<le> Inf A)"

 

class bounded_semilattice_inf_top_Inf=semilattice_inf_Inf+order_top

sublocale complete_semilattice_inf \<subseteq> semilattice_inf_Inf Inf inf "(\<le>)" "(<)"
 apply  unfold_locales
  apply (simp add: local.CInf_lower)
  using local.CInf_greatest by blast

sublocale complete_lattice \<subseteq> complete_semilattice_inf Inf inf "(\<le>)" "(<)"
 apply  unfold_locales
  apply (simp add: local.Inf_lower)
  using local.le_Inf_iff by blast


definition filter_closure::"'a::semilattice_inf_Inf set \<Rightarrow> 'a::semilattice_inf_Inf set" where
  "filter_closure A \<equiv> {a. \<exists>S\<in>Pow(A). finite S \<and>  S \<noteq> {} \<and>  Inf S \<le> a}"

definition up_closure::"'a::order set \<Rightarrow> 'a::order set" where
  "up_closure A \<equiv> {x. \<exists>a \<in> A. a \<le> x}"

definition is_prime::"'a::{order, sup} set \<Rightarrow> bool" where
  "is_prime A \<equiv> (\<forall>a. \<forall>b. (sup a b) \<in> A \<longrightarrow> (a \<in> A \<or> b \<in> A))"



definition binary_filter_sup::"'a::semilattice_inf set \<Rightarrow> 'a::semilattice_inf set \<Rightarrow> 'a::semilattice_inf set" where
  "binary_filter_sup A B = {x. \<exists>a \<in> A. \<exists>b \<in> B. inf a b \<le> x}"


definition filter_sup::"'a::semilattice_inf_Inf set set \<Rightarrow> 'a::semilattice_inf_Inf set" where
  "filter_sup EF \<equiv> filter_closure(Sup(EF))"

definition filter_inf::"'a::bounded_semilattice_inf_top set set \<Rightarrow> 'a::bounded_semilattice_inf_top set" where
  "filter_inf EF \<equiv> (if EF={} then {top} else \<Inter>EF)"

definition is_proper::"'a::order set \<Rightarrow> bool" where
  "is_proper F \<equiv> F \<noteq> UNIV"


definition is_pfilter::"'a::order set \<Rightarrow>  bool" where
  "is_pfilter F \<equiv> (is_filter F) \<and> (is_proper F)"

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


definition finer_upsets::"'a::order set \<Rightarrow> 'a::order set set" where
  "finer_upsets A = {U. is_upclosed U \<and> (A \<subseteq> U)}"


definition moore_upclosure::"'a::order_top set \<Rightarrow> 'a::order_top set" where
  "moore_upclosure A = (if A={} then {top} else up_closure A)"


definition is_chain::"'X::order set \<Rightarrow> bool" where
  "is_chain A \<equiv> (\<forall>a1 \<in> A. \<forall>a2 \<in> A. (a1 \<le> a2 \<or> a2 \<le> a1))"


definition meshes::"('a::{lattice,order_bot} set) \<Rightarrow> ('a::{lattice,order_bot} set) \<Rightarrow> bool"  (infixl "#" 50)  where
   "(A # B) \<equiv> (\<forall>a \<in> A. \<forall>b \<in> B.  ((inf a b) \<noteq> bot))"

definition grill::"'a::{lattice,order_bot} set \<Rightarrow> 'a::{lattice,order_bot} set" where
  "grill A = {x::('a::{lattice,order_bot}). {x}#A}"  

definition is_prime_alt::"'a set set \<Rightarrow> bool" where
  "is_prime_alt U \<equiv> (\<forall>a. ((a \<in> U) \<and> \<not>((UNIV-a) \<in> U)) \<or> (\<not>(a \<in> U) \<and> ((UNIV-a) \<in> U)))"

definition is_lb_of::"'a::order \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "is_lb_of l E \<equiv> (\<forall>x \<in> E. l \<le> x)"

    
section Simplifications
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

lemma is_pisystem_imp:
  assumes "is_pisystem X"
  shows "\<And>a b. (a \<in> X \<and> b \<in> X) \<Longrightarrow> (inf a b) \<in> X"
  using assms is_pisystem_def by blast

section PrincipalFiltersAndTops 
context fixes F::"'a::order set"
begin

lemma principal_filter_iso:
  assumes "is_upclosed F"
  shows "\<forall>a. a \<in> F \<longleftrightarrow> ((principal_filter a) \<subseteq> F)"
  by (metis assms is_upclosed_imp mem_Collect_eq order_refl principal_filter_def subset_eq)
end

lemma principal_filter_is_filter:
  "\<forall>a::'a::order. is_filter(principal_filter a)"
proof
  fix a::"'a::order"
  show "is_filter(principal_filter a)"
  proof-
    let ?F="principal_filter a"
    have P0:"is_inhabited ?F"
      using is_inhabited_def principal_filter_def by auto
    have P1:"is_upclosed ?F"
      using is_upclosed_def principal_filter_def principal_filter_imp by fastforce
    have P2:"is_downdir ?F"
      using is_downdir_def principal_filter_def by auto
    show ?thesis
      by (simp add: FiltersAgain7.is_filter_def P0 P1 P2)
  qed
qed


lemma topped_iff:
  "(\<forall>F::'a::{order,top} set \<in> (filters_in UNIV). top \<in> F) \<longleftrightarrow> (\<forall>x::'a::{order,top}. x \<le> top)"
proof
  assume A0:"\<forall>F::'a::{order,top} set \<in> (filters_in UNIV). top \<in> F"
  show "(\<forall>x::'a::{order,top}. x \<le> top)" 
  proof
    fix x::"'a::{order, top}"
    show "x \<le> top"
    proof-
      have B0:"principal_filter x \<in> filters_in UNIV"
        by (simp add: filters_in_def principal_filter_is_filter)
      have B1:"is_filter( principal_filter x)"
         by (simp add: principal_filter_is_filter) 
      have B2:"top \<in> (principal_filter x)"
        by (simp add: A0 B0)
      have B3:"x \<le> top"
        by (simp add: B2 principal_filter_imp)
      show ?thesis
        by (simp add: B3)
    qed
  qed
  next
  assume A1:"\<forall>x::'a::{order,top}. x \<le> top"
  show "\<forall>F::'a::{order,top} set \<in> (filters_in UNIV). top \<in> F"
  proof
    fix F::"'a::{order,top} set"
    assume A2:"F \<in> (filters_in UNIV)"
    have B0:"is_filter F"
      using A2 filters_in_def by blast
    obtain x where B1:"x \<in> F"
      using B0 FiltersAgain7.is_filter_def is_inhabited_imp by blast
    have B2:"x \<le> top"
      by (simp add: A1)
    show "top \<in> F"
      using B0 B1 B2 FiltersAgain7.is_filter_def is_upclosed_imp by auto
  qed
qed

lemma toped_iff2:
  "(\<forall>F::'a::order_top set \<in> (filters_in UNIV). top \<in> F)"
  by (simp add: topped_iff)


section FilterTypeDef
typedef (overloaded) 'a filter = "{F::('a::order set). is_filter F}"
  using principal_filter_is_filter by auto

lemma filter_simp [simp]:
  "is_filter (Rep_filter F)"
  using filter.Rep_filter by auto
  
setup_lifting type_definition_filter




section Upsets
context order_top
begin

lemma upsets_moore_family:
  "is_moore_family (upsets_in (UNIV::('X::order_top set)))"
proof-
  let ?C="upsets_in (UNIV::('X::order_top set))"
  have B0:"\<forall>(A::'X::order_top set). (\<exists>M \<in> (principal_filter_in A ?C).
           (\<forall>Y \<in> (principal_filter_in A ?C). M \<le> Y))"
  proof
    fix A::"'X::order_top set"
    let ?Pa="finer_upsets A"
    have B01:"is_upclosed (Inf ?Pa)"
      by (simp add: finer_upsets_def is_upclosed_def)
    have B02:"\<forall>E \<in> ?Pa. (Inf ?Pa) \<le> E"
      by blast
    have B03:"Inf?Pa \<in> (principal_filter_in A ?C)"
      by (smt (verit, ccfv_threshold) B01 Int_iff Inter_greatest PowI finer_upsets_def mem_Collect_eq order_top_class.top_greatest principal_filter_def principal_filter_in_def upsets_in_def)
    have B04:"?Pa = principal_filter_in A ?C"
    proof-
      have B04L:"\<forall>x \<in> ?Pa. x \<in> ( principal_filter_in A ?C)"
        by (simp add: finer_upsets_def principal_filter_def principal_filter_in_def upsets_in_def)
      have B04R:"\<forall>x \<in> ( principal_filter_in A ?C). x \<in> ?Pa"
        using finer_upsets_def principal_filter_in_def principal_filter_in_imp upsets_in_def by fastforce
      show ?thesis
        using B04L B04R by blast
    qed
    have B05:"\<forall>x \<in> ?Pa. (Inf ?Pa) \<le> x"
      by blast
    show "(\<exists>M \<in> (principal_filter_in A ?C). (\<forall>Y \<in> (principal_filter_in A ?C). M \<le> Y))"
      using B03 B04 by auto
  qed
  have ne:"is_inhabited ?C"
    by (metis B0 Int_iff empty_iff is_inhabited_def principal_filter_in_def)
  show ?thesis
    using B0 is_inhabited_def is_moore_family_def ne by blast
qed


lemma filter_topped:
  fixes F::"'X::order_top set"
  assumes A0:"is_filter F"
   shows "top \<in> F"
proof-
  have B0:"is_inhabited F"
    using A0 is_filter_def by auto
  have B1:"is_upclosed F"
    using is_filter_def assms by blast
  obtain x where B2:"x \<in> F"
    using B0 is_inhabited_def by fastforce
  have B3:"x \<le> top"
    by simp
  show ?thesis
    using B1 B2 B3 is_upclosed_def by blast
qed

lemma upclosed_then_contains_smallest_filter:
  assumes "is_upclosed (A::'X::order_top set)"
  shows "A \<noteq> {} \<longrightarrow> {top} \<subseteq> A"
  by (meson assms empty_subsetI insert_subset is_inhabited_def is_inhabited_imp 
      is_upclosed_def order_top_class.top_greatest)

lemma up_closure_expression:
  "moore_upclosure = (\<lambda>(A::'X::order_top set). if A={} then {top} else (\<Union>x \<in> (A::'X::order_top set). principal_filter x))"
proof-
  define f where fdef:"f=(\<lambda>(A::'X::order_top set). if A={} then {top} else (\<Union>x \<in> A. principal_filter x))"
  have T:"\<forall>(A::'X::order_top set). f(A) = (moore_upclosure A)"
  proof
    fix A::"'X::order_top set"
    show " f(A) = (moore_upclosure A)"
    proof(cases "A={}")
      case True
      have B0:"f(A) = {top}"
        by (simp add: True fdef)
      have B1:"moore_upclosure A = {top}"
        by (simp add: True moore_upclosure_def)
      then show ?thesis 
        by (simp add: B0 B1)
    next
      case False
      have "\<And>x. x \<in> f(A) \<longleftrightarrow> x \<in> (moore_upclosure A) "
      proof
        fix x::"'X::order_top"
        assume A0:"x \<in> f(A)" 
        obtain a where A1:"a \<in> A \<and> x \<in> principal_filter a"
          using False A0 fdef by auto
        have B0:"a \<le> x"
          by (simp add: A1 principal_filter_imp)
        show "x \<in> moore_upclosure A"
          by (metis (mono_tags, lifting) False
             \<open>\<And>thesis::bool. (\<And>a::'X::order_top. a \<in> (A::'X::order_top set) \<and> (x::'X::order_top) \<in> principal_filter a \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>
               mem_Collect_eq moore_upclosure_def principal_filter_imp up_closure_def)
      next
       fix x::"'X::order_top"
       assume A0:"x \<in> moore_upclosure A" 
       have B0:"A \<noteq> {}"
          by (simp add: False) 
       have B1:"moore_upclosure A = up_closure A"
         by (simp add: False moore_upclosure_def)
       obtain a where A1:"a \<in> A \<and> a \<le> x"
         by (smt (verit, best) A0 B1 CollectD up_closure_def)
        have B2:"x \<in> (principal_filter a) \<and> a \<in> A"
          by (simp add: A1 principal_filter_def)
        show "x \<in> f(A)"
          using B2 fdef by auto
      qed
      then show ?thesis
         by blast
    qed
  qed
  show ?thesis
    using T fdef by blast
qed



  
end



section FilterClosure

lemma set_filter_topped:
  assumes A0:"is_filter F" shows "UNIV \<in> F"
  by (simp add: assms filter_topped)


lemma filter_improper_iff:
  fixes F::"'X::order_bot set"
  assumes A0:"is_filter F"
  shows "bot \<in> F \<longleftrightarrow> F=UNIV"
proof
  assume L:"bot \<in> F"
  have LB0:"\<forall>x. x \<in> F"
    using is_filter_def L assms bot.extremum is_upclosed_imp by blast
  show "F=UNIV"
    using LB0 by blast
  next
  assume R:"F=UNIV"
  show "bot \<in> F"
    by (simp add: R)
qed
  

lemma set_filter_improper_iff:
  assumes A0:"is_filter (F::('X set set))" 
  shows "{} \<in> F \<longleftrightarrow> F=Pow(UNIV)"
  by (simp add: assms filter_improper_iff)

lemma filter_closure_obtains0:
  "\<And>x. x \<in> filter_closure A \<longleftrightarrow> (\<exists>S\<in>Pow(A). finite S \<and>  S \<noteq> {} \<and>  Inf S \<le> x)"
  by (simp add: filter_closure_def)

lemma filter_closure_extensive:
  fixes A::"'a::semilattice_inf_Inf set"
  shows " A \<subseteq> filter_closure A"
proof-
  have B0:"\<forall>a \<in> A. is_lb_set {a} a"
    by (simp add: is_lb_set_def)
  have B1:"\<forall>a \<in> A. {a} \<in> Pow(A) \<and> (finite {a}) \<and> ({a} \<noteq> {})"
    by simp
  have B2:"\<forall>a \<in> A. a \<in> (filter_closure A)"
    by (meson B1 filter_closure_obtains0 semilattice_inf_Inf_class.Finite_Inf_lower singletonI)
  show ?thesis
    by (simp add: B2 subset_iff)
qed

lemma filter_closure_isotone:
  fixes A::"'X::semilattice_inf_Inf set" and  
        B::"'X::semilattice_inf_Inf set"
  assumes A0:"A \<subseteq> B"
  shows "(filter_closure A) \<subseteq> (filter_closure B)"
proof
  fix x assume A1:"x \<in> (filter_closure A)"
  obtain S1 where A2:"S1 \<in> (Pow A) \<and> (finite S1) \<and> (S1 \<noteq> {}) \<and> Inf S1 \<le> x"
    by (meson A1 filter_closure_obtains0)
  have B0:"S1 \<in> Pow  B"
    using A2 assms by blast
  obtain S2 where A3:"S2 \<in> (Pow B) \<and> (finite S2) \<and> (S2 \<noteq> {}) \<and> Inf S2 \<le> x"
    using A2 B0 by blast
  show "x \<in> (filter_closure B)"
    using A2 B0 filter_closure_obtains0 by auto
qed


lemma finite_lower_bound:
  fixes C::"'a::order set"
  assumes A0: "\<And>a1 a2. a1 \<in> C \<Longrightarrow> a2 \<in> C \<Longrightarrow> (\<exists>l \<in> C. is_lb_of l {a1, a2})" and 
          A1:"finite E" and
          A2:"E \<noteq> {}" and
          A3:"E \<subseteq> C"
  shows "(\<exists>l \<in> C. is_lb_of l E)"
  using A1 A2 A3 
  proof (induct E rule: finite_ne_induct)
    case (singleton x)
    then show ?case
    proof-
      have S0:"x \<le> x"
        by simp
      have S1:" is_lb_of x {x}"
        by (simp add: is_lb_of_def)
      show S4:"(\<exists>l \<in> C. is_lb_of l {x})"
        using S1 singleton by auto
    qed
  next
    case (insert x F)
    have P0:"x \<in> C"
      using insert.prems by auto
    have P1: "F \<subseteq> C" 
      using insert.prems by auto
    obtain lF where A4:"lF \<in> C \<and> is_lb_of lF F"
      using P1 insert.hyps(4) by blast
    obtain l where A5:"l \<in> C \<and> is_lb_of l {lF, x}"
      using A0 A4 P0 by blast
    have P2:"\<forall>y \<in> (insert x F). l \<le> y"
      by (metis A4 A5 dual_order.trans insert_iff is_lb_of_def)
    then show ?case
      using A5 is_lb_of_def by blast
qed

section FilterPiSystemInSemilatticeinf

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
    by (simp add: AL assms downdir_inf is_pisystem_def)
  next
  let ?L="(is_downdir X)" let ?R="(is_pisystem X)"
  assume AR:"?R"
  show "?L"
  proof-
    have ARB0:"\<And>a b. (a \<in> X \<and> b \<in> X) \<longrightarrow> (\<exists>c  \<in> X. (c \<le> a) \<and>  (c \<le> b))"
    proof
      fix a b assume ARA0:"(a \<in> X \<and> b \<in> X)"
      have ARB1:"(inf a b) \<in> X"
        by (simp add: AR ARA0 is_pisystem_imp)
      have ARB2:"(inf a b) \<le> a \<and> (inf a b) \<le> b"
        by simp 
      show "(\<exists>c  \<in> X. (c \<le> a) \<and>  (c \<le> b))"
        using ARB1 ARB2 by blast
    qed
    show ?thesis
      by (simp add: ARB0 is_downdir_def)
  qed
qed

lemma filter_in_semilattice_inf_iff:
 fixes X::"'X::semilattice_inf set"
  assumes "X \<noteq> {}"
  shows "is_filter X \<longleftrightarrow> (\<forall>x y. (x \<in> X \<and> y \<in> X) \<longleftrightarrow> (inf x y) \<in> X)"
proof-
  have LtR:"is_filter X \<longrightarrow> (\<forall>x y. (x \<in> X \<and> y \<in> X) \<longleftrightarrow> (inf x y) \<in> X)"
  proof
    assume LA0:"is_filter X"
    have LA1:"is_pisystem X"
      using is_filter_def LA0 downdir_up_pisystem by blast
    have LA2:"is_upclosed X"
      using is_filter_def LA0 by blast
    show "(\<forall>x y. (x \<in> X \<and> y \<in> X) \<longleftrightarrow> (inf x y) \<in> X)"
    proof-
      have LB0:"(\<forall>x y. (x \<in> X \<and> y \<in> X) \<longrightarrow> (inf x y) \<in> X)"
        by (simp add: LA1  is_pisystem_imp)
      have LB1:"(\<forall>x y.  (inf x y) \<in> X \<longrightarrow> (x \<in> X \<and> y \<in> X))"
        by (metis LA2 inf.cobounded1 inf.cobounded2 is_upclosed_imp)
      show ?thesis
        using LB0 LB1 by blast
    qed
  qed
  have RtL:"(\<forall>x y. (x \<in> X \<and> y \<in> X) \<longleftrightarrow> (inf x y) \<in> X)\<longrightarrow> is_filter X"
    by (metis is_filter_def assms downdir_up_pisystem inf.absorb_iff2 is_inhabited_def is_pisystem_def is_upclosed_def)
  show ?thesis
    using LtR RtL by blast
qed




section SemilatticeinfWithFinite
context semilattice_inf_Inf
begin

lemma infs_eq:
  "inf x (Inf F) = Inf {x, Inf F}"
proof-
  let ?R=" Inf {x, Inf F}"
  let ?L="inf x (Inf F)"
  have B0:"?R \<le> x \<and> ?R \<le> Inf F"
    by (simp add: local.Finite_Inf_lower)
  have B1:"?L \<le> ?R"
    using local.Finite_Inf_greatest by fastforce
  have B2:"?L \<le> x \<and> ?L \<le> Inf F"
    by simp
  have B3:"?R \<le> ?L"
    by (simp add: B0)
  show ?thesis
    using B1 B3 local.dual_order.eq_iff by auto
qed

lemma infs_insert:
  assumes "finite F"
  shows "Inf {x, Inf F} = Inf (insert x F)"
proof-
  have B0:"\<forall>y \<in> (insert x F). Inf {x, Inf F} \<le> y"
    by (metis assms infs_eq insert_iff local.Finite_Inf_lower local.inf.coboundedI1 local.inf.coboundedI2 local.order.refl)
  have B1:"\<forall>y \<in>  (insert x F).  Inf (insert x F) \<le> y"
    by (simp add: assms local.Finite_Inf_lower)
  have B2:"Inf {x, Inf F} \<le> Inf (insert x F)"
    by (meson B0 assms finite.insertI local.Finite_Inf_greatest)
  have B3:"\<forall>y \<in> {x, Inf F}. (Inf (insert x F)) \<le> y"
    by (simp add: B1 assms local.Finite_Inf_greatest)
  have B4:"Inf (insert x F) \<le> Inf {x, Inf F}"
    using B3 local.Finite_Inf_greatest by force
  show ?thesis
    by (simp add: B2 B4 local.dual_order.eq_iff)
qed
  

lemma finite_meet_in_set:
  fixes C::"'a set"
  assumes A0: "\<And>a1 a2. a1 \<in> C \<Longrightarrow> a2 \<in> C \<Longrightarrow> (inf a1 a2) \<in> C" and 
          A1:"finite E" and
          A2:"E \<noteq> {}" and
          A3:"E \<subseteq> C"
  shows "(Inf E) \<in> C"
  using A1 A2 A3 
  proof (induct E rule: finite_ne_induct)
    case (singleton x)
    then show ?case
    proof-
      have S0:"Inf {x} \<le> x"
        by (simp add: local.Finite_Inf_lower)
      have S1:"x \<le> x"
        by simp
      have S2:"x \<le> Inf {x}"
        using local.Finite_Inf_greatest by fastforce
      have S3:"Inf {x} = x"
        by (simp add: S0 S2 local.dual_order.eq_iff)
      show S4:"Inf {x} \<in> C"
        using S3 singleton by force
    qed
  next
    case (insert x F)
    have P0:"x \<in> C"
      using insert.prems by auto
    have P1: "F \<subseteq> C" 
      using insert.prems by auto
    have P2:"inf x (Inf F) \<in> C"
      by (simp add: A0 P0 P1 insert.hyps(4))
    have P4:"Inf (insert x F) = inf x (Inf F)"
      by (simp add: infs_eq infs_insert insert.hyps(1))
    then show ?case
      by (simp add: P2 P4)
qed

end



lemma pi_system_then_fc:
  fixes X::"'X::semilattice_inf_Inf set"
  assumes A0:"is_pisystem X"
  shows "(\<forall>F. F \<noteq> {} \<longrightarrow> finite F \<longrightarrow> F  \<subseteq> X \<longrightarrow> (Inf F) \<in> X)"
proof-
  have B0:"\<And>a1 a2. a1 \<in> X \<Longrightarrow> a2 \<in> X \<Longrightarrow> (inf a1 a2) \<in> X"
    by (simp add: assms is_pisystem_imp)
  have B1:"\<And>F. (F \<noteq> {}) \<and> (finite F) \<and> (F \<subseteq> X) \<longrightarrow> (Inf F) \<in> X"
  proof
    fix F assume A1:"(F \<noteq> {}) \<and> (finite F) \<and> (F \<subseteq> X) "
    show "(Inf F) \<in> X"
      by (simp add: A1 B0 semilattice_inf_Inf_class.finite_meet_in_set)
  qed
  show ?thesis
    using B1 by presburger
qed

lemma filters_inf_closed:
  assumes "is_filter (F::'X::semilattice_inf_Inf set)"
  shows "\<And>E. finite E \<Longrightarrow> E \<noteq> {} \<Longrightarrow> E \<subseteq> F \<Longrightarrow> (Inf E \<in> F)"
  using is_filter_def assms downdir_up_pisystem pi_system_then_fc by blast

lemma filter_closure_idempotent:
  fixes A::"'X::semilattice_inf_Inf set"  
  shows "(filter_closure A) = (filter_closure (filter_closure A))"
proof-
  have B0:"(filter_closure(filter_closure A)) \<subseteq> filter_closure A"
  proof
    fix x assume A0:"x \<in> (filter_closure(filter_closure A))"
    obtain Ex where A1:"(Ex\<in>Pow( (filter_closure A)) \<and>  finite Ex \<and>  Ex \<noteq> {} \<and>  (Inf Ex) \<le> x)"
      by (meson A0 filter_closure_obtains0)
    have B1:"\<forall>y \<in> Ex. (\<exists>Ey \<in> Pow(A). finite Ey \<and> Ey \<noteq> {} \<and> (Inf Ey) \<le> y)"
      by (metis A1 UnionI Union_Pow_eq filter_closure_obtains0)
    define g where "g=(\<lambda>y. SOME Ey. Ey \<in> Pow(A) \<and> finite Ey \<and> Ey \<noteq> {} \<and> (Inf Ey) \<le> y)"
    have B2:"\<forall>y \<in>  Ex. ((g y) \<in> Pow(A) \<and> (finite (g y)) \<and> (g y \<noteq> {}) \<and> (Inf (g y)) \<le> y)"
      by (metis (mono_tags, lifting) B1 g_def someI)
    define E where "E=(\<Union>(g`Ex))"
    have B3:"E \<in> Pow (A) \<and> finite E \<and> E \<noteq> {}"
      using A1 B2 E_def by auto
    have B4:"\<forall>y \<in> Ex. (Inf E) \<le> (Inf (g y))"
      by (metis B2 B3 E_def UN_I semilattice_inf_Inf_class.Finite_Inf_greatest semilattice_inf_Inf_class.Finite_Inf_lower)
    have B5:"\<forall>y \<in> Ex. (Inf E) \<le> y"
      using B2 B4 order.trans by blast
    have B6:"(Inf E) \<le> (Inf Ex)"
      by (simp add: A1 B5 semilattice_inf_Inf_class.Finite_Inf_greatest)
    have B7:"(Inf E) \<le> x"
      using A1 B6 order.trans by blast
    show "x \<in> filter_closure A"
      using B3 B7 filter_closure_obtains0 by blast
  qed
  show ?thesis
    by (simp add: B0 filter_closure_extensive set_eq_subset)
qed

lemma filter_closure_is_closure:
  shows "is_closure filter_closure"
proof-
  have A0:"is_extensive filter_closure"
    by (simp add: filter_closure_extensive is_extensive_def)
  have A1:"is_isotone filter_closure"
    by (simp add: filter_closure_isotone is_isotone_def)
  have A3:"is_idempotent filter_closure"
    using filter_closure_idempotent is_idempotent_def by blast
  show ?thesis
    by (simp add: A0 A1 A3 is_closure_def)
qed


lemma filters_in_filter_cl_range:
  fixes F::"'X::semilattice_inf_Inf set"
  assumes A0:"is_filter F"
  shows "filter_closure F = F"
proof-
  have B0:"filter_closure F \<subseteq> F"
  proof-
    have B00:"filter_closure F = {a. \<exists>S\<in>Pow(F). finite S \<and>  S \<noteq> {} \<and>  Inf S \<le>  a}"
      by (simp add: filter_closure_def)
    have B01:"\<And>a. (\<exists>S\<in>Pow(F). finite S \<and>  S \<noteq> {} \<and>  Inf S \<le> a) \<longrightarrow> a \<in> F"
    proof
      fix a assume B01A0:"(\<exists>S\<in>Pow(F). finite S \<and>  S \<noteq> {} \<and>  Inf S \<le> a)"
      obtain S where B01A1:"S \<in> Pow(F) \<and> finite S \<and> S \<noteq> {} \<and>  Inf S \<le> a"
        using B01A0 by force
      have B01A1:"(Inf S) \<in> F"
        by (meson B01A1 is_filter_def PowD assms downdir_inf semilattice_inf_Inf_class.finite_meet_in_set)
      show "a \<in> F"
        by (meson B01A0 is_filter_def PowD assms downdir_inf is_upclosed_imp semilattice_inf_Inf_class.finite_meet_in_set)
    qed
    show ?thesis
      by (meson B01 filter_closure_obtains0 subsetI)
  qed
  have B1:"F \<subseteq> filter_closure F"
    by (simp add: filter_closure_extensive)
  show ?thesis
    by (simp add: B0 B1 subset_antisym)
qed


lemma filter_closure_is_filter:
  fixes E::"'X::semilattice_inf_Inf set"
  assumes A0:"E \<noteq> {}"
  shows "is_filter (filter_closure E)"
proof-
  let ?F="(filter_closure E)"
  have B0:"is_downdir ?F"
  proof-
    have B01:"(\<And>a b.  (a \<in> ?F \<and> b \<in> ?F) \<longrightarrow> (\<exists>c  \<in> ?F. (c \<le> a) \<and>  (c \<le> b)))"
    proof
       fix a b assume B0A0:"a \<in> ?F \<and> b \<in> ?F"
      obtain Sa where B0A1:"Sa \<in> Pow(E) \<and> finite Sa \<and> Sa \<noteq> {} \<and> (Inf Sa) \<le> a"
        by (meson B0A0 filter_closure_obtains0)
      obtain Sb where B0A2:"Sb \<in> Pow(E) \<and> finite Sb \<and> Sb \<noteq> {} \<and> (Inf Sb) \<le> b"
        by (meson B0A0 filter_closure_obtains0) 
      define Sc where B0A3:"Sc=Sa \<union> Sb"
      have B0B2:"Sc \<in> Pow(E) \<and> finite Sc \<and> Sc \<noteq> {}"
        using B0A1 B0A2 B0A3 by auto
      have B0B3:"(Inf Sc) \<le> (Inf Sa) \<and> (Inf Sc) \<le>(Inf Sb)"
        by (simp add: B0A1 B0A2 B0A3 semilattice_inf_Inf_class.Finite_Inf_greatest semilattice_inf_Inf_class.Finite_Inf_lower)
      have B0B4:"(Inf Sc) \<le> a \<and> (Inf Sc) \<le> b"
        using B0A1 B0A2 B0B3 dual_order.trans by blast
      show "\<exists>c  \<in> ?F. (c \<le> a) \<and>  (c \<le> b)"
        by (meson B0B2 B0B4 dual_order.refl filter_closure_obtains0)
      qed
    show ?thesis
      by (simp add: B01 is_downdir_def)
  qed
  have B1:"is_upclosed ?F"
  proof-
    have B10:"\<And>a b. (a \<le> b \<and>  a \<in> ?F) \<longrightarrow>  b \<in> ?F"
    proof 
      fix a b assume B1A0:"(a \<le> b \<and>  a \<in> ?F)" 
      obtain Sa where B1A1:"Sa \<in> Pow(E) \<and> finite Sa \<and> Sa \<noteq> {} \<and> (Inf Sa) \<le> a"
        by (meson B1A0 filter_closure_obtains0)
      have B1B1:"(Inf Sa) \<le> b"
        using B1A0 B1A1 dual_order.trans by blast
      show "b \<in> ?F"
        using B1A1 B1B1 filter_closure_obtains0 by blast
    qed
    show ?thesis
      by (meson B10 is_upclosed_def)
  qed
  have B2:"is_inhabited ?F"
    using assms filter_closure_extensive is_inhabited_def by blast
  show ?thesis
    by (simp add: B0 B1 B2 is_filter_def)
qed

lemma filter_closure_is_smallest:
  fixes E::"'X::semilattice_inf_Inf set"
  assumes A0:"E \<noteq> {}"
  shows "\<And>F. (is_filter F \<and> E \<subseteq> F) \<longrightarrow> (filter_closure E) \<subseteq> F"
proof
  fix F assume A1:"(is_filter F \<and> E \<subseteq> F)"
  show "(filter_closure E) \<subseteq> F"
  proof
    fix x assume A2:"x \<in> filter_closure E"
    show "x \<in> F"
      using A1 A2 filter_closure_isotone filters_in_filter_cl_range by blast
    qed
qed

lemma filter_sup_is_ub:
  fixes EF::"'X::semilattice_inf_Inf set set"
  assumes A0: "EF \<noteq> {}" and A0:"\<forall>F \<in> EF. is_filter F"
  shows "\<forall>F \<in> EF. F \<subseteq>  (filter_sup EF)"
  by (metis A0 Sup_upper filter_closure_isotone filter_sup_def filters_in_filter_cl_range)
  
lemma filter_sup_is_lub:
  fixes EF::"'X::semilattice_inf_Inf set set"
  assumes A0: "EF \<noteq> {}" and A0:"\<forall>F \<in> EF. is_filter F"
  shows "\<And>G. is_filter G \<Longrightarrow> (\<forall>F \<in> EF. F \<subseteq> G) \<Longrightarrow> (filter_sup EF) \<subseteq> G"
  by (metis Sup_le_iff filter_closure_isotone filter_sup_def filters_in_filter_cl_range)


lemma filter_inf_is_filter:
  fixes EF::"'X::bounded_semilattice_inf_top set set"
  assumes A0: "EF \<noteq> {}" and A1:"\<forall>F \<in> EF. is_filter F"
  shows "is_filter (filter_inf EF)"
proof-
  let ?I="filter_inf EF"
  have P0:"is_inhabited ?I"
    by (metis A0 A1 InterI empty_iff filter_inf_def filter_topped is_inhabited_def)
  have P1:"is_upclosed ?I"
  proof-
    have B01:"\<And>a b. b \<in> ?I \<and> b \<le> a \<longrightarrow> a \<in> ?I"
    proof
      fix a b assume A01:"b \<in> ?I \<and>  b \<le> a"
      have B02:"\<forall>F \<in> EF. b \<in> F"
        by (metis A0 A01 Inter_iff filter_inf_def)
      have B03:"\<forall>F \<in> EF. a \<in> F"
        by (metis A01 A1 B02 FiltersAgain7.is_filter_def is_upclosed_imp)
      show "a \<in> ?I"
        by (simp add: A0 B03 filter_inf_def)
    qed
    show ?thesis
      using B01 is_upclosed_def by blast
  qed
  have P2:"is_downdir ?I"
    proof-
    have B20:"(\<And>a b.  (a \<in> ?I \<and> b \<in> ?I) \<longrightarrow> (\<exists>c  \<in> ?I. (c \<le> a) \<and>  (c \<le> b)))"
    proof
       fix a b assume B2A0:"a \<in> ?I \<and> b \<in> ?I" 
       have B21:"\<forall>F \<in> EF. a \<in> F \<and> b \<in> F"
         by (metis A0 B2A0 InterE filter_inf_def)
       have B22:"\<forall>F \<in> EF. inf a b \<in> F"
         by (meson A1 B21 FiltersAgain7.is_filter_def downdir_inf)
       have B23:"inf a b \<in> ?I"
         by (simp add: A0 B22 filter_inf_def)
        show "(\<exists>c  \<in> ?I. (c \<le> a) \<and>  (c \<le> b))"
          by (meson B23 inf.cobounded1 inf.cobounded2)
  qed
  show ?thesis
    by (simp add: B20 is_downdir_def)
  qed
  show ?thesis
    by (simp add: FiltersAgain7.is_filter_def P0 P1 P2)
qed

lemma smallest_filter1:
  "is_filter {top::('X::bounded_semilattice_inf_top_Inf)}"
proof-
    let ?S="{top::('X::bounded_semilattice_inf_top_Inf)}"
    have B0:"is_upclosed ?S"
      by (simp add: is_upclosed_def top.extremum_unique)
    have B1:"is_downdir ?S"
      using is_downdir_def by blast
    have B2:"is_inhabited ?S"
      by (simp add: is_inhabited_def)
    show ?thesis
      by (simp add: B0 B1 B2 is_filter_def)
qed


lemma smallest_filter2:
  "\<forall>(F::('X::bounded_semilattice_inf_top_Inf set)). is_filter F \<longrightarrow>  {top::('X::bounded_semilattice_inf_top_Inf)} \<subseteq> F"
  by (simp add: filter_topped)



lemma filter_moore_family:
  "is_moore_family {F::('X::bounded_semilattice_inf_top_Inf set). is_filter F}"
proof-
  let ?EF="{F::('X::bounded_semilattice_inf_top_Inf set). is_filter F}"
  have B0:"is_filter (top::('X::bounded_semilattice_inf_top_Inf set))"
    by (simp add: filter_in_semilattice_inf_iff)
  have B1:"(top::('X::bounded_semilattice_inf_top_Inf set)) \<in> ?EF"
    by (simp add: B0)
  have B2:"\<And>(G::'X::bounded_semilattice_inf_top_Inf set). G \<noteq> {} \<longrightarrow> (\<exists>F \<in> (principal_filter_in G ?EF).
        (\<forall>H \<in> (principal_filter_in G ?EF). F \<le> H))"
  proof
    fix G::"'X::bounded_semilattice_inf_top_Inf set" assume B2A0:"G \<noteq> {}"
    have B20:"G \<subseteq> filter_closure G"
      by (simp add: filter_closure_extensive)
    have B21:"is_filter (filter_closure G)"
      by (simp add: B2A0 filter_closure_is_filter)
    have B22:" (filter_closure G) \<in> principal_filter_in G ?EF"
      by (simp add: B20 B21 principal_filter_def principal_filter_in_def)
    have B23:"(\<forall>H \<in> (principal_filter_in G ?EF). is_filter H \<and> G \<subseteq> H)"
      by (simp add: principal_filter_def principal_filter_in_def)
    have B24:"\<forall>H \<in> (principal_filter_in G ?EF). (filter_closure G) \<subseteq> H"
      by (meson B23 B2A0 filter_closure_is_smallest)
    obtain F where B25:"F \<in> (principal_filter_in G ?EF) \<and>  (\<forall>H \<in> (principal_filter_in G ?EF). F \<le> H)"
      using B22 B24 by blast
    show "(\<exists>F \<in> (principal_filter_in G ?EF). (\<forall>H \<in> (principal_filter_in G ?EF). F \<le> H))"
      using B25 by blast
  qed
  have B3:"?EF \<noteq> {}"
    using B1 by auto
  have B4:"(\<forall>(a::(('X::bounded_semilattice_inf_top_Inf set))). (\<exists>m \<in> (principal_filter_in a ?EF). (\<forall>x \<in> (principal_filter_in a ?EF). m \<le> x)))"
  proof
     fix a
     show "(\<exists>m \<in> (principal_filter_in a ?EF). (\<forall>x \<in> (principal_filter_in a ?EF). m \<le> x))"
     proof(cases "a = {}")
       case True
        have "is_filter {top::('X::bounded_semilattice_inf_top_Inf)}"
          by (simp add: smallest_filter1)
        have " (\<forall>x \<in> (principal_filter_in a ?EF). {top::('X::bounded_semilattice_inf_top_Inf)} \<le> x)"
          by (metis Int_iff mem_Collect_eq principal_filter_in_def smallest_filter2)
       then show ?thesis
         by (metis True UNIV_eq_I \<open>is_filter {top}\<close> empty_subsetI inf_top.right_neutral mem_Collect_eq principal_filter_def principal_filter_in_def)
     next
       case False
       then show ?thesis
         by (simp add: B2)
     qed
  qed
  show ?thesis
    using B3 B4 is_moore_family_def by blast
qed


context fixes X::"'X::lattice set"
begin

lemma upclosed_in_lattice_iff:
  assumes "X \<noteq> {}"
  shows "is_upclosed X \<longleftrightarrow> (\<forall>x z. x \<in> X \<longrightarrow> (sup x z) \<in> X)"
  by (metis inf_sup_ord(3) is_upclosed_def sup.commute sup.orderE)
 

end

section FilterOnLatticeInstance

lemma filter_on_lattice_inf:
  assumes A0:"is_filter (F1::('X::lattice set))" and 
          A2:"is_filter (F2::('X::lattice set))"
  shows "is_filter (inf F1 F2)"
proof-
  let ?I="inf F1 F2"
  have P0:"is_inhabited ?I"
  proof-
    have B00:"is_inhabited F1 \<and> is_inhabited F2"
      using A0 A2 FiltersAgain7.is_filter_def by auto
    obtain x1 x2 where A01:"x1 \<in> F1 \<and> x2 \<in> F2"
      using B00 is_inhabited_imp by blast
    define x where A02:"x=sup x1 x2"
    have B01:"x1 \<le> x \<and> x2 \<le> x"
      by (simp add: A02)
    have B02:"x \<in> inf F1 F2"
      using A0 A01 A2 B01 FiltersAgain7.is_filter_def is_upclosed_imp by auto
    show ?thesis
      using B02 is_inhabited_def by auto
  qed
  have P1:"is_downdir ?I"
  proof-
    have P10:"\<And>a b. (a \<in> ?I \<and> b \<in> ?I) \<longrightarrow> (\<exists>c  \<in> ?I. (c \<le> a) \<and>  (c \<le> b))"
    proof
      fix a b assume P1A0:"a \<in>?I \<and> b \<in> ?I"
      show "\<exists>c \<in> ?I. c \<le> a \<and> c \<le> b"
        by (metis A0 A2 is_filter_def Int_iff P1A0 downdir_inf inf_le1 inf_le2)
    qed
    show ?thesis
      by (simp add: P10 is_downdir_def)
  qed
  have P3:"is_upclosed ?I"
    by (metis A0 A2 is_filter_def IntD1 IntD2 IntI is_upclosed_def)
  show ?thesis
    by (simp add: is_filter_def P0 P1 P3)
qed
    


lemma filter_inlattice_inf_closed:
  assumes "is_filter (F::'X::lattice set)"
  shows "\<And>x1 x2. (x1 \<in> F \<and> x2 \<in> F) \<Longrightarrow> (inf x1 x2 \<in> F)"
  using FiltersAgain7.is_filter_def assms downdir_up_pisystem is_pisystem_imp by blast


lemma filter_on_lattice_sup:
  assumes A0:"is_filter (F1::('X::lattice set))" and 
          A2:"is_filter (F2::('X::lattice set))"
  shows "is_filter (binary_filter_sup F1 F2)"
proof-
  let ?S="binary_filter_sup F1 F2"
  have P0:"is_inhabited ?S"
  proof-
    have P00:"is_inhabited F1 \<and> is_inhabited F2"
      using A0 A2 FiltersAgain7.is_filter_def by blast
    have P01:"F1 \<noteq> {} \<and> F2 \<noteq> {}"
      using P00 is_inhabited_def by auto
    obtain x1 x2 where P0A1:"x1 \<in> F1 \<and> x2 \<in> F2"
      by (meson P00 is_inhabited_imp)
    have P02:"x1 \<le> sup x1 x2 \<and> x2 \<le> sup x1 x2"
      by simp
    show ?thesis
      using P0A1 binary_filter_sup_def is_inhabited_def by fastforce
   qed
  have P1:"is_downdir ?S"
  proof-
     have P10:"\<And>a b. (a \<in> ?S \<and> b \<in> ?S) \<longrightarrow> (\<exists>c  \<in> ?S. (c \<le> a) \<and>  (c \<le> b))"
      proof
        fix a b assume P1A0:"a \<in>?S \<and> b \<in> ?S"
        obtain a1 a2 where P1A1:"a1 \<in> F1 \<and> a2 \<in> F2 \<and> inf a1 a2 \<le> a"
          by (smt (verit, ccfv_threshold) P1A0 binary_filter_sup_def inf.coboundedI2 mem_Collect_eq)
        obtain b1 b2 where P1A2:"b1 \<in> F1 \<and> b2 \<in> F2 \<and> inf b1 b2 \<le> b"
          by (smt (verit, ccfv_threshold) P1A0 binary_filter_sup_def inf.coboundedI2 mem_Collect_eq)
        have P1B0:"inf (inf a1 b1) (inf a2 b2) \<le> a \<and> inf (inf a1 b1) (inf a2 b2) \<le> b"
          by (meson P1A1 P1A2 dual_order.trans inf_le1 inf_le2 inf_mono)
        obtain ab1 where P1A3:"ab1 \<in> F1 \<and> ab1 \<le> a1 \<and> ab1 \<le> b1"
          by (meson A0 is_filter_def P1A1 P1A2 downdir_up_pisystem inf_le1 inf_le2 is_pisystem_imp)
        obtain ab2 where P1A4:"ab2 \<in> F2 \<and> ab2 \<le> a2 \<and> ab2 \<le> b2"
          by (meson A2 FiltersAgain7.is_filter_def P1A1 P1A2 downdir_up_pisystem inf_le1 inf_le2 is_pisystem_imp)  
        have P1B1:"ab1 \<le> (inf a1 b1) \<and> ab2 \<le> (inf a2 b2)"
          by (simp add: P1A3 P1A4)
        have P1B2:"inf a1 b1 \<in> F1 \<and> inf a2 b2 \<in> F2"
          using A0 A2 is_filter_def P1A1 P1A2 downdir_up_pisystem is_pisystem_imp by blast
        have P1B3:"(inf (inf a1 b1) (inf a2 b2)) \<in> ?S"
          using P1B2 binary_filter_sup_def by blast
        show "\<exists>c \<in> ?S. c \<le> a \<and> c \<le> b"
          using P1B0 P1B3 by auto
      qed
      show ?thesis
        by (simp add: P10 is_downdir_def)
    qed
  have P2:"is_upclosed ?S"
  proof-
    have P20:"\<And>a b. (a \<le> b \<and>  a \<in> ?S) \<longrightarrow>  b \<in> ?S"
    proof
      fix a b assume P20A0:"a \<le> b \<and> a \<in> ?S"
      obtain a1 a2 where P20A1:"a1 \<in> F1 \<and> a2 \<in> F2 \<and> inf a1 a2 \<le> a"
        by (smt (verit) P20A0 binary_filter_sup_def mem_Collect_eq)
      have P20B1:"inf a1 a2 \<le> b"
        using P20A0 P20A1 by auto
      show "b \<in> ?S"
        using P20A1 P20B1 binary_filter_sup_def by blast
    qed
    show ?thesis
      by (meson P20 is_upclosed_def)
  qed
  show ?thesis
    by (simp add: FiltersAgain7.is_filter_def P0 P1 P2)
qed

lemma filter_on_lattice_sup_greatest:
  assumes A0:"is_filter (F1::('X::lattice set))" and 
          A1:"is_filter (F2::('X::lattice set))"
  shows "F1 \<subseteq> (binary_filter_sup F1 F2) \<and> F2 \<subseteq> (binary_filter_sup F1 F2)"
proof-
  let ?S="binary_filter_sup F1 F2"
  have B0:"\<And>x. x \<in> F1 \<Longrightarrow> x \<in> ?S"
  proof-
    fix x assume A2:"x \<in> F1"
    obtain b where A3:"b \<in> F2"
      using A1 FiltersAgain7.is_filter_def is_inhabited_imp by auto 
    have B1:"inf x b \<le> x"
      by simp
    show "x \<in> ?S"
      using A2 A3 B1 binary_filter_sup_def by blast
  qed
  have B2:"\<And>x. x \<in> F2 \<Longrightarrow> x \<in> ?S"
    proof-
    fix x assume A4:"x \<in> F2"
    obtain b where A5:"b \<in> F1"
      using A0 FiltersAgain7.is_filter_def is_inhabited_imp by auto 
    have B3:"inf b x \<le> x"
      by simp
    show "x \<in> ?S"
      using A4 A5 B3 binary_filter_sup_def by blast
  qed
  show ?thesis
    by (simp add: B0 B2 subsetI)
qed


lemma filter_on_lattice_sup_least:
  assumes A0:"is_filter (F1::('X::lattice set))" and 
          A1:"is_filter (F2::('X::lattice set))"
  shows "\<And>F3. is_filter F3 \<and> F1 \<subseteq> F3 \<and> F2 \<subseteq> F3 \<longrightarrow> (binary_filter_sup F1 F2) \<subseteq> F3"
proof
  fix F3 assume A2:"is_filter F3 \<and> F1 \<subseteq> F3 \<and> F2 \<subseteq> F3"
  let ?S="(binary_filter_sup F1 F2)"
  show "?S \<subseteq> F3"
  proof
    fix x assume A3:"x \<in> ?S"
    obtain x1 x2 where A4:"x1 \<in> F1 \<and> x2 \<in> F2 \<and> inf x1 x2 \<le> x"
      by (smt (verit, best) A3 binary_filter_sup_def mem_Collect_eq)
    have B0:"x1 \<in> F3 \<and> x2 \<in> F3"
      using A2 A4 by blast
    have B1:"inf x1 x2 \<in> F3"
      by (simp add: A2 B0 filter_inlattice_inf_closed)
    show "x \<in> F3"
      using A2 A4 B1 FiltersAgain7.is_filter_def is_upclosed_imp by auto
  qed
qed

 

instantiation filter:: (lattice) lattice
begin
 

lift_definition inf_filter::"'a::lattice filter \<Rightarrow> 'a::lattice filter \<Rightarrow> 'a::lattice filter" is inter
  by (simp add: filter_on_lattice_inf)

lift_definition sup_filter::"'a::lattice filter \<Rightarrow> 'a::lattice filter \<Rightarrow> 'a::lattice filter" is binary_filter_sup
  by (simp add: filter_on_lattice_sup)

lift_definition less_eq_filter::"'a::lattice filter \<Rightarrow> 'a::lattice filter \<Rightarrow> bool" is subset_eq .

lift_definition less_filter::"'a::lattice filter \<Rightarrow> 'a::lattice filter \<Rightarrow> bool" is subset .

instance
  apply intro_classes
  apply (simp add: less_eq_filter.rep_eq less_filter.rep_eq subset_not_subset_eq)
  apply (simp add: FiltersAgain7.less_eq_filter.rep_eq)
  apply (simp add: FiltersAgain7.less_eq_filter.rep_eq)
  apply (simp add: FiltersAgain7.filter.Rep_filter_inject FiltersAgain7.less_eq_filter.rep_eq)
  apply (simp add: FiltersAgain7.inf_filter.rep_eq FiltersAgain7.less_eq_filter.rep_eq)
  apply (simp add: FiltersAgain7.inf_filter.rep_eq FiltersAgain7.less_eq_filter.rep_eq)
  apply (simp add: FiltersAgain7.inf_filter.rep_eq FiltersAgain7.less_eq_filter.rep_eq)
  apply (simp add: filter_on_lattice_sup_greatest less_eq_filter.rep_eq sup_filter.rep_eq)
  apply (simp add: FiltersAgain7.less_eq_filter.rep_eq FiltersAgain7.sup_filter.rep_eq filter_on_lattice_sup_greatest)
  by (simp add: FiltersAgain7.less_eq_filter.rep_eq FiltersAgain7.sup_filter.rep_eq filter_on_lattice_sup_least)
end

 



section Meshing
lemma mesh_prop1:
  assumes A0:"{a}# F" and A1:"a \<le> b"
  shows "{b}#F"
proof-
  have B0:"\<forall>f \<in> F. ((inf a f) \<noteq> bot)"
       by (meson A0 insertI1 meshes_def)
  have B1:"\<forall>f \<in> F. ((inf a f) \<le> (inf b f))" by (simp add: A1 inf.coboundedI1)
  have B2:"\<forall>f \<in> F. ((inf b f) \<noteq> bot)"
    using B0 B1 bot.extremum_uniqueI by fastforce
  with B2 show ?thesis by (simp add: meshes_def)
qed

lemma mesh_prop2:
  assumes "is_upclosed F"
  shows "(a \<in> F \<longrightarrow> \<not>({(UNIV - a)}#F))"
  by (metis Diff_disjoint Int_commute meshes_def singletonI)

lemma mesh_prop3:
  assumes A0:"is_filter F \<and> is_filter G" and
          A1:"bot \<notin> F \<and> bot \<notin> G"
  shows "F \<le> G \<longrightarrow> F#G"
proof
  assume A1:"F \<le> G"
  show "F#G"
  proof-
    have P0:"\<forall>f \<in>F. \<forall>g \<in> G. (inf f g) \<noteq> bot"
    proof
      fix f assume B0:"f \<in> F"
      show "\<forall>g \<in> G. inf f g \<noteq> bot"
      proof
        fix g assume B1:"g \<in> G"
        have B2:"f \<in> G" 
          using A1 B0 by auto
        have B3:"is_filter G"
          by (simp add: assms)
        have B4:"is_pisystem G"
          using is_filter_def assms downdir_up_pisystem by auto
        have B5:"(inf f g) \<in> G" using B1 B2 B4 is_pisystem_def by auto
        show "inf f g \<noteq> bot"
          using B5 assms(2) by fastforce 
      qed
    qed
    show ?thesis by (simp add: P0 meshes_def)
  qed
qed

lemma mesh_prop4:
  assumes "is_upclosed A"
  shows "(x \<notin> A) \<longleftrightarrow> {(UNIV - x)}#A"
proof-
  let ?cx="UNIV-x" let ?S="{?cx}"
  let ?L="x \<notin> A" let ?R="?S#A"
  have LtR:"?L \<longrightarrow> ?R"  by (metis Diff_eq_empty_iff Int_Diff Int_commute assms inf_top.right_neutral meshes_def singletonD is_upclosed_def)
  have RtL:"?R \<longrightarrow> ?L" using assms mesh_prop2 by auto
  with LtR RtL show ?thesis by blast
qed
  
lemma mesh_prop5:
  assumes "is_upclosed A"
  shows "(x \<in> A) \<longleftrightarrow> \<not>({(UNIV - x)}#A)"
  using assms mesh_prop4 by blast

lemma mesh_prop6:
  assumes "is_upclosed A"
  shows "((UNIV-x) \<notin> A) \<longleftrightarrow> {x}#A"
  by (simp add: Diff_Diff_Int assms mesh_prop4)

lemma mesh_prop7:
  assumes "is_upclosed A"
  shows "((UNIV-x) \<in> A) \<longleftrightarrow> \<not>({x}#A)"
  using assms mesh_prop6 by auto


lemma mesh_prop8:
   "A#B \<longleftrightarrow> A \<subseteq> grill B"
proof-
  have Eq0:"A#B \<longleftrightarrow> (\<forall>a \<in> A. \<forall>b \<in> B. inf a b \<noteq> bot)" by (simp add: meshes_def)
  have Eq1:"... \<longleftrightarrow> (\<forall>a \<in> A. {a}#B)" by (simp add: meshes_def)
  have Eq2:"... \<longleftrightarrow> (\<forall>a \<in> A. a \<in> grill B)" by (simp add: grill_def)
  have Eq3:"... \<longleftrightarrow> A \<subseteq> grill B " by blast
  show ?thesis using Eq0 Eq1 Eq2 Eq3 by presburger
qed

lemma mesh_prop9:
  "A#B \<longleftrightarrow> B#A"
  by (metis inf_commute meshes_def)

lemma mesh_prop10:
   "A#B \<longleftrightarrow> B \<le> grill A"
  using mesh_prop8 mesh_prop9 by blast

lemma mesh_prop11:
   "A \<le> grill B \<longleftrightarrow> B \<le> grill A"
  using mesh_prop10 mesh_prop8 by auto

lemma mesh_prop12:
  assumes "is_upclosed A"
  shows "x \<in> A \<longleftrightarrow> (UNIV - x) \<notin> grill A"
  by (meson assms empty_subsetI insert_subset mesh_prop4 mesh_prop8)


lemma mesh_prop13:
  assumes "is_upclosed A"
  shows "x \<notin> A \<longleftrightarrow> (UNIV - x) \<in>  grill A"
  using assms mesh_prop12 by blast

lemma mesh_prop14:
  assumes "is_upclosed A"
  shows "(UNIV - x) \<in> A \<longleftrightarrow> x \<notin> grill A"
  by (simp add: assms double_diff mesh_prop12)

lemma mesh_prop15:
  assumes "is_upclosed A"
  shows "(UNIV - x) \<notin>  A \<longleftrightarrow> x \<in> grill A"
  by (simp add: assms mesh_prop14)


lemma mesh_prop16:
  fixes EF::"'X set set set"
  assumes A0:"\<forall>F \<in> EF. (is_filter F) \<and> ({} \<notin> F)" and
          A1:"finite EF" and
          A2:"is_filter G \<and> {} \<notin> G" and
          A0b:"EF \<noteq> {} \<and> EF \<noteq> {{}}"
  shows "G#(\<Inter>EF) \<longleftrightarrow> (\<exists>F \<in> EF. G#F)"
proof-
  let ?INF="\<Inter>EF" let ?L="G#?INF" let ?R=" (\<exists>F \<in> EF. G#F)"
  have A3:"is_upclosed G"
    using A2 is_filter_def by auto 
  have RtL:"?R\<longrightarrow>?L"
    by (meson Inf_lower2 mesh_prop10) 
  have LtR:"\<not>?R \<longrightarrow> \<not>?L"
  proof
    assume NR:"\<not>(?R)"
    have B0:"(\<forall>F \<in> EF. \<not>(G#F))"  using NR by blast
    have B1:"(\<forall>F \<in> EF. \<exists>f \<in> F. \<not>(G#{f}))"  by (meson NR insertI1 meshes_def)
    have B2:"(\<forall>F \<in> EF. \<exists>f \<in> F. f \<notin> grill G)"
      by (simp add: B1 grill_def mesh_prop9)
    have B3:"(\<forall>F \<in> EF. \<exists>f \<in> F. (UNIV-f) \<in> G)"
      by (meson A3 B2 mesh_prop15) 
    obtain u where A5:"u=(\<lambda>F. SOME f. (f \<in> F \<and> (UNIV-f)\<in>G ) )" by simp
    have B4:" (\<forall>F \<in> EF. (UNIV-(u(F))) \<in> G)"  by (metis (no_types, lifting) A5 B3 someI)
    let ?H="u`EF"  let ?HC="{b. \<exists>h \<in>?H. b=UNIV-h}"
    have B5:"finite ?H" by (simp add: A1)
    have B6:"finite ?HC"  by (metis B5 finite_imageI image_def)
    have B7:"(\<forall>hc \<in> ?HC. hc \<in> G)" using B4 by blast
    have B9:"?HC \<subseteq> G"
      using B7 by blast
    have B10:"?HC \<noteq> {}"
      using A0b by blast
    have B11:"?HC \<subseteq> G \<and> is_filter G \<and> ?HC \<noteq> {}"
      using A2 B10 B9 by blast
    have B11:"(Inf ?HC) \<in> G"
      by (smt (verit) A2 B10 B6 B9 complete_lattice_class.finite_meet_in_set filter_in_semilattice_inf_iff insert_absorb insert_not_empty)
    have B12:"(UNIV - (\<Inter>?HC)) = \<Union>(?H)"
       by blast
    have B13:" \<Inter>?HC \<in> G  \<longrightarrow> \<Union>(?H) \<notin> grill G"
      using A3 B12 mesh_prop12 by fastforce
    have B14:"\<forall>h \<in> ?H. \<exists>F \<in> EF. h=u(F)"
         by blast
    have B15:"\<forall>F \<in> EF. (u(F) \<in> F)"
        by (metis (mono_tags, lifting) A5 B3 someI_ex)
    have B16:"\<forall>F \<in> EF. \<exists>u \<in> ?H. u \<in> F"
       using B15 by blast
    have B17:"\<Union>(?H) \<in> ?INF"
      by (meson A0 B16 is_filter_def Inter_iff Union_upper is_upclosed_def)
    show "\<not>(?L)"
      using B11 B13 B17 mesh_prop10 by blast
  qed
  with LtR RtL show ?thesis by blast 
qed

lemma grill_is_antitone:
  "A \<subseteq> B \<longrightarrow> grill B \<subseteq> grill A"
  by (meson equalityD1 mesh_prop11 subset_trans)

lemma grill_antitone_converse:
  assumes A0:"is_upclosed (A::'a set set) \<and> is_upclosed (B::'a set set)"
  shows " grill B \<subseteq> grill A \<longrightarrow> A \<subseteq> B "
  using assms mesh_prop13 by blast


lemma grill_maps_to_upclosed_sets:
  assumes "(A::'a set set) \<noteq> {}"
  shows "is_upclosed (grill A)"
  by (simp add: grill_def mesh_prop1 is_upclosed_def)

lemma upclosure_extensive:
  "is_extensive up_closure"
  using is_extensive_def up_closure_def by fastforce

lemma upc_is_idempotent:
  "up_closure (up_closure A) = up_closure A"
proof-
  let ?A1="up_closure A" let ?A2="up_closure ?A1"
  have LtR:"?A1 \<subseteq> ?A2"
    by (meson is_extensive_def upclosure_extensive)
  have RtL:"?A2 \<subseteq> ?A1"
  proof-
    have RtLB0:"\<forall>x \<in> ?A2. x \<in> ?A1"
    proof
      fix x assume As0:"x \<in> ?A2"
      obtain a2 where As1:"a2 \<in> ?A1 \<and> a2 \<le> x"
        using As0 up_closure_def by auto
      obtain a1 where As2:"a1 \<in> A \<and> a1 \<le> a2"
        using As1 up_closure_def by auto
      have B0:"a1 \<le> x"
        using As1 As2 dual_order.trans by blast
      show "x \<in> ?A1"
        using As2 B0 up_closure_def by auto
     qed
    show ?thesis
      by (simp add: RtLB0 subsetI)
  qed
  with LtR RtL show ?thesis by fastforce
qed

lemma upclosure_is_upclosed:
  "is_upclosed (up_closure A)"
proof-
  let ?U="up_closure A"
  have B0:"(\<And>a b. (a \<le> b \<and>  a \<in> ?U) \<longrightarrow>  b \<in> ?U)"
  proof
    fix a b assume A0:"(a \<le> b \<and>  a \<in> ?U)"
    obtain c where A1:"c \<in> A \<and> c \<le> a"
      using A0 up_closure_def by auto
    have B01:"c \<in> A \<and> c \<le> b"
      using A0 A1 by force
    show "b \<in> ?U"
      using B01 up_closure_def by auto
  qed
  show ?thesis
    by (meson B0 is_upclosed_def)
qed


lemma gril_is_grill_of_upclosure:
  assumes "A \<noteq> {}"
  shows "grill A = grill (up_closure A)"
proof-
  have B0:"A \<subseteq> up_closure A"
    by (metis is_extensive_def upclosure_extensive)
  have B1:"grill (up_closure A) \<subseteq> grill A"
    by (simp add: B0 grill_is_antitone)  
  have B2:"grill A \<subseteq> grill (up_closure A)"
  proof
    fix a assume B2_A0:"a \<in> (grill A)"
    have B2_B1:"\<forall>b \<in> A. inf a b \<noteq> bot"
      by (meson B2_A0 dual_order.refl mesh_prop8 meshes_def)
    show "a \<in> grill (up_closure A)"
    proof-
      have B2_B3:"\<forall>c \<in> up_closure A. inf a c \<noteq> bot"
      proof
        fix c assume B2_A1:"c \<in> up_closure A"
        have B2_B4:"\<exists>b \<in> A. c \<ge> b"
          using B2_A1 up_closure_def by auto
        obtain b where B2_A2:"b \<in> A \<and> c \<ge> b" 
           using B2_B4 by blast
        have B2_B5:"inf a c \<ge> inf a b" 
           by (simp add: B2_A2 inf.coboundedI2)
        have B2_B6:"... \<noteq> bot"
          using B2_A2 B2_B1 B2_B5 bot.extremum_uniqueI by fastforce
        show "inf a c \<noteq> bot" 
          using B2_B6 by blast
      qed
      show ?thesis
        by (simp add: B2_B3 grill_def meshes_def)
     qed
  qed
  with B1 B2 show ?thesis by blast
qed
     
lemma grill_of_grill_is_upclosure:
  "grill (grill (A::'a set set)) = up_closure A"
proof-
  let ?U="up_closure A" and ?G="grill (grill A)"
  have L:"?G \<subseteq> ?U"
  proof 
    fix a assume A0:"a \<in> ?G"
    show "a \<in> ?U"
      by (metis A0 empty_iff gril_is_grill_of_upclosure
          grill_maps_to_upclosed_sets is_upclosed_def mesh_prop12
          mesh_prop14 upclosure_is_upclosed)
  qed
  have R:"?U \<subseteq> ?G"
  proof
     fix a assume A0:"a \<in> ?U"
     obtain x where A1:"x \<in> A \<and> x \<le> a"
       using A0 up_closure_def by auto
     show "a \<in> ?G"
       by (metis A0 \<open>\<And>thesis::bool. (\<And>x::'a set. x \<in> (A::'a set set) \<and> x \<subseteq> (a::'a set) \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> 
           empty_iff gril_is_grill_of_upclosure grill_maps_to_upclosed_sets mesh_prop12 
          mesh_prop14 upclosure_is_upclosed)
  qed
  show ?thesis
    by (simp add: L R dual_order.eq_iff)
qed  

lemma grill_involutory_in_upsets:
  "grill (grill (A::'a set set)) = A \<longleftrightarrow> is_upclosed A"
  by (metis dual_order.refl grill_antitone_converse grill_of_grill_is_upclosure mesh_prop11 subset_antisym upclosure_is_upclosed)

lemma degenerate_grill1:
  "grill (Pow UNIV) = {}"
  by (metis Pow_UNIV UNIV_I equals0I is_upclosed_def mesh_prop15)

lemma degenerate_grill2:
  "grill ({}) = Pow UNIV"
  by (metis Pow_UNIV UNIV_I degenerate_grill1 grill_involutory_in_upsets is_upclosed_def)

lemma grill_grill_is_extensive:
  "is_extensive (\<lambda>A. (grill (grill A)))"
  using is_extensive_def mesh_prop11 by auto

lemma grill_grill_is_isotone:
  "is_isotone (\<lambda>A. (grill (grill A)))"
  by (simp add: grill_is_antitone is_isotone_def)
 

lemma grill_grill_is_idempotent:
  "is_idempotent (\<lambda>A. (grill (grill A)))"
  by (metis (no_types, lifting) grill_grill_is_extensive grill_is_antitone is_extensive_def is_idempotent_def subset_antisym)
  
     
lemma grill_grill_is_closure:
  "is_closure  (\<lambda>A. (grill (grill A)))"
  by (simp add: grill_grill_is_extensive grill_grill_is_idempotent grill_grill_is_isotone is_closure_def)

lemma prime_upset_is_grill_of_filter:
  assumes A0:"A \<noteq> {} \<and> A \<noteq> {{}} \<and> (A \<noteq>  Pow UNIV)" and A1:"is_upclosed A" and A2:"is_prime A"
  shows "\<exists>F. (is_filter F) \<and> (A=grill F)" 
proof-
  have P3:"grill( grill (A) ) = A" by (simp add: A1 grill_involutory_in_upsets)
  let ?B="grill A"
  have P4:"\<forall>a \<in> ?B. (\<forall>b \<in> ?B. (a \<inter> b \<in> ?B))"
  proof
    fix a assume P4A0:"a \<in> ?B" show "\<forall>b \<in> ?B.  (a \<inter> b \<in> ?B)"
    proof
        fix b assume P4A1:"b \<in> ?B" 
        have P4B0:"(UNIV-a) \<notin> A"
          by (simp add: A1 P4A0 mesh_prop15)
        have P4B1:"(UNIV-b) \<notin> A" 
          by (simp add: P4A1 A1 mesh_prop15)
        have P4B2:"(UNIV-a) \<union> (UNIV-b) \<notin> A" 
          using A2 P4B0 P4B1 is_prime_def by blast
        have P4B3:"a \<inter> b \<in> ?B"  
          by (metis Diff_Int P4B2 A1 mesh_prop15)
        show " a \<inter> b \<in> ?B"
        by (simp add: P4B3)
      qed
  qed
  have P5:"is_pisystem ?B" by (simp add: P4 is_pisystem_def)
  have P6:"is_upclosed ?B"
    by (simp add: A0 grill_maps_to_upclosed_sets)
  have P7:"\<exists>F.  ((is_pisystem F) \<and> (is_upclosed F) \<and> (A = grill F))"
    using P3 P5 P6 by auto
  obtain F where P8:"((is_pisystem F) \<and> (is_upclosed F) \<and> (A = grill F))"
    using P7 by blast
  have P9:"is_inhabited F"
    using A0 P8 degenerate_grill2 is_inhabited_def by auto
  show ?thesis
    using is_filter_def P8 P9 downdir_up_pisystem by blast
qed

lemma filtergrill_then_upclosed_prime:
 assumes A0:"A \<noteq> {} \<and> A \<noteq> {{}}" and A1:"A=grill F" and A2:"is_filter F"
 shows "is_upclosed A \<and> is_prime A"
proof-
  have P0:"is_upclosed A" using A1 A2 grill_maps_to_upclosed_sets
    using filter_topped by auto
  have P1:"\<forall>a. \<forall>b. (a\<notin>A\<and>b\<notin>A) \<longrightarrow> a\<union>b\<notin>A"
  proof-
    fix a b
    have P10:"(a \<notin> A \<and>  b \<notin>  A)\<longrightarrow>  a \<union> b \<notin> A"
    proof
      assume P1A0:" (a \<notin> A \<and>  b \<notin>  A)"
      obtain f where P1A1:"f \<in> F \<and> f \<inter> a = {}"
        by (metis A1 A2 Diff_disjoint is_filter_def P1A0 inf.commute mesh_prop15)
      obtain g where P1A2:"g \<in> F \<and> g \<inter> b = {}"
        by (metis A1 A2 Compl_disjoint2 Diff_Compl is_filter_def P1A0 inf_top_left mesh_prop12)
      have P1B1:"(f \<inter> g) \<in> F"
        using A2 is_filter_def P1A1 P1A2 downdir_up_pisystem is_pisystem_def by blast
      have P1B2:"(a \<union> b) \<inter> (f \<inter> g) = {}"
        using P1A1 P1A2 by blast
      have P1B3:"\<exists>h \<in> F. (a \<union> b) \<inter> h = {}" 
        using P1B1 P1B2 by auto
      have P1B4:"(a\<union>b)\<notin>(grill F)"
        by (meson P1B3 dual_order.refl mesh_prop8 meshes_def) 
      show "a\<union>b\<notin>A" by (simp add: P1B4 assms)
     qed
     with P10 show ?thesis
       by (metis A1 A2 Diff_Un is_filter_def downdir_up_pisystem is_pisystem_def mesh_prop15)
  qed
  have P2:"\<forall>a. \<forall>b. a\<union>b\<in>A  \<longrightarrow>  (a\<in>A\<or>b\<in>A)"  using P1 by auto
  have P3:"is_prime A" using P1 is_prime_def by blast
  show ?thesis by (simp add: P0 P3)
qed



lemma grill_extensive:
  assumes A0:"is_filter F" and
          A1:"bot \<notin> F"
  shows "F \<subseteq> (grill F)"
  by (metis A0 A1 filter_inlattice_inf_closed mesh_prop8 meshes_def)


lemma proper_filter_iff:
  fixes F::"'X::order_bot set"
  assumes "is_filter F"
  shows  "is_proper F \<longleftrightarrow> bot \<notin> F"
  by (simp add: assms filter_improper_iff is_proper_def)



lemma ultrafilter_notprime_contradiction:
  fixes a1 a2::"'a::{distrib_lattice,bot}"
  assumes A0:"is_ultrafilter U" and
          A1:"\<not>((sup a1 a2) \<in> U \<longrightarrow> (a1 \<in> U) \<or> (a2 \<in> U))" and
          order_bot:"\<forall>x. bot \<le> x"
  shows "False"
  proof-
    have P:"((sup a1 a2) \<in> U) \<and> \<not>(a1 \<in> U \<or> a2 \<in> U) \<longrightarrow> False"
    proof
    assume A0b:"((sup a1 a2) \<in> U) \<and> \<not>(a1 \<in> U \<or> a2 \<in> U)" 
    have A1:"(sup a1 a2) \<in> U \<and> (a1 \<notin> U \<and> a2 \<notin> U)" 
      using A0 A0b by auto
    let ?S="{x. (sup a1 x) \<in> U}"
    have P2:"U \<subset> ?S"
      proof-
        have P20:"sup a1 a2 \<in> U"
           using A1 by auto
        have P21:"\<forall>u \<in> U. u \<le> sup a1 u"
           by simp
        have P22:"is_upclosed U"
          using A0 is_filter_def is_pfilter_def is_ultrafilter_def by auto
        have P23:"\<forall>u \<in> U. ((sup a1  u) \<in> U)"
          using P21 P22 is_upclosed_imp by blast
        have P24:"\<forall>u \<in> U. u \<in> ?S" 
          by (simp add: P23)
        have P25:"U \<subseteq> ?S"
          using P24 by auto
        have P26:"a2 \<in> ?S \<and> \<not>(a2 \<in> U)"
          by (simp add: A1)
        have P27:"U \<subset> ?S" 
          using P25 P26 by blast
        with P27 show ?thesis
           by simp
     qed
    have P3:"is_pfilter ?S"
      proof-
        have F1:"is_upclosed ?S"
          proof-
            have F1_0:"\<And>a b. (a \<in> ?S \<and> a \<le> b) \<longrightarrow> b \<in> ?S"
              proof
            fix a b assume A1_0:"(a \<in> ?S \<and> a \<le>  b)"
            have F1_1:"sup a1 a \<in> U"
              using A1_0 by auto
            have F1_2:"sup a1 a \<le> sup a1 b"
              by (simp add: A1_0 sup.coboundedI2)
            have F1_3:"is_upclosed U"
              using assms is_filter_def is_pfilter_def is_ultrafilter_def by blast
            have F1_4:"sup a1 b \<in> U"
              using F1_1 F1_2 F1_3 is_upclosed_def by blast
            show "b \<in> ?S"
              by (simp add: F1_4)
          qed
         show ?thesis using F1_0 is_upclosed_def by blast
       qed
       have F2:"is_pisystem ?S"
        proof-
          have F2_0:"\<And>f1 f2. (f1 \<in> ?S \<and> f2 \<in> ?S) \<longrightarrow> ((inf f1 f2) \<in> ?S)"
            proof
              fix f1 f2 assume A4:"f1 \<in> ?S \<and> f2 \<in> ?S"
              let ?f12="inf f1 f2"
              have F2_1:"sup a1 f1 \<in> U \<and> sup a1 f2 \<in> U"
                using A4 by auto
               have F2_2:"inf (sup a1 f1) (sup a1 f2) \<in> U"
                 using A0 F2_1 is_filter_def downdir_up_pisystem is_pfilter_def is_pisystem_def is_ultrafilter_def by blast
               have F2_3:"inf (sup a1 f1) (sup a1 f2) = sup a1 (inf f1 f2)"
                 by (simp add: sup_inf_distrib1)
               have F2_4:"sup a1 (inf f1  f2) \<in> U"
                 using F2_2 F2_3 by auto
               show "?f12 \<in> ?S"
                 by (simp add: F2_4)
           qed
           show ?thesis using F2_0 is_pisystem_def by blast
         qed
      have F3:"is_inhabited ?S"
        using A1 is_inhabited_def by auto
      have F4:"is_proper ?S"
        by (metis A0b UNIV_I is_proper_def mem_Collect_eq sup.idem)
      show ?thesis
        by (simp add: F1 F2 F3 F4 is_filter_def downdir_up_pisystem is_pfilter_def)
      qed
    have P4:"\<not>(is_ultrafilter U)"
      using P2 P3 is_ultrafilter_def by blast
    show "False"
      using P4 assms by blast
   qed
  show "False"
    using A1 P by auto
qed

lemma filter_is_ultra_iff_prime_alt:
  assumes A0:"is_pfilter U"
  shows "is_ultrafilter U \<longleftrightarrow> is_prime_alt U"
proof
  assume A1:"is_ultrafilter U"
  show "is_prime_alt U"
  proof-
    have B0:"\<forall>a. (a \<in> U) \<or> (UNIV-a) \<in> U"
      by (metis A1 Diff_Diff_Int Sup_UNIV Un_Diff_Int assms bot.extremum complete_lattice_class.Sup_upper double_diff is_pfilter_def iso_tuple_UNIV_I set_filter_topped ultrafilter_notprime_contradiction)
    show ?thesis
      by (metis B0 is_filter_def assms grill_extensive is_pfilter_def is_prime_alt_def mesh_prop15 proper_filter_iff subsetD)
  qed
  next
  assume A2:"is_prime_alt U"
  show "is_ultrafilter U" 
  proof-
    have B1:" (\<forall>F .  (is_pfilter F \<and> U \<subseteq> F) \<longrightarrow> U=F)"
    proof (rule ccontr)
      assume A3:"\<not> (\<forall>F .  (is_pfilter F \<and> U \<subseteq> F) \<longrightarrow> U=F)"
      obtain F where  A4:"is_pfilter F \<and> U \<subset> F "
        using A3 by blast
      obtain a where A5:"a\<in> F \<and> a \<notin> U"
        using A4 by blast
      have B2:"(UNIV-a) \<in> U"
        using A2 A5 is_prime_alt_def by blast
      show "False"
        by (metis A4 A5 B2 Diff_disjoint is_filter_def downdir_inf is_pfilter_def proper_filter_iff psubsetD)
    qed
    show ?thesis
      by (simp add: B1 assms is_ultrafilter_def)
  qed
qed


lemma not_in_grill_not_in_ultrafilter:
  assumes "is_ultrafilter U"
  shows "\<forall>u.  u \<notin> (grill U) \<longrightarrow> (u \<notin> U)"
  using assms grill_extensive is_pfilter_def is_ultrafilter_def proper_filter_iff by blast


lemma grill_of_ultrafilter_subset:
  assumes A0:"is_ultrafilter (U::'a set set)"
  shows "(grill U) \<subseteq> U"
proof
  fix a assume A1:"a \<in> grill U"
  have B0:"\<forall>x \<in> U. inf a x \<noteq> bot"
    by (meson A1 dual_order.refl mesh_prop8 meshes_def)
  show "a \<in> U"
    by (meson B0 Diff_disjoint assms filter_is_ultra_iff_prime_alt is_prime_alt_def is_ultrafilter_def)
qed

lemma ultrafilters_grill_fixpoints:
  "\<forall>U. is_ultrafilter  (U::'a set set) \<longrightarrow> (grill U) = U"
  by (meson grill_extensive grill_of_ultrafilter_subset is_pfilter_def is_ultrafilter_def proper_filter_iff subset_antisym)


lemma filter_then_prime_imp_grillid:
  assumes A0:"is_pfilter F" and A1:"is_prime_alt F"
  shows "grill F = F"
  by (simp add: A0 A1 ultrafilters_grill_fixpoints
      filter_is_ultra_iff_prime_alt)


(* voll vereinigungsdualer operator*)

lemma grill_intersection_union_dual:
  assumes A0:"I \<noteq> {}" and A1:"\<forall>i \<in> I. (is_upclosed (EF(i)::'a set set))"
  shows "grill ( \<Inter>i \<in> I. EF(i) ) = (\<Union>i \<in> I. grill (EF(i)))"
proof-
  have B0:"\<forall>i \<in> I. ( \<Inter>i \<in> I. EF(i) ) \<subseteq> (EF(i))" 
     by (simp add: INT_lower)
  have B1:"\<forall>i \<in> I. grill (EF(i)) \<subseteq> grill ( \<Inter>i \<in> I. EF(i) )"
    by (simp add: INF_lower grill_is_antitone)
  have B2:"(\<Union>i \<in> I. grill (EF(i))) \<subseteq>  grill ( \<Inter>i \<in> I. EF(i))"
    using B1 by blast
  have B3:"\<forall>a. a \<notin> (\<Union>i \<in> I. grill (EF(i))) \<longrightarrow> (\<forall>i \<in> I. \<exists>fi \<in> (EF(i)). fi \<inter> a = {})"
    using A1 mesh_prop15 by fastforce
  have B12:"\<And>a. (a \<notin> (\<Union>i \<in> I. grill (EF(i)))) \<longrightarrow> (a \<notin> grill(( \<Inter>i \<in> I. EF(i))))"
  proof
  fix a assume A2:"a \<notin> (\<Union>i \<in> I. grill (EF(i)))"
  have B4:"\<forall>i \<in> I. \<exists>fi \<in> (EF(i)). fi \<inter> a = {}"
    by (meson A2 B3)
  obtain f where A3:"f=(\<lambda>i. SOME fi. fi \<in> (EF(i)) \<and>  (fi \<inter> a = {}) )"
    by simp
  have B5:"\<forall>i \<in> I. (f i) \<inter> a = {}"
    by (smt (verit, best) A3 B4 someI)
  have B6:"a \<inter> (\<Union>i \<in> I. (f i)) = {}"
    using B5 by blast
  have B7:"\<forall>i \<in> I. (f i) \<in> (EF(i))"
    by (smt (verit, del_insts) A3 B4 someI_ex)
  have B8:"\<forall>i \<in> I. (f i)\<subseteq> (\<Union>i \<in> I. (f i))" by blast
  have B9:"\<forall>i \<in> I. (\<Union>i \<in> I. (f i)) \<in> (EF(i))"
    by (meson A1 B7 B8 is_upclosed_def)
  have B10:"(\<Union>i \<in> I. (f i)) \<in>  ( \<Inter>i \<in> I. EF(i))"
    using B9 by blast
  have B11:"a \<notin> grill(( \<Inter>i \<in> I. EF(i)))"
    by (meson B10 B6 mesh_prop8 meshes_def subset_refl)
  show "a \<notin> grill(( \<Inter>i \<in> I. EF(i)))"
    using B11 by blast
  qed
  from B12 have B13:"(\<Union>i \<in> I. grill (EF(i))) \<supseteq>  grill ( \<Inter>i \<in> I. EF(i))" by blast
  with B2 B13 show ?thesis
    by blast
qed


lemma grill_union_intersection_dual:
  assumes A0:"I \<noteq> {}" and A1:"\<forall>i \<in> I. (is_upclosed (EF(i)::'a set set))"
  shows "grill ( \<Union>i \<in> I. EF(i) ) = (\<Inter>i \<in> I. grill (EF(i)))"
proof-
  have B0:"\<forall>a. a \<in> grill ( \<Union>i \<in> I. EF(i) ) \<longleftrightarrow> (\<forall>i \<in> I. \<forall>fi \<in> (EF(i)). a \<inter> fi \<noteq> {})"
    by (simp add: grill_def meshes_def)
  have B1:"\<forall>a. (\<forall>i \<in> I. \<forall>fi \<in> (EF(i)). a \<inter> fi \<noteq> {})  \<longleftrightarrow> (\<forall>i \<in> I. a \<in> grill (EF(i)))"
    by (simp add: grill_def meshes_def)
  have B2:"\<forall>a. a \<in> grill ( \<Union>i \<in> I. EF(i) ) \<longleftrightarrow>  (\<forall>i \<in> I. a \<in> grill (EF(i)))"
    using B0 B1 by presburger
  have B3:"\<forall>a. a \<in> grill ( \<Union>i \<in> I. EF(i) ) \<longleftrightarrow>  a \<in>  (\<Inter>i \<in> I. grill (EF(i)))"
    by (simp add: B2)
  with B3 show ?thesis
    by blast
qed



lemma union_fchain_is_filter3:
  fixes EF::"'X::order_bot set set"
  assumes A0: "\<forall>F \<in> EF. is_pfilter F" 
      and A1: "is_chain(EF)" 
      and A2: "EF \<noteq> {}"
  shows "is_pfilter (Sup (EF))"
proof -
  let ?F = "Sup (EF)"
  have F1: "is_upclosed ?F"
  proof -
    have F1_0: "\<And>a b. (a \<in> ?F \<and> a \<le> b) \<longrightarrow> b \<in> ?F"
    proof
      fix a b assume A3: "a \<in> ?F \<and> a \<le> b"
      then obtain F where B0: "F \<in> EF \<and> a \<in> F"
        using SUP_upper by blast
      then have "b \<in> F"
        using A0 A3 is_filter_def is_pfilter_def is_upclosed_def by blast
      thus "b \<in> ?F"
        using B0 SUP_upper by blast
    qed
    show ?thesis
      by (meson F1_0 is_upclosed_def)
  qed
  have F2: "is_downdir ?F"
  proof -
    have F2_0: "\<And>f1 f2. (f1 \<in> ?F \<and> f2 \<in> ?F) \<longrightarrow> (\<exists>f3 \<in> ?F. f3 \<le> f1 \<and> f3 \<le> f2)"
    proof
      fix f1 f2 assume A4: "f1 \<in> ?F \<and> f2 \<in> ?F"
      then obtain F1 where B0: "F1 \<in> EF \<and> f1 \<in> F1"
        by blast 
      then obtain F2 where B1: "F2 \<in> EF \<and> f2 \<in> F2"
        using A4 by blast 
      from A1 have "F1 \<subseteq> F2 \<or> F2 \<subseteq> F1"
        by (simp add: B0 B1 is_chain_def)
      obtain f3 where B2:"(f3 \<in> F1 \<or> f3 \<in> F2) \<and>  (f3 \<le> f1 \<and> f3 \<le> f2)"
        by (metis A0 B0 B1 is_filter_def \<open>(F1::'X set) \<subseteq> (F2::'X set) \<or> F2 \<subseteq> F1\<close> 
            insert_absorb insert_subset is_downdir_imp is_pfilter_def)
      show "(\<exists>f3 \<in> ?F. f3 \<le> f1 \<and> f3 \<le> f2)"
        using B0 B1 B2 by blast
    qed
    show ?thesis
      by (metis F2_0 is_downdir_def)
  qed
  have F3: "is_inhabited ?F"
    by (metis A0 A2 is_filter_def Union_upper all_not_in_conv bot.extremum_uniqueI is_inhabited_def is_pfilter_def)
  have F4: "is_proper ?F"
    by (metis A0 UNIV_I UnionE is_pfilter_def is_proper_def proper_filter_iff)
  show ?thesis
    by (simp add: F1 F2 F3 F4 is_filter_def is_pfilter_def)
qed


lemma union_of_finer_filter_chain:
  fixes F::"'X::order_bot set" and
        C::"('X::order_bot set set)" 
  assumes A0:"C \<noteq> {}" and
          A1: "C \<subseteq>  (finer_pfilters F)" and
          A2:"is_chain C"
  shows "Sup(C) \<in> (finer_pfilters F)"
proof-
  have B0:"is_pfilter (Sup(C))"
    by (metis A0 A1 A2 CollectD finer_pfilters_def subset_eq union_fchain_is_filter3)
  have B1:"\<forall>c \<in> C. F \<subseteq> c"
    using A1 finer_pfilters_def by auto
  have B2:"\<forall>c \<in> C. c \<subseteq> (Sup(C))"
    by (simp add: complete_lattice_class.Sup_upper)
  have B3:"F \<subseteq> (Sup(C))"
    by (simp add: A0 B1 less_eq_Sup)
  show ?thesis
    by (simp add: B0 B3 finer_pfilters_def)
qed

lemma superset_ultrafilter_existence:
  fixes F::"'X::order_bot set"
  assumes A0:"is_pfilter F"
    shows "\<forall>C \<in> chains(finer_pfilters F).  C \<noteq> {} \<longrightarrow> (\<Union>C) \<in> (finer_pfilters F)"
proof
  let ?U="finer_pfilters F"
  fix C::"('X::order_bot set set)" 
  assume A1:"C \<in> chains ?U"
  show "C \<noteq> {} \<longrightarrow> \<Union>C \<in> (finer_pfilters F)"
  proof
    assume A2:"C \<noteq> {} "
    show "\<Union>C \<in> (finer_pfilters F)"
      by (meson A1 A2 chainsD chainsD2 is_chain_def union_of_finer_filter_chain)
  qed
qed


lemma existence_of_union_in_finer_filters_set:
  fixes F::"'X::order_bot set"
  assumes "is_pfilter F" and "(finer_pfilters F) \<noteq> {}"
  shows "\<And>C. \<lbrakk>C\<noteq>{}; subset.chain (finer_pfilters F) C\<rbrakk> \<Longrightarrow> (Sup(C)) \<in> (finer_pfilters F)"
  by (simp add: is_chain_def subset_chain_def union_of_finer_filter_chain)


lemma exists_finer_ultrafilter:
  fixes F::"'X::order_bot set"
  assumes A0:"is_pfilter F"
    shows "\<exists>G . is_ultrafilter G \<and> F \<subseteq> G"
proof-
  let ?U="finer_pfilters F"
  have B0:"\<forall>C \<in> chains ?U .C \<noteq> {} \<longrightarrow> \<Union>C \<in> ?U"
    by (simp add: assms superset_ultrafilter_existence)
  have B1:"\<exists>S\<in>?U . \<forall>X\<in>?U . S \<subseteq> X \<longrightarrow> X = S"
    by (smt (verit, del_insts) assms empty_Collect_eq finer_pfilters_def order_refl
        subset_Zorn_nonempty existence_of_union_in_finer_filters_set)
  obtain S where B2:"S \<in> ?U \<and> (\<forall>X\<in>?U . S \<subseteq> X \<longrightarrow> X = S)" 
    using B1 by blast
  have B3:"S \<noteq> {}"
    using B2 is_filter_def finer_pfilters_def is_inhabited_def is_pfilter_def by fastforce
  have B4:"\<And>G. (is_pfilter G) \<and> (S \<subseteq> G) \<Longrightarrow> F \<subseteq> G \<Longrightarrow> S = G"
    by (metis B2 CollectI finer_pfilters_def)
  show ?thesis
    by (metis B2 B4 CollectD finer_pfilters_def is_ultrafilter_def order_trans)
qed


lemma finer_ultrafilters_notempty:
  fixes F::"'X::order_bot set"
  assumes "is_pfilter F"
  shows "\<exists>U. (is_ultrafilter U) \<and> (F \<subseteq> U)"
  by (simp add: assms exists_finer_ultrafilter)



definition antitone :: "('X::order \<Rightarrow> 'Y::order) \<Rightarrow> bool" where
"antitone f \<longleftrightarrow> (\<forall>x y. x \<le> y \<longrightarrow> f y \<le> f x)"

definition comp_extensive :: "('X::order \<Rightarrow> 'Y::order) \<Rightarrow> ('Y::order \<Rightarrow> 'X::order) \<Rightarrow> bool" where
"comp_extensive f g \<longleftrightarrow> (\<forall>x. x \<le> g (f x)) \<and> (\<forall>y. y \<le> f (g y))"

definition relation_to_fgc::"('X \<times> 'Y) set \<Rightarrow> (('X set) \<Rightarrow> ('Y set))" where
  "relation_to_fgc R = (\<lambda>(A::('X set)). {(y::'Y). \<forall>x \<in> A. (x, y) \<in> R}) "

definition relation_to_ggc::"('X \<times> 'Y) set \<Rightarrow> (('Y set) \<Rightarrow> ('X set))" where
  "relation_to_ggc R = (\<lambda>(B::('Y set)). {(x::'X). \<forall>y \<in> B. (x, y) \<in> R}) "

definition fgc_to_relation::"(('X set) \<Rightarrow> ('Y set)) \<Rightarrow> ('X \<times> 'Y) set" where
  "fgc_to_relation f = {(x, y). y \<in> f({x}) }"

definition ggc_to_relation::"(('Y set) \<Rightarrow> ('X set)) \<Rightarrow> ('X \<times> 'Y) set" where
  "ggc_to_relation g = {(x, y). x \<in> g({y}) }"

definition is_gc2::"('X::order \<Rightarrow> 'Y::order) \<Rightarrow> ('Y::order \<Rightarrow> 'X::order) \<Rightarrow> bool" where
  "is_gc2 f g \<equiv> (comp_extensive f g) \<and> (antitone f) \<and> (antitone g)"

definition is_join_dual::"('X::{Sup,order} \<Rightarrow> 'Y::{Inf,order}) \<Rightarrow> bool" where
  "is_join_dual f \<equiv> (\<forall>A. ( (f (Sup A)) = (Inf (f`(A))) ))"

definition join_dual_partner::"('X::{Sup,order} \<Rightarrow> 'Y::{Inf,order}) \<Rightarrow> ('Y::{Inf,order} \<Rightarrow> 'X::{Sup,order})" where
  "join_dual_partner f = (\<lambda>y::('Y::{Inf,order}). Sup {x::('X::{Sup,order}). y \<le> (f x)})"

definition is_gc4::"('X::order \<Rightarrow> 'Y::order) \<Rightarrow> ('Y::order \<Rightarrow> 'X::order) \<Rightarrow> bool" where
  "is_gc4 f g \<equiv> \<forall>(x::('X::order)). \<forall>(y::('Y::order)). y \<le> (f x) \<longleftrightarrow> x \<le> (g y)"


lemma finite_ne_subset_induct[consumes 3, case_names singleton insert]:
  assumes "finite F"
      and "F \<noteq> {}"
      and "F \<subseteq> X"
      and singleton: "\<And>x . P {x}"
      and insert: "\<And>x E . finite E \<Longrightarrow> E \<noteq> {} \<Longrightarrow> E \<subseteq> X \<Longrightarrow> x \<in> X \<Longrightarrow> x \<notin> E \<Longrightarrow> P E \<Longrightarrow> P (insert x E)"
    shows "P F"
  using assms(1-3)
  apply (induct rule: finite_ne_induct)
  apply (simp add: singleton)
  by (simp add: insert)


lemma gc2_iff_gc4:
  "is_gc2 f g \<longleftrightarrow> is_gc4 f g"
proof-
  have LtR:"is_gc2 f g \<longrightarrow> is_gc4 f g"
  proof
    assume A0:"is_gc2 f g "
    have LR:"\<And>x y.  y \<le> (f x) \<longrightarrow> x \<le> (g y)"
    proof
      fix x y assume A1:"y \<le> f x"
      have B0:"(g (f x)) \<le> g y"
        using A0 A1 antitone_def is_gc2_def by auto
      have B1:"x \<le> (g (f x))"
        using A0 comp_extensive_def is_gc2_def by blast
      have B2:"... \<le> g y"
        by (simp add: B0)
      show "x \<le> g y"
        using B1 B2 by auto
    qed
    have RL:"\<And>x y.  x \<le> (g y) \<longrightarrow> y \<le> (f x)"
    proof
      fix x y assume A2:"x \<le> g y"
      have B3:"(f (g y)) \<le> f x"
        using A0 A2 antitone_def is_gc2_def by auto
      have B4:"y \<le> (f (g y))"
        using A0 comp_extensive_def is_gc2_def by blast
      have B5:"... \<le> f x"
        by (simp add: B3)
      show "y \<le> f x"
        using B4 B5 by auto
    qed
    show "is_gc4 f g"
      by (metis LR RL is_gc4_def)
  qed
  have RtL:"is_gc4 f g \<longrightarrow> is_gc2 f g"
  proof
    assume A3:"is_gc4 f g"
    have B6:"\<forall>x. x \<le> (g (f x))"
      using A3 is_gc4_def by blast
    have B7:"\<forall>y. y \<le> (f (g y))"
      using A3 is_gc4_def by auto
    have B8:"\<And>x1 x2. x1 \<le> x2 \<longrightarrow> (f x2) \<le> (f x1)"
      by (meson B6 A3 dual_order.trans is_gc4_def)
    have B9:"\<And>y1 y2. y1 \<le> y2 \<longrightarrow> (g y2) \<le> (g y1)"
      by (meson B7 A3 dual_order.trans is_gc4_def)
    show "is_gc2 f g"
      by (simp add: B6 B7 B8 B9 antitone_def comp_extensive_def is_gc2_def)
  qed
  show ?thesis
    using LtR RtL by blast
qed

lemma gc2_imp_join_dual:
  fixes f::"('X::complete_lattice \<Rightarrow> 'Y::complete_lattice)"
  fixes g::"('Y::complete_lattice \<Rightarrow> 'X::complete_lattice)"
  assumes A0:"is_gc2 f g"
  shows "is_join_dual f"
proof-
  have B0:"is_gc4 f g" using assms gc2_iff_gc4 by blast 
  have B1:"\<forall>A. (\<forall>a \<in> A. (f (Sup(A))) \<le> (f a))"
    by (meson antitone_def assms complete_lattice_class.Sup_upper is_gc2_def)
  have B2:"\<forall>A. (\<forall>a \<in> A. (f (Sup(A))) \<le> (Inf (f`A)))"
    by (simp add: B1 INF_greatest)
  have B3:"\<And>y A. y \<le> Inf(f`(A)) \<longleftrightarrow> (\<forall>a \<in> A. (y \<le> (f a)))"
    by (simp add: le_INF_iff)
  have B4:"\<And>y A. y \<le> Inf(f`(A)) \<longleftrightarrow> (\<forall>a \<in> A. (a \<le> (g y)))"
    by (meson B0 B3 is_gc4_def)
  have B5:"\<And>y A. y \<le> Inf(f`(A)) \<longleftrightarrow> ((Sup A) \<le> (g y))"
    by (simp add: B4 Sup_le_iff)
  have B6:"\<And>y A. y \<le> Inf(f`(A)) \<longleftrightarrow> (y \<le> (f (Sup A)))"
    using B0 B5 is_gc4_def by blast
  show ?thesis
    by (meson B6 antisym dual_order.refl is_join_dual_def)
qed

lemma join_dual_imp_gc2:
  fixes f::"('X::complete_lattice \<Rightarrow> 'Y::complete_lattice)"
  fixes g::"('Y::complete_lattice \<Rightarrow> 'X::complete_lattice)"
  assumes A0:"is_join_dual f"
  shows "is_gc2 f (join_dual_partner f)"
proof-
  let ?g="(join_dual_partner f)"
  have B0:"\<And>x1 x2. (x1 \<le> x2) \<longrightarrow> (f x2) \<le> (f x1)"
  proof
    fix x1 x2 assume A1:"(x1::('X::complete_lattice)) \<le> (x2::('X::complete_lattice))"
    have B00:"Sup {x1, x2} = x2"
      using A1 le_iff_sup by auto
    have B01:"(f x2) = (f (Sup {x1, x2}))"
      using B00 by auto
    have B01:"... = (Inf {(f x1), (f x2)})"
      by (metis (mono_tags, lifting) assms image_insert image_is_empty is_join_dual_def)
    have B02:"... \<le> (f x1)"
      by simp
    show "(f x2) \<le> (f x1)"
      using B00 B01 B02 by auto
  qed
  have B1:"\<And>y1 y2. (y1 \<le> y2) \<longrightarrow> (?g y2) \<le> (?g y1)"
  proof
    fix y1 y2 assume A2:"(y1::('Y::complete_lattice)) \<le> (y2::('Y::complete_lattice))" 
    let ?B2="{x::('X::complete_lattice). y2 \<le> (f x)}"
    let ?B1="{x::('X::complete_lattice). y1 \<le> (f x)}"
    have B10:"(?g y2) = Sup ?B2"
      by (simp add: join_dual_partner_def)   
    have B11:"(?g y1) = Sup ?B1"
      by (simp add: join_dual_partner_def)   
    have B12:"?B2 \<subseteq> ?B1"
      using A2 by force
    have B13:"(?g y2) \<le> (?g y1)"
      by (simp add: B10 B11 B12 Sup_subset_mono)
    show "(?g y2) \<le> (?g y1)"
      by (simp add: B13)
  qed
  have B2:"\<And>(y::('Y::complete_lattice)). y \<le> (f (?g y))"
    by (metis assms is_join_dual_def join_dual_partner_def le_INF_iff mem_Collect_eq)
  have B3:"\<And>(x::('X::complete_lattice)). x \<le> (?g (f x))"
    by (simp add: complete_lattice_class.Sup_upper join_dual_partner_def)
  have B4:"(comp_extensive f ?g)"
    by (simp add: B2 B3 comp_extensive_def)
  have B5:"(antitone f) \<and> (antitone ?g)"
    by (simp add: B0 B1 antitone_def)
  show ?thesis
    by (simp add: B4 B5 is_gc2_def)
qed
      
lemma relation_to_gc2:
  "is_gc2 (relation_to_fgc R) (relation_to_ggc R)"
  by (simp add: antitone_def comp_extensive_def is_gc2_def relation_to_fgc_def relation_to_ggc_def subset_eq)

lemma gc2_to_relation1:
  assumes "is_gc2 f g"
  shows "fgc_to_relation f = ggc_to_relation g"
proof-
  have B0:"\<forall>x. \<forall>y. x \<in> (g {y}) \<longrightarrow> y \<in> (f {x})"
    by (meson assms empty_subsetI gc2_iff_gc4 insert_subset is_gc4_def)
  have B1:"\<forall>x. \<forall>y. y \<in> (f {x}) \<longrightarrow> x \<in> (g {y})"
    by (meson assms empty_subsetI gc2_iff_gc4 insert_subset is_gc4_def)
  have B2:"\<forall>x. \<forall>y. y \<in> (f {x}) \<longleftrightarrow>  x \<in> (g {y})"
     using B0 B1 by blast
  have B3:"\<forall>x. \<forall>y. (x, y) \<in>(fgc_to_relation f) \<longleftrightarrow> (x, y) \<in> (ggc_to_relation g)"
    by (simp add: B2 fgc_to_relation_def ggc_to_relation_def)
  show ?thesis
    by (simp add: B3 set_eq_iff)
qed

lemma gc2_to_relation2:
  assumes A0:"is_gc2 f g"
  shows "(relation_to_fgc (fgc_to_relation f)) = f"
proof-
  let ?Rf="fgc_to_relation f"
  let ?f1="relation_to_fgc ?Rf"
  have B0:"is_join_dual f"
    using assms gc2_imp_join_dual by auto
  have B11:"\<And>A y. {y} \<subseteq> ?f1(A) \<longleftrightarrow> (\<forall>a \<in> A. (a, y) \<in> ?Rf)"
    by (simp add: relation_to_fgc_def)
  have B12:"\<And>A y. y \<in> ?f1(A) \<longleftrightarrow> (\<forall>a \<in> A. y \<in> (f {a}))"
    by (simp add: fgc_to_relation_def relation_to_fgc_def)
  have B13:"\<And>A y. {y} \<subseteq> ?f1(A) \<longleftrightarrow> (\<forall>a \<in> A. {y} \<subseteq> (f {a}))"
    by (simp add: B12)
  have B14:"\<And>A y.{y} \<subseteq> ?f1(A) \<longleftrightarrow> ({y} \<subseteq> (\<Inter>a \<in> A. f {a}))"
    by (simp add: B12)
  have B15:"\<And>A. (\<Inter>a \<in> A. f {a}) = (f (\<Union>a \<in> A. {a}))"
    by (metis B0 INT_extend_simps(10) is_join_dual_def)
  have B16:"\<And>A y. {y} \<subseteq> ?f1(A) \<longleftrightarrow> ({y} \<subseteq> (f (\<Union>a \<in> A. {a})))"
    using B14 B15 by force
  have B17:"\<And>A y. {y} \<subseteq> ?f1(A) \<longleftrightarrow> {y} \<subseteq> (f A)"
    using B16 by auto
  have B18:"\<And>A y. y \<in> ?f1(A) \<longleftrightarrow> y \<in> (f A)"
    using B17 by auto
  have B19:"\<And>A.   ?f1(A) = (f A)"
    by (simp add: B18 set_eq_iff)
  show ?thesis
    using B19 by auto
qed

lemma gc2_to_relation3:
  "fgc_to_relation (relation_to_fgc R) = R"
proof-
  let ?f1="relation_to_fgc R"
  let ?R1="fgc_to_relation ?f1"
  have LtR:"\<And>x y. (x, y) \<in> ?R1 \<longrightarrow> (x, y) \<in> R"
  proof
    fix x y assume A0:"(x, y) \<in> ?R1"
    have B0:"y \<in> ?f1({x})"
      by (metis (no_types, lifting) A0 CollectD Pair_inject case_prodE fgc_to_relation_def)
    show "(x, y) \<in> R"
      by (metis (no_types, lifting) B0 CollectD relation_to_fgc_def singletonI)
  qed
  have RtL:"\<And>x y. (x, y) \<in> R \<longrightarrow> (x, y) \<in> ?R1"
  proof
    fix x y assume A0:"(x, y) \<in>R"
    show "(x, y) \<in> ?R1"
      by (simp add: A0 fgc_to_relation_def relation_to_fgc_def)
  qed
  show ?thesis
    using LtR RtL by auto
qed

lemma gc_double_comp:
  assumes A0:"is_gc2 f g"
  shows "(f \<circ> g \<circ> f = f) \<and> (g \<circ> f \<circ> g = g)"
proof-
  have B0:"\<forall>x. (f x) \<le> f ( g (f (x)))"
    using A0 gc2_iff_gc4 is_gc4_def by blast
  have B1:"\<forall>x. x \<le> g (f (x))"
    using A0 comp_extensive_def is_gc2_def by blast
  have B2:"\<forall>x. f ( g (f (x))) \<le> (f x)"
    using B1 antitone_def assms is_gc2_def by blast
  have B3:"\<forall>x. (f x) = f ( g (f (x)))"
    by (simp add: B0 B2 order_antisym)
  have B4:"\<forall>y. (g y) \<le> g ( f (g (y)))"
    using A0 gc2_iff_gc4 is_gc4_def by blast
  have B5:"\<forall>y. y \<le> f (g (y))"
    using A0 comp_extensive_def is_gc2_def by blast
  have B6:"\<forall>y. g ( f (g (y))) \<le> (g y)"
    using B5 antitone_def assms is_gc2_def by blast
  have B7:"\<forall>y. (g y) = g ( f (g (y)))"
    by (simp add: B4 B6 order_antisym)
  show ?thesis
    using B3 B7 by fastforce
qed

lemma gc_composed_idempotent1:
  assumes A0:"is_gc2 f g"
  shows "(f \<circ> g) \<circ> (f \<circ> g) = (f \<circ> g)"
  by (simp add: assms fun.map_comp gc_double_comp)

lemma gc_composed_idempotent2:
  assumes A0:"is_gc2 f g"
  shows "(g \<circ> f) \<circ> (g \<circ> f) = (g \<circ> f)"
  by (simp add: assms gc_double_comp o_assoc)

lemma gc_closure:
  assumes A0:"is_gc2 f g"
  shows "is_closure (f \<circ> g) \<and> is_closure (g \<circ> f)"
proof-
  let ?h1="f \<circ> g" and ?h2="g \<circ> f"
  have C0:"is_extensive ?h1 \<and> is_extensive ?h2"
    by (metis assms comp_apply comp_extensive_def is_extensive_def is_gc2_def)
  have C1:"is_isotone ?h1 \<and> is_isotone ?h2"
    by (metis (mono_tags, lifting) antitone_def assms comp_apply is_gc2_def is_isotone_def)
  have C20:"?h1 \<circ> ?h1 = ?h1"
    by (simp add: assms gc_composed_idempotent1)
  have C21:"?h2 \<circ> ?h2 = ?h2"
    by (simp add: assms gc_composed_idempotent2)
  have C2:"is_idempotent ?h1 \<and> is_idempotent ?h2"
    by (simp add: C20 C21 idempotent_req)
  show ?thesis
    by (simp add: C0 C1 C2 is_closure_def)
qed


lemma grill_is_galois:
  "is_gc2 grill grill"
  by (simp add: gc2_iff_gc4 is_gc4_def mesh_prop11)
     
end