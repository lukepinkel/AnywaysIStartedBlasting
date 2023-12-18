theory FiltersAgain6
  imports Main "./Closures"
begin

(*6th times the charm*)

(*
TODO: The upclosed set of a topped  poset form a moore collection (dually for ideals)

DONE: upsets_moore_family

TODO: The filters on a topped semilattice inf form a moore collection (dually for ideals)

DONE: filter_moore_family

The filters on a lattice form a lattice and a complete semilattice sup (and dually for ya bois) where
  - the finite sup is just finite intersection of filters whose elements are finite joins
  - the arbitrary sup is the upclosure of finite meets for all finite collections  of the union
modularity and distributivity is inherited and in fact the filter lattice is modular iff the 
underlying lattice is and ditto for distributivity
distributivity  means 
  -finite sups are meets of elements from each filter
  -arbitrary sups are  the infs of finitely many elements from the union
  - ultrafilters are prime filters
*)


hide_const(open) List.list.Nil
no_notation List.list.Nil ("[]")  
no_notation Cons (infixr "#" 65)

declare [[show_types]]
declare [[show_sorts]]
declare [[show_consts]]


definition is_inhabited::"'X set  \<Rightarrow> bool" where
   "is_inhabited X \<equiv> (X \<noteq> {})"

lemma is_inhabited_imp:
  "\<And>X. is_inhabited X \<Longrightarrow> \<exists>x. x \<in> X"
  by (simp add: ex_in_conv is_inhabited_def)

definition is_downdir::"'X::ord set \<Rightarrow> bool" where
   "is_downdir X \<equiv> (\<forall>a b. (a \<in> X) \<longrightarrow> ( b \<in> X) \<longrightarrow> (\<exists>c  \<in> X. (c \<le> a) \<and>  (c \<le> b)))"

lemma is_downdir_imp:
  assumes "is_downdir X"
  shows "\<And>a b. (a \<in> X \<and> b \<in> X) \<Longrightarrow> (\<exists>c  \<in> X. (c \<le> a) \<and>  (c \<le> b))"
  using assms is_downdir_def by blast

definition is_upclosed::"'X::ord set \<Rightarrow> bool" where
   "is_upclosed X \<equiv> (\<forall>a b. a \<le> b \<longrightarrow>  a \<in> X \<longrightarrow>  b \<in> X)"

lemma is_upclosed_imp:
  assumes "is_upclosed X"
  shows "\<And>a b. (a \<le> b \<and> a \<in> X) \<Longrightarrow> b \<in> X"
  using assms is_upclosed_def by blast

lemma upsets_moore_family:
  "is_moore_family {E::('X::order_top set). is_upclosed E}"
proof-
  let ?C="{E::('X::order_top set). is_upclosed E}"
  have B0:"\<forall>(a::'X::order_top set). (\<exists>m \<in> (principal_filter_in a ?C). (\<forall>x \<in> (principal_filter_in a ?C). m \<le> x))"
  proof
    fix A::"'X::order_top set"
    let ?Pa="{E::('X::order_top set). is_upclosed E \<and> A \<subseteq> E}"
    have B01:"is_upclosed (Inf ?Pa)"
      by (simp add: is_upclosed_def)
    have B02:"\<forall>E \<in> ?Pa. (Inf ?Pa) \<le> E"
      by blast
    have B03:"Inf?Pa \<in>  (principal_filter_in A ?C)"
      by (simp add: B01 le_Inf_iff principal_filter_def principal_filter_in_def)
    have B04:"?Pa = principal_filter_in A ?C"
      by (simp add: Collect_conj_eq principal_filter_def principal_filter_in_def)
    have B05:"\<forall>x \<in> ?Pa. (Inf ?Pa) \<le> x"
      by blast
    show "(\<exists>m \<in> (principal_filter_in A ?C). (\<forall>x \<in> (principal_filter_in A ?C). m \<le> x))"
      using B03 B04 by auto
  qed
  show ?thesis
    by (metis B0 empty_iff is_moore_family_def is_upclosed_def mem_Collect_eq)
qed


definition is_pisystem::"'X::{ord,inf} set \<Rightarrow> bool" where
   "is_pisystem X \<equiv> (\<forall>a b. a \<in> X  \<longrightarrow> b \<in> X \<longrightarrow> (inf a b)  \<in> X)"


lemma is_pisystem_imp:
  assumes "is_pisystem X"
  shows "\<And>a b. (a \<in> X \<and> b \<in> X) \<Longrightarrow> (inf a b) \<in> X"
  using assms is_pisystem_def by blast


definition is_filter::"'X::ord set \<Rightarrow> bool" where 
  "is_filter F \<equiv> (is_downdir F \<and> is_upclosed F \<and> is_inhabited F)"

context fixes F::"'X::order set"
begin
lemma principal_filter_iso:
  assumes "is_upclosed F"
  shows "\<forall>a. a \<in> F \<longleftrightarrow> ((principal_filter a) \<subseteq> F)"
  by (metis assms is_upclosed_imp mem_Collect_eq order_refl principal_filter_def subset_eq)

end



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


definition binary_filter_sup::"'X::{ord, inf} set \<Rightarrow> 'X::{ord, inf} set \<Rightarrow> 'X::{ord, inf} set" where
  "binary_filter_sup A B = {x. \<exists>a \<in> A. \<exists>b \<in> B. (inf a b) \<le> x}"


(*this is valid even without top element which is only needed for the degenerate case*)
definition filter_closure::"'X::complete_semilattice_inf set \<Rightarrow> 'X::complete_semilattice_inf set" where
  "filter_closure A \<equiv> {a. \<exists>S\<in>Pow(A). finite S \<and>  S \<noteq> {} \<and>  (Inf S) \<le> a}"


definition up_closure::"'X::order set \<Rightarrow> 'X::order set" where
  "up_closure A \<equiv> {x. \<exists>a \<in> A. a \<le> x}"

lemma filter_closure_obtains0:
  "\<And>x. x \<in> filter_closure A \<longleftrightarrow> (\<exists>S\<in>Pow(A). finite S \<and>  S \<noteq> {} \<and>  (Inf S) \<le> x)"
  by (simp add: filter_closure_def)

lemma filter_closure_extensive:
  fixes A::"'X::complete_semilattice_inf set"
  shows " A \<subseteq> filter_closure A"
proof-
  have B0:"\<forall>a \<in> A. Inf {a} \<le> a"
    by (simp add: complete_semilattice_inf_class.Inf_lower)
  have B1:"\<forall>a \<in> A. {a} \<in> Pow(A) \<and> (finite {a}) \<and> ({a} \<noteq> {})"
    by simp
  have B2:"\<forall>a \<in> A. a \<in> (filter_closure A)"
    using B0 B1 filter_closure_def by blast
  show ?thesis
    by (simp add: B2 subset_iff)
qed

lemma filter_closure_isotone:
  fixes A::"'X::complete_semilattice_inf set" and  
        B::"'X::complete_semilattice_inf set"
  assumes A0:"A \<subseteq> B"
  shows "(filter_closure A) \<subseteq> (filter_closure B)"
proof
  fix x assume A1:"x \<in> (filter_closure A)"
  obtain S1 where A2:"S1 \<in> (Pow A) \<and> (finite S1) \<and> (S1 \<noteq> {}) \<and> (Inf S1) \<le> x"
    by (meson A1 filter_closure_obtains0)
  have B0:"S1 \<in> Pow  B"
    using A2 assms by blast
  obtain S2 where A3:"S2 \<in> (Pow B) \<and> (finite S2) \<and> (S2 \<noteq> {}) \<and> (Inf S2) \<le> x"
    using A2 B0 by blast
  show "x \<in> (filter_closure B)"
    using A2 B0 filter_closure_obtains0 by auto
qed




context fixes X::"'X::semilattice_inf set"
begin

lemma downdir_inf:
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

end

context bounded_semilattice_inf_top
begin



end

context fixes X::"'X::lattice set"
begin

lemma upclosed_in_lattice_iff:
  assumes "X \<noteq> {}"
  shows "is_upclosed X \<longleftrightarrow> (\<forall>x z. x \<in> X \<longrightarrow> (sup x z) \<in> X)"
  by (metis inf_sup_ord(3) is_upclosed_def sup.commute sup.orderE)
  
end


context complete_semilattice_inf
begin

lemma infs_eq:
  "inf x (Inf F) = Inf {x, Inf F}"
proof-
  let ?R=" Inf {x, Inf F}"
  let ?L="inf x (Inf F)"
  have B0:"?R \<le> x \<and> ?R \<le> Inf F"
    by (simp add: local.Inf_lower)
  have B1:"?L \<le> ?R"
    using local.Inf_greatest by fastforce
  have B2:"?L \<le> x \<and> ?L \<le> Inf F"
    by simp
  have B3:"?R \<le> ?L"
    by (simp add: B0)
  show ?thesis
    using B1 B3 local.dual_order.eq_iff by auto
qed

lemma infs_insert:
  "Inf {x, Inf F} = Inf (insert x F)"
proof-
  have B0:"\<forall>y \<in> (insert x F). Inf {x, Inf F} \<le> y"
    by (metis infs_eq insertCI insertE local.Inf_lower local.inf.coboundedI2)
  have B1:"\<forall>y \<in>  (insert x F).  Inf (insert x F) \<le> y"
    by (simp add: local.Inf_lower)
  have B2:"Inf {x, Inf F} \<le> Inf (insert x F)"
    using B0 local.Inf_greatest by blast
  have B3:"\<forall>y \<in> {x, Inf F}. (Inf (insert x F)) \<le> y"
    by (simp add: local.Inf_greatest local.Inf_lower)
  have B4:"Inf (insert x F) \<le> Inf {x, Inf F}"
    using B3 local.Inf_greatest by blast
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
        by (simp add: local.Inf_lower)
      have S1:"x \<le> x"
        by simp
      have S2:"x \<le> Inf {x}"
        using local.Inf_greatest by fastforce
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
      by (simp add: infs_eq infs_insert)
    then show ?case
      by (simp add: P2 P4)
qed

end

context 
  fixes    C::"'X::{semilattice_inf, Inf} set"
  assumes  Inf_lower: "\<And>(x::('X::{semilattice_inf, Inf})) A. x \<in> A \<Longrightarrow> Inf A \<le> x" and
           Inf_greatest: "\<And>(z::('X::{semilattice_inf, Inf})) A. ((\<And>x. x \<in> A \<Longrightarrow> z \<le> x) \<Longrightarrow> z \<le> Inf A)"
begin
lemma infs_eq:
  fixes F::"'X::{semilattice_inf, Inf} set"
  shows "inf x (Inf F) = Inf {x, Inf F}"
proof-
  let ?R=" Inf {x, Inf F}"
  let ?L="inf x (Inf F)"
  have B0:"?R \<le> x \<and> ?R \<le> Inf F"
    by (simp add: local.Inf_lower)
  have B1:"?L \<le> ?R"
    using local.Inf_greatest by fastforce
  have B2:"?L \<le> x \<and> ?L \<le> Inf F"
    by simp
  have B3:"?R \<le> ?L"
    by (simp add: B0)
  show ?thesis
    using B1 B3 dual_order.eq_iff by blast
qed

lemma infs_insert:
  fixes F::"'X::{semilattice_inf, Inf} set"
  shows "Inf {x, Inf F} = Inf (insert x F)"
proof-
  have B0:"\<forall>y \<in> (insert x F). Inf {x, Inf F} \<le> y"
    by (metis inf.coboundedI2 insert_iff local.Inf_lower local.infs_eq)
  have B1:"\<forall>y \<in>  (insert x F).  Inf (insert x F) \<le> y"
    by (simp add: local.Inf_lower)
  have B2:"Inf {x, Inf F} \<le> Inf (insert x F)"
    using B0 local.Inf_greatest by blast
  have B3:"\<forall>y \<in> {x, Inf F}. (Inf (insert x F)) \<le> y"
    by (simp add: local.Inf_greatest local.Inf_lower)
  have B4:"Inf (insert x F) \<le> Inf {x, Inf F}"
    using B3 local.Inf_greatest by blast
  show ?thesis
    by (simp add: B2 B4 dual_order.eq_iff)
qed
  

lemma finite_meet_in_set:
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
        by (simp add: local.Inf_lower)
      have S1:"x \<le> x"
        by simp
      have S2:"x \<le> Inf {x}"
        using local.Inf_greatest by fastforce
      have S3:"Inf {x} = x"
        by (simp add: S0 S2 dual_order.eq_iff)
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
      by (simp add: infs_eq infs_insert)
    then show ?case
      by (simp add: P2 P4)
qed

end


lemma pi_system_then_fc:
  fixes X::"'X::{semilattice_inf,Inf} set"
  assumes A0:"is_pisystem X" and
          Inf_lower: "\<And>(x::('X::{semilattice_inf, Inf})) A. x \<in> A \<Longrightarrow> Inf A \<le> x" and
          Inf_greatest: "\<And>(z::('X::{semilattice_inf, Inf})) A. ((\<And>x. x \<in> A \<Longrightarrow> z \<le> x) \<Longrightarrow> z \<le> Inf A)"
  shows "(\<forall>F. F \<noteq> {} \<longrightarrow> finite F \<longrightarrow> F  \<subseteq> X \<longrightarrow> (Inf F) \<in> X)"
proof-
  have B0:"\<And>a1 a2. a1 \<in> X \<Longrightarrow> a2 \<in> X \<Longrightarrow> (inf a1 a2) \<in> X"
    by (simp add: assms is_pisystem_imp)
  have B1:"\<And>F. (F \<noteq> {}) \<and> (finite F) \<and> (F \<subseteq> X) \<longrightarrow> (Inf F) \<in> X"
  proof
    fix F assume A1:"(F \<noteq> {}) \<and> (finite F) \<and> (F \<subseteq> X) "
    show "(Inf F) \<in> X"
      by (simp add: A1 B0 finite_meet_in_set local.Inf_greatest local.Inf_lower)
  qed
  show ?thesis
    using B1 by presburger
qed


lemma filter_closure_idempotent:
  fixes A::"'X::complete_semilattice_inf set"  
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
      by (metis E_def UnionI Union_Pow_eq complete_semilattice_inf_class.Inf_greatest complete_semilattice_inf_class.Inf_lower image_subset_iff subset_Pow_Union)
    have B5:"\<forall>y \<in> Ex. (Inf E) \<le> y"
      using B2 B4 order.trans by blast
    have B6:"(Inf E) \<le> (Inf Ex)"
      by (simp add: B5 complete_semilattice_inf_class.Inf_greatest)
    have B7:"(Inf E) \<le> x"
      using A1 B6 order.trans by blast
    show "x \<in> filter_closure A"
      using B3 B7 filter_closure_obtains0 by blast
  qed
  show ?thesis
    by (simp add: B0 filter_closure_extensive set_eq_subset)
qed

lemma filter_closure_is_closure:
  "is_closure filter_closure"
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

definition filter_sup::"'X::complete_semilattice_inf set set \<Rightarrow> 'X::complete_semilattice_inf set" where
  "filter_sup EF \<equiv> filter_closure(Sup(EF))"

lemma filters_in_filter_cl_range:
  fixes F::"'X::complete_semilattice_inf set"
  assumes A0:"is_filter F"
  shows "filter_closure F = F"
proof-
  have B0:"filter_closure F \<subseteq> F"
  proof-
    have B00:"filter_closure F = {a. \<exists>S\<in>Pow(F). finite S \<and>  S \<noteq> {} \<and>  (Inf S) \<le> a}"
      by (simp add: filter_closure_def)
    have B01:"\<And>a. (\<exists>S\<in>Pow(F). finite S \<and>  S \<noteq> {} \<and>  (Inf S) \<le> a) \<longrightarrow> a \<in> F"
    proof
      fix a assume B01A0:"(\<exists>S\<in>Pow(F). finite S \<and>  S \<noteq> {} \<and>  (Inf S) \<le> a)"
      obtain S where B01A1:"S \<in> Pow(F) \<and> finite S \<and> S \<noteq> {} \<and> (Inf S) \<le> a"
        using B01A0 by force
      have B01B0:"Inf S \<in> F"
        by (meson B01A1 is_filter_def PowD assms complete_semilattice_inf_class.finite_meet_in_set downdir_inf)
      show "a \<in> F"
        using B01A1 B01B0 is_filter_def assms is_upclosed_imp by blast
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
  fixes E::"'X::complete_semilattice_inf set"
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
        by (simp add: B0A3 complete_semilattice_inf_class.Inf_greatest complete_semilattice_inf_class.Inf_lower)
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
  have "is_inhabited ?F"
    using assms filter_closure_extensive is_inhabited_def by blast
  show ?thesis
    by (simp add: B0 B1 FiltersAgain6.is_filter_def \<open>is_inhabited (filter_closure (E::'X set))\<close>)
qed

lemma filter_closure_is_smallest:
  fixes E::"'X::complete_semilattice_inf set"
  assumes A0:"E \<noteq> {}"
  shows "\<And>F. (is_filter F \<and> E \<subseteq> F) \<longrightarrow> (filter_closure E) \<subseteq> F"
proof
  fix F assume "(is_filter F \<and> E \<subseteq> F)"
  show "(filter_closure E) \<subseteq> F"
  proof
    fix x assume "x \<in> filter_closure E"
    show "x \<in> F"
      using \<open>(x::'X) \<in> filter_closure (E::'X set)\<close> \<open>is_filter (F::'X set) \<and> (E::'X set) \<subseteq> F\<close> filter_closure_isotone filters_in_filter_cl_range by blast
    qed
qed

class csemilattice_inftop = complete_semilattice_inf+top+
    assumes top_largest: "\<And>x. x \<le> top"
  
lemma smallest_filter1:
  "is_filter {top::('X::csemilattice_inftop)}"
proof-
    let ?S="{top::('X::csemilattice_inftop)}"
    have B0:"is_upclosed ?S"
      by (simp add: is_upclosed_def order_antisym top_largest)
    have B1:"is_downdir ?S"
      using is_downdir_def by blast
    have B2:"is_inhabited ?S"
      by (simp add: is_inhabited_def)
    show ?thesis
      by (simp add: B0 B1 B2 is_filter_def)
qed


lemma smallest_filter2:
  "\<forall>(F::('X::csemilattice_inftop set)). is_filter F \<longrightarrow>  {top::('X::csemilattice_inftop)} \<subseteq> F"
  by (metis FiltersAgain6.is_filter_def empty_subsetI equals0I filter_in_semilattice_inf_iff inf.orderE insert_subset is_inhabited_def top_largest)

lemma filter_moore_family:
  "is_moore_family {F::('X::csemilattice_inftop set). is_filter F}"
proof-
  let ?EF="{F::('X::csemilattice_inftop set). is_filter F}"
  have B0:"is_filter (top::('X::csemilattice_inftop set))"
    by (simp add: filter_in_semilattice_inf_iff)
  have B1:"(top::('X::csemilattice_inftop set)) \<in> ?EF"
    by (simp add: B0)
  have B2:"\<And>(G::'X::csemilattice_inftop set). G \<noteq> {} \<longrightarrow> (\<exists>F \<in> (principal_filter_in G ?EF).
        (\<forall>H \<in> (principal_filter_in G ?EF). F \<le> H))"
  proof
    fix G::"'X::csemilattice_inftop set" assume B2A0:"G \<noteq> {}"
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
  have B4:"(\<forall>(a::(('X::csemilattice_inftop set))). (\<exists>m \<in> (principal_filter_in a ?EF). (\<forall>x \<in> (principal_filter_in a ?EF). m \<le> x)))"
  proof
     fix a
     show "(\<exists>m \<in> (principal_filter_in a ?EF). (\<forall>x \<in> (principal_filter_in a ?EF). m \<le> x))"
     proof(cases "a = {}")
       case True
        have "is_filter {top::('X::csemilattice_inftop)}"
          by (simp add: smallest_filter1)
        have " (\<forall>x \<in> (principal_filter_in a ?EF). {top::('X::csemilattice_inftop)} \<le> x)"
          by (metis Int_iff mem_Collect_eq principal_filter_in_def smallest_filter2)
       then show ?thesis
         by (metis True UNIV_eq_I \<open>FiltersAgain6.is_filter {top}\<close> empty_subsetI inf_top.right_neutral mem_Collect_eq principal_filter_def principal_filter_in_def)
     next
       case False
       then show ?thesis
         by (simp add: B2)
     qed
  qed
  show ?thesis
    using B3 B4 is_moore_family_def by blast
qed

definition meshes::"('X set set) \<Rightarrow> ('X set set) \<Rightarrow> bool"  (infixl "#" 50)  where
   "(A # B) \<equiv> (\<forall>a \<in> A. \<forall>b \<in> B.  (a\<inter>b \<noteq> {}))"

definition grill::"'X set set \<Rightarrow> 'X set set" where
  "grill A = {x::('X set). {x}#A}"  

definition is_prime::"'X set set \<Rightarrow> bool" where
  "is_prime A \<equiv> (\<forall>a. \<forall>b. a \<union> b \<in> A \<longrightarrow> (a \<in> A \<or> b \<in> A))"

lemma mesh_prop1:
  assumes A0:"{a}# F" and A1:"a \<subseteq> b"
  shows "{b}#F"
proof-
  have B0:"\<forall>f \<in> F. ((a \<inter> f) \<noteq> {})" by (meson A0 insertI1 meshes_def)
  have B1:"\<forall>f \<in> F. ((a \<inter> f) \<subseteq> (b \<inter> f))" by (simp add: A1 inf.coboundedI1)
  have B2:"\<forall>f \<in> F. (b \<inter> f \<noteq> {})"  using B0 B1 by fastforce
  with B2 show ?thesis by (simp add: meshes_def)
qed

lemma mesh_prop2:
  assumes "is_upclosed F"
  shows "(a \<in> F \<longrightarrow> \<not>({(UNIV - a)}#F))"
  by (metis Diff_disjoint Int_commute meshes_def singletonI)

lemma mesh_prop3:
  assumes A0:"is_filter F \<and> is_filter G" and
          A1:"{} \<notin> F \<and> {} \<notin> G"
  shows "F \<subseteq> G \<longrightarrow> F#G"
proof
  assume A1:"F \<subseteq> G"
  show "F#G"
  proof-
    have P0:"\<forall>f \<in>F. \<forall>g \<in> G. f \<inter> g \<noteq> {}"
    proof
      fix f assume B0:"f \<in> F"
      show "\<forall>g \<in> G. f \<inter> g \<noteq> {}"
      proof
        fix g assume B1:"g \<in> G"
        have B2:"f \<in> G" 
          using A1 B0 by auto
        have B3:"is_filter G"
          by (simp add: assms)
        have B4:"is_pisystem G"
          using is_filter_def assms downdir_up_pisystem by auto
        have B5:"f \<inter> g \<in> G" using B1 B2 B4 is_pisystem_def by auto
        show "f \<inter> g \<noteq> {}"
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
  have Eq0:"A#B \<longleftrightarrow> (\<forall>a \<in> A. \<forall>b \<in> B. a \<inter> b \<noteq> {})" by (simp add: meshes_def)
  have Eq1:"... \<longleftrightarrow> (\<forall>a \<in> A. {a}#B)" by (simp add: meshes_def)
  have Eq2:"... \<longleftrightarrow> (\<forall>a \<in> A. a \<in> grill B)" by (simp add: grill_def)
  have Eq3:"... \<longleftrightarrow> A \<subseteq> grill B " by blast
  show ?thesis using Eq0 Eq1 Eq2 Eq3 by presburger
qed

lemma mesh_prop9:
  "A#B \<longleftrightarrow> B#A" by (metis Int_commute meshes_def)

lemma mesh_prop10:
   "A#B \<longleftrightarrow> B \<subseteq> grill A"
  using mesh_prop8 mesh_prop9 by blast

lemma mesh_prop11:
   "A \<subseteq> grill B \<longleftrightarrow> B \<subseteq> grill A"
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
    have B11:"(\<Inter>?HC) \<in> G"
      by (metis (no_types, lifting) A2 B10 B6 B9 is_filter_def Inter_greatest Inter_lower downdir_up_pisystem pi_system_then_fc)
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
  assumes A0:"is_upclosed A \<and> is_upclosed B"
  shows " grill B \<subseteq> grill A \<longrightarrow> A \<subseteq> B "
  using assms mesh_prop13 by blast


lemma grill_maps_to_upclosed_sets:
  assumes "A \<noteq> {}"
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
    have B2_B1:"\<forall>b \<in> A. a \<inter> b \<noteq> {}"
      by (metis B2_A0 Int_commute mesh_prop10 meshes_def order_refl)
    show "a \<in> grill (up_closure A)"
    proof-
      have B2_B3:"\<forall>c \<in> up_closure A. a \<inter> c \<noteq> {}"
      proof
        fix c assume B2_A1:"c \<in> up_closure A"
        have B2_B4:"\<exists>b \<in> A. c \<supseteq> b"
          using B2_A1 up_closure_def by auto
        obtain b where B2_A2:"b \<in> A \<and> c \<supseteq> b" 
           using B2_B4 by blast
        have B2_B5:"a \<inter> c \<supseteq> a \<inter> b" 
           by (simp add: B2_A2 inf.coboundedI2)
        have B2_B6:"... \<noteq> {}"
           using B2_A2 B2_B1 by fastforce
        show "a \<inter> c \<noteq> {}" 
          using B2_B6 by blast
      qed
      show ?thesis
        using B2_B3 mesh_prop15 upclosure_is_upclosed by auto
     qed
  qed
  with B1 B2 show ?thesis by blast
qed
     
lemma grill_of_grill_is_upclosure:
  "grill (grill A) = up_closure A"
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
  "grill (grill A) = A \<longleftrightarrow> is_upclosed A"
  by (metis dual_order.refl grill_antitone_converse grill_of_grill_is_upclosure mesh_prop11 subset_antisym upclosure_is_upclosed)

lemma degenerate_grill1:
  "grill (Pow UNIV) = {}"
  by (metis Pow_UNIV UNIV_I equals0I is_upclosed_def mesh_prop15)

lemma degenerate_grill2:
  "grill ({}) = Pow UNIV"
  by (metis Pow_UNIV UNIV_I degenerate_grill1 grill_involutory_in_upsets is_upclosed_def)


definition is_prime_alt::"'X set set \<Rightarrow> bool" where
  "is_prime_alt U \<equiv> (\<forall>a. ((a \<in> U) \<and> \<not>((UNIV-a) \<in> U)) \<or> (\<not>(a \<in> U) \<and> ((UNIV-a) \<in> U)))"


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
  using A0 A1 mesh_prop10 mesh_prop3 by blast

definition is_proper::"'X::order set \<Rightarrow> bool" where
  "is_proper F \<equiv> F \<noteq> UNIV"

lemma proper_filter_iff:
  fixes F::"'X::order_bot set"
  assumes "is_filter F"
  shows  "is_proper F \<longleftrightarrow> bot \<notin> F"
  by (simp add: assms filter_improper_iff is_proper_def)

definition is_pfilter::"'X::order set \<Rightarrow>  bool" where
  "is_pfilter F \<equiv> (is_filter F) \<and> (is_proper F)"

definition is_ultrafilter::"'X::order set  \<Rightarrow> bool" where
  "is_ultrafilter U \<equiv> (is_pfilter U  \<and> (\<forall>F .  (is_pfilter F \<and> U \<subseteq> F) \<longrightarrow> U=F))"



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
        by (simp add: F1 F2 F3 F4 FiltersAgain6.is_filter_def downdir_up_pisystem is_pfilter_def)
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
  assumes A0:"is_ultrafilter U"
  shows "(grill U) \<subseteq> U"
proof
  fix a assume A1:"a \<in> grill U"
  have B0:"\<forall>x \<in> U. inf a x \<noteq> bot"
    by (meson A1 dual_order.refl mesh_prop8 meshes_def)
  show "a \<in> U"
    by (meson B0 Diff_disjoint assms filter_is_ultra_iff_prime_alt is_prime_alt_def is_ultrafilter_def)
qed

lemma ultrafilters_grill_fixpoints:
  "\<forall>U. is_ultrafilter U \<longrightarrow> (grill U) = U"
  by (meson grill_extensive grill_of_ultrafilter_subset is_pfilter_def is_ultrafilter_def proper_filter_iff subset_antisym)


lemma filter_then_prime_imp_grillid:
  assumes A0:"is_pfilter F" and A1:"is_prime_alt F"
  shows "grill F = F"
  by (simp add: A0 A1 ultrafilters_grill_fixpoints
      filter_is_ultra_iff_prime_alt)


(* voll vereinigungsdualer operator*)

lemma grill_intersection_union_dual:
  assumes A0:"I \<noteq> {}" and A1:"\<forall>i \<in> I. (is_upclosed (EF(i)))"
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
  assumes A0:"I \<noteq> {}" and A1:"\<forall>i \<in> I. (is_upclosed (EF(i)))"
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

definition is_chain::"'X::ord set \<Rightarrow> bool" where
  "is_chain A \<equiv> (\<forall>a1 \<in> A. \<forall>a2 \<in> A. (a1 \<le> a2 \<or> a2 \<le> a1))"



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
    by (simp add: F1 F2 F3 F4 FiltersAgain6.is_filter_def is_pfilter_def)
qed

definition finer_pfilters::"'X::order_bot set \<Rightarrow> 'X::order_bot set set" where
  "finer_pfilters F = {U. is_pfilter U \<and> (F \<subseteq> U)}"
    
definition finer_ultrafilters::"'X::order_bot set \<Rightarrow> 'X::order_bot set set" where
  "finer_ultrafilters F = {U. is_ultrafilter U \<and> (F \<subseteq> U)}"


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




end