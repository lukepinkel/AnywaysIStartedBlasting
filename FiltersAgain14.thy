theory FiltersAgain14
  imports Main "./PartialOrders"
begin
hide_const(open) List.list.Nil
no_notation List.list.Nil ("[]")  
no_notation Cons (infixr "#" 65) 


declare [[show_types]]
declare [[show_sorts]]
declare [[show_consts]]


(*
\strikethrough{6th7th8th9th10th11th12th13th times the charm last one I swear} (it wasnt the last time) 
*)

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

(0).
  (0.1) I shat the bed and ended up referring to both closure ranges as  moore closures in addition
     to the real thing.  Gotta go through and rename
  (0.2) A lot of redundancy can be cut.
     

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
        DONE (filter_on_lattice_binf filter_inlattice_binf_closed filter_on_lattice_bsup
              filter_on_Lattice_bsup_greatest filter_on_lattice_bsup_least)
  (3.2)complete semilattice sup. the finite sup is just finite intersection of filters whose
       elements are finite joins the arbitrary sup is the upclosure of finite meets
        for all finite collections  of the union
      DONE (filter_on_lattice_sup, filter_on_lattice_sup_greater, filter_on_lattice_sup_least_upper)

modularity and distributivity is inherited and in fact the filter lattice is modular iff the 
underlying lattice is and ditto for distributivity
distributivity  means 
  -finite sups are meets of elements from each filter
  -arbitrary sups are  the infs of finitely many elements from the union
  - ultrafilters are prime filters

Every proper filter in a topped distributive lattice is the inf of finer ultrafilters

*)
(*

  Adapted from  https://isabelle.in.tum.de/library/HOL/HOL/Lattices_Big.html 

  and

  T. Nipkow, L.C. Paulson (2005), "Proof Pearl: Defining Functions over Finite Sets", 
  in J. Hurd, T. Melham (Eds.), Theorem Proving in Higher Order Logics, TPHOLs 2005, 
  LNCS, Vol. 3603, Springer, Berlin, Heidelberg. 
  Available at: https://doi.org/10.1007/11541868_25

*)


lemma moore_family_imp:
  "\<And>C. is_moore_family C \<Longrightarrow>(\<And>a. has_min (ub_set_in {a} C))"  
  by (simp add: is_moore_family_def)

lemma moore_family_imp_ne:
  "\<And>C. is_moore_family C \<Longrightarrow> C \<noteq> {}"
  by (simp add: is_moore_family_def)  

lemma moore_family_if_lpf:
  assumes "C \<noteq> {}"
  shows "is_moore_family C \<longleftrightarrow> (\<forall>a. has_min (ub_set_in {a} C))"
  by (simp add: assms is_moore_family_def)

lemma top_principal_filter:
  fixes top::"'a::order"
  assumes is_top:"\<forall>x. x \<le> top"
  shows "ub_set {top} = {top}"
  by (simp add: is_top order_antisym_conv ub_set_def)

lemma top_least_in_principal_filter:
  fixes top::"'a::order"
  assumes is_top:"\<forall>x. x \<le> top"
  shows "is_min top (ub_set {top})"
  by (simp add: is_min_singleton is_top top_principal_filter)


lemma moore_closure_topped:
  fixes C::"'a::order set" and
        top::"'a::order"
  assumes A0:"is_moore_family C" and 
          A1:"\<forall>x. x \<le> top"
  shows "top \<in> C"
  by (metis A0 A1 has_min_iff is_moore_family_def order_antisym_conv singletonI ub_set_in_mem_iff)

lemma in_cl_range_idempotent:
  assumes A0:"is_closure f"
  shows "\<And>x. x \<in> (range f) \<longrightarrow> f x = x"
  by (metis assms image_iff is_closure_def is_idempotent_def)


lemma closure_range_inf_closed_:
  fixes E::"'a::order set" and  f::"'a::order \<Rightarrow> 'a::order" and  i::"'a::order" 
  assumes A0:"is_closure f" and
          A1:"E \<subseteq> range f" and
          A2:"is_inf i E"
  shows "i \<in> range f"
proof-
  have B0:"\<And>x. x \<in> E \<longrightarrow> f i \<le> x"
  proof
    fix x assume A3:"x \<in> E"
    have B00:"f i \<le> f x"
      using A0 A2 A3 is_closure_def is_inf_imp2 is_isotone_def by blast
    have B01:"... =  x"
      using A0 A1 A3 in_cl_range_idempotent by blast
    show "(f i) \<le> x"
      using B00 B01 by force
  qed
  have B1:"(f i) \<in> lb_set E"
    by (simp add: B0 lb_set_elm)
  have B2:"i \<le> f i"
    using A0 is_closure_def is_extensive_def by blast
  have B3:"f i \<le> i"
    using A2 B0 is_inf_imp3 by auto
  show ?thesis
    using B2 B3 order_antisym by blast
qed

lemma closure_range_inf_closed_gen:
  fixes E::"'a::order set" and  f::"'a::order \<Rightarrow> 'a::order" and  i::"'a::order" 
  assumes A0:"is_closure f" and
          A1:"E \<subseteq> range f" and
          A2:"is_inf i E"
  shows "f (i) = i "
  using A0 A1 A2 closure_range_inf_closed_ in_cl_range_idempotent by blast


lemma moore_closure_imp:
  fixes C::"'X::order set"
  assumes A0:"is_moore_family C"
  shows "\<forall>x. (moore_to_closure C) x = InfUn (ub_set_in {x} C)"
  by (simp add: moore_to_closure_def)

lemma moore_family_is_cofinal:
  fixes C::"'X::order set"
  assumes A0:"is_moore_family C"
  shows "\<forall>x. ub_set_in {x} C \<noteq> {}"
  using assms has_min_iff2 is_moore_family_def min_imp_ne by auto


lemma inf_closed_then_moore:
  fixes C::"'X::complete_semilattice_inf set"
  assumes A0:"\<forall>E \<in> Pow(C). (Inf E) \<in> C"
  shows "is_moore_family C"
proof-
  have B0:"\<forall>a. (ub_set_in {a} C) \<in> Pow(C)"
    by (metis Pow_bottom Pow_iff ub_set_in_antitone1 ub_set_in_degenerate)
  have B1:"\<forall>a. Inf(ub_set_in {a} C) \<in> C"
    using B0 assms by auto
  have B2:"\<forall>a. Inf(ub_set_in {a} C) \<in> (ub_set_in {a} C)"
    by (meson B1 CInf_greatest ub_set_in_elm ub_set_in_mem)
  have B3:"\<forall>a. (\<forall>x \<in> (ub_set_in {a} C).  Inf(ub_set_in {a} C) \<le> x)"
    by (simp add: complete_semilattice_inf_class.CInf_lower)
  show ?thesis
    by (metis B2 CInf_lower Pow_top assms empty_iff has_min_iff is_moore_family_def)
qed  



lemma closure_range_inf_closed:
  fixes E::"'X::complete_semilattice_inf set" and
        f::"'X::complete_semilattice_inf \<Rightarrow> 'X::complete_semilattice_inf"
  assumes A0:"is_closure f" and
          A1:"E \<subseteq> range f"
  shows "f (Inf E) = Inf E "
  by (meson A0 A1 closure_range_inf_closed_gen complete_semilattice_inf_is_inf)


lemma moore_closure_imp_csemilattice_inf:
  fixes C::"'X::complete_semilattice_inf set"
  assumes A0:"is_moore_family C"
  shows "\<forall>x. (moore_to_closure C) x = Inf(ub_set_in {x} C)"
  by (metis complete_semilattice_inf_is_inf has_inf_def has_max_iff2 inf_is_inf is_inf_iff is_inf_unique moore_to_closure_def)



lemma moore_to_closure_is_extensive:
  fixes C::"'a::order set"
  assumes A0:"is_moore_family C" 
  shows "is_extensive (moore_to_closure C)"
proof-
  let ?f="moore_to_closure C"
  have C01:"\<forall>x. x \<le> ?f x"
  proof
    fix x
    have B0:"has_min (ub_set_in {x} C)"
      by (simp add: assms moore_family_imp)
    obtain y where A1:"is_min y ( ub_set_in {x} C)"
      using B0 has_min_iff2 by auto
    have B1:"is_inf y (ub_set_in {x} C)"
      by (metis A1 is_inf_def is_max_iff is_min_iff lb_set_mem_iff)
    have B2:"?f x = y"
      by (metis B1 has_inf_def has_max_iff2 inf_is_inf is_inf_def is_inf_unique moore_to_closure_def)
    have B3:"?f x \<in> ub_set_in {x} C"
      using A1 B2 is_min_iff by auto
    show "x \<le> ?f x"
      using B3 ub_set_in_mem by auto
  qed
  show ?thesis
    by (simp add: C01 is_extensive_def) 
qed

lemma principle_filter_anti:
  "\<And>(x1::'a::order) x2 X. x1 \<le> x2 \<Longrightarrow> (ub_set_in {x2} X) \<subseteq>  (ub_set_in {x1} X)"
  by (simp add: order_trans subset_eq ub_set_in_mem_iff)


lemma min_then_inf:
  assumes A0:"has_min A"
  shows "has_inf A"
proof-
  obtain y where A1:"is_min y A"
    using A0 has_min_iff2 by auto
  have B1:"is_inf y A"
    by (metis A1 is_inf_iff is_max_iff is_min_iff lb_set_mem_iff) 
  show ?thesis
    using B1 has_inf_def has_max_iff2 is_inf_def by blast
qed 

lemma moore_to_closure_is_isotone:
  fixes C::"'a::order set"
  assumes A0:"is_moore_family C" 
  shows "is_isotone (moore_to_closure C)"
proof-
  let ?f="moore_to_closure C"
  have C10:"\<And>x1 x2. x1 \<le> x2 \<longrightarrow> (?f x1) \<le> (?f x2)"
  proof
    fix x1 x2::"'a::order" assume A1:"x1 \<le> x2"
    have B0:"(ub_set_in {x2} C) \<subseteq>  (ub_set_in {x1} C)"
      by (simp add: A1 principle_filter_anti)
    have B1:"has_min (ub_set_in {x1} C) \<and> has_min (ub_set_in {x2} C) "
      using assms moore_family_imp by auto
    have B2:"has_inf (ub_set_in {x1} C) \<and> has_inf (ub_set_in {x2} C) "
      by (simp add: B1 min_then_inf)
    have B3:"InfUn  (ub_set_in {x1} C) \<le> InfUn  (ub_set_in {x2} C)"
      using B0 B2 inf_antitone1 by blast
    show "?f x1 \<le> ?f x2"
      by (simp add: B3 moore_to_closure_def)
  qed
  show ?thesis
    by (simp add: C10 is_isotone_def)
qed

lemma moore_to_closure_is_idempotent:
  fixes C::"'a::order set"
  assumes A0:"is_moore_family C" 
  shows "is_idempotent (moore_to_closure C)"
proof-
  let ?f="moore_to_closure C"
  have C0:"is_extensive ?f"
    by (simp add: assms moore_to_closure_is_extensive)
  have C2:"is_idempotent ?f"
  proof-
    have C20:"\<forall>x. ?f x = ?f (?f x)"
    proof 
      fix x
      let ?y1="?f x" and ?y2="?f (?f x)"
      let ?Px="ub_set_in {x} C" and ?Pfx="ub_set_in {?y1} C"
      have C2B0:"?y1 \<in> ?Px"
        by (metis assms has_min_iff2 inf_is_inf is_inf_def is_inf_unique is_max_iff is_min_iff lb_set_mem_iff min_then_inf moore_family_imp moore_to_closure_def)
      have C2B1:"?y2 \<in> ?Pfx"
        by (metis assms has_min_iff2 inf_is_inf is_inf_def is_inf_unique is_max_iff is_min_iff lb_set_mem_iff min_then_inf moore_family_imp moore_to_closure_def)
      have C2B2:"?y1 \<in> C"
        using C2B0 ub_set_in_mem_iff by auto
      have C2B3:"?y1 \<in> ?Pfx"
        by (simp add: C2B2 ub_set_in_mem_iff)
      have C2B4:"\<forall>z \<in> ?Pfx. ?y1 \<le> z"
        by (simp add: ub_set_in_mem_iff)
      have C2B3:"?y1 = InfUn ?Pfx"
        by (metis (no_types, lifting) C2B1 C2B3 assms empty_subsetI has_inf_singleton inf_antitone1 inf_singleton insert_subsetI min_then_inf moore_family_imp moore_to_closure_def order_antisym_conv singleton_iff ub_set_in_mem)
      show "?f x = ?f (?f x)"
        by (metis C2B3 moore_to_closure_def)
      qed
    show ?thesis
      using C20 is_idempotent_def by blast
  qed
  show ?thesis
    using C2 by auto
qed

lemma moore_to_closure_is_idempotent2:
  fixes C::"'a::order set"
  assumes A0:"is_moore_family C" 
  shows "\<forall>c \<in> C. (moore_to_closure C)(c) = c"
proof
  fix c assume A1:"c \<in> C"
  define f where "f=(moore_to_closure C)"
  have B0:"f(c) = InfUn(ub_set_in {c} C)"
    by (simp add: assms f_def moore_closure_imp)
  have B1:"... = c"
    by (metis A1 B0 assms f_def inf_is_inf is_extensive_def is_inf_def is_max_iff is_max_singleton
        lb_set_mem min_then_inf moore_family_imp moore_to_closure_is_extensive order_antisym ub_set_in_elm)
  show "f(c) = c"
    by (simp add: B0 B1)
qed 



lemma moore_to_closure_is_idempotent3:
  fixes C::"'a::order set"
  defines"f \<equiv> (moore_to_closure C)"
  assumes A0:"is_moore_family C" 
  shows "\<And>c. (f(c) = c) \<longrightarrow> c \<in> C"
proof
  fix c 
  assume A1:"f(c) = c"
  have B0:"... = InfUn(ub_set_in {c} C)"
    by (metis A1 f_def moore_to_closure_def)
  have B1:"... = min (ub_set_in {c} C)"
    by (simp add: assms has_least_imp_inf_eq_least moore_family_imp)
  have B2:"c \<in> ub_set_in {c} C"
    by (metis A0 B0 B1 has_sup_in_def is_min_iff is_sup_in_def moore_family_imp
         sup_in_degenerate supin_is_sup ub_set_in_degenerate)
  show "c \<in> C"
    using B2 ub_set_in_mem_iff by blast
qed

lemma moore_to_closure_iscl:
  fixes C::"'a::order set"
  assumes A0:"is_moore_family C"
  shows "is_closure (moore_to_closure C)"
proof-
  let ?f="moore_to_closure C"
  have C0:"is_extensive ?f"
    by (simp add: assms moore_to_closure_is_extensive)
  have C1:"is_isotone ?f"
    by (simp add: assms moore_to_closure_is_isotone)
  have C2:"is_idempotent ?f"
    by (simp add: assms moore_to_closure_is_idempotent)
  show ?thesis
    by (simp add: C0 C1 C2 is_closure_def)
qed


lemma moore_then_inf_closed:
  fixes C::"'a::order set" and top::"'a::order"
  assumes A0:"is_moore_family C" and
          is_top:"\<forall>(a::'a::order). a \<le> top"
  shows "\<And>A. (A \<in> (Pow C) \<and> has_inf A) \<longrightarrow> InfUn A \<in> C"
proof
  fix A assume A1:"(A \<in> (Pow C) \<and> has_inf A)"
  define i where "i = InfUn A"
  show "InfUn A \<in> C"
  proof(cases "A = {}")
    case True
    have B0:"InfUn A = top"
      by (metis A1 True has_max_iff2 if_has_max_max_unique inf_is_inf is_inf_def is_max_top is_top lb_set_degenerate)
    then show ?thesis
      by (simp add: A0 is_top moore_closure_topped)
  next
    case False
    define f where "f=(moore_to_closure C)"
    have B1:"\<forall>a \<in> A. i \<le> a \<and> a \<in> C"
      by (metis A1 Pow_iff empty_subsetI has_inf_singleton i_def inf_antitone1 inf_singleton insert_absorb insert_subset)
    have B2:"\<forall>a \<in> A. f i \<le> f a"
      using A0 B1 f_def is_isotone_def moore_to_closure_is_isotone by blast
    have B3:"\<forall>a \<in> A. f a = a"
      by (simp add: A0 B1 f_def moore_to_closure_is_idempotent2)
    have B4:"f i \<le> i"
      by (metis A1 B2 B3 i_def inf_is_inf is_inf_def is_max_iff lb_set_mem_iff)
    have B5:"f i = i"
      by (metis A0 B4 f_def is_extensive_def moore_to_closure_is_extensive order_class.order_eq_iff)
    have B6:"i \<in> C"
      using A0 B5 f_def moore_to_closure_is_idempotent3 by auto
    then show ?thesis
      by (simp add: i_def)
  qed
qed
  
lemma complete_semilattice_sup_inf_closed_then_moore:
  fixes C::"'a::complete_semilattice_sup set"
  assumes A0:"C \<noteq> {}" and A0:"\<And>E. (E \<in> Pow(C) \<and> (has_inf E)) \<Longrightarrow> (InfUn E) \<in> C"
  shows "is_moore_family C"
proof-
    have P:"\<forall>x. has_min (ub_set_in {x} C)"
    proof
      fix x
      define Cx where "Cx= ub_set_in {x} C"
      have B0:"x \<in> lb_set Cx"
        by (metis Cx_def lb_set_mem_iff singletonI ub_set_in_mem)
      have B1:"lb_set Cx \<noteq> {}"
        using B0 by auto
      have B3:"has_inf (Cx)"
        by (simp add: B1 complete_semilattice_sup_lb_imp_inf)
      define i where "i = InfUn Cx"
      have B4:"x \<le> i"
        by (simp add: B0 B1 CSup_upper complete_semilattice_sup_lb_imp_inf i_def)
      have B5:"i \<in> C"
        by (metis A0 B3 Cx_def Pow_iff i_def inf_le2 ub_set_in_ub_inter)
      have B6:"i \<in> Cx"
        by (metis B4 B5 Cx_def singletonD ub_set_in_elm)
      have B7:"i \<in> lb_set Cx"
        using B3 i_def inf_is_inf is_inf_def is_max_iff by blast
      have B8:"is_min i Cx"
        using B6 B7 is_min_def lb_set_in_lb_univ by fastforce
      show "has_min (ub_set_in {x} C)"
        using B8 Cx_def has_min_def by blast
    qed
    show ?thesis
      by (simp add: P assms(1) is_moore_family_def)
qed

subsubsection ClosureRangeIsMooreFamily
lemma clrange_is_moore:
  fixes f::"'a::order \<Rightarrow> 'a::order"
  assumes A0:"is_closure f"
  shows "is_moore_family (range f)"
proof-
  let ?C="range f"
  have B0:"\<forall>x. (f x) \<in> ?C \<and> (x \<le> f x)"
    using assms is_closure_def is_extensive_def by auto
  have B1:"\<forall>x. (f x) \<in> principal_filter_in x ?C"
    by (metis B0 singletonD ub_set_in_elm)
  have B2:"\<forall>x. principal_filter_in x ?C \<noteq> {}"
    using B1 by blast
  have B3:"\<forall>x. (\<exists>m \<in> (principal_filter_in x ?C). (\<forall>y \<in> (principal_filter_in x ?C). m \<le> y))"
  proof
    fix x
    let ?Px="(principal_filter_in x ?C)"
    define m where B3A0:"m= (f x)"
    have B3B0:"m \<in> ?Px"
      by (simp add: B1 B3A0)
    have B3B1:"\<forall>y \<in> ?Px. m \<le> y"
      by (metis B3A0 assms in_cl_range_idempotent is_closure_def is_isotone_def singletonI ub_set_in_mem_iff)
    show "(\<exists>m \<in> (principal_filter_in x ?C). (\<forall>y \<in> (principal_filter_in x ?C). m \<le> y))"
      using B3B0 B3B1 by blast
    qed
  have B4:"\<forall>x. (has_min (principal_filter_in x ?C))"
    by (meson B3 has_min_iff)
  show ?thesis
    by (simp add: B4 is_moore_family_def)
qed

(*if f is a closure then f(a) is a lower bound of [a, \<rightarrow>)\<inter>(range f)  *)
lemma cl_range_inf1:
  fixes f::"'a::order \<Rightarrow> 'a::order" and
        a::"'a::order"
  assumes A0:"is_closure f" 
  shows "\<forall>y \<in> principal_filter_in a (range f). f(a) \<le> y"
proof
  fix y assume A3A0:"y \<in> principal_filter_in a (range f)"
  have A3B0:"a \<le> y \<and> (\<exists>x. y = (f x))"
    by (meson A3A0 imageE insertI1 ub_set_in_mem)
  have A3B1:"(f y) = y"
    using A3B0 assms in_cl_range_idempotent by blast
  have A3B2:"(f a) \<le> (f y)"
    using A3B0 assms is_closure_def is_isotone_def by blast
  have A3B3:"... = y"
    by (simp add: A3B1)
  show "f(a) \<le> y"
    using A3B2 A3B3 by auto
qed

(*if C is a moore family then f=f_C is such f(a) that a lower bound of [a, \<rightarrow>)\<inter>(range f)  *)
lemma cl_range_inf2:
  fixes C::"'a::order set" and
        a::"'a::order"
  assumes A0:"is_moore_family C" 
  defines "f \<equiv> moore_to_closure C" 
  shows "\<forall>y \<in> (principal_filter_in a (range f)). (f a) \<le> y"
proof
  fix y assume A0:"y \<in> principal_filter_in a (range f)"
  have B0:"is_closure f"
    by (simp add: assms moore_to_closure_iscl)
  have B0:"a \<le> y \<and> (\<exists>x. y = (f x))"
    by (metis A0 B0 in_cl_range_idempotent singletonI ub_set_in_mem)
  have B1:"(f y) = y"
    using B0 assms in_cl_range_idempotent moore_to_closure_iscl by blast
  have B2:"(f a) \<le> (f y)"
    using B0 assms(1) f_def is_isotone_def moore_to_closure_is_isotone by blast
  have B3:"... = y"
    by (simp add: B1)
  show "f(a) \<le> y"
    using B2 B3 by auto
qed


subsubsection DualIsomorphismBetweenMooreFamiliesAndClosures

(*
  Let X=(X, leq) be a poset and if F:Pow(X)\<rightarrow>F(X, X) be the map moore_to_closure and
  G:F(X, X)\<longrightarrow>Pow(X) be the range map, and let (\<C>, \<subseteq>) be the moore familes on X ordered by inclusion
  and  (\<F>, \<le>) be the closure operators ordered pointwise.  Then for any f \<in> \<F> or C \<in> \<C>
  F \<circ> G (f) = f
  G \<circ> F (C) = C
  for any f g \<in> \<F> 
  G(g) \<subseteq> G(f) \<longrightarrow> f \<le> g
  while for any C D \<in> \<C>
  f \<le> g \<longrightarrow> G(g) \<subseteq> G(f)
   
*)


lemma ub_set_single:
  "ub_set {x} = {y. x \<le> y}"
  by (simp add: set_eq_iff ub_set_mem_iff)


lemma moore_cl_iso_inv1:
  fixes f::"'X::order \<Rightarrow> 'X::order"
  assumes A0:"is_closure f" 
  defines "g \<equiv> moore_to_closure (range f)"
  shows "g = f"
proof-
  have B0:"\<forall>x. (g x) =  (f x)"
  proof
    fix a
    have A0:"\<forall>x. (f x) \<in> principal_filter_in x (range f)"
      by (metis A0 is_closure_def is_extensive_def rangeI singletonD ub_set_in_elm)
    have A1:"a \<le> (f a)"
      using assms is_closure_def is_extensive_def by auto
    let ?Pfa = " principal_filter_in a (range f)" and ?fa="f a"
    have A2:"?fa\<in>?Pfa"
      by (simp add: A0)
    have A3:"\<forall>y. y \<in> ?Pfa \<longrightarrow> ?fa \<le> y"
      using assms cl_range_inf1 by blast
    have A30:"has_min (principal_filter_in a (range f))"
      by (simp add: assms(1) clrange_is_moore moore_family_imp)
    have A31:"?fa \<in> lb_set ?Pfa"
      by (simp add: A3 lb_set_elm)
    have A32:"is_min ?fa ?Pfa"
      by (simp add: A2 A3 is_min_iff)
    have A33:"min(?Pfa) = ?fa"
      by (metis A30 A32 has_sup_in_def is_sup_in_def sup_in_degenerate sup_in_unique supin_is_sup ub_set_in_degenerate)
    have A4:"f(a) = InfUn(principal_filter_in a (range f))"
      by (simp add: A30 A33 has_least_imp_inf_eq_least)
    have B1:"principal_filter_in a (range f) = (range f) \<inter> {y. a \<le> y}"
      by (metis Int_commute ub_set_in_ub_inter ub_set_single)
    have B2:"(g a) = InfUn(principal_filter_in a (range f))"
      by (simp add: g_def moore_to_closure_def)
    have B3:"... = InfUn{y \<in> range f. a \<le> y}"
      by (simp add: B1 Collect_conj_eq)
    have B4:"... = InfUn{y. \<exists>x. (y = f x) \<and> (a \<le> (f x))}"
      by (metis rangeE rangeI)
    have B5:"... = f a"
      using A4 B3 B4 by presburger
    show "(g a) = (f a)"
      using A4 B2 by presburger
  qed
  show ?thesis
    using B0 by auto
qed    


lemma moore_cl_iso_inv2:
  fixes C::"'X::complete_semilattice_inf set"
  assumes A0:"is_moore_family C" 
  defines "f \<equiv> moore_to_closure C"
  shows "C = range f"
proof-
  have B0:"\<And>y. (y \<in> (range f)) \<longrightarrow>  y \<in> C"
    proof
      fix y assume B0A0:"(y \<in> (range f))"
      obtain x where B0A1:"(f x) = y"
        using B0A0 by blast
      have B0B1:"y = InfUn(principal_filter_in x C)"
        using A0 B0A1 f_def moore_closure_imp by blast
      show "y \<in> C"
        using A0 B0A0 f_def in_cl_range_idempotent moore_to_closure_is_idempotent3 moore_to_closure_iscl by blast
    qed
  have B1:"\<And>y. (y \<in> C) \<longrightarrow> (y \<in> (range f))"
  proof
    fix y assume B1A0:"y \<in> C"
    have B1B0:"f y = y"
      by (simp add: A0 B1A0 f_def moore_to_closure_is_idempotent2)
    show "y \<in> range(f)"
      by (metis B1B0 rangeI) 
  qed
  show ?thesis
    using B0 B1 by blast
qed


lemma moore_cl_iso1:
  fixes f1::"'a::order \<Rightarrow> 'a::order" and
        f2::"'a::order \<Rightarrow> 'a::order"
  assumes A0:"pointwise_less_eq f1 f2" and
          A1:"is_closure f1 \<and> is_closure f2" 
  shows "(range f2) \<subseteq> (range f1)"
proof-
  let ?G1="range f1" and ?G2="range f2"
  have B0:"\<forall>x \<in> ?G2. f1 x =x"
  proof
    fix x assume B0A0:"x \<in> ?G2"
    have B0B0:"x \<le> (f1 x)"
      using A1 is_closure_def is_extensive_def by blast
    have B0B1:"... \<le> (f2 x)"
      by (meson A0 pointwise_less_def pointwise_less_eq_def)
    have B0B2:"... = x"
      using A1 B0A0 in_cl_range_idempotent by blast
    show "(f1 x) = x"
      using B0B0 B0B1 B0B2 by auto
  qed
  have B1:"\<forall>x \<in> ?G2. x \<in> ?G1"
    by (metis B0 range_eqI)
  show ?thesis
    using B1 by blast
qed

lemma moore_cl_iso2:
  fixes f1::"'a::order \<Rightarrow> 'a::order" and
        f2::"'a::order \<Rightarrow> 'a::order"
  assumes A0:"(range f2) \<subseteq> (range f1)" and
          A1:"is_closure f1 \<and> is_closure f2" 
  shows "pointwise_less_eq f1 f2"
proof-
  let ?G1="range f1" and ?G2="range f2"
  have B0:"?G2 \<subseteq> ?G1"
    using A0 by force
  have B1:"\<forall>x.  (?G2 \<inter> (ub_set {x})) \<subseteq> (?G1 \<inter> (ub_set {x})) "
    using B0 by blast
  have B2:"\<forall>x. principal_filter_in x ?G2 \<subseteq>  principal_filter_in x ?G1"
    by (simp add: B0 ub_set_in_isotone2)
  have B3:"\<forall>x. InfUn( principal_filter_in x ?G1) \<le> InfUn( principal_filter_in x ?G2)"
    by (simp add: A1 B2 clrange_is_moore inf_antitone1 min_then_inf moore_family_imp)
  have B3:"\<forall>x. f1 x \<le> f2 x"
    by (metis A1 B3 moore_cl_iso_inv1 moore_to_closure_def)
  show ?thesis
    by (simp add: B3 pointwise_less_eq_def)
qed

(*Converse is true as well TODO*)
lemma moore_family_is_complete_semilattice_inf:
  fixes A C::"'a::complete_semilattice_inf set"
  assumes A0:"is_moore_family C" and A1:"A \<noteq> {} \<and> A \<subseteq> C"
  shows "((has_inf_in A C) \<and> (InfIn A C = InfUn A))"
proof-
  define i where "i=Inf A"
  have B0:"is_inf i A"
    by (simp add: complete_semilattice_inf_is_inf i_def)
  have B1:"i \<in> C"
    by (metis A0 A1 B0 closure_range_inf_closed_gen moore_cl_iso_inv2 moore_to_closure_is_idempotent3 
        moore_to_closure_iscl)
  have B2:"is_inf_in i A C"
    apply(simp add:is_inf_in_def lb_set_in_def is_max_def ub_set_in_def)
    by (metis B1 CInf_greatest CInf_lower i_def)
  have B3:"has_inf_in A C"
    using B2 has_inf_in_def has_max_def is_inf_in_def by blast
  have B4:"InfUn A = i"
    using B0 has_inf_def has_max_iff2 inf_is_inf is_inf_def is_inf_unique by blast
  have B5:"InfIn A C  = i"
    using B2 B3 inf_in_unique infin_is_inf by blast
  have B6: "InfIn A C = InfUn A"
    by (simp add: B4 B5)
  show ?thesis
    by (simp add: B3 B6)
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
  "\<And>x. x \<in> filter_closure A \<longleftrightarrow> (\<exists>S\<in>Pow(A). finite S \<and>  S \<noteq> {} \<and>  fInf S \<le> x)"
  by (simp add: filter_closure_def)

lemma filter_closure_extensive:
  fixes A::"'a::semilattice_inf set"
  shows " A \<subseteq> filter_closure A"
proof-
  have B0:"\<forall>a. a \<in> A \<longrightarrow>   a \<in> lb_set {a}"
    by (simp add: lb_set_def)
  have B1:"\<forall>a \<in> A. {a} \<in> Pow(A) \<and> (finite {a}) \<and> ({a} \<noteq> {})"
    by simp
  have B2:"\<forall>a \<in> A. a \<in> (filter_closure A)"
    by (metis B1 dual_order.refl filter_closure_obtains0 semilattice_inf_class.singleton)
  show ?thesis
    by (simp add: B2 subset_iff)
qed

lemma filter_closure_isotone:
  fixes A::"'X::semilattice_inf set" and  
        B::"'X::semilattice_inf set"
  assumes A0:"A \<subseteq> B"
  shows "(filter_closure A) \<subseteq> (filter_closure B)"
proof
  fix x assume A1:"x \<in> (filter_closure A)"
  obtain S1 where A2:"S1 \<in> (Pow A) \<and> (finite S1) \<and> (S1 \<noteq> {}) \<and> fInf S1 \<le> x"
    by (meson A1 filter_closure_obtains0)
  have B0:"S1 \<in> Pow  B"
    using A2 assms by blast
  obtain S2 where A3:"S2 \<in> (Pow B) \<and> (finite S2) \<and> (S2 \<noteq> {}) \<and> fInf S2 \<le> x"
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

subsection FilterPiSystemInSemilatticeinf

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
        using is_filter_def LA0 downdir_inf by auto
      have LB1:"(\<forall>x y.  (inf x y) \<in> X \<longrightarrow> (x \<in> X \<and> y \<in> X))"
        by (metis LA2 inf.cobounded1 inf.cobounded2 is_upclosed_imp)
      show ?thesis
        using LB0 LB1 by blast
    qed
  qed
  have RtL:"(\<forall>x y. (x \<in> X \<and> y \<in> X) \<longleftrightarrow> (inf x y) \<in> X)\<longrightarrow> is_filter X"
    by (metis is_filter_def assms binf_def downdir_up_pisystem inf.orderE is_inhabited_def 
        is_pisystem_def is_upclosed_def semilattice_inf_infp_eq_small_inf)
  show ?thesis
    using LtR RtL by blast
qed




lemma filters_inf_closed:
  assumes "is_filter (F::'X::semilattice_inf set)"
  shows "\<And>E. finite E \<Longrightarrow> E \<noteq> {} \<Longrightarrow> E \<subseteq> F \<Longrightarrow> (fInf E \<in> F)"
  using is_filter_def assms downdir_up_pisystem pi_system_then_fc by blast

lemma filter_closure_idempotent:
  fixes A::"'X::semilattice_inf set"  
  shows "(filter_closure A) = (filter_closure (filter_closure A))"
proof-
  have B0:"(filter_closure(filter_closure A)) \<subseteq> filter_closure A"
  proof
    fix x assume A0:"x \<in> (filter_closure(filter_closure A))"
    obtain Ex where A1:"(Ex\<in>Pow( (filter_closure A)) \<and>  finite Ex \<and>  Ex \<noteq> {} \<and>  (fInf Ex) \<le> x)"
      by (meson A0 filter_closure_obtains0)
    have B1:"\<forall>y \<in> Ex. (\<exists>Ey \<in> Pow(A). finite Ey \<and> Ey \<noteq> {} \<and> (fInf Ey) \<le> y)"
      by (metis A1 UnionI Union_Pow_eq filter_closure_obtains0)
    define g where "g=(\<lambda>y. SOME Ey. Ey \<in> Pow(A) \<and> finite Ey \<and> Ey \<noteq> {} \<and> (fInf Ey) \<le> y)"
    have B2:"\<forall>y \<in>  Ex. ((g y) \<in> Pow(A) \<and> (finite (g y)) \<and> (g y \<noteq> {}) \<and> (fInf (g y)) \<le> y)"
      by (metis (mono_tags, lifting) B1 g_def someI)
    define E where "E=(\<Union>(g`Ex))"
    have B3:"E \<in> Pow (A) \<and> finite E \<and> E \<noteq> {}"
      using A1 B2 E_def by auto
    have B4:"\<forall>y \<in> Ex. (fInf E) \<le> (fInf (g y))"
      by (metis B2 B3 E_def SUP_upper subset_imp)
    have B5:"\<forall>y \<in> Ex. (fInf E) \<le> y"
      using B2 B4 order.trans by blast
    have B6:"(fInf E) \<le> (fInf Ex)"
      by (simp add: A1 B5 boundedI)
    have B7:"(fInf E) \<le> x"
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
  fixes F::"'X::semilattice_inf set"
  assumes A0:"is_filter F"
  shows "filter_closure F = F"
proof-
  have B0:"filter_closure F \<subseteq> F"
  proof-
    have B00:"filter_closure F = {a. \<exists>S\<in>Pow(F). finite S \<and>  S \<noteq> {} \<and>  fInf S \<le>  a}"
      by (simp add: filter_closure_def)
    have B01:"\<And>a. (\<exists>S\<in>Pow(F). finite S \<and>  S \<noteq> {} \<and>  fInf S \<le> a) \<longrightarrow> a \<in> F"
    proof
      fix a assume B01A0:"(\<exists>S\<in>Pow(F). finite S \<and>  S \<noteq> {} \<and>  fInf S \<le> a)"
      obtain S where B01A1:"S \<in> Pow(F) \<and> finite S \<and> S \<noteq> {} \<and>  fInf S \<le> a"
        using B01A0 by force
      have B01A1:"(fInf S) \<in> F"
        using B01A1 assms filters_inf_closed by auto
      show "a \<in> F"
        by (meson B01A0 is_filter_def PowD assms filters_inf_closed is_upclosed_imp)
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
  fixes E::"'X::semilattice_inf set"
  assumes A0:"E \<noteq> {}"
  shows "is_filter (filter_closure E)"
proof-
  let ?F="(filter_closure E)"
  have B0:"is_downdir ?F"
  proof-
    have B01:"(\<And>a b.  (a \<in> ?F \<and> b \<in> ?F) \<longrightarrow> (\<exists>c  \<in> ?F. (c \<le> a) \<and>  (c \<le> b)))"
    proof
       fix a b assume B0A0:"a \<in> ?F \<and> b \<in> ?F"
      obtain Sa where B0A1:"Sa \<in> Pow(E) \<and> finite Sa \<and> Sa \<noteq> {} \<and> (fInf Sa) \<le> a"
        by (meson B0A0 filter_closure_obtains0)
      obtain Sb where B0A2:"Sb \<in> Pow(E) \<and> finite Sb \<and> Sb \<noteq> {} \<and> (fInf Sb) \<le> b"
        by (meson B0A0 filter_closure_obtains0) 
      define Sc where B0A3:"Sc=Sa \<union> Sb"
      have B0B2:"Sc \<in> Pow(E) \<and> finite Sc \<and> Sc \<noteq> {}"
        using B0A1 B0A2 B0A3 by auto
      have B0B3:"(fInf Sc) \<le> (fInf Sa) \<and> (fInf Sc) \<le>(fInf Sb)"
        by (simp add: B0A1 B0A2 B0A3 subset_imp)
      have B0B4:"(fInf Sc) \<le> a \<and> (fInf Sc) \<le> b"
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
      obtain Sa where B1A1:"Sa \<in> Pow(E) \<and> finite Sa \<and> Sa \<noteq> {} \<and> (fInf Sa) \<le> a"
        by (meson B1A0 filter_closure_obtains0)
      have B1B1:"(fInf Sa) \<le> b"
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
  fixes E::"'X::semilattice_inf set"
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
  fixes EF::"'X::semilattice_inf set set"
  assumes A0: "EF \<noteq> {}" and A0:"\<forall>F \<in> EF. is_filter F"
  shows "\<forall>F \<in> EF. F \<subseteq>  (filter_sup EF)"
  by (metis A0 Sup_upper filter_closure_isotone filter_sup_def filters_in_filter_cl_range)
  
lemma filter_sup_is_lub:
  fixes EF::"'X::semilattice_inf set set"
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
        by (metis A01 A1 B02 is_filter_def is_upclosed_imp)
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
         by (meson A1 B21 is_filter_def downdir_inf)
       have B23:"inf a b \<in> ?I"
         by (simp add: A0 B22 filter_inf_def)
        show "(\<exists>c  \<in> ?I. (c \<le> a) \<and>  (c \<le> b))"
          by (meson B23 inf.cobounded1 inf.cobounded2)
  qed
  show ?thesis
    by (simp add: B20 is_downdir_def)
  qed
  show ?thesis
    by (simp add: is_filter_def P0 P1 P2)
qed

lemma smallest_filter1:
  "is_filter {top::('X::bounded_semilattice_inf_top)}"
proof-
    let ?S="{top::('X::bounded_semilattice_inf_top)}"
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
  "\<forall>(F::('X::bounded_semilattice_inf_top set)). is_filter F \<longrightarrow>  {top::('X::bounded_semilattice_inf_top)} \<subseteq> F"
  by (simp add: filter_topped)



lemma filter_moore_family:
  "is_moore_family {F::('X::bounded_semilattice_inf_top set). is_filter F}"
proof-
  let ?EF="{F::('X::bounded_semilattice_inf_top set). is_filter F}"
  have B0:"is_filter (top::('X::bounded_semilattice_inf_top set))"
    by (simp add: filter_in_semilattice_inf_iff)
  have B1:"(top::('X::bounded_semilattice_inf_top set)) \<in> ?EF"
    by (simp add: B0)
  have B2:"\<And>(G::'X::bounded_semilattice_inf_top set). G \<noteq> {} \<longrightarrow> (\<exists>F \<in> (principal_filter_in G ?EF).
        (\<forall>H \<in> (principal_filter_in G ?EF). F \<le> H))"
  proof
    fix G::"'X::bounded_semilattice_inf_top set" assume B2A0:"G \<noteq> {}"
    have B20:"G \<subseteq> filter_closure G"
      by (simp add: filter_closure_extensive)
    have B21:"is_filter (filter_closure G)"
      by (simp add: B2A0 filter_closure_is_filter)
    have B22:" (filter_closure G) \<in> principal_filter_in G ?EF"
      by (simp add: B20 B21 ub_set_in_mem_iff)
    have B23:"(\<forall>H \<in> (principal_filter_in G ?EF). is_filter H \<and> G \<subseteq> H)"
      by (simp add: ub_set_in_mem_iff)
    have B24:"\<forall>H \<in> (principal_filter_in G ?EF). (filter_closure G) \<subseteq> H"
      by (meson B23 B2A0 filter_closure_is_smallest)
    obtain F where B25:"F \<in> (principal_filter_in G ?EF) \<and>  (\<forall>H \<in> (principal_filter_in G ?EF). F \<le> H)"
      using B22 B24 by blast
    show "(\<exists>F \<in> (principal_filter_in G ?EF). (\<forall>H \<in> (principal_filter_in G ?EF). F \<le> H))"
      using B25 by blast
  qed
  have B3:"?EF \<noteq> {}"
    using B1 by auto
  have B4:"(\<forall>(a::(('X::bounded_semilattice_inf_top set))). (\<exists>m \<in> (principal_filter_in a ?EF). (\<forall>x \<in> (principal_filter_in a ?EF). m \<le> x)))"
  proof
     fix a
     show "(\<exists>m \<in> (principal_filter_in a ?EF). (\<forall>x \<in> (principal_filter_in a ?EF). m \<le> x))"
     proof(cases "a = {}")
       case True
        have "is_filter {top::('X::bounded_semilattice_inf_top)}"
          by (simp add: smallest_filter1)
        have " (\<forall>x \<in> (principal_filter_in a ?EF). {top::('X::bounded_semilattice_inf_top)} \<le> x)"
          by (metis mem_Collect_eq smallest_filter2 ub_set_in_mem_iff)
       then show ?thesis
         by (metis Int_Collect True mem_Collect_eq singleton_insert_inj_eq smallest_filter1 ub_set_in_ub_inter ub_set_single)
     next
       case False
       then show ?thesis
         by (simp add: B2)
     qed
  qed
  have B5:"(\<forall>(a::(('X::bounded_semilattice_inf_top set))). has_min (principal_filter_in a ?EF))"
    by (meson B4 has_min_iff)
  show ?thesis
    using B3 B5 is_moore_family_def by auto
qed


subsection FilterOnLattice

lemma filter_on_lattice_inf:
  assumes A0:"is_filter (F1::('X::lattice set))" and 
          A2:"is_filter (F2::('X::lattice set))"
  shows "is_filter (inf F1 F2)"
proof-
  let ?I="inf F1 F2"
  have P0:"is_inhabited ?I"
  proof-
    have B00:"is_inhabited F1 \<and> is_inhabited F2"
      using A0 A2 is_filter_def by auto
    obtain x1 x2 where A01:"x1 \<in> F1 \<and> x2 \<in> F2"
      using B00 is_inhabited_imp by blast
    define x where A02:"x=sup x1 x2"
    have B01:"x1 \<le> x \<and> x2 \<le> x"
      by (simp add: A02)
    have B02:"x \<in> inf F1 F2"
      using A0 A01 A2 B01 is_filter_def is_upclosed_imp by auto
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
  by (metis assms empty_iff filter_in_semilattice_inf_iff)


lemma filter_on_lattice_bsup:
  assumes A0:"is_filter (F1::('X::lattice set))" and 
          A2:"is_filter (F2::('X::lattice set))"
  shows "is_filter (binary_filter_sup F1 F2)"
proof-
  let ?S="binary_filter_sup F1 F2"
  have P0:"is_inhabited ?S"
  proof-
    have P00:"is_inhabited F1 \<and> is_inhabited F2"
      using A0 A2 is_filter_def by blast
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
          by (meson A0 P1A1 P1A2 filter_inlattice_inf_closed inf_le1 inf_le2)
        obtain ab2 where P1A4:"ab2 \<in> F2 \<and> ab2 \<le> a2 \<and> ab2 \<le> b2"
          by (meson A2 P1A1 P1A2 filter_inlattice_inf_closed inf_le1 inf_le2)
        have P1B1:"ab1 \<le> (inf a1 b1) \<and> ab2 \<le> (inf a2 b2)"
          by (simp add: P1A3 P1A4)
        have P1B2:"inf a1 b1 \<in> F1 \<and> inf a2 b2 \<in> F2"
          by (simp add: A0 A2 P1A1 P1A2 filter_inlattice_inf_closed)
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
    by (simp add: is_filter_def P0 P1 P2)
qed

lemma filter_on_lattice_bsup_greatest:
  assumes A0:"is_filter (F1::('X::lattice set))" and 
          A1:"is_filter (F2::('X::lattice set))"
  shows "F1 \<subseteq> (binary_filter_sup F1 F2) \<and> F2 \<subseteq> (binary_filter_sup F1 F2)"
proof-
  let ?S="binary_filter_sup F1 F2"
  have B0:"\<And>x. x \<in> F1 \<Longrightarrow> x \<in> ?S"
  proof-
    fix x assume A2:"x \<in> F1"
    obtain b where A3:"b \<in> F2"
      using A1 is_filter_def is_inhabited_imp by auto 
    have B1:"inf x b \<le> x"
      by simp
    show "x \<in> ?S"
      using A2 A3 B1 binary_filter_sup_def by blast
  qed
  have B2:"\<And>x. x \<in> F2 \<Longrightarrow> x \<in> ?S"
    proof-
    fix x assume A4:"x \<in> F2"
    obtain b where A5:"b \<in> F1"
      using A0 is_filter_def is_inhabited_imp by auto 
    have B3:"inf b x \<le> x"
      by simp
    show "x \<in> ?S"
      using A4 A5 B3 binary_filter_sup_def by blast
  qed
  show ?thesis
    by (simp add: B0 B2 subsetI)
qed


lemma filter_on_lattice_bsup_least:
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
      using A2 A4 B1 is_filter_def is_upclosed_imp by auto
  qed
qed

lemma filter_on_lattice_sup:
  fixes EF::"'a::lattice set set"
  assumes A0:"EF \<noteq> {}" and A1:"\<forall>F \<in> EF. is_filter F"
  shows "is_filter (filter_sup(EF))"
proof-
  let ?S="filter_sup(EF)"
  have P0:"is_inhabited ?S"
    by (metis A0 A1 is_filter_def empty_Union_conv ex_in_conv filter_closure_is_filter
         filter_sup_def is_inhabited_def)
  have P1:"is_downdir ?S"
    by (metis is_filter_def P0 filter_closure_idempotent filter_closure_is_filter filter_sup_def is_inhabited_def)
  have P2:"is_upclosed ?S"
    by (metis is_filter_def P0 filter_closure_idempotent filter_closure_is_filter filter_sup_def is_inhabited_def)
  show ?thesis
    by (simp add: is_filter_def P0 P1 P2)
qed

lemma filter_on_lattice_sup_greater:
  fixes EF::"'a::lattice set set"
  assumes A0:"EF \<noteq> {}" and A1:"\<forall>F \<in> EF. is_filter F"
  shows "\<forall>F \<in> EF. F \<le> filter_sup(EF)"
  by (simp add: A0 A1 filter_sup_is_ub)


lemma filter_on_lattice_sup_least_upper:
  fixes EF::"'a::lattice set set"
  assumes A0:"EF \<noteq> {}" and A1:"\<forall>F \<in> EF. is_filter F"
  shows "\<And>G. (is_filter G \<and>  (\<forall>F \<in> EF. F \<le> G))\<longrightarrow>  filter_sup(EF) \<le> G"
  by (simp add: A0 A1 filter_sup_is_lub)



    
subsection MeshingAndGrilling
subsubsection PropertiesOfMeshing
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
  assumes A0:"is_upclosed (F::'X::boolean_algebra set)" and A1:"a \<in> F"
  shows "\<not>({(-a)}#F)"
proof(rule ccontr)
  assume A2:"\<not>(\<not>({(-a)}#F))"
  have B0:"{(-a)}#F"
    using A2 by blast
  have B1:"inf (-a) a = bot"
    by simp
  show "False"
    by (meson A1 B0 B1 insertCI meshes_def)
qed


lemma mesh_prop3:
  assumes A0:"is_filter (F::'X::boolean_algebra set) \<and> is_filter G" and
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
        have B5:"(inf f g) \<in> G"
          by (simp add: A0 B1 B2 filter_inlattice_inf_closed)
        show "inf f g \<noteq> bot"
          using B5 assms(2) by fastforce 
      qed
    qed
    show ?thesis by (simp add: P0 meshes_def)
  qed
qed

lemma mesh_prop4:
  assumes "is_upclosed (A::'X::boolean_algebra set)"
  shows "(x \<notin> A) \<longleftrightarrow> {(- x)}#A"
proof-
  let ?cx="-x" let ?S="{?cx}"
  let ?L="x \<notin> A" let ?R="?S#A"
  have LtR:"?L \<longrightarrow> ?R"
    by (metis assms compl_le_compl_iff inf_shunt is_upclosed_imp meshes_def singletonD)  
  have RtL:"?R \<longrightarrow> ?L" using assms mesh_prop2 by auto
  with LtR RtL show ?thesis by blast
qed
  
lemma mesh_prop5:
  assumes "is_upclosed (A::'X::boolean_algebra set)"
  shows "(x \<in> A) \<longleftrightarrow> \<not>({( - x)}#A)"
  using assms mesh_prop4 by blast

lemma mesh_prop6:
  assumes "is_upclosed (A::'X::boolean_algebra set)"
  shows "((-x) \<notin> A) \<longleftrightarrow> {x}#A"
  by (simp add: Diff_Diff_Int assms mesh_prop4)

lemma mesh_prop7:
  assumes "is_upclosed (A::'X::boolean_algebra set)"
  shows "((-x) \<in> A) \<longleftrightarrow> \<not>({x}#A)"
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
  assumes "is_upclosed (A::'X::boolean_algebra set)"
  shows "x \<in> A \<longleftrightarrow> (-x) \<notin> grill A"
  by (meson assms empty_subsetI insert_subset mesh_prop4 mesh_prop8)


lemma mesh_prop13:
  assumes "is_upclosed (A::'X::boolean_algebra set)"
  shows "x \<notin> A \<longleftrightarrow> (-x) \<in>  grill A"
  using assms mesh_prop12 by blast

lemma mesh_prop14:
  assumes "is_upclosed (A::'X::boolean_algebra set)"
  shows "(-x) \<in> A \<longleftrightarrow> x \<notin> grill A"
  by (simp add: assms double_diff mesh_prop12)

lemma mesh_prop15:
  assumes "is_upclosed (A::'X::boolean_algebra set)"
  shows "(- x) \<notin>  A \<longleftrightarrow> x \<in> grill A"
  by (simp add: assms mesh_prop14)


lemma mesh_prop16:
  fixes EF::"'X::complete_boolean_algebra set set"
  assumes A0:"\<forall>F \<in> EF. (is_filter F) \<and> (bot \<notin> F)" and
          A1:"finite EF" and
          A2:"is_filter G \<and> bot \<notin> G" and
          A0b:"EF \<noteq> bot \<and> EF \<noteq> {bot}"
  shows "G#(fInf (EF)) \<longleftrightarrow> (\<exists>F \<in> EF. G#F)"
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
    have B3:"(\<forall>F \<in> EF. \<exists>f \<in> F. (-f) \<in> G)"
      by (meson A3 B2 mesh_prop15) 
    obtain u where A5:"u=(\<lambda>F. SOME f. (f \<in> F \<and> (-f)\<in>G ) )" by simp
    have B4:" (\<forall>F \<in> EF. (-(u(F))) \<in> G)"  by (metis (no_types, lifting) A5 B3 someI)
    let ?H="u`EF" let ?HC="{b. \<exists>h \<in>?H. b=-h}"
    have B5:"finite ?H" by (simp add: A1)
    have B6:"finite ?HC"  by (metis B5 finite_imageI image_def)
    have B7:"(\<forall>hc \<in> ?HC. hc \<in> G)" using B4 by blast
    have B9:"?HC \<subseteq> G"
      using B7 by blast
    have B10:"?HC \<noteq> {}"
      using A0b by blast
    have B11:"?HC \<subseteq> G \<and> is_filter G \<and> ?HC \<noteq> {}"
      using A2 B10 B9 by blast
    have B11:"(fInf ?HC) \<in> G"
      using B11 B6 filters_inf_closed by auto
    have B12:"(-(fInf ?HC)) = fSup (?H)"
      by (metis (no_types) B10 B5 B6 boolean_algebra_class.boolean_algebra.double_compl finf_complete_lattice fsup_complete_lattice image_def image_empty uminus_Sup)
    have B13:" (fInf ?HC) \<in> G  \<longrightarrow> (fSup(?H)) \<notin> grill G"
      using A3 B12 mesh_prop12 by fastforce
    have B14:"\<forall>h \<in> ?H. \<exists>F \<in> EF. h=u(F)"
         by blast
    have B15:"\<forall>F \<in> EF. (u(F) \<in> F)"
        by (metis (mono_tags, lifting) A5 B3 someI_ex)
    have B16:"\<forall>F \<in> EF. \<exists>u \<in> ?H. u \<in> F"
       using B15 by blast
    have B17:"\<forall>F \<in> EF. \<exists>u \<in> F. u \<le> (fSup(?H))"
      by (metis A1 B16 Sup_upper finite_imageI fsup_complete_lattice insert_absorb insert_not_empty)
    have B17:"(fSup(?H)) \<in> ?INF"
      by (meson A0 B17 is_filter_def InterI is_upclosed_imp)
    show "\<not>(?L)"
      using B11 B13 B17 mesh_prop10 by blast
  qed
  with LtR RtL show ?thesis
    by (metis A0b A1 finf_complete_lattice) 
qed

subsubsection PropertiesOfGrilling

lemma grill_is_antitone:
  "A \<subseteq> B \<longrightarrow> grill B \<subseteq> grill A"
  by (meson equalityD1 mesh_prop11 subset_trans)

lemma grill_antitone_converse:
  assumes A0:"is_upclosed (A::'a::complete_boolean_algebra set) \<and> is_upclosed (B::'a::complete_boolean_algebra set)"
  shows " grill B \<subseteq> grill A \<longrightarrow> A \<subseteq> B "
  using assms mesh_prop13 by blast


lemma grill_maps_to_upclosed_sets:
  assumes "(A::'a::complete_boolean_algebra set) \<noteq> {}"
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
  "grill A = grill (up_closure A)"
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

lemma upclosure_if:
  fixes A::"'a::complete_boolean_algebra set" and
        a::"'a::complete_boolean_algebra"
  assumes A0:"a \<in> up_closure A"
  shows "a \<in> grill( grill A)"
proof-
  have B0:"\<forall>x. x \<in> grill (grill A) \<longleftrightarrow> (\<forall>y \<in> grill A. inf x y \<noteq> bot)"
    by (simp add: grill_def meshes_def)
  have B1:"\<forall>x. x \<in> grill (grill A) \<longleftrightarrow> (\<forall>y. (\<forall>z \<in> A. inf y z \<noteq> bot) \<longrightarrow> inf x y \<noteq> bot)"
    by (simp add: grill_def meshes_def)
  have B2:"is_upclosed (up_closure A)"
    using upclosure_is_upclosed by auto
  have B3:"-a \<notin> grill (up_closure A)"
    using B2 assms mesh_prop12 by blast
  have B4:"a \<in> grill (grill (up_closure A))"
    using B3 assms grill_maps_to_upclosed_sets mesh_prop15 by auto
  have B5:"grill (up_closure A) = grill A"
    using gril_is_grill_of_upclosure by blast
  show ?thesis
    using B4 B5 by force
qed
     
lemma grill_of_grill_is_upclosure:
  "grill (grill (A::'a::complete_boolean_algebra set)) = up_closure A"
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
       by (simp add: A0 upclosure_if)
  qed
  show ?thesis
    by (simp add: L R dual_order.eq_iff)
qed  

lemma grill_involutory_in_upsets:
  "grill (grill (A::'a::complete_boolean_algebra set)) = A \<longleftrightarrow> is_upclosed A"
  by (metis dual_order.refl grill_antitone_converse grill_of_grill_is_upclosure mesh_prop11 subset_antisym upclosure_is_upclosed)

lemma degenerate_grill1:
  "grill (UNIV::'a::complete_boolean_algebra set) = bot"
  by (metis UNIV_I equals0I is_upclosed_def mesh_prop15)

lemma degenerate_grill2:
  "grill (bot) = (UNIV::'a::complete_boolean_algebra set)"
  by (metis UNIV_I degenerate_grill1 grill_involutory_in_upsets is_upclosed_def)

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
  fixes A::"'a::complete_boolean_algebra set"
  assumes A0:"bot \<notin> A \<and> (A \<noteq>  UNIV)" and A1:"is_upclosed A" and A2:"is_prime A"
  shows "\<exists>F. (is_filter F) \<and> (A=grill F)" 
proof-
  let ?B="grill A"
  have P3:"grill(?B ) = A"
    by (simp add: A1 grill_involutory_in_upsets)
  have P4:"\<forall>a \<in> ?B. (\<forall>b \<in> ?B. (inf a b \<in> ?B))"
  proof
    fix a assume P4A0:"a \<in> ?B" show "\<forall>b \<in> ?B.  (inf a b \<in> ?B)"
    proof
        fix b assume P4A1:"b \<in> ?B" 
        have P4B0:"(-a) \<notin> A"
          by (simp add: A1 P4A0 mesh_prop15)
        have P4B1:"(-b) \<notin> A" 
          by (simp add: P4A1 A1 mesh_prop15)
        have P4B2:"sup (-a) (-b) \<notin> A" 
          using A2 P4B0 P4B1 is_prime_def by blast
        have P4B3:"inf a b \<in> ?B"
          using A1 P4B2 mesh_prop15 by fastforce  
        show " inf a b \<in> ?B"
          by (simp add: P4B3)
      qed
  qed
  have P5:"is_pisystem ?B"
    by (simp add: P4 is_pi_system_imp)
  have P6:"is_upclosed ?B"
    using P3 grill_involutory_in_upsets by fastforce
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
  fixes A::"'a::complete_boolean_algebra set"
  assumes A0:"bot \<notin> A" and A1:"A=grill F" and A2:"is_filter F"
  shows "is_upclosed A \<and> is_prime A"
proof-
  have P0:"is_upclosed A" using A1 A2 grill_maps_to_upclosed_sets
    using filter_topped by auto
  have P1:"\<forall>a. \<forall>b. (a\<notin>A\<and>b\<notin>A) \<longrightarrow> sup a b\<notin>A"
  proof-
    fix a b
    have P10:"(a \<notin> A \<and>  b \<notin>  A)\<longrightarrow>  sup a b \<notin> A"
    proof
      assume P1A0:" (a \<notin> A \<and>  b \<notin>  A)"
      obtain f where P1A1:"f \<in> F \<and> (inf f a) = bot"
        using A1 A2 is_filter_def P1A0 boolean_algebra.conj_cancel_left mesh_prop15 by blast
      obtain g where P1A2:"g \<in> F \<and> (inf g b) = bot"
        using A1 A2 is_filter_def P1A0 boolean_algebra.conj_cancel_left mesh_prop15 by blast
      have P1B1:"(inf f g) \<in> F"
        by (simp add: A2 P1A1 P1A2 filter_inlattice_inf_closed)
      have P1B2:"inf (sup a b) (inf f g) = bot"
        by (metis (no_types, lifting) P1A1 P1A2 boolean_algebra.conj_disj_distrib2 inf.left_commute inf_bot_right inf_commute)
      have P1B3:"\<exists>h \<in> F. inf (sup a b) h = bot" 
        using P1B1 P1B2 by auto
      have P1B4:"(sup a b)\<notin>(grill F)"
        by (meson P1B3 dual_order.refl mesh_prop8 meshes_def) 
      show "sup a b\<notin>A" by (simp add: P1B4 assms)
     qed
     with P10 show ?thesis
       by (metis (no_types, lifting) A1 A2 is_filter_def bex_empty boolean_algebra.abstract_boolean_algebra_axioms boolean_algebra.de_Morgan_disj filter_in_semilattice_inf_iff filter_topped grill_involutory_in_upsets mesh_prop13)
  qed
  have P2:"\<forall>a. \<forall>b. sup a b\<in>A  \<longrightarrow>  (a\<in>A\<or>b\<in>A)" 
     using P1 by auto
  have P3:"is_prime A" 
    using P1 is_prime_def by blast
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
                 using A0 F2_1 filter_inlattice_inf_closed is_pfilter_def is_ultrafilter_def by blast
               have F2_3:"inf (sup a1 f1) (sup a1 f2) = sup a1 (inf f1 f2)"
                 by (simp add: sup_inf_distrib1)
               have F2_4:"sup a1 (inf f1  f2) \<in> U"
                 using F2_2 F2_3 by auto
               show "?f12 \<in> ?S"
                 by (simp add: F2_4)
           qed
           show ?thesis
             using F2_0 is_pi_system_imp by blast
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
  fixes U::"'a::{boolean_algebra, order_bot} set"
  assumes A0:"is_pfilter U"
  shows "is_ultrafilter U \<longleftrightarrow> is_prime_alt U"
proof
  assume A1:"is_ultrafilter U"
  show "is_prime_alt U"
  proof-
    have B0:"\<forall>a. (a \<in> U) \<or> (-a) \<in> U"
      by (metis A1 assms bot_least compl_sup_top filter_topped is_pfilter_def ultrafilter_notprime_contradiction)
    show ?thesis
      by (metis B0 assms boolean_algebra.conj_cancel_right filter_inlattice_inf_closed is_pfilter_def is_prime_alt_def proper_filter_iff)
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
      have B2:"(-a) \<in> U"
        using A2 A5 is_prime_alt_def by blast
      show "False"
        by (metis A4 A5 B2 boolean_algebra.conj_cancel_right filter_inlattice_inf_closed is_pfilter_def proper_filter_iff psubsetD)
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
  assumes A0:"is_ultrafilter (U::'a::{boolean_algebra, order_bot} set)"
  shows "(grill U) \<subseteq> U"
proof
  fix a assume A1:"a \<in> grill U"
  have B0:"\<forall>x \<in> U. inf a x \<noteq> bot"
    by (meson A1 dual_order.refl mesh_prop8 meshes_def)
  show "a \<in> U"
    using B0 assms boolean_algebra.conj_cancel_right filter_is_ultra_iff_prime_alt is_prime_alt_def is_ultrafilter_def by blast
qed

lemma ultrafilters_grill_fixpoints:
  "\<forall>U. is_ultrafilter  (U::'a::{boolean_algebra, order_bot} set) \<longrightarrow> (grill U) = U"
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

lemma exists_finer_filter_iff:
  fixes F::"'X::{boolean_algebra,order_bot} set" and 
        a::"'X::{boolean_algebra,order_bot}"
  assumes A0:"is_pfilter F" and A1:"\<forall>f \<in> F. inf f a \<noteq> bot"
  shows "is_pfilter (filter_closure (\<Union>{F, {a}})) \<and> a \<in> (filter_closure (\<Union>{F, {a}})) \<and>  F \<subseteq> (filter_closure (\<Union>{F, {a}}))"
proof-
  define Fa where "Fa=\<Union>{F, {a}}"
  define G where "G=filter_closure Fa"
  have B0:"is_pfilter G"
  proof-
    have A01:"is_filter G"
      by (simp add: G_def Fa_def filter_closure_is_filter)
    have A02:"bot \<notin> G"
    proof-
      have A020:"a \<noteq> bot"
        using A0 A1 boolean_algebra.conj_zero_right filter_topped is_pfilter_def by blast
      have A021:"bot \<notin> F"
        using A1 inf_bot_left by blast
      have A022:"bot \<notin> Fa"
        using Fa_def A020 A021 by blast
      have A024:"\<forall>S \<in> Pow(F). finite S \<and> S \<noteq> {} \<longrightarrow> fInf S \<noteq> bot"
        by (metis A0 A021 Pow_iff filters_inf_closed is_pfilter_def)
      have A025:"\<And>S. S \<in> Pow(Fa) \<and> finite S \<and> S \<noteq> {} \<longrightarrow> fInf S \<noteq> bot"
      proof
        fix S assume A0250:"S \<in> Pow(Fa) \<and> finite S \<and> S \<noteq> {} "
        show "fInf S \<noteq> bot"
        proof(cases "a \<in> S")
          case True
          have A0251:"fInf S = (if (S-{a}={}) then a else (inf a (fInf(S - {a}))))"
            using A0250 True semilattice_inf_class.remove by blast
          have "fInf S \<noteq> bot"
          proof(cases "S-{a}={}")
            case True
            then show ?thesis
              using A020 A0251 by presburger
          next
            case False
            have A0252:"(finite (S - {a})) \<and> ((S - {a}) \<noteq> {}) \<and> ((S - {a}) \<subseteq> F)"
              using A0250 Fa_def False by blast
            have A0253:"fInf(S - {a}) \<noteq> bot"
              by (meson A024 A0252 PowI)
            have A0254:"(inf (fInf(S - {a})) a) \<noteq> bot"
              by (meson A0 A0252 A1 filters_inf_closed is_pfilter_def)
            then show ?thesis
              by (metis A0251 False inf_commute)
          qed
          then show ?thesis 
            by simp
        next
          case False
          then show ?thesis
            by (metis A0 A021 A0250 Fa_def PowD Sup_insert Un_insert_right ccpo_Sup_singleton
                filters_inf_closed is_pfilter_def subset_insert_iff sup_bot.right_neutral)
          qed
        qed
      show ?thesis
        by (metis A025 G_def bot.extremum_uniqueI filter_closure_obtains0)
      qed
    show ?thesis
      by (simp add: A01 A02 is_pfilter_def proper_filter_iff)
  qed
  have B1:"F \<subseteq> G"
    using Fa_def G_def filter_closure_extensive by force
  have B2:"a \<in> G"
    using Fa_def G_def filter_closure_extensive by fastforce
  show ?thesis
    using B0 B1 B2 Fa_def G_def by fastforce
qed

lemma filter_is_ultrafilter_inter:
  fixes F::"'X::{boolean_algebra,order_bot} set"
  assumes A0:"is_pfilter F"
  shows "F = \<Inter>(finer_ultrafilters F)"
proof-
  define UF where "UF=finer_ultrafilters F" 
  define I where"I=\<Inter>UF"
  have B0:"\<forall>U. U \<in> UF \<longleftrightarrow> (is_ultrafilter U \<and> F \<subseteq> U)"
    by (simp add: UF_def finer_ultrafilters_def)
  have L:"F \<subseteq> I"
    using B0 I_def by blast
  have R:"I \<subseteq> F"
  proof (rule ccontr)
    assume RA0:"\<not>(F \<supseteq> I)"
    obtain a where RA1:"a \<in> I \<and> a \<notin> F"
      using RA0 by blast
    have RB1:"(-a) \<in> grill F"
      using is_filter_def RA1 assms is_pfilter_def mesh_prop12 by blast
    have RB2:"\<forall>f \<in> F. inf (-a) f \<noteq> bot"
      by (metis RB1 dual_order.refl inf_commute mesh_prop10 meshes_def)
    define G where "G=(filter_closure (\<Union>{F, {-a}}))"
    have RB2:"is_pfilter G \<and> F \<subseteq> G \<and> (-a) \<in> G"
      by (metis G_def RB2 assms exists_finer_filter_iff inf_commute)
    obtain U where RA3:"is_ultrafilter U \<and> G \<subseteq> U"
      using RB2 finer_ultrafilters_notempty by blast
    have RB3:"(-a) \<in> U \<and> U \<in>(finer_ultrafilters F)"
      using B0 RA3 RB2 UF_def by blast
    have RB4:"a \<notin> U"
      by (metis is_filter_def RA3 RB3 is_pfilter_def is_ultrafilter_def mesh_prop15 not_in_grill_not_in_ultrafilter)
    show "False"
      using I_def RA1 RB3 RB4 UF_def by blast
  qed
  show ?thesis
    using I_def L R UF_def by auto
qed


lemma filtergrill_is_coarser_ultra_union:
  fixes G::"'X::{boolean_algebra,order_bot} set"
  assumes A0:"is_prime_alt G \<and> is_pfilter G"
  shows "(G= \<Union>(coarser_ultrafilters G))"
proof-
  have "G = \<Union> {X. is_ultrafilter X \<and> X \<subseteq> G}"
    using assms filter_is_ultra_iff_prime_alt by auto
  then show ?thesis
    by (simp add: coarser_ultrafilters_def)
qed


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
  fixes f::"'a::order \<Rightarrow> 'b::order" and g::"'b::order \<Rightarrow> 'a::order"
  shows "is_gc2 f g \<longleftrightarrow> is_gc4 f g"
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


lemma complete_lattice_inf_exists:
  fixes A::"'a::complete_lattice set"
  shows "Inf A = InfUn A"
proof-
  have B0:"is_inf (Inf A) A"
    by (simp add: complete_lattice_inf_is_inf)
  show "Inf A = InfUn A"
    using B0 has_inf_def has_max_iff2 is_inf_def is_inf_inf_eq by blast
qed

lemma complete_lattice_sup_exists:
  fixes A::"'a::complete_lattice set"
  shows "Sup A = SupUn A"
proof-
  have B0:"is_sup (Sup A) A"
    by (simp add: complete_lattice_sup_is_sup)
  show "Sup A = SupUn A"
    using B0 has_sup_def has_min_iff2 is_sup_def is_sup_sup_eq by blast
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
  have B7:"\<And>y A. y \<le> InfUn(f`(A)) \<longleftrightarrow> (y \<le> (f (SupUn A)))"
  proof
    fix y A assume A1:"y \<le> InfUn(f`(A))"
    have B70:"... = Inf(f`(A))"
      by (simp add: complete_lattice_inf_exists)
    have B71:"SupUn A = Sup A"
      by (simp add: complete_lattice_sup_exists)
    have B72:"(f (SupUn A)) = (f((Sup A)))"
      by (simp add: B71)
    show "(y \<le> (f (SupUn A)))"
      using A1 B6 B70 B71 by fastforce
    next
    fix y A assume "(y \<le> (f (SupUn A)))"
    have B73:"SupUn A = Sup A"
      by (simp add: complete_lattice_sup_exists)
    have B74:"(f (SupUn A)) = (f((Sup A)))"
      by (simp add: B73)
    have B75:"(y \<le> (f (Sup A)))"
      using B74 \<open>(y::'Y::complete_lattice) \<le> (f::'X::complete_lattice \<Rightarrow> 'Y::complete_lattice) (SupUn (A::'X::complete_lattice set))\<close> by auto
    have B75:"y \<le> Inf(f`(A))"
      using B6 B75 by blast
    show "y \<le> InfUn(f`(A))"
      by (metis B75 complete_lattice_inf_exists)
  qed
  show ?thesis
    by (meson B7 dual_order.refl is_join_dual_def order_antisym)
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
    have B00:"SupUn {x1, x2} = x2"
      by (metis A1 Sup_insert ccpo_Sup_singleton complete_lattice_sup_exists sup.absorb_iff2)
    have B01:"(f x2) = (f (SupUn {x1, x2}))"
      by (simp add: B00)
    have B01:"... = (InfUn {(f x1), (f x2)})"
      by (metis (mono_tags, lifting) assms image_insert image_is_empty is_join_dual_def)
    have B02:"... \<le> (f x1)"
      by (simp add: semilattice_inf_infp_eq)
    show "(f x2) \<le> (f x1)"
      using B00 B01 B02 by auto
  qed
  have B1:"\<And>y1 y2. (y1 \<le> y2) \<longrightarrow> (?g y2) \<le> (?g y1)"
  proof
    fix y1 y2 assume A2:"(y1::('Y::complete_lattice)) \<le> (y2::('Y::complete_lattice))" 
    let ?B2="{x::('X::complete_lattice). y2 \<le> (f x)}"
    let ?B1="{x::('X::complete_lattice). y1 \<le> (f x)}"
    have B10:"(?g y2) = SupUn ?B2"
      by (simp add: join_dual_partner_def)   
    have B11:"(?g y1) = SupUn ?B1"
      by (simp add: join_dual_partner_def)   
    have B12:"?B2 \<subseteq> ?B1"
      using A2 by force
    have B13:"is_sup (Sup ?B1) ?B1"
      using complete_lattice_sup_is_sup by blast
    have B14:"has_sup ?B1"
      by (metis B13 has_min_iff has_sup_def is_min_iff is_sup_def)
    have B14b:"is_sup (Sup ?B2) ?B2"
      by (simp add: complete_lattice_sup_is_sup)
    have B14c:"has_sup ?B2"
      by (metis B14b has_min_iff has_sup_def is_min_iff is_sup_def)
    have B15:"(?g y2) \<le> (?g y1)"
      by (simp add: B10 B11 B12 B14 B14c sup_monotone1)
    show "(?g y2) \<le> (?g y1)"
      by (simp add: B15)
  qed
  have B2:"\<And>(y::('Y::complete_lattice)). y \<le> (f (?g y))"
  proof-
    fix y::"'Y::complete_lattice"
    have B20:"?g y =  SupUn {x. y \<le> (f x)}"
      by (simp add: join_dual_partner_def)
    have B21:"f (?g y) = InfUn (f`{x. (f x) \<ge> y})"
      using B20 assms is_join_dual_def by auto
    have B22:"y \<in> lb_set (f`{x. (f x) \<ge> y})"
      by (simp add: imp_in_lower_bounds)
    have B23:"y \<le>  InfUn (f`{x. (f x) \<ge> y})"
      by (metis B22 complete_lattice_inf_exists complete_lattice_inf_greatest)
    show "y \<le> (f (?g y))"
      by (simp add: B21 B23)
  qed
  have B3:"\<forall>(x::('X::complete_lattice)). x \<le> (?g (f x))"
  proof
    fix x::"'X::complete_lattice"
    show "x \<le> (?g (f x))"
      by (metis (mono_tags) complete_lattice_sup_exists csls.CSup_upper join_dual_partner_def mem_Collect_eq order_refl)
  qed
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
  fixes f::"'a set \<Rightarrow> 'b set" and
        g::"'b set \<Rightarrow> 'a set"
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
  have B15:"\<forall>A. (\<Inter>a \<in> A. f {a}) = (f (\<Union>a \<in> A. {a}))"
    proof
      fix A::"'a set"
      let ?L="(\<Inter>a \<in> A. f {a})" and ?R="(f (\<Union>a \<in> A. {a}))"
      let ?fA="{y. \<exists>a \<in> A. y = f {a}}"
      let ?sA="{y. \<exists>a \<in> A. y={a}}"
      have B150:"?L=Inf ?fA"
        by (simp add: image_def)
      have B151:"... = InfUn ?fA"
        by (simp add: complete_lattice_inf_exists)
      have B152:"?R= f (Sup ?sA)"
        by (simp add: image_def)
      have B153:"... = f (SupUn ?sA)"
        by (simp add: complete_lattice_sup_exists)
      have B54:"?L=   f (Sup ?sA)"
        by (metis (no_types) B0 INT_extend_simps(10) complete_lattice_inf_exists 
            complete_lattice_sup_exists image_def is_join_dual_def)
      have LR:"?L = ?R"
        using B152 B54 by blast
      show "(\<Inter>a \<in> A. f {a}) = (f (\<Union>a \<in> A. {a}))"
        using LR by auto
    qed
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
  fixes f::"'a::order \<Rightarrow> 'b::order" and g::"'b::order \<Rightarrow> 'a::order"
  assumes A0:"is_gc2 f g"
  shows "(f \<circ> g \<circ> f = f) \<and> (g \<circ> f \<circ> g = g)"
proof-
  have B0:"\<forall>x. (f x) \<le> f ( g (f (x)))"
    by (meson assms comp_extensive_def is_gc2_def)
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
  fixes f::"'a::order \<Rightarrow> 'b::order" and g::"'b::order \<Rightarrow> 'a::order"
  assumes A0:"is_gc2 f g"
  shows "(f \<circ> g) \<circ> (f \<circ> g) = (f \<circ> g)"
  by (simp add: assms fun.map_comp gc_double_comp)

lemma gc_composed_idempotent2:
  fixes f::"'a::order \<Rightarrow> 'b::order" and g::"'b::order \<Rightarrow> 'a::order"
  assumes A0:"is_gc2 f g"
  shows "(g \<circ> f) \<circ> (g \<circ> f) = (g \<circ> f)"
  by (simp add: assms gc_double_comp o_assoc)


lemma idempotent_req:
  assumes "f \<circ> f = f"
  shows "is_idempotent f"
  by (metis assms comp_apply is_idempotent_def)

lemma gc_closure:
  fixes f::"'a::order \<Rightarrow> 'b::order" and g::"'b::order \<Rightarrow> 'a::order"
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