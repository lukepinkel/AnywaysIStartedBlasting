theory Closures
  imports Main
begin
hide_type Filter.filter
hide_const(open) List.list.Nil
no_notation List.list.Nil ("[]")  
no_notation Cons (infixr "#" 65)

declare [[show_types]]


class complete_semilattice_inf = semilattice_inf + Inf +
    assumes CInf_lower: "x \<in> A \<Longrightarrow> Inf A \<le> x"
    and CInf_greatest: "(\<And>x. x \<in> A \<Longrightarrow> z \<le> x) \<Longrightarrow> z \<le> Inf A"

  
class complete_semilattice_sup = semilattice_sup + Sup +
   assumes CSup_upper: "x \<in> A \<Longrightarrow> x \<le>  Sup A"
    and CSup_least: "(\<And>x. x \<in> A \<Longrightarrow> x \<le> z) \<Longrightarrow> Sup A \<le> z"



definition is_extensive::"('a::ord \<Rightarrow> 'a::ord) \<Rightarrow> bool" where
  "is_extensive f \<equiv> (\<forall>x. (x \<le> (f x)))"

definition is_isotone::"('a::ord \<Rightarrow> 'b::ord) \<Rightarrow> bool" where
  "is_isotone f \<equiv> (\<forall>x1 x2. x1 \<le> x2 \<longrightarrow> (f x1) \<le> (f x2))"

definition is_idempotent::"('a::ord \<Rightarrow> 'a::ord) \<Rightarrow> bool" where
  "is_idempotent f \<equiv> (\<forall>x.  (f x)= f (f x))"

lemma idempotent_req:
  assumes "f \<circ> f = f"
  shows "is_idempotent f"
  by (metis assms comp_apply is_idempotent_def)

definition is_closure::"('a::ord \<Rightarrow> 'a::ord) \<Rightarrow> bool" where
  "is_closure f \<equiv> (is_extensive f) \<and> (is_isotone f) \<and> (is_idempotent f)"

context order
begin
lemma isotone_idempotent_imp_extensive:
  fixes f::"('X::order \<Rightarrow> 'X::order)"
  shows "is_closure f \<longleftrightarrow> (\<forall>x1 x2. ((x1 \<le> (f x2)) \<longleftrightarrow>( (f x1) \<le> (f x2))))"
proof 
  assume A0:"is_closure f"
  have LR:"\<And>x1 x2.  x1 \<le> (f x2) \<longrightarrow> (f x1) \<le> (f x2)"
  proof
    fix x1 x2 assume A01:"x1 \<le> (f x2)"
    have B0:"(f x1) \<le> (f (f x2))"
      using A0 A01 is_closure_def is_isotone_def by auto
    have B1:"... = f x2"
      by (metis A0 is_closure_def is_idempotent_def)
    show "(f x1) \<le> (f x2)"
      using B0 B1 by auto
  qed
  show "(\<forall>x1 x2. ((x1 \<le> (f x2)) \<longleftrightarrow>( (f x1) \<le> (f x2))))"
    by (metis A0 LR is_closure_def is_extensive_def preorder_class.dual_order.trans)
  next
  assume A1:" (\<forall>(x1::'X) x2::'X. ((x1 \<le> (f x2)) \<longleftrightarrow>( (f x1) \<le> (f x2))))"
  have C0:"\<And>(x1::'X) x2::'X. x1 \<le> x2 \<longrightarrow> (f x1) \<le> (f x2)"
  proof
    fix x1 x2 assume C01:"(x1::'X) \<le> (x2::'X)"
    have B2:"x1 \<le> (f x2)"
      using A1 C01 preorder_class.order.trans by blast
    show "(f x1) \<le> (f x2)"
      using A1 B2 by blast
  qed
  have C1:"\<forall>x. (f x) = f( (f x))"
    by (meson A1 order_class.order_eq_iff)
  have C2:"\<forall>x. x \<le> f x"
    by (simp add: A1)
  have RL:"is_extensive f \<and> is_idempotent f \<and> is_isotone f"
    by (meson C0 C1 C2 is_extensive_def is_idempotent_def is_isotone_def)
  show "is_closure f"
    by (simp add: RL is_closure_def)
qed

 
end


definition pointwise_less_eq::"('X::order \<Rightarrow> 'Y::order) \<Rightarrow>('X::order \<Rightarrow> 'Y::order) \<Rightarrow> bool" where
  "pointwise_less_eq f g \<equiv> (\<forall>x. (f x) \<le> (g x))"

lemma pw_less_antisym:
  assumes "(pointwise_less_eq f g) \<and> (pointwise_less_eq g f)"
  shows "f = g"
  by (meson assms dual_order.eq_iff ext pointwise_less_eq_def)


definition pointwise_less::"('X::order \<Rightarrow> 'Y::order) \<Rightarrow>('X::order \<Rightarrow> 'Y::order) \<Rightarrow> bool" where
  "pointwise_less f g \<equiv> (pointwise_less_eq f g) \<and> (f \<noteq> g)"



definition principal_filter::"'X::ord \<Rightarrow> 'X::ord set" where
  "principal_filter a = {x. x \<ge> a}"

lemma principal_filter_imp:
  "\<And>x a. x \<in> (principal_filter a) \<Longrightarrow> a \<le> x"
  by (simp add: principal_filter_def)


lemma principal_filter_order_iso:
  "\<And>(x::'X::order) y::'X::order. x \<le> y \<Longrightarrow> (principal_filter y) \<subseteq> (principal_filter x) "
  by (metis atLeast_def atLeast_subset_iff principal_filter_def)

definition principal_filter_in::"'X::ord \<Rightarrow> 'X::ord set \<Rightarrow> 'X::ord set" where
  "principal_filter_in a C = C \<inter> (principal_filter a)"


lemma principal_filter_in_order_iso:
  "\<And>(x::'X::order) (y::'X::order) (C::('X::order set)). x \<le> y \<Longrightarrow> (principal_filter_in y C) \<subseteq> (principal_filter_in x C) "
  by (simp add: inf.coboundedI2 principal_filter_in_def principal_filter_order_iso)


lemma principal_filter_in_imp:
  "\<And>x a C. x \<in> (principal_filter_in a C) \<Longrightarrow> a \<le> x"
  by (simp add: principal_filter_imp principal_filter_in_def)

definition is_moore_family::"'a::order set \<Rightarrow> bool" where
  "is_moore_family C \<equiv> (C \<noteq> {}) \<and> (\<forall>(a::'a). (\<exists>m \<in> (principal_filter_in a C). (\<forall>x \<in> (principal_filter_in a C). m \<le> x)))"

definition moore_to_closure::"'X::{order,inf, Inf} set \<Rightarrow> ('X::{order, inf, Inf} \<Rightarrow> 'X::{order, inf, Inf})" where
  "moore_to_closure C \<equiv> (\<lambda>x. Inf(principal_filter_in x C))"


lemma inf_closed_then_moore:
  fixes C::"'X::complete_semilattice_inf set"
  assumes A0:"\<forall>E \<in> Pow(C). (Inf E) \<in> C"
  shows "is_moore_family C"
proof-
  have B0:"\<forall>a. (principal_filter_in a C) \<in> Pow(C)"
    by (simp add: principal_filter_in_def)
  have B1:"\<forall>a. Inf(principal_filter_in a C) \<in> C"
    using B0 assms by auto
  have B2:"\<forall>a. Inf(principal_filter_in a C) \<in> (principal_filter_in a C)"
    by (metis B1 IntI CInf_greatest mem_Collect_eq principal_filter_def principal_filter_in_def principal_filter_in_imp)
  have B3:"\<forall>a. (\<forall>x \<in> (principal_filter_in a C).  Inf(principal_filter_in a C) \<le> x)"
    by (simp add: complete_semilattice_inf_class.CInf_lower)
  show ?thesis
    by (metis B1 B2 CInf_lower empty_iff is_moore_family_def)
qed  


lemma in_cl_range_idempotent:
  assumes A0:"is_closure f"
  shows "\<And>x. x \<in> (range f) \<longrightarrow> f x = x"
proof
  fix y assume A1:"y \<in> range f"   
  obtain x where A2:"y = f x"
    using A1 by blast
  have B0:"f (f x) = f x"
    by (metis assms is_closure_def is_idempotent_def)
  show "f y = y"
    by (simp add: A2 B0)
qed

lemma closure_range_inf_closed:
  fixes E::"'X::complete_semilattice_inf set" and
        f::"'X::complete_semilattice_inf \<Rightarrow> 'X::complete_semilattice_inf"
  assumes A0:"is_closure f" and
          A1:"E \<subseteq> range f"
  shows "f (Inf E) = Inf E "
proof-
  let ?i = "Inf E"
  have B0:"?i \<le> f ?i"
    using A0 is_closure_def is_extensive_def by blast
  have B1:"\<forall>x \<in> E. ?i \<le> x"
    using complete_semilattice_inf_class.CInf_lower by blast
  have B2:"\<forall>x \<in> E. f ?i \<le> f x"
    using A0 B1 is_closure_def is_isotone_def by blast
  have B3:"\<forall>x \<in> E. f x = x"
    using A0 A1 in_cl_range_idempotent by blast
  have B4:"\<forall>x \<in> E. f ?i \<le> x"
    using B2 B3 by fastforce
  have B5:"f ?i \<le> ?i"
    by (simp add: B4 complete_semilattice_inf_class.CInf_greatest)
  have B6:"f ?i = ?i"
    by (simp add: B0 B5 dual_order.antisym)
  show ?thesis 
    by (simp add: B6)
qed

lemma moore_closure_imp:
  fixes C::"'X::complete_semilattice_inf set"
  assumes A0:"is_moore_family C"
  shows "\<forall>x. (moore_to_closure C) x = Inf(principal_filter_in x C)"
  by (simp add: moore_to_closure_def)

lemma moore_closure_imp2:
  fixes C::"'X::complete_semilattice_inf set"
  assumes A0:"is_moore_family C"
  shows "\<forall>x. ((moore_to_closure C) x) \<in> (principal_filter_in x C)"
  by (metis A0 CInf_greatest CInf_lower is_moore_family_def moore_to_closure_def order_class.order_eq_iff)


lemma moore_to_closure_iscl:
  fixes C::"'X::complete_semilattice_inf set"
  assumes A0:"is_moore_family C"
  shows "is_closure (moore_to_closure C)"
proof-
  let ?f="moore_to_closure C"
  have C0:"is_extensive ?f"
  proof-
    have C01:"\<forall>x. x \<le> ?f x"
    proof
      fix x
      let ?Px="principal_filter_in x C"
      have C0B0:"\<exists>m \<in> ?Px. (\<forall>x \<in>?Px. m \<le> x)"
        using A0 is_moore_family_def by blast
      have C0B1:"(?f x) = Inf(?Px)"
        by (simp add: moore_to_closure_def)
      obtain m where C0B2:"m \<in> ?Px \<and> (\<forall>x \<in>?Px. m \<le> x)"
        using C0B0 by blast
      have C0B3:"m= Inf(?Px)"
        by (simp add: C0B2 CInf_greatest CInf_lower dual_order.antisym)
      have C0B4:"?f x \<in> principal_filter_in x C"
        using C0B1 C0B2 C0B3 by fastforce
      show "x \<le> ?f x"
        using C0B4 principal_filter_in_imp by blast
      qed
      show ?thesis
        by (simp add: C01 is_extensive_def)
    qed
  have C1:"is_isotone ?f"
  proof-
    have C10:"\<And>x1 x2. x1 \<le> x2 \<longrightarrow> (?f x1) \<le> (?f x2)"
    proof
      fix x1 x2::"'X::complete_semilattice_inf" assume C10A0:"x1 \<le> x2"
      let ?Px1="principal_filter_in x1 C" and ?Px2="principal_filter_in x2 C"
      have C10B0:"?Px2 \<subseteq>?Px1"
        by (simp add: C10A0 principal_filter_in_order_iso)
      have C10B1:"Inf ?Px1 \<le> Inf ?Px2"
        by (meson C10B0 CInf_greatest CInf_lower subset_eq)
      show "(?f x1) \<le> (?f x2)"
        by (simp add: C10B1 moore_to_closure_def)
      qed
    show ?thesis
      by (simp add: C10 is_isotone_def)
    qed
  have C2:"is_idempotent ?f"
  proof-
    have C20:"\<forall>x. ?f x = ?f (?f x)"
    proof 
      fix x
      let ?y1="?f x" and ?y2="?f (?f x)"
      let ?Px="principal_filter_in x C" and ?Pfx="principal_filter_in ?y1 C"
      have C2B0:"?y1 \<in> ?Px"
        by (simp add: assms moore_closure_imp2)
      have C2B1:"?y2 \<in> ?Pfx"
        by (simp add: assms moore_closure_imp2)
      have C2B2:"?y1 \<in> C"
        using C2B0 principal_filter_in_def by auto
      have C2B3:"?y1 \<in> ?Pfx"
        by (simp add: C2B2 principal_filter_def principal_filter_in_def)
      have C2B4:"\<forall>z \<in> ?Pfx. ?y1 \<le> z"
        using principal_filter_in_imp by blast
      have C2B3:"?y1 = Inf ?Pfx"
        by (metis C0 C2B3 CInf_lower dual_order.antisym is_extensive_def moore_to_closure_def)
      show "?f x = ?f (?f x)"
        by (metis C2B3 moore_to_closure_def)
      qed
    show ?thesis
      using C20 is_idempotent_def by blast
  qed
  show ?thesis
    by (simp add: C0 C1 C2 is_closure_def)
qed

lemma clrange_is_moore:
  fixes f::"'X::complete_semilattice_inf \<Rightarrow> 'X::complete_semilattice_inf"
  assumes A0:"is_closure f"
  shows "is_moore_family (range f)"
proof-
  let ?C="range f"
  have B0:"\<forall>x. (f x) \<in> ?C \<and> (x \<le> f x)"
    using assms is_closure_def is_extensive_def by auto
  have B1:"\<forall>x. (f x) \<in> principal_filter_in x ?C"
    by (simp add: B0 principal_filter_def principal_filter_in_def)
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
      by (metis B3A0 Int_iff assms in_cl_range_idempotent isotone_idempotent_imp_extensive 
         principal_filter_in_def principal_filter_in_imp)
    show "(\<exists>m \<in> (principal_filter_in x ?C). (\<forall>y \<in> (principal_filter_in x ?C). m \<le> y))"
      using B3B0 B3B1 by blast
    qed
  show ?thesis
    by (simp add: B3 is_moore_family_def)
qed


lemma cl_range_inf1:
  fixes f::"'X::complete_semilattice_inf \<Rightarrow> 'X::complete_semilattice_inf" and
        a::"'X::complete_semilattice_inf"
  assumes A0:"is_closure f" 
  shows "\<forall>y \<in> principal_filter_in a (range f). f(a) \<le> y"
proof
  fix y assume A3A0:"y \<in> principal_filter_in a (range f)"
  have A3B0:"a \<le> y \<and> (\<exists>x. y = (f x))"
    using A3A0 principal_filter_def principal_filter_in_def by fastforce
  have A3B1:"(f y) = y"
    using A3B0 assms in_cl_range_idempotent by blast
  have A3B2:"(f a) \<le> (f y)"
    using A3B0 A3B1 assms isotone_idempotent_imp_extensive by auto
  have A3B3:"... = y"
    by (simp add: A3B1)
  show "f(a) \<le> y"
    using A3B2 A3B3 by auto
qed


lemma cl_range_inf2:
  fixes C::"'X::complete_semilattice_inf set" and
        a::"'X::complete_semilattice_inf"
  assumes A0:"is_moore_family C" 
  shows "\<forall>y \<in> (principal_filter_in a(range(moore_to_closure C))). ((moore_to_closure C)(a)) \<le> y"
proof
  let ?f="moore_to_closure C"
  fix y assume A0:"y \<in> principal_filter_in a (range ?f)"
  have B0:"is_closure ?f"
    by (simp add: assms moore_to_closure_iscl)
  have B0:"a \<le> y \<and> (\<exists>x. y = (?f x))"
    by (metis A0 B0 IntD1 in_cl_range_idempotent principal_filter_in_def principal_filter_in_imp)
  have B1:"(?f y) = y"
    using B0 assms in_cl_range_idempotent moore_to_closure_iscl by blast
  have B2:"(?f a) \<le> (?f y)"
    by (simp add: A0 B1 assms cl_range_inf1 moore_to_closure_iscl)
  have B3:"... = y"
    by (simp add: B1)
  show "?f(a) \<le> y"
    using B2 B3 by auto
qed

lemma principal_inf1:
  "\<forall>x::('X::complete_semilattice_inf). x = (Inf(principal_filter x))"
proof
  fix x::"'X::complete_semilattice_inf"
  have A0:"x \<in> principal_filter x"
    by (simp add: principal_filter_def)
  have A1:"\<forall>y \<in> principal_filter x. x \<le> y"
    by (simp add: principal_filter_imp)
  show "x=(Inf(principal_filter x))"
    by (simp add: A0 A1 CInf_greatest CInf_lower dual_order.eq_iff)
qed


lemma principal_inf2:
  fixes C::"'X::complete_semilattice_inf set"
  assumes A0:"x \<in> C"
  shows "x = Inf(principal_filter_in x C)"
proof-
  have B0:"x = Inf(principal_filter x)"
    by (simp add: principal_inf1)
  have B1:"principal_filter_in x C \<subseteq> principal_filter x"
    by (simp add: principal_filter_in_def) 
  have B2:"x \<in> principal_filter_in x C"
    by (simp add: assms principal_filter_def principal_filter_in_def)
  have B3:"\<forall>y \<in> principal_filter_in x C. x \<le> y"
    by (simp add: principal_filter_in_imp)
  show ?thesis
    by (simp add: B2 B3 CInf_greatest CInf_lower dual_order.antisym)
qed  

lemma moore_cl_iso_inv1:
  fixes f::"'X::complete_semilattice_inf \<Rightarrow> 'X::complete_semilattice_inf"
  assumes A0:"is_closure f" 
  shows "(moore_to_closure (range f)) = f"
proof-
  have B0:"\<forall>x. (moore_to_closure (range f))(x) =  (f x)"
  proof
    fix a
    have A0:"\<forall>x. f(x) \<in> principal_filter_in x (range f)"
      by (metis Int_iff assms is_closure_def   is_extensive_def mem_Collect_eq principal_filter_def
          principal_filter_in_def rangeI)
    have A1:"a \<le> (f a)"
      using assms is_closure_def is_extensive_def by auto
    have A2:"(f a) \<in> principal_filter_in a (range f)"
      by (simp add: A0)
    have A3:"\<forall>y \<in> principal_filter_in a (range f). f(a) \<le> y"
      using assms cl_range_inf1 by blast
    have A4:"f(a) = Inf(principal_filter_in a (range f))"
      by (simp add: A2 A3 complete_semilattice_inf_class.CInf_greatest complete_semilattice_inf_class.CInf_lower order_antisym)
    have B1:"principal_filter_in a (range f) = (range f) \<inter> {y. a \<le> y}"
      by (simp add: principal_filter_def principal_filter_in_def)
    have B2:"(moore_to_closure (range f))(a) = Inf(principal_filter_in a (range f))"
      by (simp add: moore_to_closure_def)
    have B3:"... = Inf{y \<in> range f. a \<le> y}"
      by (simp add: B1 Collect_conj_eq)
    have B4:"... = Inf{y. \<exists>x. (y = f x) \<and> (a \<le> (f x))}"
      by (metis rangeE rangeI)
    have B5:"... = f a"
      using A4 B3 B4 by presburger
    show "(moore_to_closure (range f))(a) = (f a)"
      using A4 B2 by presburger
  qed
  show ?thesis
    using B0 by auto
qed    


lemma moore_cl_iso_inv2:
  fixes C::"'X::complete_semilattice_inf set"
  assumes A0:"is_moore_family C" 
  shows "C = range(moore_to_closure C)"
proof-
  let ?f="moore_to_closure C"
  have B0:"\<And>y. (y \<in> range(?f)) \<longrightarrow>  y \<in> C"
    proof
      fix y assume B0A0:"(y \<in> range(?f))"
      obtain x where B0A1:"(?f)(x) = y"
        using B0A0 by blast
      have B0B1:"y = Inf(principal_filter_in x C)"
        by (metis B0A1 moore_to_closure_def)
      show "y \<in> C"
        using B0A1 assms moore_closure_imp2 principal_filter_in_def by fastforce
    qed
  have B1:"\<And>y. (y \<in> C) \<longrightarrow> (y \<in> range(?f))"
  proof
    fix y assume B1A0:"y \<in> C"
    have B1B0:"?f y = y"
      by (metis B1A0 moore_to_closure_def principal_inf2)
    show "y \<in> range(moore_to_closure C)"
      by (metis B1B0 rangeI) 
  qed
  show ?thesis
    using B0 B1 by blast
qed


lemma moore_cl_iso1:
  fixes f1::"'X::complete_semilattice_inf \<Rightarrow> 'X::complete_semilattice_inf" and
        f2::"'X::complete_semilattice_inf \<Rightarrow> 'X::complete_semilattice_inf"
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
  fixes f1::"'X::complete_semilattice_inf \<Rightarrow> 'X::complete_semilattice_inf" and
        f2::"'X::complete_semilattice_inf \<Rightarrow> 'X::complete_semilattice_inf"
  assumes A0:"(range f2) \<subseteq> (range f1)" and
          A1:"is_closure f1 \<and> is_closure f2" 
  shows "pointwise_less_eq f1 f2"
proof-
  let ?G1="range f1" and ?G2="range f2"
  have B0:"?G2 \<subseteq> ?G1"
    using A0 by force
  have B1:"\<forall>x.  (?G2 \<inter> (principal_filter x)) \<subseteq> (?G1 \<inter> (principal_filter x)) "
    using B0 by blast
  have B2:"\<forall>x. principal_filter_in x ?G2 \<subseteq>  principal_filter_in x ?G1"
    by (metis B1 principal_filter_in_def)
  have B3:"\<forall>x. Inf( principal_filter_in x ?G1) \<le> Inf( principal_filter_in x ?G2)"
    by (meson B2 CInf_greatest CInf_lower in_mono)
  have B3:"\<forall>x. f1 x \<le> f2 x"
    by (metis A1 B0 in_cl_range_idempotent is_closure_def is_extensive_def isotone_idempotent_imp_extensive range_subsetD)
  show ?thesis
    by (simp add: B3 pointwise_less_eq_def)
qed


    

(*
typedef (overloaded) 'a::order closure_operator = "{f::('a::order \<Rightarrow> 'a::order). is_closure f}"
  using isotone_idempotent_imp_extensive by force

setup_lifting type_definition_closure_operator
instantiation closure_operator:: (order) order
begin

lift_definition less_eq_closure_operator :: "'a closure_operator \<Rightarrow> 'a closure_operator \<Rightarrow> bool" is  pointwise_less_eq .

lift_definition less_closure_operator :: "'a closure_operator \<Rightarrow> 'a closure_operator \<Rightarrow> bool" is pointwise_less .

instance
  apply intro_classes
  apply (metis Closures.less_eq_closure_operator.rep_eq less_closure_operator.rep_eq pointwise_less_def pw_less_antisym)
  apply (simp add: less_eq_closure_operator.rep_eq pointwise_less_eq_def)
  apply (meson dual_order.trans less_eq_closure_operator.rep_eq pointwise_less_eq_def)
  by (meson Closures.less_eq_closure_operator.rep_eq Rep_closure_operator_inject pw_less_antisym)
end



definition principal_filter::"'X::ord \<Rightarrow> 'X::ord set" where
  "principal_filter a = {x. x \<ge> a}"

definition principal_filter_in::"'X::ord \<Rightarrow> 'X::ord set \<Rightarrow> 'X::ord set" where
  "principal_filter_in a C = C \<inter> (principal_filter a)"

definition is_moore_family::"'a::order set \<Rightarrow> bool" where
  "is_moore_family C \<equiv> (C \<noteq> {}) \<and> (\<forall>(a::'a). (\<exists>m \<in> (principal_filter_in a C). (\<forall>x \<in> (principal_filter_in a C). m \<le> x)))"

typedef (overloaded) 'a::order moore_family = "{C::('a::order set). is_moore_family C}"
  unfolding is_moore_family_def principal_filter_in_def principal_filter_def
  apply(simp)
  by auto
  

setup_lifting type_definition_moore_family
instantiation moore_family:: (order) order
begin

lift_definition less_eq_moore_family :: "'a moore_family \<Rightarrow> 'a moore_family \<Rightarrow> bool" is subset_eq .

lift_definition less_moore_family :: "'a moore_family \<Rightarrow> 'a moore_family \<Rightarrow> bool" is  subset .

instance
  apply intro_classes
  apply (simp add: less_eq_moore_family.rep_eq less_moore_family.rep_eq subset_not_subset_eq)
  apply (simp add: Closures.less_eq_moore_family.rep_eq)
  apply (meson Closures.less_eq_moore_family.rep_eq order.trans)
  by (simp add: Closures.less_eq_moore_family.rep_eq Rep_moore_family_inject)
end



definition closure_range::"'a::order closure_operator \<Rightarrow> 'a::order moore_family" where
  "closure_range f \<equiv> Abs_moore_family {x. x = ((Rep_closure_operator f) x)}" 

definition moore_closure::"'a::order moore_family \<Rightarrow> 'a::order closure_operator" where
  "moore_closure C \<equiv>
  (Abs_closure_operator
   (\<lambda>x. SOME z. (z \<in> principal_filter_in x (Rep_moore_family C)) \<and> 
    (\<forall>y \<in> (principal_filter_in x (Rep_moore_family C)). z \<le> y) ))"

lemma moore_iso1:
  fixes f::"'a::order closure_operator"
  shows "is_moore_family( Rep_moore_family (closure_range f))"
  using Rep_moore_family by auto

lemma moore_iso2:
  fixes C::"'a::order moore_family"
  shows "is_closure (Rep_closure_operator (moore_closure C))"
  using Rep_closure_operator by auto
*)
end