theory Closures10
imports Main "./Posets10"
begin

definition is_closure_on::"('a::order \<Rightarrow> 'a::order) \<Rightarrow> 'a::order set \<Rightarrow>  bool" where
  "is_closure_on f X \<equiv> (is_proj_on f X) \<and> (is_extensive_on f X)"

definition closure_eq::"('a::order \<Rightarrow> 'a::order) \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "closure_eq f X \<equiv> (\<forall>x1 \<in> X. \<forall>x2 \<in> X. (( x1 \<le> f x2) \<longleftrightarrow> (f x1 \<le> f x2)))"

definition is_moore_family::"'a set set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_moore_family C X \<equiv> C \<in> Pow (Pow X) \<and> (\<forall>A \<in> Pow C. (Inf A (Pow X)) \<in> C)"

definition closure_from_clr::"'a::order set \<Rightarrow> ('a::order \<Rightarrow> 'a::order)" where
  "closure_from_clr C \<equiv> (\<lambda>x. min (ub_set {x} C))"

definition clr_from_closure::"('a::order \<Rightarrow> 'a::order) \<Rightarrow> 'a::order set \<Rightarrow> 'a::order set" where
  "clr_from_closure f X \<equiv> (f`X)"

definition is_clr::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "is_clr C X \<equiv> (C \<noteq> {}) \<and> (C \<subseteq> X) \<and> (\<forall>x. x \<in> X \<longrightarrow> has_min (ub_set {x} C))"

definition is_galois_connection::"('a::order \<Rightarrow> 'b::order) \<Rightarrow> 'a::order set \<Rightarrow> ('b::order \<Rightarrow> 'a::order) \<Rightarrow> 'b::order set \<Rightarrow> bool" where
  "is_galois_connection f X g Y \<equiv> (is_map f X Y) \<and> (is_map g Y X) \<and> 
                                   (is_antitone_on f X) \<and> (is_antitone_on g Y) \<and>
                                   (is_extensive_on (f \<circ> g) Y) \<and> (is_extensive_on (g \<circ> f) X)" 

definition galois_equiv::"('a::order \<Rightarrow> 'b::order) \<Rightarrow> 'a::order set \<Rightarrow> ('b::order \<Rightarrow> 'a::order) \<Rightarrow> 'b::order set \<Rightarrow> bool" where
  "galois_equiv f X g Y \<equiv> (\<forall>x \<in> X. \<forall>y \<in> Y.  (x \<le> g y \<longleftrightarrow> y \<le> f x))"

definition filter_closure::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> 'a::order set" where
  "filter_closure A X \<equiv> if A={} then {max X} else {x \<in> X. \<exists>F \<in> Fpow_ne A. Inf F X \<le> x}"

definition principal_filter_closure::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> 'a::order set" where
  "principal_filter_closure A X \<equiv> if A={} then {max X} else \<Union>a \<in> A. ub_set {a} X"

lemma is_closure_on_iff:
  "is_closure_on f X \<longleftrightarrow>  (is_idempotent_on f X) \<and> (is_isotone_on f X) \<and> (is_extensive_on f X)"
  by(simp add:is_closure_on_def is_proj_on_def)

lemma closure_eq_imp1:
  "closure_eq f X \<Longrightarrow> x1 \<in> X \<Longrightarrow> x2 \<in> X \<Longrightarrow> x1 \<le> f x2 \<Longrightarrow> f x1 \<le> f x2"
  by (simp add: closure_eq_def)

lemma closure_eq_imp2:
  "closure_eq f X \<Longrightarrow> x1 \<in> X \<Longrightarrow> x2 \<in> X \<Longrightarrow> f x1 \<le> f x2 \<Longrightarrow> x1 \<le> f x2"
  by (simp add: closure_eq_def)

lemma cl_eq_imp_ext1:
  "is_self_map f X \<Longrightarrow> closure_eq f X \<Longrightarrow> x \<in> X \<Longrightarrow>  x \<le> f x"
  by (simp add: closure_eq_imp2)

lemma is_closure_on_imp2:
  "is_closure_on f X \<Longrightarrow> is_self_map f X"
  by (simp add: is_closure_on_def is_proj_on_imp3) 

lemma cl_eq_imp_iso1:
  "is_self_map f X \<Longrightarrow> closure_eq f X \<Longrightarrow> x1 \<in> X \<Longrightarrow> x2 \<in> X \<Longrightarrow> x1 \<le> x2 \<Longrightarrow> x1 \<le> f x2"
  using cl_eq_imp_ext1 order.trans by blast     

lemma cl_eq_imp_iso2:
  "is_self_map f X \<Longrightarrow> closure_eq f X \<Longrightarrow> x1 \<in> X \<Longrightarrow> x2 \<in> X \<Longrightarrow> x1 \<le> x2 \<Longrightarrow> f x1 \<le> f x2"
  by (simp add: cl_eq_imp_iso1 closure_eq_imp1)

lemma cl_eq_imp_idemp:
  "is_self_map f X \<Longrightarrow> closure_eq f X \<Longrightarrow> x \<in> X \<Longrightarrow> f (f x) = f x"
  by (simp add: cl_eq_imp_ext1 closure_eq_imp1 dual_order.eq_iff is_self_map_imp2)

lemma closure_eq_if_closure_l:
  "is_closure_on f X \<Longrightarrow> x1 \<in> X \<Longrightarrow> x2 \<in> X \<Longrightarrow> f x1 \<le> f x2 \<Longrightarrow> x1 \<le> f x2"
  using is_ext_imp1 is_closure_on_def by blast

lemma closure_eq_if_closure_r:
  "is_closure_on f X \<Longrightarrow> x1 \<in> X \<Longrightarrow> x2 \<in> X \<Longrightarrow>  x1 \<le> f x2 \<Longrightarrow> f x1 \<le> f x2"
  by(simp add:is_closure_on_def is_closure_on_imp2[of "f" "X"] proj_imp_lt_cl_lt[of "f" "X" "x1" "x2"])

lemma closure_eq_if_closure:
  "is_closure_on f X \<Longrightarrow> closure_eq f X"
  by(auto simp add:closure_eq_def closure_eq_if_closure_l closure_eq_if_closure_r)

lemma closure_eq_imp_closure:
  "is_self_map f X \<Longrightarrow> closure_eq f X \<Longrightarrow> (is_extensive_on f X) \<and> (is_isotone_on f X) \<and> (is_idempotent_on f X)"
  by (simp add: cl_eq_imp_ext1 cl_eq_imp_idemp cl_eq_imp_iso2 is_extensive_on_def is_idempotent_on_def is_isotone_on_def)

lemma closure_if_cl_eq:
   "is_closure_on f X \<longleftrightarrow> (is_self_map f X \<and> closure_eq f X)"
  using closure_eq_if_closure closure_eq_imp_closure is_closure_on_iff is_extensive_on_def by blast

lemma closure_on_ineq1:
  "is_closure_on f X \<Longrightarrow> A \<subseteq> X \<Longrightarrow> has_sup A X \<Longrightarrow> f (Sup A X) ub (f`A)"
  by (meson has_sup_in_imp1 has_sup_in_set is_closure_on_iff is_isotone_imp2 ub_set_imp1)

lemma lt_closed_point:
  "is_closure_on f X \<Longrightarrow> b \<in> f`X \<Longrightarrow> a \<in> X \<Longrightarrow> a \<le> b \<Longrightarrow> f a \<le> b"
  using closure_eq_if_closure_r by blast

lemma closure_of_sup_lt_ub:
  "is_closure_on f X \<Longrightarrow> A \<subseteq> X \<Longrightarrow> has_sup A X  \<Longrightarrow> b \<in> ub_set (f`A) (f`X) \<Longrightarrow> f (Sup A X ) \<le> b"
  by (meson greater_sup_if1b has_sup_in_set is_closure_on_def is_closure_on_imp2 is_ext_imp2 is_map_def lt_closed_point subsetD ub_set_imp1 ub_set_imp2)


lemma closure_of_sup_is_sup1:
  "is_closure_on f X \<Longrightarrow> A \<subseteq> X \<Longrightarrow> has_sup A X \<Longrightarrow> is_sup (f (Sup A X)) (f`A) (f`X)"
  by (simp add: closure_of_sup_lt_ub closure_on_ineq1 has_sup_in_set is_min_if2 is_sup_def ub_set_if)

lemma closure_of_sup_is_sup2:
  "is_closure_on f X \<Longrightarrow> A \<subseteq> X \<Longrightarrow> has_sup A X \<Longrightarrow> has_sup (f`A) (f`X) \<and> (f (Sup A X) = (Sup (f`A) (f`X)))"
  by (meson closure_of_sup_is_sup1 has_min_ub_imp_has_sup is_min_imp_has_min is_sup_def is_sup_sup_eq)

lemma is_clr_imp1:
  "is_clr C X \<Longrightarrow> (C \<noteq> {}) \<and> (C \<subseteq> X)"
  by(simp add:is_clr_def)

lemma is_clr_imp2:
  "is_clr C X \<Longrightarrow> x \<in> X \<Longrightarrow> has_min (ub_set {x} C)"
  by(simp add:is_clr_def)

lemma is_clr_imp3:
  "is_clr C X \<Longrightarrow> x \<in> X \<Longrightarrow> (ub_set {x} C) \<noteq> {}"
  by (simp add: has_min_imp_ne is_clr_def)

lemma clr_is_cofinal:
  "is_clr C X \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> ub_set {x} C \<noteq> {})"
  by (simp add: is_clr_imp3)

lemma clr_is_cofinal_in_space:
  "is_clr C X \<Longrightarrow> X is_cofinal_in C"
  by (simp add: clr_is_cofinal is_cofinal_in_if_ub_in_ne)

lemma clr_is_cofinal2:
  "C \<subseteq> X \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> ub_set {x} C \<noteq> {}) \<Longrightarrow> is_max m X \<Longrightarrow> m \<in> C"
  by (metis Int_insert_right_if0 inf_le2 is_max_iff subset_empty ub_set_max ub_set_restrict1)
  
lemma is_clr_imp4:
  "is_clr C X \<Longrightarrow> x \<in> X \<Longrightarrow> has_inf (ub_set {x} C) C"
  by (simp add: has_min_imp_has_inf is_clr_imp2 ub_set_subset_space)

lemma is_clr_imp5:
  "is_clr C X \<Longrightarrow> x \<in> X \<Longrightarrow> Inf (ub_set {x} C) C \<in> C"
  by (simp add: has_inf_in_set is_clr_imp4)

lemma is_clr_imp6:
  "is_clr C X \<Longrightarrow> C \<subseteq> X \<Longrightarrow> x \<in> X \<Longrightarrow> Inf (ub_set {x} C) C \<in> X"
  by (simp add: has_inf_in_set in_mono is_clr_imp4)

lemma is_clr_imp_max:
  "has_max X \<Longrightarrow> is_clr C X \<Longrightarrow> has_max C"
  by (meson clr_is_cofinal clr_is_cofinal2 has_max_iff2 is_clr_imp1 is_max_subset)

lemma clr_obtains0:
  assumes "is_clr C X" and " x \<in> X "
  obtains m where "is_min m (ub_set {x} C)"
  using assms(1) assms(2) has_min_iff2 is_clr_imp2 by blast

lemma clr_obtains1:
  assumes "is_clr C X" and " x \<in> X "
  obtains m where "m \<in> C \<and> is_min m (ub_set {x} C)"
  by (meson assms(1) assms(2) clr_obtains0 is_min_imp ub_set_imp2)

locale closure_range=
  fixes C X::"'a::order set"                     
  assumes clr:"is_clr C X"
begin

abbreviation Cl::"'a::order \<Rightarrow> 'a::order" where
  "Cl x \<equiv> (closure_from_clr C) x"

lemma crange_is_ne:
  "C \<noteq> {}" using clr is_clr_imp1 by blast

lemma space_is_ne:
  "X \<noteq> {}" using clr is_clr_imp1 by blast

lemma least_closed_in_space:
  "xa \<in> X \<Longrightarrow> min (ub_set {xa} C) \<in> X"
  by (metis clr clr_obtains1 in_mono is_clr_imp1 min_if)

lemma Cl_maps_to:
  "Cl`X \<subseteq> X"
  by(auto simp add:closure_from_clr_def clr least_closed_in_space  )

lemma cl_is_self_map:
  "is_self_map Cl X"
  by(simp add:is_map_def Cl_maps_to space_is_ne)

lemma cl_is_iso:
  "x \<in> X \<Longrightarrow> y \<in> X \<Longrightarrow> x \<le> y \<Longrightarrow> (Cl x)  \<le>  (Cl y)"
  by (metis closure_from_clr_def clr is_clr_imp2 min_antitone2 ub_set_singleton_antitone)

lemma cl_is_iso_on:
  "is_isotone_on Cl X"
  by(simp add:is_isotone_on_def cl_is_iso)

lemma cl_is_ext:
  "x \<in> X \<Longrightarrow> x \<le> Cl x"
  by (metis closure_from_clr_def clr clr_obtains1 is_min_imp min_if singletonI ub_set_imp)

lemma cl_is_ext_on:
  "is_extensive_on Cl X"
  by(auto simp add:is_extensive_on_def cl_is_ext cl_is_self_map)

lemma cl_fp:
  "c \<in> C \<Longrightarrow> Cl c = c"
  by (simp add: closure_from_clr_def min_ub_set_singleton2)

lemma cl_is_idm:
  "x \<in> X \<Longrightarrow> (Cl (Cl x)) = Cl x "
  by (metis cl_fp closure_from_clr_def clr clr_obtains1 min_if)

lemma cl_is_idm_on:
  "is_idempotent_on Cl X"
  by(simp add:cl_is_self_map is_idempotent_on_def cl_is_idm) 

lemma cl_is_closure:
  "is_closure_on Cl X"
  by(simp add:is_closure_on_def is_proj_on_def cl_is_idm_on cl_is_iso_on cl_is_ext_on)

lemma element_in_clr_iff:
  "y \<in> clr_from_closure (closure_from_clr C) X  \<longleftrightarrow> y \<in> C"
  apply(auto simp add:clr_from_closure_def)
  apply (metis closure_from_clr_def clr clr_obtains1 min_if)
  by (metis closure_range.cl_fp closure_range_axioms clr image_eqI in_mono is_clr_imp1)

end

locale closure= 
  fixes f::"'a::order \<Rightarrow> 'a::order" and X::"'a::order set"
  assumes is_cl:"is_closure_on f X" and ne:"X \<noteq> {}"
begin

abbreviation Cf::"'a::order set" where
  "Cf \<equiv> clr_from_closure f X"

lemma Cf_is_ne:
  "Cf \<noteq> {}"
  by (simp add: clr_from_closure_def ne)

lemma Cf_subseteq_space:
  "Cf \<subseteq> X"
  by (metis clr_from_closure_def is_cl is_closure_on_def is_extensive_on_def is_map_def)

lemma cl_ub_im:
  "x \<in> X \<Longrightarrow> (f x) \<in> ub_set {x} Cf"
  using clr_from_closure_def is_cl is_closure_on_iff is_ext_imp0 ub_set_mem_iff by fastforce

lemma cl_ub_is_ne:
  "x \<in> X \<Longrightarrow> ub_set {x} Cf \<noteq> {}"
  using cl_ub_im by blast

lemma cl_ub_min:
  "x \<in> X \<Longrightarrow> y \<in> ub_set {x} Cf \<Longrightarrow> f x \<le> y"
  by (metis clr_from_closure_def is_cl lt_closed_point singletonI ub_set_imp ub_set_imp2)

lemma cl_is_min_ub:
  "x \<in> X \<Longrightarrow>  has_min (ub_set {x} Cf)"
  by (meson cl_ub_im cl_ub_min has_min_iff)

lemma Cf_is_clr:
  "is_clr Cf X"
  by(simp add:is_clr_def Cf_subseteq_space cl_is_min_ub Cf_is_ne)

end 

lemma cl_cr_cl_eq_cl:
  assumes A0:"is_closure_on f X" and A1:"a \<in> X"
  shows "closure_from_clr (clr_from_closure f X) a = f a"
  by (metis A0 A1 closure.cl_ub_im closure.cl_ub_min closure.intro closure_from_clr_def empty_iff min_if2)

lemma cr_cl_cr_eq_cr:
  assumes A0:"is_clr C X"
  shows "clr_from_closure (closure_from_clr C) X = C"
  using assms closure_range.element_in_clr_iff closure_range.intro by blast

lemma cl_order_iso:
  fixes f1 f2::"'a::order \<Rightarrow> 'a::order" and X::"'a::order set"
  assumes A0:"is_closure_on f1 X"  and A1:"is_closure_on f2 X" and A3:"\<forall>x. x \<in> X \<longrightarrow> f1 x \<le> f2 x"
  shows "clr_from_closure f2 X \<subseteq> clr_from_closure f1 X"
  apply(auto) by (metis A0 A1 A3 clr_from_closure_def image_insert insertI1 insert_absorb insert_subset is_closure_on_iff is_extensive_on_def is_idempotent_imp2 is_self_map_imp order_antisym_conv)

lemma clr_order_iso:
  fixes C1 C2 X::"'a::order set"
  assumes A0:"is_clr C1 X" and A1:"is_clr C2 X" and A2:"C2 \<subseteq> C1"
  shows "\<And>x. x \<in> X \<longrightarrow> closure_from_clr C1 x \<le> closure_from_clr C2 x"
  by (metis A0 A1 A2 closure_from_clr_def is_clr_imp2 min_antitone2 ub_set_in_isotone2)
(*
sublocale closure_range \<subseteq> cl:closure "closure_from_clr C" "X"
  apply(unfold_locales)
  apply (simp add: cl_is_closure)
  by (simp add: space_is_ne)

locale closure_space=closure

sublocale closure_space \<subseteq> cr:closure_range "f`X" "X"
  apply(unfold_locales)
  by (metis Cf_is_clr clr_from_closure_def)

print_locale! closure_space
print_locale! closure_range
*)
lemma top_is_closed1:
  "is_closure_on f X \<Longrightarrow> is_max m X \<Longrightarrow> f m = m"
  by (simp add: is_closure_on_iff is_extensive_on_def is_max_iff is_self_map_imp2 order_antisym)

lemma top_is_closed2:
   "is_clr C X \<Longrightarrow> is_max m X \<Longrightarrow> m \<in> C"
  by (metis Int_insert_right_if0 clr_is_cofinal inf_le2 is_clr_imp1 is_max_iff subset_empty ub_set_max ub_set_restrict1)

lemma clr_inf_ne1:
  "is_clr C X  \<Longrightarrow> A \<subseteq> C \<Longrightarrow> has_inf A X \<Longrightarrow> a \<in> A \<Longrightarrow>  (closure_from_clr C) (Inf A X ) \<le> (closure_from_clr C) a"
  by (meson closure_range.cl_is_iso closure_range.intro has_inf_in_imp2 has_inf_in_set in_mono is_clr_imp1)

lemma clr_inf_ne2:
  "is_clr C X \<Longrightarrow> A \<subseteq> C \<Longrightarrow> has_inf A X \<Longrightarrow> a \<in> A \<Longrightarrow>  (closure_from_clr C) (Inf A X ) \<le>a"
  by (metis closure_range.cl_fp closure_range.intro clr_inf_ne1 subsetD)

lemma clr_inf_ne3:
  "is_clr C X \<Longrightarrow> A \<subseteq> C \<Longrightarrow> has_inf A X \<Longrightarrow> a \<in> A \<Longrightarrow>  (closure_from_clr C) (Inf A X ) \<le> Inf A X"
  by (metis closure_from_clr_def closure_range.intro closure_range.least_closed_in_space clr_inf_ne2 has_inf_imp3 has_inf_in_set)

lemma clr_inf_ne4:
  "is_clr C X \<Longrightarrow> A \<subseteq> C \<Longrightarrow> has_inf A X \<Longrightarrow> a \<in> A \<Longrightarrow>  (closure_from_clr C) (Inf A X ) = Inf A X"
  by (meson closure_range.cl_is_ext closure_range.intro clr_inf_ne3 has_inf_in_set order_antisym)

lemma clr_inf_ne:
  "is_clr C X \<Longrightarrow> A \<subseteq> C \<Longrightarrow> has_inf A X \<Longrightarrow> a \<in> A \<Longrightarrow>  Inf A X \<in> C"
  by (metis closure_from_clr_def clr_inf_ne4 clr_obtains1 has_inf_in_set min_if)

lemma clr_inf_semilattice:
  "is_inf_complete X \<Longrightarrow> is_clr C X \<Longrightarrow> A \<subseteq> C \<Longrightarrow> A \<noteq> {} \<Longrightarrow> Inf A X \<in> C"
  by (meson Pow_iff all_not_in_conv clr_inf_ne dual_order.trans is_clr_imp1 is_inf_complete_def pow_ne_if)


lemma is_galois_connection_imp1:
  "is_galois_connection f X g Y \<Longrightarrow> x1 \<in> X \<Longrightarrow> x2 \<in> X \<Longrightarrow> x1 \<le> x2 \<Longrightarrow> f x2 \<le> f x1"
  by(simp add:is_galois_connection_def is_antitone_on_def)

lemma is_galois_connection_imp2:
  "is_galois_connection f X g Y \<Longrightarrow> y1 \<in> Y \<Longrightarrow> y2 \<in> Y \<Longrightarrow> y1 \<le> y2 \<Longrightarrow> g y2 \<le> g y1"
  by(simp add:is_galois_connection_def is_antitone_on_def)

lemma is_galois_connection_imp3:
  "is_galois_connection f X g Y \<Longrightarrow> x \<in> X \<Longrightarrow> x \<le> (g \<circ> f) x "
  by(simp add:is_galois_connection_def is_extensive_on_def)

lemma is_galois_connection_imp4:
  "is_galois_connection f X g Y \<Longrightarrow> y \<in> Y \<Longrightarrow> y \<le> (f \<circ> g) y "
  by(simp add:is_galois_connection_def is_extensive_on_def)

lemma galois_equiv_imp1:
  "galois_equiv f X g Y \<Longrightarrow> (is_map f X Y) \<Longrightarrow> (is_antitone_on f X)"
  apply(auto simp add:is_antitone_on_def galois_equiv_def is_map_def)
  by (metis dual_order.trans image_subset_iff order_refl)

lemma galois_equiv_imp2:
  "galois_equiv f X g Y \<Longrightarrow> (is_map g Y X) \<Longrightarrow> (is_antitone_on g Y)"
  apply(auto simp add:is_antitone_on_def galois_equiv_def is_map_def)
  by (metis dual_order.trans image_subset_iff order_refl)

lemma galois_equiv_imp3:
  "galois_equiv f X g Y \<Longrightarrow> (is_map f X Y) \<Longrightarrow>  (is_map g Y X) \<Longrightarrow>(is_extensive_on (f \<circ> g) Y)"
  apply(auto simp add:is_extensive_on_def  galois_equiv_def is_map_def)
  apply blast
  by (simp add: image_subset_iff)

lemma galois_equiv_imp4:
  "galois_equiv f X g Y \<Longrightarrow> (is_map f X Y) \<Longrightarrow>  (is_map g Y X) \<Longrightarrow>(is_extensive_on (g \<circ> f) X)"
  apply(auto simp add:is_extensive_on_def  galois_equiv_def is_map_def)
  by (simp add: image_subset_iff)
    

lemma gc_imp_ineq1a:
  "is_galois_connection f X g Y \<Longrightarrow> x \<in> X \<Longrightarrow> y \<in> Y \<Longrightarrow> x \<le> g y \<Longrightarrow> (f \<circ> g) y \<le> f x"
  by (simp add: image_subset_iff is_antitone_on_def is_galois_connection_def is_map_def)

lemma gc_imp_ineq1b:
  "is_galois_connection f X g Y \<Longrightarrow> x \<in> X \<Longrightarrow> y \<in> Y \<Longrightarrow> y \<le> f x \<Longrightarrow> (g \<circ> f) x \<le> g y"
  by (simp add: image_subset_iff is_antitone_on_def is_galois_connection_def is_map_def)

lemma gc_imp_ineq2a:
  "is_galois_connection f X g Y \<Longrightarrow> x \<in> X \<Longrightarrow> y \<in> Y \<Longrightarrow> x \<le> g y \<Longrightarrow>y  \<le> f x"
  using gc_imp_ineq1a is_galois_connection_imp4 order_trans by blast

lemma gc_imp_ineq2b:
  "is_galois_connection f X g Y \<Longrightarrow> x \<in> X \<Longrightarrow> y \<in> Y \<Longrightarrow> y \<le> f x \<Longrightarrow> x  \<le> g y"
  using gc_imp_ineq1b is_galois_connection_imp3 order_trans by blast

lemma gc_imp_ge:
  "is_galois_connection f X g Y \<Longrightarrow> galois_equiv f X g Y"
  by(auto simp add:galois_equiv_def gc_imp_ineq2a gc_imp_ineq2b)
  
lemma ge_imp_gc:
  "galois_equiv f X g Y \<and>  (is_map f X Y) \<and> (is_map g Y X) \<Longrightarrow> is_galois_connection f X g Y"
  using galois_equiv_imp1 galois_equiv_imp2 galois_equiv_imp3 galois_equiv_imp4 is_galois_connection_def by blast

lemma galois_triple_comp01:
  "is_galois_connection f X g Y \<Longrightarrow> x \<in> X \<Longrightarrow> f x \<le> (f \<circ> g \<circ> f) x"
  by (simp add: image_subset_iff is_extensive_on_def is_galois_connection_def is_map_def)
 
lemma galois_triple_comp02:
  "is_galois_connection f X g Y \<Longrightarrow> x \<in> X \<Longrightarrow> (f \<circ> g \<circ> f) x \<le> f x "
  by (metis comp_apply is_antitone_on_def is_extensive_on_def is_galois_connection_def is_self_map_imp2)
 
lemma galois_triple_comp0:
  "is_galois_connection f X g Y \<Longrightarrow> x \<in> X \<Longrightarrow> (f \<circ> g \<circ> f) x = f x "
  using galois_triple_comp01 galois_triple_comp02 order_antisym by blast

lemma galois_quad_comp0:
  "is_galois_connection f X g Y \<Longrightarrow> x \<in> X \<Longrightarrow> (g \<circ> f \<circ> g \<circ> f) x = (g \<circ> f) x "
  using galois_triple_comp0 by fastforce
 
lemma galois_triple_comp11:
  "is_galois_connection f X g Y \<Longrightarrow> y \<in> Y \<Longrightarrow> g y \<le> (g \<circ> f \<circ> g) y"
  by (simp add: image_subset_iff is_extensive_on_def is_galois_connection_def is_map_def)

lemma galois_triple_comp12:
  "is_galois_connection f X g Y \<Longrightarrow> y \<in> Y \<Longrightarrow> g y \<ge> (g \<circ> f \<circ> g) y"
  by (meson galois_triple_comp02 is_galois_connection_def)

lemma galois_triple_comp1:
  "is_galois_connection f X g Y \<Longrightarrow> y \<in> Y \<Longrightarrow> g y = (g \<circ> f \<circ> g) y"
  using galois_triple_comp11 galois_triple_comp12 order_antisym by blast

lemma galois_quad_comp1:
  "is_galois_connection f X g Y \<Longrightarrow> y \<in> Y \<Longrightarrow> (f \<circ> g \<circ> f \<circ> g) y = (f \<circ> g) y"
  using galois_triple_comp1 by fastforce 

lemma galois_quad_comp1b:
  "is_galois_connection f X g Y \<Longrightarrow> y \<in> Y \<Longrightarrow> f( g ( f ( g y) ) ) = f (g y)"
  using galois_triple_comp1 by fastforce           

lemma galois_quad_comp0b:
  "is_galois_connection f X g Y \<Longrightarrow> x \<in> X \<Longrightarrow> g( f ( g ( f x) ) ) = g (f x )"
  using galois_triple_comp0 by fastforce 

lemma galois_double_comp_is_ext:
  "is_galois_connection f X g Y \<Longrightarrow> is_extensive_on (f \<circ> g) Y \<and> is_extensive_on (g \<circ> f) X"
  by (simp add: is_galois_connection_def)
 
lemma galois_double_comp_is_iso:
  "is_galois_connection f X g Y \<Longrightarrow> is_isotone_on (f \<circ> g) Y \<and> is_isotone_on (g \<circ> f) X"
  by (meson antitone_comp is_galois_connection_def)

lemma galois_double_comp_is_map:
  "is_galois_connection f X g Y \<Longrightarrow> is_self_map (f \<circ> g) Y \<and> is_self_map (g \<circ> f) X"
  by (simp add: galois_double_comp_is_ext is_extensive_on_imp_map)
 
lemma galois_double_comp0_is_idm:
  "is_galois_connection f X g Y \<Longrightarrow> is_idempotent_on (f \<circ> g) Y \<and>  is_idempotent_on (g \<circ> f) X"
  by(auto simp add:is_idempotent_on_def galois_double_comp_is_map galois_quad_comp0b galois_quad_comp1b)

lemma galois_double_comp1_is_cl:
  "is_galois_connection f X g Y \<Longrightarrow> is_closure_on (f \<circ> g) Y \<and> is_closure_on (g \<circ> f) X"
  by (simp add: galois_double_comp0_is_idm galois_double_comp_is_ext galois_double_comp_is_iso is_closure_on_iff)


lemma l_is_map:
  "is_map (\<lambda>A. lb_set A X) (Pow X) (Pow X)"
  by (simp add: Pow_not_empty image_subset_iff is_map_def lb_set_subset_space)

lemma u_is_map:
  "is_map (\<lambda>A. ub_set A X) (Pow X) (Pow X)"
  by (simp add: Pow_not_empty image_subset_iff is_map_def ub_set_subset_space)

lemma l_is_antitone:
  "is_antitone_on (\<lambda>A. lb_set A X) (Pow X)"
  by (simp add: is_antitone_on_def lb_set_antitone1)

lemma u_is_antitone:
  "is_antitone_on (\<lambda>A. ub_set A X) (Pow X)"
  by (simp add: is_antitone_on_def ub_set_antitone1)

lemma lu_is_map:
  "is_self_map ((\<lambda>A. lb_set A X) \<circ> (\<lambda>A. ub_set A X)) (Pow X)"
  using is_map_comp l_is_map u_is_map by blast

lemma ul_is_map:
  "is_self_map ((\<lambda>A. ub_set A X) \<circ> (\<lambda>A. lb_set A X)) (Pow X)"
  using is_map_comp l_is_map u_is_map by blast

lemma lu_is_extensive:
  "is_extensive_on ((\<lambda>A. lb_set A X) \<circ> (\<lambda>A. ub_set A X)) (Pow X)"
  by (simp add: is_extensive_on_def lu_extensive lu_is_map)

lemma ul_is_extensive:
  "is_extensive_on ((\<lambda>A. ub_set A X) \<circ> (\<lambda>A. lb_set A X)) (Pow X)"
  by (simp add: is_extensive_on_def ul_extensive ul_is_map)

lemma ul_is_galois:
  "is_galois_connection (\<lambda>A. lb_set A X) (Pow X) (\<lambda>A. ub_set A X) (Pow X)"
  by (simp add: is_galois_connection_def l_is_antitone l_is_map lu_is_extensive u_is_antitone u_is_map ul_is_extensive)

lemma lu_is_galois:
  "is_galois_connection (\<lambda>A. ub_set A X) (Pow X) (\<lambda>A. lb_set A X) (Pow X)"
  by (simp add: is_galois_connection_def l_is_antitone l_is_map lu_is_extensive u_is_antitone u_is_map ul_is_extensive)

definition moore_family_cl::"'a set set \<Rightarrow> 'a set \<Rightarrow> ('a set \<Rightarrow> 'a set)" where
  "moore_family_cl A X \<equiv> (\<lambda>E. Inf (ub_set {E} A) (Pow X))"

lemma moore_family_ne:
  "is_moore_family A X \<Longrightarrow> A \<noteq> {}"
  by(auto simp add: is_moore_family_def)

lemma moore_family_imp1:
  "is_moore_family A X \<Longrightarrow> A \<subseteq> Pow X"
  by (simp add: is_moore_family_def)

lemma moore_family_imp21:
  "is_moore_family A X \<Longrightarrow> x \<in> Pow X \<Longrightarrow>  (Inf (ub_set {x} A) (Pow X)) \<in> A"
  by (simp add: is_moore_family_def ub_set_subset_space)

lemma moore_family_imp22:
  "is_moore_family A X \<Longrightarrow> x \<in> Pow X \<Longrightarrow>  (Inf (ub_set {x} A) (Pow X)) lb (ub_set {x} A)"
  by (simp add: has_inf_in_imp2 lb_def sets_have_inf5)

lemma moore_family_imp23:
  "is_moore_family A X \<Longrightarrow> x \<in> Pow X \<Longrightarrow> x \<le>  (Inf (ub_set {x} A) (Pow X))"
  by (simp add: has_inf_imp3 sets_have_inf5 ub_set_imp)

lemma moore_family_imp24:
  "is_moore_family A X \<Longrightarrow> x \<in> Pow X \<Longrightarrow> (Inf (ub_set {x} A) (Pow X)) \<in> (ub_set {x} A)"
  by (metis (no_types, lifting) moore_family_imp21 moore_family_imp23 singletonI up_cl_ub up_closure_in_imp)

lemma moore_family_imp2:
  "is_moore_family A X \<Longrightarrow> x \<in> Pow X \<Longrightarrow> is_min (Inf (ub_set {x} A) (Pow X)) (ub_set {x} A)"
  by (simp add: is_min_iff2 moore_family_imp22 moore_family_imp24)

lemma moore_family_imp3:
  "is_moore_family A X \<Longrightarrow> x \<in> Pow X \<Longrightarrow> has_min (ub_set {x} A)"
  using has_min_iff2 moore_family_imp2 by blast

lemma moore_family_is_clr:
  "is_moore_family A X \<Longrightarrow> is_clr A (Pow X)"
  by(auto simp add:is_clr_def moore_family_ne moore_family_imp1 moore_family_imp3)

lemma moore_family_cl_is_cl1:
  "is_moore_family A X \<Longrightarrow> is_extensive_on (moore_family_cl A X) (Pow X)"
  apply(auto simp add:is_extensive_on_def is_map_def moore_family_cl_def is_moore_family_def)
  apply (meson PowI has_inf_imp3 insertI1 sets_have_inf5 subsetD ub_set_mem_iff)
  by (simp add: sets_have_inf6)

lemma moore_family_cl_is_cl2:
  "is_moore_family A X \<Longrightarrow> is_isotone_on (moore_family_cl A X) (Pow X)"
  apply(auto simp add:is_isotone_on_def is_map_def moore_family_cl_def is_moore_family_def)
  by (meson inf_antitone1 sets_have_inf5 subsetD ub_set_singleton_antitone)

lemma moore_family_cl_is_cl3:
  "is_moore_family A X \<Longrightarrow> is_idempotent_on (moore_family_cl A X) (Pow X)"
  apply(auto simp add:is_idempotent_on_def is_map_def moore_family_cl_def is_moore_family_def)
  apply (meson PowI has_inf_in_imp2 in_mono sets_have_inf5 singleton_in_lb_set ub_set_subset_space)
  apply (metis PowI empty_subsetI inf_subset_eq1 insert_subset sets_have_inf5 sup_in_eq_inf_in_ub sup_singleton2 ub_set_subset_space)
  by (simp add: sets_have_inf6)

lemma moore_family_cl_is_cl:
  "is_moore_family A X \<Longrightarrow> is_closure_on (moore_family_cl A X) (Pow X)"
  by (simp add: is_closure_on_def is_proj_on_def moore_family_cl_is_cl1 moore_family_cl_is_cl2 moore_family_cl_is_cl3)

lemma has_max_imp_ub_ne:
  "has_max X \<Longrightarrow> A \<in> Pow X \<Longrightarrow> ub_set A X \<noteq> {}"
  by (metis Pow_iff empty_iff has_max_def is_max_imp_set)

lemma has_min_imp_lb_ne:
  "has_min X \<Longrightarrow> A \<in> Pow X \<Longrightarrow> lb_set A X \<noteq> {}"
  by (metis Pow_iff empty_iff has_min_def is_min_imp_set)

lemma is_inf_complete_imp_binf_complete:
  "is_inf_complete X \<Longrightarrow> is_binf_complete X"
  by(simp add:is_inf_complete_def is_binf_complete_def)

lemma is_sup_complete_imp_bsup_complete:
  "is_sup_complete X \<Longrightarrow> is_bsup_complete X"
  by(simp add:is_sup_complete_def is_bsup_complete_def)

definition is_lattice::"'a::order set \<Rightarrow> bool" where
  "is_lattice X \<equiv> (is_bsup_complete X) \<and> (is_binf_complete X)"

definition is_complete_lattice::"'a::order set \<Rightarrow> bool" where
  "is_complete_lattice X \<equiv> (is_sup_complete X) \<and> (is_inf_complete X)"

lemma is_complete_imp_is_lattice:
  "is_complete_lattice X  \<Longrightarrow> is_lattice X"
  by (simp add:is_complete_lattice_def is_lattice_def is_inf_complete_imp_binf_complete is_sup_complete_imp_bsup_complete)

lemma is_complete_imp_max_and_inf:
  "is_complete_lattice X \<Longrightarrow> X \<noteq> {} \<Longrightarrow> (is_inf_complete X \<and> has_max X)"
  by (simp add: is_complete_lattice_def sup_complete_max2)

lemma is_complete_imp_min_and_sup:
  "is_complete_lattice X \<Longrightarrow> X \<noteq> {} \<Longrightarrow> (is_sup_complete X \<and> has_min X)"
  by (simp add: is_complete_lattice_def inf_complete_min2)

lemma max_imp_ub_set_ne:
  "has_max X \<Longrightarrow> A \<in> Pow_ne X \<Longrightarrow> ub_set A X \<noteq> {}"
  by (simp add: has_max_imp_ub_ne)

lemma min_imp_lb_set_ne:
  "has_min X \<Longrightarrow> A \<in> Pow_ne X \<Longrightarrow> lb_set A X \<noteq> {}"
  by (simp add: has_min_imp_lb_ne)

lemma inf_complete_max_exists_sup:
  "is_inf_complete X \<and> has_max X\<Longrightarrow> A \<in> Pow_ne X \<Longrightarrow> has_sup A X"
  by (simp add: inf_complete_imp0 inf_ub_imp_has_sup max_imp_ub_set_ne ub_set_subset_space)


lemma sup_complete_min_exists_inf:
  "is_sup_complete X \<and> has_min X\<Longrightarrow> A \<in> Pow_ne X \<Longrightarrow> has_inf A X"
  by (simp add: sup_complete_imp0 sup_lb_imp_has_inf min_imp_lb_set_ne lb_set_subset_space)

lemma inf_comp_max_imp_sup_comp_min:
 "(is_inf_complete X \<and> has_max X) \<Longrightarrow> (is_sup_complete X \<and> has_min X)"
  by (simp add: has_max_imp_ne inf_complete_max_exists_sup inf_complete_min2 is_sup_complete_def)

lemma sup_comp_max_imp_inf_comp_min:
 "(is_sup_complete X \<and> has_min X) \<Longrightarrow> (is_inf_complete X \<and> has_max X)"
  by (simp add: has_min_imp_ne is_inf_complete_def sup_complete_max2 sup_complete_min_exists_inf)


lemma sup_comp_min_imp_comp:
  "(is_sup_complete X \<and> has_min X) \<Longrightarrow> is_complete_lattice X"
  by (simp add: is_complete_lattice_def sup_comp_max_imp_inf_comp_min)

lemma inf_comp_max_imp_comp:
  "(is_inf_complete X \<and> has_max X) \<Longrightarrow> is_complete_lattice X"
  by (simp add: inf_comp_max_imp_sup_comp_min sup_comp_min_imp_comp)


section ClosureRangesAndCompleteness
context
  fixes C X::"'a::order set" 
  assumes A0:"is_inf_complete X" and
          A1:"C \<subseteq> X" and
          A2:"C \<noteq> {}"
begin

lemma clr_inf_complete1:
  "is_clr C X \<Longrightarrow> A \<in> Pow_ne C \<Longrightarrow> has_inf A X"
  using A0 A1 inf_complete_imp2 by blast

lemma clr_inf_complete2:
  "is_clr C X \<Longrightarrow> A \<in> Pow_ne C \<Longrightarrow> Inf A X \<in> C"
  using clr_inf_ne clr_inf_complete1 by blast

lemma clr_inf_complete3:
  "is_clr C X \<Longrightarrow> A \<in> Pow_ne C \<Longrightarrow>  Inf A C = Inf A X"
  by (simp add: A1 clr_inf_complete1 clr_inf_complete2 inf_subset_eq1)

lemma clr_inf_on_cinf_converse:
  assumes A3:"\<forall>A \<in> Pow_ne C. has_inf A C \<and> Inf A C = Inf A X" and
          A4:"\<forall>x \<in> X. ub_set {x} C \<noteq> {}" and
          A5:"C \<noteq> {}"
  shows "is_clr C X"
proof-
  have B0:"\<forall>x \<in> X. (has_min (ub_set {x} C))"
  proof
    fix x assume A5:"x \<in> X"
    let ?P="ub_set {x} C"
    have B0:"?P \<noteq> {}"
      by (simp add: A4 A5)
    have B2:"?P \<subseteq> X"
      by (simp add: A1 ub_set_subset2)
    have B3:"has_inf ?P X"
      by (simp add: A0 B0 B2 inf_complete_imp0)
    obtain i where B30:"is_inf i ?P X"
      using B3 inf_obtain by blast
    have B31:"i \<in> C \<and> i lb ?P"
      by (metis A3 B0 B30 PowI has_inf_in_set is_inf_in_imp1 is_inf_inf_eq lb_set_imp1 pow_ne_if ub_set_subset_space)
    have B32:"x \<le> i"
      by (meson A5 B30 insertCI is_inf_in_imp3 ub_set_mem)
    have B33:"i \<in> ?P"
      by (metis B31 B32 singletonI up_cl_ub up_closure_in_imp)
    have B10:"is_min i ?P"
      using B2 B30 B33 is_inf_in_set_imp_is_min by auto
    show "has_min (ub_set {x} C)"
      using B10 has_min_iff2 by blast
  qed
  show ?thesis
    by (simp add: A1 A5 B0 is_clr_def)
qed

lemma clr_on_comp_semilattice:
  assumes A2:"has_min X" and
          A3:"is_closure_on f X"
  shows "\<forall>x \<in> X. Inf {y \<in> (f`X). x \<le> f y} X = min (ub_set {x} (f`X))" 
proof
  fix x assume A2:"x \<in> X"
  let ?E1="{y \<in> (f`X). x \<le> (f y)}" let ?E2="ub_set {x} (f`X)"
  have B0:"?E1 = ?E2"
    apply(auto simp add:ub_set_def ub_def)
    apply (metis A3 cl_eq_imp_idemp closure_eq_if_closure is_closure_on_imp2)
    by (metis A3 is_closure_on_iff is_idempotent_imp1)
  have B1:"has_min ?E2"
    by (metis A2 A3 closure.Cf_is_clr closure.intro clr_from_closure_def insert_absorb insert_not_empty is_clr_def)
  have B2:"(min ?E2) lb ?E2"
    using B1 has_min_def is_sup_imp_lt_ub is_sup_in_iff min_if by blast
  have B3:"(min ?E2) \<in> X"
    by (metis A3 B1 has_sup_def has_sup_in_imp1 is_closure_on_imp2 is_self_map_imp min_if subsetD ub_set_subset_space)
  have B4:"\<forall>l \<in> lb_set ?E2 X. l \<le> (min ?E2)"
    by (metis B1 has_sup_def has_sup_in_imp1 lb_set_imp min_if)
  have B5:"(min ?E2) \<in> lb_set ?E2 X"
    using B2 B3 lb_set_if by blast
  have B6:"is_max (min ?E2) (lb_set ?E2 X)"
    by (simp add: B4 B5 is_max_if2)
  have B7:"is_inf (min ?E2) ?E2 X"
    by (simp add: B6 is_inf_def)
  have B8:"is_inf (min ?E2) ?E1 X"
    by (simp add: B0 B7)
  show "Inf {y \<in> (f`X). x \<le> f y} X = min (ub_set {x} (f`X))"
    using B8 is_inf_inf_eq by fastforce
qed
end

lemma clr_on_comp_semilattice2:
  fixes X::"'a::order set" 
  assumes A0:"is_inf_complete X" and
          A2:"has_min X" and
          A3:"is_closure_on f X"
  shows "\<forall>x \<in> X. Inf {y \<in> (f`X). x \<le> f y} X = f x" 
proof-
  have B0:"\<forall>x \<in> X. closure_from_clr (clr_from_closure f X) x = min (ub_set {x} (f`X))"
    by (simp add: closure_from_clr_def clr_from_closure_def)
  have B1:"\<forall>x \<in> X. closure_from_clr (clr_from_closure f X) x = f x"
    using A3 cl_cr_cl_eq_cl by auto
  have B2:"\<forall>x \<in> X. f x = min (ub_set {x} (f`X))"
    using B0 B1 by fastforce
  have B3:"\<forall>x \<in> X.  Inf {y \<in> (f`X). x \<le> f y} X =  min (ub_set {x} (f`X))"
    using A0 A2 A3 clr_on_comp_semilattice by blast
  have B4:"\<forall>x \<in> X. f x = min (ub_set {x} (f`X))"
    using B2 by blast
  show ?thesis
    using B3 B4 by fastforce
qed

context
  fixes C X::"'a::order set" 
  assumes A0:"is_complete_lattice X" and
          A1:" C \<subseteq> X"
begin


lemma complete_clr1:
  "is_clr C X \<Longrightarrow> A \<in> Pow C \<Longrightarrow> Inf A X \<in> C"
  by (metis A0 clr_inf_complete2 has_inf_in_set inf_empty_iff inf_in_degenerate is_clr_def is_complete_imp_max_and_inf is_max_sanity_check max_gt_elem pow_ne_if subset_empty top_is_closed2)

lemma complete_clr2:
  "is_clr C X \<Longrightarrow> A \<in> Pow C \<Longrightarrow> Inf A C = Inf A X"
  by (metis A0 Pow_iff clr_inf_complete3 complete_clr1 inf_in_degenerate2 inf_subset_eq1 is_clr_imp1 is_complete_imp_max_and_inf pow_ne_if subset_empty)

lemma complet_clr31:
  "(\<And>A. A \<in> Pow C \<Longrightarrow> has_inf A X \<and> Inf A X \<in> C) \<Longrightarrow> x \<in> X \<Longrightarrow>x \<le>  Inf (ub_set {x} C) X"
  by (simp add: has_inf_imp3 ub_set_imp ub_set_subset_space)

lemma complet_clr32:
  "(\<And>A. A \<in> Pow C \<Longrightarrow> has_inf A X \<and> Inf A X \<in> C) \<Longrightarrow> x \<in> X \<Longrightarrow>Inf (ub_set {x} C) X \<in> ub_set {x} C"
  by (metis Pow_iff complet_clr31 singletonI ub_set_subset_space up_cl_ub up_closure_in_imp)

lemma complet_clr33:
  "(\<And>A. A \<in> Pow C \<Longrightarrow> has_inf A X \<and> Inf A X \<in> C) \<Longrightarrow> x \<in> X \<Longrightarrow> Inf (ub_set {x} C) X lb (ub_set {x} C)"
  by (simp add: has_inf_in_imp2 lb_def ub_set_subset_space)

lemma complet_clr34:
  "(\<And>A. A \<in> Pow C \<Longrightarrow> has_inf A X \<and> Inf A X \<in> C) \<Longrightarrow> x \<in> X \<Longrightarrow>is_min (Inf (ub_set {x} C) X) (ub_set {x} C)"
  by (meson complet_clr32 complet_clr33 is_min_iff2)

lemma complet_clr35:
  "(\<And>A. A \<in> Pow C \<Longrightarrow> has_inf A X \<and> Inf A X \<in> C) \<Longrightarrow> x \<in> X \<Longrightarrow> has_min (ub_set {x} C)"
  using complet_clr34 has_min_def by auto

lemma complet_clr3:
  "(\<And>A. A \<in> Pow C \<Longrightarrow> has_inf A X \<and> Inf A X \<in> C) \<Longrightarrow> is_clr C X"
  by (metis A1 Pow_top complet_clr35 empty_iff is_clr_def)

end

context
  fixes C X::"'a::order set" 
  assumes A0:"is_complete_lattice X" and
          A1:" C \<subseteq> X" and
          A2:"is_clr C X"
begin

lemma complete_clr_sup10:
  "A \<subseteq> C \<Longrightarrow> (ub_set A C \<noteq> {})"
  by (metis A0 A2 Pow_iff closure_range.intro closure_range.space_is_ne has_max_imp_ub_ne is_clr_imp_max is_complete_imp_max_and_inf)

lemma complete_clr_sup11:
  "A \<subseteq> C \<Longrightarrow> has_inf (ub_set A C) X"
  by (meson A0 A1 PowI complete_clr_sup10 inf_complete_imp0 is_complete_lattice_def pow_ne_if ub_set_subset2)

lemma complete_clr_sup12:
  "A \<subseteq> C \<Longrightarrow> Inf (ub_set A C) X = Inf (ub_set A C) C"
  by (metis A0 A1 A2 PowI complete_clr2 ub_set_subset_space)

lemma complete_clr_sup13:
  "A \<subseteq> C \<Longrightarrow> has_inf (ub_set A C) C"
  by (meson A0 A1 A2 PowI complete_clr1 complete_clr_sup11 inf_subset_eq1 ub_set_subset_space)

lemma complete_clr_sup14:
  "A \<subseteq> C \<Longrightarrow>is_sup (Inf (ub_set A C) C) A C \<and> Sup A C =  (Inf (ub_set A C) C)"
  by (metis complete_clr_sup13 inf_ub_imp_has_sup sup_in_eq_inf_in_ub sup_is_sup)


lemma complete_clr_inf_sup_complete:
  "A \<subseteq> C \<Longrightarrow> has_inf A C \<and> has_sup A C"
  by (simp add: complete_clr_sup13 inf_ub_imp_has_sup lb_set_subset_space sup_lb_imp_has_inf)

lemma clr_on_complete_lattice_is_complete:
  "is_complete_lattice C"
  by (simp add: complete_clr_inf_sup_complete is_sup_complete_def sup_comp_min_imp_comp sup_in_degenerate3)

end

context
 fixes f::"'a::order \<Rightarrow> 'a::order" and 
       A X::"'a::order set" 
  assumes A0:"X \<noteq> {}" and 
          A1:"is_complete_lattice X" and
          A2:"is_closure_on f X"      
begin

lemma closure_of_min:
  "f (min X) = min (f`X)"
proof-
  let ?mx="min X" let ?Y="f`X" let ?my="min ?Y"
  have B0:"f ?mx \<in> ?Y"
    by (metis A0 A1 if_has_min_min_unique image_eqI is_complete_imp_min_and_sup is_min_imp min_if)
  have B1:"\<forall>y \<in> ?Y. (f ?mx) \<le> y"
  proof
    fix y assume A3:"y \<in> ?Y"
    obtain x where B1:"x \<in> X \<and> y = f x"
      using A3 by blast
    have B2:"?mx \<le> x"
      by (metis A0 A1 B1 has_min_iff2 is_complete_imp_min_and_sup is_min_iff min_if)
    have B3:"f ?mx \<le> f x"
      by (metis A0 A1 A2 B1 B2 cl_eq_imp_iso2 closure_if_cl_eq has_sup_in_set is_complete_imp_min_and_sup sup_empty_iff sup_in_degenerate)
    show "(f ?mx) \<le> y"
      by (simp add: B1 B3)
  qed
  have B2:"is_min (f ?mx) ?Y"
    by (simp add: B0 B1 is_min_if2)
  show ?thesis
    using B2 min_if by auto
qed

lemma complete_clr_sup3:
  assumes "A \<subseteq> X"
  shows "f (Sup A X) = f (Sup (f`A) X) \<and> f (Sup (f`A) (f`X)) = f (Sup (f`A) X)"
proof(cases "A={}")
  case True
  have B0:"Sup A X = min X"
    by (simp add: True sup_in_degenerate)
  have B1:"f`A = {}"
    by (simp add: True)
  have B2:"f (Sup (f`A) (f`X)) = f (Sup (f`A) X)"
    by (metis A1 A2 B1 True closure_of_min has_sup_in_set is_closure_on_iff is_complete_imp_min_and_sup is_idempotent_imp1 sup_empty_iff sup_in_degenerate)
  then show ?thesis
    using True by fastforce
next
  case False
  have B2:"\<forall>a \<in> A. a \<le> f a"
    using A2 assms closure_eq_if_closure_l by blast
  have B3:"(f`A) \<subseteq> X"
    by (meson A2 assms dual_order.trans image_mono is_closure_on_imp2 is_self_map_imp)
  have B4:"has_sup (f`A) X"
    by (meson A0 A1 B3 False PowI image_is_empty is_complete_imp_min_and_sup is_sup_complete_def pow_ne_if)
  have B5:"\<forall>a \<in> A. f a \<le> Sup (f`A) X"
    using B4 has_sup_in_imp2 by blast
  have B6:"\<forall>a \<in> A. a \<le> Sup (f`A) X"
    using B2 B5 dual_order.trans by blast
  have B7:"Sup A X \<le> Sup (f`A) X"
    by (meson A0 A1 B4 B6 False PowI assms has_sup_imp3 has_sup_in_set is_complete_imp_min_and_sup is_sup_complete_def pow_ne_if)
  have B8:"f (Sup A X) \<le>  f (Sup (f`A) X)"
    by (meson A0 A1 A2 B4 B7 False PowI assms has_sup_in_set is_closure_on_iff is_complete_imp_min_and_sup is_isotone_imp1 pow_ne_if sup_complete_imp1)
  have B9:"f`X \<subseteq> X"
    by (simp add: A2 is_closure_on_imp2 is_self_map_imp)
  have B10:"Sup (f`A) X \<le> Sup (f`A) (f`X)"
    by (simp add: A0 A1 A2 B4 B9 False assms closure_of_sup_is_sup2 inf_complete_max_exists_sup is_complete_imp_max_and_inf sup_antitone2)
  have B11:"is_clr (f`X) X"
    by (metis A0 A2 closure.Cf_is_clr closure.intro clr_from_closure_def)
  have B12:"(f`A) \<subseteq> (f`X)"
    by (simp add: assms image_mono)
  have B13:"has_sup (f`A) (f`X)"
    by (meson A1 B11 B12 B9 complete_clr_inf_sup_complete)
  have B14:"Sup (f`A) (f`X) \<in> X"
    by (metis B13 B9 has_sup_in_set subsetD)
  have B15:"f (Sup (f`A) X) \<le> f (Sup (f`A) (f`X))"
    using A2 B10 B14 B4 has_sup_in_set is_closure_on_iff is_isotone_on_def by blast
  have B16:"\<forall>a \<in> A. a \<le> Sup A X"
    by (meson A0 A1 False PowI assms has_sup_in_imp2 is_complete_imp_min_and_sup is_sup_complete_def pow_ne_if)
  have B17:"\<forall>a \<in> A. f a \<le> f (Sup A X)"
    by (meson A0 A1 A2 B16 False PowI assms is_closure_on_iff is_complete_imp_min_and_sup is_isotone_imp1 pow_ne_if subsetD sup_complete_imp1)
  have B18:"f (Sup A X) \<in> (f`X)"
    by (simp add: A0 A1 False assms is_complete_imp_min_and_sup sup_complete_imp1)
  have B19:"Sup (f`A) (f`X) \<le> f (Sup A X)"
    using B13 B17 B18 has_sup_imp3 by fastforce
  have B20:"f (Sup (f`A) (f`X)) = f (Sup (f`A) X)"
    by (meson A2 B14 B15 B19 B4 B8 closure_eq_if_closure_r has_sup_in_set order_antisym_conv order_trans)
  have B21:"f (Sup A X) = f (Sup (f`A) X)"
    by (meson A1 A2 B10 B19 B4 B8 False Orderings.order_eq_iff Pow_iff assms closure_eq_if_closure_r has_sup_in_set is_complete_lattice_def order_trans pow_ne_if sup_complete_imp1)
  then show ?thesis
    using B20 by blast
qed

end

lemma closure_sups1:
  fixes f::"'a::order \<Rightarrow> 'a::order" and A X::"'a::order set" 
  assumes A0:"is_closure_on f X" and A1:"A \<subseteq> X" and  A2:"is_complete_lattice X" and A3:"X \<noteq> {}"
  shows "f (Sup A X) = (Sup (f`A) (f`X))"
  by (metis A0 A1 A2 A3 PowI closure_of_sup_is_sup2 is_complete_imp_min_and_sup is_sup_complete_def pow_ne_if sup_empty_iff sup_in_degenerate)

lemma closure_sups2:
  fixes f::"'a::order \<Rightarrow> 'a::order" and A X::"'a::order set" 
  assumes A0:"is_closure_on f X" and A1:"A \<subseteq> (f`X)" and  A2:"is_complete_lattice X" and A3:"X \<noteq> {}"
  shows "Sup A (f`X) = f (Sup A X)"
  by (metis (full_types) A0 A1 A2 A3 closure_sups1 complete_clr_sup3 subset_imageE)

lemma closure_sups3:
  assumes A0:"is_closure_on f X" and A1:"A \<subseteq> X" and  A2:"is_complete_lattice X" and A3:"X \<noteq> {}"
  shows "f (Sup A X) = f (Sup (f`A) X) \<and> f (Sup (f`A) (f`X)) = f (Sup (f`A) X)"
  using A0 A1 A2 A3 complete_clr_sup3 by blast

lemma closure_range_on_complete_lattice_is_complete:
  "is_complete_lattice X \<Longrightarrow> C \<subseteq> X \<Longrightarrow> is_clr C X \<Longrightarrow> is_complete_lattice C"
  using clr_on_complete_lattice_is_complete by blast

lemma pow_is_complete_lattice:
  "is_complete_lattice(Pow X)"
  by (simp add: inf_comp_max_imp_comp inf_in_degenerate3 is_inf_complete_def sets_have_inf5)

lemma dpow_is_complete_lattice:
  "is_complete_lattice(Pow (Pow X))"
  by (simp add: pow_is_complete_lattice)

lemma is_moore_family_contains_space:
  "is_moore_family C X \<Longrightarrow>X \<in> C"
  by (metis Pow_bottom is_moore_family_def sets_have_infb)

lemma is_moore_family_imp1:
  "is_moore_family C X \<Longrightarrow> a \<in> C \<Longrightarrow> a \<subseteq> X"
  using PowD is_moore_family_def by auto

lemma is_moore_family_imp2:
  "is_moore_family C X \<Longrightarrow> A \<subseteq> C \<Longrightarrow> a \<in> A \<Longrightarrow> a \<subseteq> X"
  by (meson PowD is_moore_family_def subsetD)

lemma is_moore_family_imp3:
  "is_moore_family (C::'a::order set set) X \<Longrightarrow> A \<subseteq> X \<Longrightarrow> (\<Inter>(ub_set {A} C)) lb (ub_set {A} C)"
  by (simp add: Inter_lower is_lb_simp2)

lemma is_moore_family_inf1:
  "is_moore_family C X \<Longrightarrow> A \<in> Pow C \<Longrightarrow> (Inf A (Pow X)) \<in> C"
  by (simp add: is_moore_family_def)

lemma is_moore_family_inf2:
  "is_moore_family C X \<Longrightarrow> A \<in> Pow C \<Longrightarrow> is_inf (Inf A (Pow X)) A C"
  by (meson PowD inf_is_inf inf_subset_eq0 is_moore_family_inf1 moore_family_imp1 sets_have_inf5)

lemma is_moore_family_inter:
  assumes "is_moore_family C X" and "A \<in> Pow_ne C" 
  shows "\<Inter>A \<in> C"
proof-
  have B0:"(Inf A (Pow X)) = \<Inter>A \<inter> X"
    by (simp add: sets_have_inf6)
  have B1:"... = \<Inter>A "
    using assms(1) assms(2) is_moore_family_imp1 by fastforce
  show ?thesis
    by (metis B0 B1 DiffD1 assms(1) assms(2) is_moore_family_def)
qed

lemma is_moore_family_closure_eq:
  assumes A0:"is_moore_family C X" and A1:"A \<subseteq> X"  
  shows "(moore_family_cl C X) A = \<Inter>{c \<in> C. A \<subseteq> c}"
proof-
  have B0:"(moore_family_cl C X) A =  Inf (ub_set {A} C) (Pow X)"
    by (simp add: moore_family_cl_def)
  have B1:"... = (\<Inter>(ub_set {A} C)) \<inter> X"
    by (simp add: sets_have_inf6)
  have B2:"... = (\<Inter>(ub_set {A} C))"
    by (metis A0 A1 Inf_lower inf_absorb1 is_moore_family_contains_space singletonD ub_set_elm)
  have B3:"... = \<Inter>{c \<in> C. A \<subseteq> c}"
    by (simp add: ub_set_in_singleton)
  show ?thesis
    using B0 B1 B2 B3 by auto
qed

lemma is_moore_family_imp4:
  "is_moore_family C X \<Longrightarrow> A \<subseteq> X \<Longrightarrow> A \<noteq> {} \<Longrightarrow> (\<Inter>(ub_set {A} C)) \<in> C"
  by (simp add: has_min_imp_ne is_moore_family_inter moore_family_imp3 ub_set_subset_space)

lemma is_moore_family_imp5:
  "is_moore_family C X \<Longrightarrow> A \<subseteq> X \<Longrightarrow> A \<subseteq> (\<Inter>(ub_set {A} C))"
  by (simp add: le_Inf_iff ub_set_imp)

lemma is_moore_family_imp6:
  "is_moore_family C  X \<Longrightarrow> A \<subseteq> X \<Longrightarrow>(\<Inter>(ub_set {A} C)) \<in> (ub_set {A} C)"
  by (metis (mono_tags, lifting) PowI has_min_imp_ne is_moore_family_imp5 is_moore_family_inter moore_family_imp3 pow_ne_if singletonI ub_set_subset_space up_cl_ub up_closure_in_imp)

lemma is_moore_family_imp7:
  "is_moore_family C X \<Longrightarrow> A \<subseteq> X \<Longrightarrow> is_min (\<Inter>(ub_set {A} C))  (ub_set {A} C)"
  by (simp add: Inter_lower is_min_if2 is_moore_family_imp6)

lemma is_moore_family_imp8:
  "is_moore_family C X \<Longrightarrow> A \<subseteq> X \<Longrightarrow> has_min (ub_set {A} C)"
  using has_min_iff2 is_moore_family_imp7 by blast

lemma is_moore_family_is_clr:
  "is_moore_family C X \<Longrightarrow> is_clr C (Pow X)"
  by (simp add: moore_family_is_clr)

lemma moore_family_is_complete_lattice:
  "is_moore_family C X \<Longrightarrow> is_complete_lattice C"
  by (meson closure_range_on_complete_lattice_is_complete moore_family_imp1 moore_family_is_clr pow_is_complete_lattice)

lemma lattice_inf_is_inf:
  "is_inf (inf (a::'a::lattice) b) {a, b} UNIV"
  by (simp add: is_inf_def is_max_iff lb_set_mem_iff)

lemma lattice_sup_is_sup:
  "is_sup (sup (a::'a::lattice) b) {a, b} UNIV"
  by (simp add: is_sup_def is_min_iff ub_set_mem_iff)

lemma order_bot_is_min:
  "is_min (bot::'a::order_bot) UNIV"
  by (simp add: is_min_bot)



lemma filter_closure_mem_iff:
  "A \<noteq> {} \<Longrightarrow> x \<in> filter_closure A X  \<longleftrightarrow> (x \<in> X \<and> (\<exists>F \<in> Fpow_ne A. Inf F X \<le> x))"
  by (simp add: filter_closure_def)

lemma principal_filter_closure_mem_iff:
  "A \<noteq> {} \<Longrightarrow> x \<in> principal_filter_closure A X \<longleftrightarrow> (\<exists>a \<in> A. x \<in> ub_set {a} X)"
  by (simp add: principal_filter_closure_def)

lemma principal_filter_closure_mem_iff2:
  "A \<noteq> {} \<Longrightarrow> x \<in> principal_filter_closure A X \<longleftrightarrow> (x \<in> X) \<and> (\<exists>a \<in> A. a \<le> x)"
  by(simp add: principal_filter_closure_mem_iff ub_set_def ub_def )

lemma filter_closure_obtains:
  assumes "A \<noteq> {}" and "x \<in> filter_closure A X"
  obtains Fx where "Fx \<in> Fpow_ne A \<and> Inf Fx X \<le> x"
  by (meson assms filter_closure_mem_iff)

lemma principal_filter_closure_obtains:
  assumes "A \<noteq> {}"  and "x \<in>  principal_filter_closure A X"
  obtains a where "a \<in> A \<and>  x \<in> ub_set {a} X"
  using assms principal_filter_closure_mem_iff by blast

lemma principal_filter_closure_obtains2:
  assumes "A \<noteq> {}" and "x \<in>  principal_filter_closure A X"
  obtains a where "a \<in> A \<and>  a \<le> x"
  by (meson assms principal_filter_closure_mem_iff2)

lemma inf_complete_imp_downdir:
  assumes A0:"X \<noteq> {}" and A1:"is_inf_complete X" 
  shows  "is_dwdir X"
proof-
  have B0:"\<And>x1 x2. x1 \<in> X \<and> x2 \<in> X \<longrightarrow> (\<exists>x3 \<in> X. x3 lb {x1, x2})"
  proof
    fix x1 x2 assume A2:" x1 \<in> X \<and> x2 \<in> X "
    have B01:"Inf {x1, x2} X \<in> X \<and> Inf {x1, x2} X lb {x1, x2}"
      by (meson A1 A2 binf_complete_imp0 binf_complete_imp1 has_inf_in_imp1 is_inf_complete_imp_binf_complete lb_set_imp1)
    show "(\<exists>x3 \<in> X. x3 lb {x1, x2})"
      using B01 by blast
  qed
  show ?thesis
    by (simp add: A0 B0 is_dwdir_def)
qed

context
  fixes X::"'a::order set"
  assumes is_ne:"X \<noteq> {}" and
          toped:"has_max X" and
          csinf:"is_inf_complete X"
begin

lemma max_filter:
  "is_filter {max X} X"
  apply(auto simp add:is_filter_def is_dwdir_def is_up_cl_def lb_def up_cl_def)
  using if_has_max_max_unique is_max_imp1 max_if toped apply blast
  apply (simp add: antisym max_gt_elem toped)
  using has_max_def is_max_imp1 max_if toped by blast

lemma max_filter_least:
  "is_filter F X \<Longrightarrow> {max X} \<subseteq> F"
  using filter_contains_max if_has_max_max_unique max_if toped by blast

lemma max_filter2:
  "{max X} \<in> filters X"
  by (meson filters_mem_iff is_filter_imp21 max_filter)

lemma max_filter_least2:
  "{max X} lb filters X"
  by (meson filters_mem_iff is_lb_simp2 max_filter_least)

lemma max_filter_min:
  "is_min {max X} (filters X)"
  by (simp add: is_min_iff2 max_filter2 max_filter_least2)

lemma max_filter_inf:
  "is_inf {max X} (filters X) (filters X)"
  by (simp add: inf_eq_bot1 max_filter_min)


lemma filter_csinf_moore_family1:
  assumes "EF \<in> Pow_ne (filters X)"
  shows "(\<Inter>EF) \<in> (filters X)"
proof-
  let ?I="(\<Inter>EF)"
  have B0:"\<forall>F \<in> EF. max X \<in> F"
    by (metis assms filter_contains_max filters_mem_iff if_has_max_max_unique max_if pow_ne_imp2 subset_eq toped)
  have B1:"is_dwdir ?I"
  proof-
    have B10:"\<And>a b. a \<in>?I \<and> b \<in> ?I\<longrightarrow> (\<exists>c\<in>?I. c lb {a, b})"
    proof
      fix a b assume A1:"a \<in>?I \<and> b \<in> ?I"
      have B11:"\<forall>F \<in> EF. a \<in> F \<and> b \<in> F"
        using A1 by blast
      have B12:"\<forall>F \<in> EF. F \<subseteq> X"
        by (meson PowD assms filters_mem_iff in_mono pow_ne_imp2)
      have B13:"a \<in> X \<and> b \<in> X"
        using B11 B12 assms by fastforce
      have B14:"\<forall>F \<in> EF. has_inf {a, b} X"
        by (simp add: B13 csinf inf_complete_imp0)
      have B15:"\<forall>F \<in> EF. Inf {a, b} X \<in> F"
        by (meson B11 B14 assms filter_inf_closed filters_mem_iff in_mono pow_ne_imp2)
      have B16:"Inf {a, b} X \<in> ?I"
        by (simp add: B15)
      have B17:"Inf {a, b} X lb {a, b}"
        by (metis B14 DiffD2 assms has_inf_in_imp2 insert_iff lb_def subset_empty subset_emptyI)
      show "\<exists>c\<in>?I. c lb {a, b}"
        using B16 B17 by blast
    qed
    show ?thesis
      by (metis B0 B10 InterI empty_iff is_dwdir_if1)
  qed
  have B2:"is_up_cl ?I X"
    apply(auto simp add:is_up_cl_def up_cl_def)
    apply (meson is_filter_def assms filters_mem_iff is_up_cl_imp2 pow_ne_imp2 subset_iff)
    by (metis DiffE Pow_iff all_not_in_conv assms filters_mem_iff in_mono insertI1)
  show ?thesis
    by (simp add: B1 B2 is_filter_def filters_mem_iff in_upsets_in_imp_subset up_sets_in_def)
qed

lemma improper_filter1:
  "is_filter (Pow X) (Pow X)"
  by (meson is_filter_def Pow_bottom Pow_iff Pow_not_empty Pow_top is_dwdir_if2 is_up_cl_if2)

lemma improper_filter2:
  "is_filter X X"
  apply(auto simp add:is_filter_def is_dwdir_def is_up_cl_def)
  apply (simp add: is_ne)
  apply (metis csinf has_inf_def has_lb_def has_lb_iff has_max_imp_ne is_binf_complete_def is_inf_complete_imp_binf_complete)
  using up_cl_in_carrier1 apply blast
  by (meson subset_iff up_cl_in_extensive)

lemma filters_have_min_ub:
  assumes "x \<le> X"
  shows "has_min (ub_set {x} (filters X))"
proof-
  have B0:"\<And>x. x \<le> X \<longrightarrow> has_min (ub_set {x} (filters X))"
  proof
    fix x assume A0:"x \<le> X"
    let ?m="\<Inter>(ub_set {x} (filters X))"
    have B01:"(ub_set {x} (filters X)) \<subseteq> (filters X)"
      by (simp add: ub_set_subset_space)
    have B02:"(ub_set {x} (filters X)) \<noteq> {}"
      by (metis A0 empty_iff filters_mem_iff improper_filter2 is_filter_imp21 singletonI up_cl_ub up_closure_in_imp)
    have B03:"?m \<in> filters X"
      by (simp add: B01 B02 filter_csinf_moore_family1)
    have B04:"?m \<in> (ub_set {x} (filters X))"
      by (meson B03 Inter_greatest ub_set_elm ub_set_mem)
    show "has_min (ub_set {x} (filters X))"
      by (meson B04 Inf_lower has_min_def is_min_if2)
  qed
  show ?thesis
    by (simp add: B0 assms)
qed



lemma filters_is_clr:
  "is_clr (filters X) (Pow X)"
  apply(auto simp add:is_clr_def)
  using max_filter2 apply auto[1]
  using filters_mem_iff apply auto[1]
  by (simp add: filters_have_min_ub)

lemma filter_closure_of_empty:
  "(closure_from_clr (filters X)) {} = {max X}"
proof-
  have B0:"ub_set {} (filters X) = (filters X)"
    by (simp add: ub_set_in_degenerate)
  have B1:"is_min {max X} (ub_set {} (filters X))"
    by (simp add: B0 max_filter_min)
  have B2:"min (ub_set {} (filters X)) = {max X}"
    using B1 min_if by auto
  show ?thesis
    by (smt (verit, ccfv_threshold) B0 B2 PowI Pow_bottom Pow_empty closure_from_clr_def closure_range.cl_fp closure_range.cl_is_iso closure_range.intro emptyE filters_is_clr insertE is_clr_imp2 is_filter_imp20 is_min_imp_has_min max_filter max_filter2 max_filter_min min_antitone2 singleton_insert_inj_eq' subset_singletonD ub_set_subset_space)
qed

lemma filter_cl0:
  assumes A0:"A \<subseteq> X"
  shows "A \<subseteq> filter_closure A X"
proof(cases "A = {}")
  case True
  then show ?thesis
    by simp
next
  case False
  then show ?thesis
  proof-
    have B0:"A \<subseteq> filter_closure A X"
      proof
        fix a assume A2:"a \<in> A"
        have B0:"{a} \<in> Fpow_ne A"
          using A2 Fpow_def by blast
        have B1:"Inf {a} X \<le> a"
          by (metis A0 A2 inf_singleton2 order_class.order_eq_iff subsetD)
        show "a \<in> filter_closure A X"
          by (meson A2 B0 B1 False assms filter_closure_mem_iff in_mono)
      qed
    show ?thesis
      by (simp add: B0)
  qed
qed


lemma filter_cl1:
  assumes A0:"A \<subseteq> X"
  shows "is_up_cl (filter_closure A X) X"
proof(cases "A = {}")
  case True
  then show ?thesis
    by (simp add: filter_closure_def is_filter_imp1 max_filter)
next
  case False
  let ?ClA="(filter_closure A X)"
  have B0:"(\<And>a b. (b \<in> X \<and> a \<le> b \<and> a \<in> ?ClA) \<longrightarrow> b \<in> ?ClA)"
  proof
    fix a b assume A2:"b \<in> X \<and> a \<le> b \<and> a \<in> ?ClA"
    show "b \<in> ?ClA"
      by (meson A2 False dual_order.trans filter_closure_mem_iff)
  qed
  then show ?thesis
    by (metis False filter_closure_mem_iff is_up_cl_if2 subsetI)
qed



lemma filter_cl2:
  assumes A0:"A \<subseteq> X"
  shows "is_dwdir (filter_closure A X)"
proof(cases "A = {}")
  case True
  then show ?thesis
    by (metis filter_closure_def is_filter_imp0 max_filter)
next
  case False
  then show ?thesis 
  proof-
    let ?ClA="(filter_closure A X)"
    have B0:"\<And>a b. a \<in> ?ClA \<and> b \<in> ?ClA \<longrightarrow> (\<exists>c \<in> ?ClA. c lb {a, b})"
    proof
      fix a b assume A2:"a \<in> ?ClA \<and> b \<in> ?ClA" 
      obtain Fa Fb where B1:"Fa \<in> Fpow_ne A \<and> Inf Fa X \<le> a  \<and> Fb \<in> Fpow_ne A \<and>  Inf Fb X \<le> b"
        by (meson A2 False filter_closure_obtains)
      let ?Fab="(Fa \<union> Fb)"
      have B2:"?Fab \<subseteq> A \<and> ?Fab \<subseteq> X"
        using A0 B1 fpow_ne_imp2 by auto
      have B3:"Inf ?Fab  X \<le> Inf Fa X \<and> Inf ?Fab X \<le> Inf Fb X"
        by (metis B1 B2 Diff_iff Pow_iff csinf inf_antitone1 is_inf_complete_def le_supE pow_ne_if sup_bot.eq_neutr_iff sup_ge1 sup_ge2)
      have B4:"Inf ?Fab X \<le> a \<and> Inf ?Fab X \<le> b"
        using B1 B3 dual_order.trans by blast
      have B5:"Inf ?Fab X \<le> Inf ?Fab X"
        by simp
      have B6:"?Fab \<in> Fpow_ne A"
        by (metis B1 B2 bot_eq_sup_iff finite_UnI fpow_ne_mem_iff)
      have B7:"Inf ?Fab X \<in> ?ClA "
        by (metis B2 B5 B6 Diff_iff False PowI csinf filter_closure_mem_iff inf_complete_imp1)
      have B8:"Inf ?Fab X \<in> ?ClA \<and>  Inf ?Fab X lb {a, b}"
        using B4 B7 lb_def by auto
      show "(\<exists>c \<in> ?ClA. c lb {a, b})"
        using B8 by auto
    qed
    show ?thesis
      by (metis B0 False assms bot.extremum_uniqueI filter_cl0 is_dwdir_def)
  qed
qed


lemma filter_cl_is_filter:
  assumes A0:"A \<subseteq> X"
  shows "is_filter (filter_closure A X) X"
  by (simp add: is_filter_def assms filter_cl1 filter_cl2 in_upsets_in_imp_subset up_sets_in_def)

lemma filter_cl_least:
  assumes A0:"A \<subseteq> X"  and A2:"is_filter F X" and A3:"A \<subseteq> F"
  shows "(filter_closure A X) \<subseteq> F"
proof(cases "A = {}")
  case True
  then show ?thesis
    by (metis A2 filter_closure_def max_filter_least)
next
  case False
  then show ?thesis
  proof-
    have B0:"(filter_closure A X) \<subseteq> F"
      proof
      fix x assume A4:"x \<in> (filter_closure A X)"
      obtain Fx where B0:"Fx  \<in> Fpow_ne A \<and> Inf Fx X \<le> x"
        using A4 False filter_closure_obtains by blast
      have B1:"Fx \<subseteq> F"
        using A3 B0 fpow_ne_imp2 by blast 
      have B2:"Inf Fx X \<in> F"
        by (metis A0 A2 B0 B1 DiffD2 DiffI PowI csinf filter_finf_closed fpow_ne_mem_iff inf_complete_imp2)
      have B3:"Inf Fx X \<le> x"
        by (simp add: B0)
      show "x \<in> F"
        by (meson A2 A4 B2 B3 False filter_closure_mem_iff is_filter_imp1 is_up_cl_imp2)
    qed
  show ?thesis
    by (simp add: B0)
  qed
qed

lemma filter_cl_is_ub:
  "A \<subseteq> X \<Longrightarrow> (filter_closure A X) \<in>  (ub_set {A} (filters X))"
  by (metis filter_cl0 filter_cl_is_filter filters_mem_iff is_filter_imp21 singletonD ub_set_elm)

lemma filter_cl_lt_ub:
  "A \<subseteq> X  \<Longrightarrow> F \<in>  (ub_set {A} (filters X)) \<Longrightarrow> (filter_closure A X) \<le> F"
  by (simp add: filter_cl_least filters_mem_iff ub_set_mem_iff)

lemma filter_cl_is_lub:
  "A \<subseteq> X \<Longrightarrow>  is_inf (filter_closure A X) (ub_set {A} (filters X)) (Pow X)"
  by (metis filter_cl_is_filter filter_cl_is_ub filter_cl_lt_ub is_filter_imp21 is_inf_if3)

lemma filter_closure_eq_closure:
  "A \<subseteq> X  \<Longrightarrow> filter_closure A X = (closure_from_clr (filters X)) A "
  by (simp add: filter_cl_is_ub filter_cl_lt_ub closure_from_clr_def csinf is_min_iff is_ne min_if toped)


end
end