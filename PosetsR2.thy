theory PosetsR2
  imports Main
begin
declare [[show_types]]

definition is_preorder::"'X set \<Rightarrow> 'X rel \<Rightarrow> bool" where
  "is_preorder A R \<equiv> (refl_on A R) \<and> (trans_on A R)"

definition is_partialorder::"'X set \<Rightarrow> 'X rel \<Rightarrow> bool" where
  "is_partialorder A R \<equiv> (is_preorder A R) \<and> (antisym_on A R)"

definition is_ub::"'X \<Rightarrow> 'X set \<Rightarrow> 'X rel \<Rightarrow> bool" where
  "is_ub u A R \<equiv>  (\<forall>a \<in> A. (a, u) \<in> R) "

definition is_lb::"'X \<Rightarrow> 'X set \<Rightarrow> 'X rel  \<Rightarrow> bool" where
  "is_lb l A R \<equiv> (\<forall>a \<in> A. (l, a) \<in> R) "

definition is_max::"'X \<Rightarrow> 'X set \<Rightarrow> 'X rel \<Rightarrow> bool" where
  "is_max m A R \<equiv> is_ub m A R \<and> (m \<in> A)"

definition is_min::"'X \<Rightarrow> 'X set \<Rightarrow> 'X rel \<Rightarrow> bool" where
  "is_min m A R \<equiv> is_lb m A R \<and> (m \<in> A)"

definition max::"'X set \<Rightarrow> 'X rel \<Rightarrow> 'X" where
  "max A R \<equiv> (THE m. is_max m A R)"

definition min::"'X set \<Rightarrow> 'X rel \<Rightarrow> 'X" where
  "min A R \<equiv> (THE m. is_min m A R)"

definition upper_bounds::"'X set \<Rightarrow> 'X rel \<Rightarrow> 'X set" where
  "upper_bounds A R \<equiv> \<Inter>a \<in> A. R``{a}"

definition lower_bounds::"'X set \<Rightarrow> 'X rel \<Rightarrow> 'X set" where
  "lower_bounds A R \<equiv> \<Inter>a \<in> A. converse(R)``{a}"


definition is_lub::"'X \<Rightarrow> 'X set \<Rightarrow> 'X rel  \<Rightarrow> bool" where
  "is_lub s A R \<equiv> is_min s (upper_bounds A R) R"

definition is_glb::"'X \<Rightarrow> 'X set \<Rightarrow> 'X rel \<Rightarrow>bool" where
  "is_glb i A R \<equiv> is_max i (lower_bounds A R) R"


definition lub::"'X set \<Rightarrow> 'X rel \<Rightarrow> 'X" where
  "lub A R \<equiv> min(upper_bounds A R) R"

definition glb::"'X set \<Rightarrow> 'X rel \<Rightarrow> 'X" where
  "glb A R \<equiv> max(lower_bounds A R) R"


lemma ub_iff_in_upper_bounds:
  "\<forall>u. (u \<in> upper_bounds A R) \<longleftrightarrow> (is_ub u A R)"
proof-
  have LR:"\<And>u. (u \<in> upper_bounds A R) \<longrightarrow> (is_ub u A R)"
  proof
    fix u assume A0:"u \<in> upper_bounds A R" 
    have B0:"u \<in> (\<Inter>a \<in> A. R``{a})"
      by (metis A0 upper_bounds_def)
    have B1:"\<forall>a \<in> A. (a, u) \<in> R"
      using B0 by blast
    show "is_ub u A R"
      by (simp add: B1 is_ub_def)
  qed
  have RL:"\<And>u. (is_ub u A R) \<longrightarrow>  (u \<in> upper_bounds A R)"
  proof
    fix u assume A1:"is_ub u A R"
    have B2:"\<forall>a \<in> A. (a, u) \<in> R"
      using A1 is_ub_def by fastforce
    have B3:"u \<in> (\<Inter>a \<in> A. R``{a})"
      using B2 by blast
    show "u \<in> upper_bounds A R"
      by (simp add: B2 upper_bounds_def)
  qed
  show ?thesis
    using LR RL by blast
qed

lemma ub_is_dual_lb:
  "(is_ub u A R) \<longleftrightarrow> (is_lb u A (converse(R)))"
  by (simp add: is_lb_def is_ub_def)

lemma lb_is_dual_ub:
  "(is_lb u A R) \<longleftrightarrow> (is_ub u A (converse(R)))"
  by (simp add: is_lb_def is_ub_def)


lemma lb_iff_in_lower_bounds:
  "\<forall>l. (l \<in> lower_bounds A R) \<longleftrightarrow> (is_lb l A R)"
  by (simp add: is_ub_def lb_is_dual_ub lower_bounds_def)



end
