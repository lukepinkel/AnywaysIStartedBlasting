theory PosetsR3
  imports Main "./FiltersAgain3" "./Posets" "./GaloisConnectionsAgain"
begin

locale filter_of_sets = 
  fixes EF::"'X set set set"
  assumes "\<forall>F \<in> EF. is_filter F"
begin

definition Inf::"'X set set set \<Rightarrow> 'X set set"
  where "Inf ES = (\<Inter>ES)"

definition Sup::"'X set set set \<Rightarrow> 'X set set"
  where "Sup ES = (fgenby ES)"

definition inf::"'X set set \<Rightarrow> 'X set set \<Rightarrow> 'X set set" where
  "inf F1 F2 = Inf {F1, F2}"

definition sup::"'X set set \<Rightarrow> 'X set set \<Rightarrow> 'X set set" where
  "sup F1 F2 = Sup {F1, F2}"

definition top::"'X set set" where
  "top = Pow UNIV"

definition bot::"'X set set" where
  "bot = {UNIV}"

lemma sup_gt:
  assumes "\<forall>F \<in> ES. is_filter F"
  shows "\<forall>F \<in> ES. F \<subseteq> (fgenby ES)"
  by (metis Sup_le_iff filter_generated_by_def order_trans pfmc_extensive upc_extensive)

lemma inf_eq:
  "inf F1 F2 = F1 \<inter> F2"
  by (simp add: Inf_def inf_def)

lemma fgen_extensive:
  "\<forall>ES. \<forall>F \<in> ES. F \<subseteq> fgenby ES"
  by (metis Sup_le_iff filter_generated_by_def order_trans pfmc_extensive upc_extensive)

lemma fgen_sup:
  fixes ES
  assumes A0:"is_filter G" and A1:"\<forall>F \<in> ES. is_filter F" and A2:"(\<forall>F \<in> ES. F \<subseteq> G)"
  shows "(fgenby ES) \<subseteq> G"
proof
  fix a assume LtR_A0:"a \<in> (fgenby ES)"
  obtain b where LtR_A1:"b \<in> (pfmc (\<Union>ES)) \<and> a \<supseteq> b "
    by (metis LtR_A0 filter_generated_by_def in_upclosure_imp)
  obtain F where LtR_A2:"(F \<in> Pow((\<Union>ES))) \<and> (finite F) \<and> b=(\<Inter>F)"
  show "a \<in> G"

end

sublocale filter_of_sets \<subseteq> complete_lattice filter_of_sets.Inf
                                             filter_of_sets.Sup
                                             filter_of_sets.inf
                                             "(\<subseteq>)" "(\<subset>)"
                                             filter_of_sets.sup
                                             filter_of_sets.bot
                                             filter_of_sets.top
proof unfold_locales
fix x::"'a set set" fix y::"'a set set"
show "filter_of_sets.inf x y \<subseteq> x"
  by (metis Inter_lower equals0D filter_of_sets.Inf_def filter_of_sets.inf_def filter_of_sets.intro insertI1)
show "filter_of_sets.inf x y \<subseteq> y"
  by (metis Inter_lower empty_iff filter_of_sets.Inf_def filter_of_sets.inf_def filter_of_sets.intro insert_iff)
show "x \<subseteq> filter_of_sets.sup x y"
  by (metis Sup_insert Un_subset_iff empty_iff filter_generated_by_def filter_of_sets.Sup_def filter_of_sets.intro filter_of_sets.sup_def pfmc_extensive sup.orderE upc_extensive)
show "y \<subseteq> filter_of_sets.sup x y"
  by (metis (no_types, opaque_lifting) Sup_insert Un_subset_iff empty_iff filter_generated_by_def filter_of_sets.Sup_def filter_of_sets.intro filter_of_sets.sup_def pfmc_extensive sup.orderE upc_extensive)
fix z::"'a set set"
show "x \<subseteq> y \<Longrightarrow> x \<subseteq> z \<Longrightarrow> x \<subseteq> filter_of_sets.inf y z"
  by (metis Int_subset_iff empty_iff filter_of_sets.inf_eq filter_of_sets.intro)
show "y \<subseteq> x \<Longrightarrow> z \<subseteq> x \<Longrightarrow> filter_of_sets.sup y z \<subseteq> x"

end
end