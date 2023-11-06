theory SystemsOfSets
  imports Main "./Posets"
begin

section Definitions

subsection PropertiesOfSystems

definition UpClosed::"'X set set \<Rightarrow> bool" where
  "UpClosed \<A>  \<equiv> (\<forall>B. (\<exists>A \<in>\<A>. B \<supseteq> A) \<longrightarrow> B \<in> \<A> )"

definition UpClosed_In::"'X set set \<Rightarrow> 'X set \<Rightarrow> bool" where
  "UpClosed_In \<A> X  \<equiv> (\<forall>B \<in> Pow X. (\<exists>A \<in>\<A>. B \<supseteq> A) \<longrightarrow> B \<in> \<A> )"


definition is_upclosed_by_inclusion::"'X set set \<Rightarrow> 'X set \<Rightarrow> bool" where
  "is_upclosed_by_inclusion \<A> X  \<equiv> is_up_closed \<A> (Pow X)"

definition Centered::"'X set set \<Rightarrow> bool" where
  "Centered \<A> \<equiv> (\<forall>A \<in> \<A>. \<forall>B \<in> \<A>. (A \<inter> B \<noteq> {}))"

definition FIP::"'X set set \<Rightarrow> bool" where
  "FIP \<A> \<equiv> (\<forall>B  \<in> (Pow  \<A>). finite B \<longrightarrow> (\<Inter>B \<noteq> {}))"


definition DownDirected::"'X set set \<Rightarrow> bool" where
  "DownDirected \<A> \<equiv> (\<forall>A \<in> \<A>. \<forall>B \<in> \<A>. (\<exists>C \<in>\<A>. A \<inter> B \<supseteq> C))"

definition PiSystem::"'X set set \<Rightarrow> bool" where
  "PiSystem \<A> \<equiv> (\<forall>A \<in> \<A>. \<forall>B \<in> \<A>. A \<inter> B \<in>\<A> )"

definition Proper::"'X set set \<Rightarrow> bool" where
  "Proper \<A> \<equiv> {} \<notin> \<A>"

definition ProperNE::"'X set set \<Rightarrow> bool" where
  "ProperNE A \<equiv> (Proper A) \<and> (A \<noteq> {})"



subsection TypesOfSystems

definition FilterSubbase::"'X set set \<Rightarrow> bool" where
  "FilterSubbase \<A> \<equiv> (\<A> \<noteq> {}) \<and> (Proper \<A>) \<and> (FIP \<A>) "

definition FilterBase::"'X set set \<Rightarrow> bool" where
  "FilterBase \<A> \<equiv> (\<A> \<noteq> {}) \<and> (Proper \<A>) \<and> (DownDirected \<A>) "

definition FilterOfSets::"'X set set \<Rightarrow> bool" where
  "FilterOfSets \<A> \<equiv> (\<A> \<noteq> {}) \<and> (Proper \<A>) \<and> (PiSystem \<A>) \<and> (UpClosed \<A>) "


definition FilterSubbaseIn::"'X set set \<Rightarrow> 'X set \<Rightarrow> bool" where
  "FilterSubbaseIn \<A> X  \<equiv> (\<A> \<noteq> {}) \<and> (Proper \<A>) \<and> (FIP \<A>) "

definition FilterBaseIn::"'X set set \<Rightarrow> 'X set \<Rightarrow> bool" where
  "FilterBaseIn \<A> X \<equiv> (\<A> \<noteq> {}) \<and> (Proper \<A>) \<and> (DownDirected \<A>) "

definition FilterOfSetsIn::"'X set set\<Rightarrow> 'X set \<Rightarrow> bool" where
  "FilterOfSetsIn \<A> X \<equiv> (\<A> \<noteq> {}) \<and> (Proper \<A>) \<and> (PiSystem \<A>) \<and> (UpClosed_In \<A> X) "

definition \<FF>::"'X set \<Rightarrow> 'X set set set" where
  "\<FF> X = {\<F> \<in> Pow (Pow X). FilterOfSetsIn \<F> X} "


subsection RelationsAndOperations

definition preceq:: "'X set set \<Rightarrow> 'X set set \<Rightarrow> bool" (infix "\<preceq>" 50) where
  "\<A> \<preceq> \<B>  \<longleftrightarrow> (\<forall>A\<in>\<A>. (\<exists>B\<in>\<B>. (A \<supseteq> B)))"

definition fequiv:: "'X set set \<Rightarrow> 'X set set \<Rightarrow> bool" (infix "~" 50) where
  "\<A> ~ \<B>  \<longleftrightarrow> ((\<A> \<preceq> \<B>) \<and> ( \<B> \<preceq>  \<A>))"

definition upclosure:: "'X set set \<Rightarrow> 'X set set" where
  "upclosure \<A>  = {E. (\<exists>A \<in>\<A>.( A \<subseteq> E)) }"

definition upclosure_in:: "'X set set \<Rightarrow> 'X set \<Rightarrow> 'X set set" where
  "upclosure_in \<A> X  = {E \<in> Pow X. (\<exists>A \<in>\<A>. ( A \<subseteq> E)) }"

definition fmeetclosure:: "'X set set \<Rightarrow> 'X set set" where
  "fmeetclosure \<A> = {A. (\<exists>\<B>\<in>(Pow \<A>). (finite \<B>) \<and> ( A=\<Inter>\<B>) \<and> (\<B> \<noteq> {}))}"

definition fmeetclosure_in:: "'X set set \<Rightarrow> 'X set \<Rightarrow> 'X set set" where
  "fmeetclosure_in \<A> X = {A \<in> Pow X. (\<exists>\<B>\<in>(Pow \<A>). (finite \<B>) \<and> ( A=\<Inter>\<B>) \<and> (\<B> \<noteq> {}))}"

definition fmeet_in::"'X set set \<Rightarrow> 'X set \<Rightarrow> 'X set \<Rightarrow> bool" where
  "fmeet_in \<A> X A \<equiv> ((A \<in> Pow X) \<and> (\<exists>\<B>\<in>(Pow \<A>).  (finite \<B>) \<and> ( A=\<Inter>\<B>) \<and> (\<B> \<noteq> {})))"

(*finite_inter_of_idemp*)
definition FilUpSets::"'X set set \<Rightarrow>  'X set \<Rightarrow> 'X set set set" where
  "FilUpSets A X = {F \<in> Pow (Pow X). (FilterOfSetsIn F X) \<and> (A \<preceq> F)}"

definition meshes:: "'X set set \<Rightarrow> 'X set set \<Rightarrow> bool" where
  "meshes \<A> \<B> \<equiv> \<forall>A \<in> \<A>. \<forall>B \<in>\<B>. (A \<inter> B \<noteq> {})"

definition grill_of::"'X set set \<Rightarrow> 'X set  \<Rightarrow> 'X set set" where
  "grill_of \<A> X =  {E \<in> Pow X. meshes {E} \<A> } "

definition filter_generated_by:: "'X set set \<Rightarrow> 'X set set" where
  "filter_generated_by \<C> =  upclosure (fmeetclosure \<C>) "

definition filter_generated_by_in:: "'X set set\<Rightarrow> 'X set  \<Rightarrow> 'X set set" where
  "filter_generated_by_in \<C> X =  upclosure_in (fmeetclosure_in \<C> X) X "

subsection SyntaxForFC

definition is_f_many::"'X set \<Rightarrow>'X set \<Rightarrow> bool" where
  "is_f_many \<B> \<A> \<equiv>  (\<B> \<subseteq> \<A>) \<and> (finite \<B>) \<and> (\<B> \<noteq> {}) "

definition f_many::"'X set \<Rightarrow> 'X set set" where
  "f_many \<A> = {\<B>. is_f_many \<B> \<A> }"


section Lemmas

subsection PropertiesOfRelations

(*1.70.1*)
lemma preceq_transitive:
   "\<forall>\<A> \<B> \<C>. (\<A> \<preceq> \<B> \<and>  \<B> \<preceq> \<C>) \<longrightarrow> (\<A> \<preceq> \<C>)"
  by (meson dual_order.trans preceq_def)

lemma preceq_reflexive:
  "\<forall>\<A>. \<A> \<preceq> \<A>"
  using preceq_def by auto

(*1.70.2*)
lemma subseteq_imp_preceq:
  " \<forall>\<A> \<B>. \<A> \<subseteq> \<B>\<longrightarrow>\<A> \<preceq> \<B>"
  by (meson dual_order.refl in_mono preceq_def)

lemma preceq_trns2:
  "\<forall>\<A> \<B> \<C>. \<A> \<subseteq> \<B> \<and> \<B> \<preceq> \<C> \<longrightarrow> \<A> \<preceq> \<C>  "
  using preceq_transitive subseteq_imp_preceq by blast

(*1.70.3*)
lemma upclosed_then_preceq_imp_subseteq:
  assumes A0: "(Proper \<A>) \<and> (\<A> \<noteq> {})" and
          A1: "(Proper \<B>) \<and> (\<B> \<noteq> {})" and
          A2: "UpClosed \<B>" and
          A3: "\<A> \<preceq> \<B>" 
  shows "\<A> \<subseteq> \<B>"
proof-
  have B0:"\<forall>A. (\<exists>B \<in> \<B>. B \<subseteq> A) \<longrightarrow> A \<in> \<B>"
    using A2 UpClosed_def by blast
  have B1:"\<forall>A \<in> \<A>. (\<exists>B \<in> \<B>. B \<subseteq> A)"
    using A3 preceq_def by blast
  with B0 B1 show ?thesis
    by (meson subsetI)
qed


(*1.70.4*)
lemma upclosed_equiv_then_equal:
  assumes A0:"UpClosed  \<A> \<and> UpClosed \<B> " and
          A1:"\<A> ~ \<B>"
 shows  "\<A>=\<B>"
  by (meson A0 A1 UpClosed_def fequiv_def preceq_def subsetI subset_antisym)

lemma upclosed_then_upclosed_in:
  "\<forall>X. \<forall>\<A>. UpClosed \<A> \<longrightarrow> UpClosed_In \<A> X"
  by (simp add: UpClosed_In_def UpClosed_def)

lemma upclosed_in_equiv_then_equal:
  assumes A0: "\<A> \<in> Pow (Pow X) \<and> \<B> \<in> Pow (Pow X)" and
          A1:"UpClosed_In \<A> X  \<and> UpClosed_In \<B> X " and
          A2:"\<A> ~ \<B>"
 shows  "\<A>=\<B>"
proof-
  have B0:"\<forall>A \<in> \<A>. \<exists>B \<in> \<B>. A \<supseteq> B"
    by (meson A2 fequiv_def preceq_def)
  have B1:"\<forall>A \<in> \<A>. \<exists>B \<in> \<B>. A \<supseteq> B \<longrightarrow> A \<in> \<B>"
    by (metis A0 A1 B0 UnionI Union_Pow_eq UpClosed_In_def)
  have B2:"\<forall>B \<in> \<B>. \<exists>A \<in> \<A>. A \<subseteq>  B"
    by (meson A2 fequiv_def preceq_def)
  have B3:"\<forall>B \<in> \<B>. \<exists>A \<in> \<A>. A \<subseteq>  B \<longrightarrow> B \<in> \<A>"
    by (meson A0 A1 B2 PowD UpClosed_In_def in_mono)
  have B4:"\<B> \<subseteq> \<A>  \<and> \<A> \<subseteq> \<B>"
    by (meson A0 A1 B0 B2 PowD UpClosed_In_def in_mono subsetI)
  have B5:"\<A> =\<B>"  by (simp add: B4 subset_antisym)
  with B5 show ?thesis by simp
qed

lemma upclosure_is_upclosed1:
  assumes "\<A>=upclosure \<B>"
  shows "UpClosed \<A>"
  by (smt (verit, ccfv_SIG) CollectD CollectI UpClosed_def assms dual_order.trans upclosure_def)

(*1.70.5*)
lemma upclosure_in_is_upclosed_in1:
  assumes "\<A>=upclosure_in \<B> X"
  shows "UpClosed_In \<A> X"
  by (smt (verit, ccfv_SIG) CollectD CollectI UpClosed_In_def assms subset_eq upclosure_in_def)

(*1.70.5*)
lemma upclosure_is_upclosed2:
  assumes "\<A>=upclosure \<B>"
  shows "\<A> ~ \<B>"
  by (smt (verit, ccfv_threshold) assms dual_order.refl fequiv_def mem_Collect_eq preceq_def upclosure_def)

(*1.70.7*)
lemma upclosure_in_is_upclosed_in2:
  assumes A0: "\<B> \<in> Pow (Pow X)" and
          A1: "ProperNE \<B>" and
          A2:"\<A>=(upclosure_in \<B> X)"
  shows "\<A> ~ \<B>"
proof-
  have B0: "\<forall>A \<in> \<A>. \<exists>B \<in> \<B>. A \<supseteq> B"
    by (simp add: A2 upclosure_in_def)
  have B1:"\<A> \<preceq> \<B>"
    by (simp add: B0 preceq_def)
  have B2:"(\<forall>B \<in> \<B>. B \<in>\<A>) \<longrightarrow> (\<forall>B \<in> \<B>. (\<exists>A \<in> \<A>. A \<supseteq> B))"
    by auto
  have B3:"(\<forall>B \<in> \<B>. (\<exists>A \<in> \<A>. A \<supseteq> B)) "
    by (metis (no_types, lifting) A0 A2 UnionI Union_Pow_eq dual_order.refl mem_Collect_eq upclosure_in_def)
  have B4:"\<B> \<preceq> \<A>"
    by (metis (no_types, lifting) A0 A2 PowD in_mono mem_Collect_eq subsetI subseteq_imp_preceq upclosure_in_def)
  have B5:"\<A> ~ \<B>"
    by (simp add: B1 B4 fequiv_def)
  with B5 show ?thesis
    by simp
qed

lemma upclosure_preserves_properness:
  assumes A0:"Proper \<A>"
  shows "Proper( upclosure \<A>)"
  by (smt (verit, best) Proper_def assms mem_Collect_eq subset_empty upclosure_def)


lemma fequiv_iff_upclosure_equal:
  "\<A> ~ \<B> \<longleftrightarrow> (upclosure \<A>) = (upclosure \<B>) "
  by (smt (verit) fequiv_def preceq_transitive upclosed_equiv_then_equal upclosure_is_upclosed1 upclosure_is_upclosed2)



lemma lem_meshing1:
  "\<forall>\<A>. \<forall>\<B>. meshes \<A> \<B> \<longleftrightarrow> {} \<notin> {E. ( \<exists>A \<in>\<A>. \<exists>B \<in>\<B>. E=(A \<inter> B))}"
  using meshes_def by fastforce


lemma lem_meshing2:
 "\<forall>A \<F>.  (meshes {A} \<F>) \<longleftrightarrow> (\<forall>F \<in> \<F>. ((A \<inter> F) \<noteq> {}))"
  by (simp add: meshes_def)

lemma lem_meshing3:
  "\<forall>\<F> B A. ((meshes {A} \<F>) \<and> (A \<subseteq> B) \<longrightarrow> (meshes {B} \<F>))"
proof-
  have B0:"\<forall>\<F> B A. ((meshes {A} \<F>) \<and> (A \<subseteq> B))  \<longleftrightarrow> ((\<forall>F \<in> \<F>. F \<inter> A \<noteq> {}) \<and> (A \<subseteq> B))"
    by (simp add: inf_commute lem_meshing2)
  have B1: "\<forall>F B A. ( F \<inter> A \<noteq> {}) \<and> (A \<subseteq> B) \<longrightarrow> (F \<inter> B \<noteq> {})"
    by auto
  have B2: "\<forall>\<F> B A. ((\<forall>F \<in> \<F>. F \<inter> A \<noteq> {}) \<and> (A \<subseteq> B)) \<longrightarrow>  ((\<forall>F \<in> \<F>. F \<inter> B \<noteq> {})) "
    by (meson B1)
  have B3: "\<forall>\<F> B A. (meshes {A} \<F>) \<and> (A \<subseteq> B) \<longrightarrow> meshes {B} \<F> "
    by (metis B1 Int_commute lem_meshing2)
  with B3 show ?thesis
    by blast
qed


lemma lem_meshing3p2:
  assumes A0: "\<F> \<in> Pow( Pow X) \<and> A \<in> (Pow X)" and
          A1: "FilterOfSets \<F> "
  shows "\<not>(A \<in> \<F> \<and> meshes {X-A} \<F>) "
  by (metis Diff_disjoint Int_commute lem_meshing2)


lemma lem_meshing4:
  assumes A0: "\<F> \<in> Pow( Pow X) \<and> \<G> \<in> Pow (Pow X)" and
          A1: "\<F> \<preceq> \<G> " and
          A2: "FilterOfSets \<F>  \<and> FilterOfSets \<G>"
  shows "meshes \<F> \<G> "
proof-
  have B0: "\<forall>F \<in> \<F>. \<exists> G \<in>\<G>. (F \<supseteq> G)" using A1 preceq_def by auto
  have B1: "\<forall>F \<in> \<F>. \<forall>G \<in>\<G>. F \<inter> G \<noteq> {}"
    by (metis A2 B0 FilterOfSets_def PiSystem_def Proper_def UpClosed_def)
  have B2: "meshes \<F> \<G>"
    by (simp add: B1 meshes_def)
  with B2 show ?thesis by simp
qed

lemma lem_meshing5:
  fixes X::"'X set"
  assumes A0: "UpClosed_In  \<A> X" and
          A1: "\<Union>\<A> \<subseteq> X" and
          A2: "E \<subseteq> X"
  shows "(meshes {X-E} \<A>) \<longrightarrow> (E \<notin> \<A>)"
  by (metis Diff_disjoint Int_commute lem_meshing2)

subsection PropertiesOfTypes

(*1.70.8*)
lemma equiv_fbase_imp_fbase:
  assumes A0:"FilterBase \<B> "and
        A1: "\<A> ~\<B> "
  shows "FilterBase \<A>"
proof-
  have B0: "\<forall>A \<in> \<A>. (\<exists>B \<in> \<B>. B \<subseteq> A)"
    by (meson A1 fequiv_def preceq_def)
  have B1: "\<forall>B \<in> \<B>. B \<noteq> {} "
    using A0 FilterBase_def Proper_def by auto
  have B2: "\<forall>A \<in> \<A>.  A \<noteq> {}"
    using B0 B1 by blast
  have B3:"\<forall>A1 \<in> \<A>. \<forall> A2 \<in> \<A>.( \<exists>B1 \<in> \<B>. B1 \<subseteq> A1)\<and>( \<exists>B2 \<in> \<B>. B2 \<subseteq> A2)"
    by (simp add: B0)
  have B4:"\<forall>A1 \<in> \<A>. \<forall> A2 \<in> \<A>.( \<exists>B1 \<in> \<B>. B1 \<subseteq> A1)\<and>( \<exists>B2 \<in> \<B>. B2 \<subseteq> A2)"
    by (simp add: B0)
 have B5:"\<forall>A1 \<in> \<A>. \<forall> A2 \<in> \<A>. (\<exists>B1 \<in> \<B>. (\<exists>B2 \<in> \<B>. ( (B1 \<inter> B2)\<subseteq> (A1 \<inter> A2))))"
   by (meson B4 Int_mono)
  have B6: "\<forall>A1 \<in> \<A>. \<forall> A2 \<in> \<A>. (\<exists>B1 \<in> \<B>. (\<exists>B2 \<in> \<B>.(\<exists>B3 \<in> \<B>. (B3 \<subseteq> (B1 \<inter> B2)) \<and> ((B1 \<inter> B2)\<subseteq> (A1 \<inter> A2))) ))"
    by (metis A0 B5 DownDirected_def FilterBase_def)
  have B7: "\<forall>A1 \<in> \<A>. \<forall> A2 \<in> \<A>. (\<exists>B1 \<in> \<B>. (\<exists>B2 \<in> \<B>.(\<exists>B3 \<in> \<B>. \<exists>A3 \<in> \<A>. ((A3 \<subseteq> B3) \<and> (B3 \<subseteq> (B1 \<inter> B2))) \<and> ((B1 \<inter> B2)\<subseteq> (A1 \<inter> A2))) ))"
    by (smt (verit) A1 B6 fequiv_def preceq_def)
  have B8: "\<forall>A1 \<in> \<A>. \<forall> A2 \<in> \<A>. \<exists>A3 \<in> \<A>. A3 \<subseteq> A1 \<inter> A2"
    by (metis B7 subset_trans)
  have B9:"DownDirected \<A>"
    using B8 DownDirected_def by blast
  have B10:"Proper \<A>"
    using B2 Proper_def by blast
  have B11:"\<A> \<noteq> {}"
    by (metis A0 A1 FilterBase_def UpClosed_def empty_iff fequiv_def preceq_def upclosed_equiv_then_equal)
  with B9 B10 B11 show ?thesis
    by (simp add: FilterBase_def)
qed

(*1.70.9*)
lemma fbase_gen_filter:
  assumes A0: "FilterBase A"
  shows "FilterOfSets (upclosure A)"
proof-
  let ?F="upclosure A"
  have B0: "f \<in> ?F \<longleftrightarrow> (\<exists>a \<in> A. a \<subseteq> f)"
    by (simp add: upclosure_def)
  have B1:"Proper A"
    using FilterBase_def assms by blast
  from B0 B1 have  B2:"{} \<notin> ?F"
    by (metis FilterBase_def Proper_def assms equiv_fbase_imp_fbase upclosure_is_upclosed2)
  have B3:"Proper ?F"
    by (simp add: B2 Proper_def)
  have B4: "\<forall>F1 \<in> ?F. \<forall>F2 \<in> ?F. \<exists>B1\<in>A. \<exists>B2\<in> A. \<exists>B3 \<in> A. (B1 \<subseteq>F1) \<and> (B2 \<subseteq> F2) \<and> (B3 \<subseteq> (B1 \<inter> B2))"
    by (smt (verit, ccfv_threshold) CollectD DownDirected_def FilterBase_def assms upclosure_def)
  have B5: "\<forall>F1 \<in> ?F. \<forall>F2 \<in> ?F. \<exists>B3 \<in> A. (B3 \<subseteq> (F1 \<inter> F2)) "
    by (metis B4 DownDirected_def FilterBase_def UpClosed_def assms equiv_fbase_imp_fbase upclosure_is_upclosed1 upclosure_is_upclosed2)
  have B6: "\<forall>F1 \<in> ?F. \<forall>F2 \<in> ?F. ((F1 \<inter> F2) \<in> ?F)"
    by (metis (mono_tags, lifting) B5 mem_Collect_eq upclosure_def)
  have B7: "PiSystem ?F"
    using B6 PiSystem_def by blast
  have B8: "UpClosed ?F"
    by (simp add: upclosure_is_upclosed1)
  from B3 B7 B8 have B9: "FilterOfSets ?F"
    by (metis FilterBase_def FilterOfSets_def assms equiv_fbase_imp_fbase upclosure_is_upclosed2)
  with B9 show ?thesis by simp
qed

(*1.70.10*)
lemma upclosure_iff:
  assumes A0:"X \<noteq> {}" and A1:"A \<in> Pow (Pow X)"
  shows "\<forall>f \<in> Pow X. ((f \<in> (upclosure_in A X) \<longleftrightarrow> (\<exists>a \<in> A. a \<subseteq> f)))"
proof-
  let ?L="\<lambda>f. f \<in> (upclosure_in A X)" and ?R="\<lambda>f. (\<exists>a \<in> A. a \<subseteq> f)"
  have LR:"\<forall>f \<in> Pow X. (?L f \<longrightarrow>?R f)"
    by (simp add: upclosure_in_def)
  have RL:"\<forall>f \<in> Pow X. (?R f \<longrightarrow>?L f)"
    by (simp add: upclosure_in_def)
  with LR RL show ?thesis by blast
qed

(*1.70.9*)
lemma fbase_gen_filterb:
  assumes A0: "FilterBaseIn A X" and A1:"X \<noteq> {}" and A2:"A \<in> Pow(Pow X)"
  shows "FilterOfSetsIn (upclosure_in A X) X"
proof-
  let ?F="upclosure_in A X"
  have B0: "\<forall>f \<in> Pow X. (f \<in> ?F \<longleftrightarrow> (\<exists>a \<in> A. a \<subseteq> f))"
    by (simp add: upclosure_in_def)
  have B1:"Proper A"
    using A0 FilterBaseIn_def by blast
  from B0 B1 have  B2:"{} \<notin> ?F"
    by (simp add: Proper_def)
  have B3:"Proper ?F"
    by (simp add: B2 Proper_def)
  have B4: "\<forall>F1 \<in> ?F. \<forall>F2 \<in> ?F. \<exists>B1\<in>A. \<exists>B2\<in> A. \<exists>B3 \<in> A. (B1 \<subseteq>F1) \<and> (B2 \<subseteq> F2) \<and> (B3 \<subseteq> (B1 \<inter> B2))"
    by (smt (verit, best) A0 CollectD DownDirected_def FilterBaseIn_def upclosure_in_def)
  have B5: "\<forall>F1 \<in> ?F. \<forall>F2 \<in> ?F. \<exists>B3 \<in> A. (B3 \<subseteq> (F1 \<inter> F2)) "
    by (smt (verit, ccfv_SIG) B4 inf.absorb_iff2 inf.cobounded2 inf_assoc)
  have B6: "\<forall>F1 \<in> ?F. \<forall>F2 \<in> ?F. ((F1 \<inter> F2) \<in> ?F)"
    by (metis (mono_tags, lifting) B5 Pow_iff inf.absorb_iff2 inf_assoc mem_Collect_eq upclosure_in_def)
  have B7: "PiSystem ?F"
    using B6 PiSystem_def by blast
  have B8: "UpClosed_In ?F X"
    by (simp add: upclosure_in_is_upclosed_in1)
  from B3 B7 B8 have B9: "FilterOfSetsIn ?F X"
    by (metis (no_types, lifting) A0 A2 B0 FilterBaseIn_def FilterOfSetsIn_def Pow_iff bot.extremum_uniqueI in_mono subsetI)
  with B9 show ?thesis by simp
qed
(*1.70.10*)
lemma fbase_condition:
  assumes A0: "(Proper B)" and
          A1: "FilterOfSets F"
  shows "(F=upclosure B) \<longleftrightarrow> (F \<preceq> B) \<and> (B \<subseteq> F)"
  by (metis A0 A1 FilterOfSets_def UpClosed_def empty_iff fequiv_def fequiv_iff_upclosure_equal subseteq_imp_preceq upclosed_equiv_then_equal upclosed_then_preceq_imp_subseteq upclosure_is_upclosed1 upclosure_is_upclosed2)

(*1.70.11*)
lemma upprop_fip:
  assumes A0:"Centered B" and
          A1: "A \<preceq> B"
  shows"Centered A"
  by (metis (no_types, lifting) A0 A1 Centered_def inf_mono preceq_def subset_empty)




lemma union_inter_c:
  "\<Inter>(\<A> \<union> \<B>) = (\<Inter>\<A>)\<inter>(\<Inter>\<B> )"
  by blast

lemma union_inter_c2:
  assumes  "I \<noteq> {}" and
           "B \<in> Pow X" and
           "\<forall>i \<in> I. A(i) \<in> Pow X" and
           "X \<noteq> {}"
  shows "B \<inter> (\<Union>i \<in> I. A(i)) = (\<Union>i \<in> I. (B \<inter> A(i)))"
  by simp

lemma union_inter_c3:
  assumes "\<forall>j \<in> J. I(j) \<noteq> {}" and "J \<noteq> {}" and
          "\<forall>j \<in> J. \<forall>i \<in> I(j). A(i) \<in> Pow X" and "X \<noteq> {}"
  shows "(\<Union>i\<in>(\<Union>j \<in> J. I(j)). A(i)) =(\<Union>j\<in>J. (\<Union>i\<in>I(j). A(i)))"
  by blast


lemma union_inter_c4:
  assumes "I \<noteq> {}" and "finite I" and "\<forall>i \<in> I. (A i) \<in> Pow X" and 
          "\<forall>i \<in> I. (finite (A i))"
  shows "finite (\<Union>i\<in>I. A (i))"
  using assms(2) assms(4) by blast

lemma sup_subbase0:
  assumes A0:"FilterSubbase \<C>"
  shows "Proper (fmeetclosure \<C>)"
  by (smt (verit, ccfv_threshold) FIP_def FilterSubbase_def Proper_def assms fmeetclosure_def mem_Collect_eq)

lemma misc1:
  assumes A0:"A \<noteq> {} \<and> B \<noteq> {}" and
          A1:"{} \<notin> A \<and> {} \<notin> B" and
          A2: "\<forall>a \<in> A. (\<exists> b \<in> B. b \<subseteq>  a)"
  shows "(\<Inter>B)\<subseteq> (\<Inter>A)"
  by (simp add: A2 Inf_mono)



lemma upprop_fip2:
  assumes A0:"FIP \<B>" and
          A1: "\<A> \<preceq> \<B>"
   shows"FIP \<A>"
proof-
  have B0: "\<forall>\<E> \<in> Pow \<A>. (\<forall>E \<in> \<E>. (\<exists>F \<in>\<B>. F \<subseteq> E)) "
    by (metis A1 Pow_iff preceq_def preceq_trns2)
  let ?f="\<lambda>E. (SOME F. ((F \<subseteq> E) \<and> (F \<in> \<B>)))"
  have B0:"\<forall>\<E> \<in> Pow \<A>. finite \<E> \<longrightarrow> finite (?f`(\<E>))"
    by simp
  have B1:"\<forall>\<E> \<in> Pow \<A>.  (?f`(\<E>))\<subseteq> \<B>"
  proof -
    { fix AA :: "'a set set"
      have ff1: "\<And>A. \<not> A \<subseteq> \<A> \<or> A \<preceq> \<B>"
        using A1 preceq_transitive subseteq_imp_preceq by blast
      have "\<forall>A f Aa. \<exists>Ab. (f ` A \<subseteq> Aa \<or> (Ab::'a set) \<in> A) \<and> ((f Ab::'a set) \<notin> Aa \<or> f ` A \<subseteq> Aa)"
        by (metis image_subset_iff)
      then have "AA \<notin> Pow \<A> \<or> (\<lambda>A. SOME Aa. Aa \<subseteq> A \<and> Aa \<in> \<B>) ` AA \<subseteq> \<B>"
        using ff1 by (smt (z3) Pow_iff preceq_def someI_ex) }
    then show ?thesis
      by simp
  qed
  have B3:"\<forall>\<E> \<in> Pow \<A>. finite \<E> \<longrightarrow> (finite (?f`(\<E>))) \<and> ((?f`(\<E>)) \<in> Pow \<B>)"
    by (simp add: B1)
  have B4:"\<forall>\<E> \<in> Pow \<A>. finite \<E> \<longrightarrow> \<Inter>(?f`(\<E>)) \<noteq> {}"
    by (metis (mono_tags, lifting) A0 B3 FIP_def)
  have B5:"\<forall>\<E> \<in> Pow \<A>. ( \<forall>E \<in> \<E>. ((?f E) \<subseteq> E))"
    by (metis (no_types, lifting) A1 PowD preceq_def preceq_transitive someI_ex subseteq_imp_preceq)
  have B6:"\<forall>\<E> \<in> Pow \<A>.  \<Inter>(?f`(\<E>)) \<subseteq> (\<Inter>\<E>)"
    using B5 by blast
  have B7:"\<forall>\<E> \<in> Pow \<A>. finite \<E>\<longrightarrow> ( \<Inter>(?f`(\<E>)) \<noteq> {}) \<and> ( \<Inter>(?f`(\<E>)) \<subseteq> (\<Inter>\<E>))"
    using B4 B6 by force
  have B8: "\<forall>\<E> \<in> Pow \<A>. finite \<E> \<longrightarrow> (\<Inter>\<E>) \<noteq> {}"
    by (metis (no_types, lifting) B4 B6 subset_empty)
  with B8 show ?thesis by (simp add: FIP_def)
qed


lemma union_fiter0:
  assumes A0:"FilterSubbase \<C>" 
  shows "B \<in> (fmeetclosure \<C>) \<longleftrightarrow> (\<exists>\<E>\<in>(f_many \<C>). B=\<Inter>\<E> )"
proof-
  have B0:"B \<in>(fmeetclosure \<C>) \<longleftrightarrow> (\<exists>\<B>\<in>Pow \<C>. (finite \<B>) \<and> ( B=\<Inter>\<B>) \<and> (\<B> \<noteq> {})) "
    by (simp add: fmeetclosure_def)
  have B1:"\<forall>\<E>. (\<E>\<in>(f_many \<C>) \<longleftrightarrow>  is_f_many \<E> \<C>)"
    by (simp add: f_many_def)
  have B2:"\<forall>\<E>. ( is_f_many \<E> \<C>) \<longleftrightarrow> ((\<E> \<subseteq>\<C>) \<and> (finite \<E>) \<and> (\<E> \<noteq> {}))"
    by (simp add: is_f_many_def)
  have B3:"\<forall>\<E>. (\<E>\<in>(f_many \<C>)) \<longleftrightarrow> ((\<E>  \<in> Pow \<C>) \<and> (finite \<E>) \<and> (\<E> \<noteq> {}))"
    by (simp add: B1 B2)
  have B4:"B\<in>(fmeetclosure \<C>) \<longrightarrow> (\<exists>\<E>. ((\<E>  \<in> Pow \<C>) \<and> (finite \<E>) \<and> (\<E> \<noteq> {})) \<and>( B=\<Inter>\<E>) )"
    using B0 by blast
  have B5:"B\<in>(fmeetclosure \<C>) \<longrightarrow>  (\<exists>\<E>\<in>(f_many \<C>). B=\<Inter>\<E> )"
    using B0 B3 by blast
  have B6:"\<forall>B. ((\<exists>\<E>\<in>(f_many \<C>). B=\<Inter>\<E> ) \<longrightarrow> B\<in>(fmeetclosure \<C>))"
    by (smt (verit, del_insts) B3 CollectI fmeetclosure_def is_f_many_def)
  with B5 B6 show ?thesis by blast
qed



lemma union_fiter0b:
  assumes A0:"FilterSubbaseIn C X" 
  shows "\<forall>B \<in> Pow X. (B \<in> (fmeetclosure_in C X) \<longleftrightarrow> (\<exists>\<E>\<in>(f_many C). B=\<Inter>\<E> ))"
proof-
  have B0:"B \<in>(fmeetclosure_in C X) \<longleftrightarrow> (B \<in> Pow X \<and> (\<exists>\<B>\<in>Pow C. (finite \<B>) \<and> ( B=\<Inter>\<B>) \<and> (\<B> \<noteq> {}))) "
    by (simp add: fmeetclosure_in_def)
  have B1:"\<forall>\<E>. (\<E>\<in>(f_many C) \<longleftrightarrow>  is_f_many \<E> C)"
    by (simp add: f_many_def)
  have B2:"\<forall>\<E>. ( is_f_many \<E> C) \<longleftrightarrow> ((\<E> \<subseteq>C) \<and> (finite \<E>) \<and> (\<E> \<noteq> {}))"
    by (simp add: is_f_many_def)
  have B3:"\<forall>\<E>. (\<E>\<in>(f_many C)) \<longleftrightarrow> ((\<E>  \<in> Pow C) \<and> (finite \<E>) \<and> (\<E> \<noteq> {}))"
    by (simp add: B1 B2)
  have B4:"B\<in>(fmeetclosure_in C X) \<longrightarrow> (\<exists>\<E>. ((\<E>  \<in> Pow C) \<and> (finite \<E>) \<and> (\<E> \<noteq> {})) \<and>( B=\<Inter>\<E>) )"
    using B0 by blast
  have B5:"B\<in>(fmeetclosure_in C X) \<longrightarrow>  (\<exists>\<E>\<in>(f_many C). B=\<Inter>\<E> )"
    using B0 B3 by blast
  have B6:"\<forall>B \<in> Pow X. (((\<exists>\<E>\<in>(f_many C). B=\<Inter>\<E> ) \<longrightarrow> B\<in>(fmeetclosure_in C X)))"
    by (metis (mono_tags, lifting) B3 CollectI fmeetclosure_in_def)
  with B5 B6 show ?thesis
    by (smt (verit, best) B3 fmeetclosure_in_def mem_Collect_eq)
qed

subsection Subbases

lemma sup_subbase1:
  assumes A0:"FilterSubbase \<C>" and
          A1:"(A1\<in>(fmeetclosure \<C>)) \<and> (A2 \<in>(fmeetclosure \<C>))"
  shows "(A1 \<inter> A2) \<in> (fmeetclosure \<C>)"
  by (smt 
      (verit, ccfv_threshold)
         A1 CollectD CollectI Pow_iff Un_empty
         finite_Un fmeetclosure_def le_sup_iff
         union_inter_c)


lemma sup_subbase1b:
  assumes A0:"FilterSubbaseIn C X" and
          A1:"(A1\<in>(fmeetclosure_in C X)) \<and> (A2 \<in>(fmeetclosure_in C X))"
  shows "(A1 \<inter> A2) \<in> (fmeetclosure_in C X)"
  by (smt (verit) A1 CollectD CollectI IntD2 Pow_iff Un_empty finite_Un fmeetclosure_in_def le_sup_iff subset_eq union_inter_c)





lemma sup_subbase2:
  assumes A0:"FilterSubbase \<C>"
  shows "PiSystem (fmeetclosure \<C>)"
  by (simp add: PiSystem_def assms sup_subbase1)


lemma sup_subbase2b:
  assumes A0:"FilterSubbaseIn C X"
  shows "PiSystem (fmeetclosure_in C X)"
  by (simp add: PiSystem_def assms sup_subbase1b)


lemma sup_subbase3:
  assumes A0: "PiSystem \<A>"
  shows "DownDirected \<A>"
  by (meson DownDirected_def PiSystem_def assms subsetI)


lemma sup_subbase5:
  assumes A0:"FilterSubbase \<C>"
  shows "( fmeetclosure \<C>) \<noteq> {}"
  by (metis CollectI FilterSubbase_def assms bot.extremum ex_in_conv f_many_def finite.emptyI finite.insertI insert_subset is_f_many_def union_fiter0)


lemma sup_subbase5b:
  assumes A0:"X \<noteq> {}" and A1:"C \<in> Pow (Pow X)" and A2:"FilterSubbaseIn C X"
  shows "(fmeetclosure_in C X) \<noteq> {}"
proof -
  obtain bb :: "'a set set \<Rightarrow> 'a set set \<Rightarrow> bool" where
    f1: "\<forall>X0 X1. bb X0 X1 = is_f_many X1 X0"
    by moura
  then have "\<forall>A. f_many A = Collect (bb A)"
    using f_many_def by blast
  then show ?thesis
    using f1 by (metis (no_types) A1 A2 FilterSubbaseIn_def Pow_iff cInf_singleton ex_in_conv finite.emptyI finite_insert insert_not_empty insert_subset is_f_many_def mem_Collect_eq subset_eq union_fiter0b)
qed


lemma sup_subbase4:
  assumes A0:"FilterSubbase \<C>"
  shows "FilterBase (fmeetclosure \<C> )"
  by (simp add: FilterBase_def assms sup_subbase0 sup_subbase2 sup_subbase3 sup_subbase5)

lemma sup_subbase4b:
  assumes A0:"X \<noteq> {}" and A1:"C \<in> Pow (Pow X)" and A2:"FilterSubbaseIn C X"
  shows "FilterBaseIn (fmeetclosure_in C X) X"
  by (smt (verit) A0 A1 A2 CollectD FIP_def FilterBaseIn_def FilterSubbaseIn_def Proper_def fmeetclosure_in_def sup_subbase2b sup_subbase3 sup_subbase5b)


subsection Bases

lemma sup_base5:
  assumes A0:"FilterBase \<B>"
  shows "(upclosure \<B>) \<noteq> {}"
  using FilterOfSets_def assms fbase_gen_filter by auto

lemma sup_base5b:
  assumes A0: "X \<noteq> {}" and A1:"B \<in> Pow(Pow X)" and A2:"FilterBaseIn B X"
  shows "(upclosure_in B X) \<noteq> {}"
  by (metis A0 A1 A2 FilterOfSetsIn_def fbase_gen_filterb)


lemma sup_base6:
  assumes A0: "FilterBase \<B>"
  shows "Proper ( upclosure( \<B> ))"
  using FilterBase_def assms upclosure_preserves_properness by auto

lemma sup_base6b:
  assumes A0:"X \<noteq> {}" and A1:"B \<in> Pow(Pow X)" and A2:"FilterBaseIn B X"
  shows "Proper ( upclosure_in B  X)"
  by (meson A0 A1 A2 FilterOfSetsIn_def fbase_gen_filterb)


lemma sup_base7:
  assumes A0: "FilterBase \<B>"
  shows "PiSystem (upclosure \<B>)"
  using FilterOfSets_def assms fbase_gen_filter by auto



lemma sup_base7b:
  assumes A0: "FilterBaseIn B X"
  shows "PiSystem (upclosure_in B X)"
  by (smt (verit, ccfv_threshold) A0 CollectD CollectI DownDirected_def FilterBaseIn_def PiSystem_def Pow_iff inf.absorb_iff2 inf.bounded_iff inf_aci(2) upclosure_in_def)

lemma sup_base8:
   assumes A0: "FilterBase \<B>"
   shows "UpClosed (upclosure \<B>)"
  by (simp add: upclosure_is_upclosed1)


lemma sup_base8b:
   assumes A0: "FilterBaseIn B X"
   shows "UpClosed_In (upclosure_in B X) X"
  by (simp add: upclosure_in_is_upclosed_in1)

lemma sup_base9:
  assumes A0: "FilterBase \<B>"
  shows "FilterOfSets (upclosure \<B>)"
  by (simp add: assms fbase_gen_filter)

(*1.70.9*)
lemma sup_base9b:
  assumes A0:"X \<noteq> {}" and A1:"B \<in> Pow (Pow X)" and A2: "FilterBaseIn B X"
  shows "FilterOfSetsIn (upclosure_in B X) X"
  using A0 A1 A2 fbase_gen_filterb by blast

lemma generated_filter:
  assumes A0:"FilterSubbase \<C>"
  shows "FilterOfSets( upclosure (fmeetclosure \<C>))"
  by (simp add: assms sup_base9 sup_subbase4) 

lemma generated_filter_in:
   assumes A0:"X \<noteq> {}" and A1:"C \<in> Pow (Pow X)" and A2:"FilterSubbaseIn C X"
   shows "FilterOfSetsIn (filter_generated_by_in C X) X"
  by (metis (no_types, lifting) A0 A1 A2 CollectD PowI fbase_gen_filterb filter_generated_by_in_def fmeetclosure_in_def subsetI sup_subbase4b)



lemma fmc_monotone:
  assumes A0:"C \<in> Pow (Pow X)" and A1:"C \<noteq> {}"
  shows "C \<subseteq> (fmeetclosure_in C X)"
proof-
  have B00:"\<forall>c \<in> C. finite({c})" by simp
  have B01:"\<forall>c \<in> C. {c} \<noteq> {}" by simp 
  have B02:"\<forall>c \<in> C. ({c} \<in> (Pow C))" by auto
  have B03:"\<forall>c \<in> C. \<Inter>{c}=c" by simp
  have B04:"\<forall>c \<in> C. c \<in> (fmeetclosure_in C X)"
        by (smt (verit, ccfv_SIG) A0 B00 B01 B02 B03 CollectI PowD fmeetclosure_in_def subset_eq)
  with B04 show ?thesis
    by (simp add: subsetI)
qed


lemma finite_intersections_in_set:
  fixes X::"'X set"
  assumes A1:"C \<in> Pow(Pow (X))" and
          A2: "\<And>a1 a2. a1 \<in> C \<Longrightarrow> a2 \<in> C \<Longrightarrow> a1 \<inter> a2 \<in> C"and 
          A3:"finite E" and
          A4:"E \<noteq> {}"  and
          A5:"E \<subseteq> C"
  shows "(\<Inter>E) \<in> C"
proof -
  from A3 A4 A5 show ?thesis
  proof (induct E rule: finite_ne_induct)
    case (singleton x)
    with assms show ?case
      by simp
    next
    case (insert x F)
    then have "(\<Inter>(insert x F)) \<in> C" using assms
    proof-
      have P0:"x \<in> C"
        using insert.prems by auto
      have P1: "F \<subseteq> C"
        using insert.prems by auto
      with A2 have P2:"x \<inter> (\<Inter>F) \<in> C"
        by (simp add: P0 insert.hyps(4))
      from insert.hyps have P3:"(\<Inter>F) \<in> C"
        using P1 by blast
      have  P4:"\<Inter>(insert x F) = x \<inter> (\<Inter>F)" by simp
      then show "(\<Inter>(insert x F)) \<in> C"
        by (simp add: P2)
    qed
    show ?case
      using \<open>\<Inter> (insert (x::'X set) (F::'X set set)) \<in> (C::'X set set)\<close> by auto
  qed
qed


lemma fmeet_invol:
  assumes A0:"C \<in> Pow (Pow X)" and A1:"C \<noteq> {}"
  shows "(fmeetclosure_in C X) = fmeetclosure_in (fmeetclosure_in C X) X"
proof-
  let ?C1= "(fmeetclosure_in C X)"
  let ?C2= "(fmeetclosure_in ?C1 X)"
  have B0: "C \<subseteq> ?C1"
    by (metis A0 A1 fmc_monotone)
  have B1:"?C1 \<subseteq> ?C2"
    by (metis (no_types, lifting) Pow_iff empty_iff fmc_monotone fmeetclosure_in_def mem_Collect_eq subsetI)
  have B2:"?C2 \<subseteq> ?C1"
  proof
    fix a assume "a \<in> ?C2"    
    have "a \<in> Pow X"
      by (metis (no_types, lifting) CollectD \<open>(a::'a set) \<in> fmeetclosure_in (fmeetclosure_in (C::'a set set) (X::'a set)) X\<close> fmeetclosure_in_def)
    let ?r="\<lambda>a. \<lambda>C.  (\<exists>B\<in>(Pow C). (finite B) \<and> (a=\<Inter>B) \<and> (B \<noteq> {}))"
    have B20:"a \<in> ?C2 \<longleftrightarrow> (\<exists>B\<in>(Pow ?C1). (finite B) \<and> (a=\<Inter>B) \<and> (B \<noteq> {}))"
      by (smt (verit, ccfv_SIG) \<open>a \<in> Pow X\<close> fmeetclosure_in_def mem_Collect_eq)
    have B30:"a \<in> ?C1 \<longleftrightarrow> (\<exists>b\<in>(Pow C). (finite b) \<and> (a=\<Inter>b) \<and> (b \<noteq> {}))"
      by (smt (verit, ccfv_SIG) \<open>a \<in> Pow X\<close> fmeetclosure_in_def mem_Collect_eq)
    have B40:"a \<in> ?C2 \<longleftrightarrow> ?r a ?C1"
      using B20 by blast
    have B50:"d \<in> ?C1 \<longleftrightarrow> ?r d C"
      by (smt (verit, ccfv_threshold) A0 Inf_lower2 Pow_iff Set.set_insert finite_has_minimal fmeetclosure_in_def insert_subset mem_Collect_eq)
   obtain B where "(B \<in> (Pow ?C1)) \<and> finite B \<and> (a=(\<Inter>B)) \<and> (B \<noteq> {})"
     by (smt (verit, best) CollectD \<open>(a::'a set) \<in> fmeetclosure_in (fmeetclosure_in (C::'a set set) (X::'a set)) X\<close> fmeetclosure_in_def)
   have B60:"B \<in> Pow ?C1"
        using \<open>(B::'a set set) \<in> Pow (fmeetclosure_in (C::'a set set) (X::'a set)) \<and> finite B \<and> (a::'a set) = \<Inter> B \<and> B \<noteq> {}\<close> by blast
   obtain f where "f=(\<lambda>x.  SOME t. ( (is_f_many t C) \<and> (x=\<Inter>t)))"
      by simp
   have B70: "\<forall>b \<in> B. (?r b C)"
        by (smt (verit, best) CollectD PowD Set.set_insert \<open>(B::'a set set) \<in> Pow (fmeetclosure_in (C::'a set set) (X::'a set)) \<and> finite B \<and> (a::'a set) = \<Inter> B \<and> B \<noteq> {}\<close> fmeetclosure_in_def insert_subset)
   have B80:"\<forall>b \<in> B. (\<exists>t. ((is_f_many t C) \<and> (b=\<Inter>t)))"
        by (meson PowD \<open>\<forall>b::'a set\<in>B::'a set set. \<exists>B::'a set set\<in>Pow (C::'a set set). finite B \<and> b = \<Inter> B \<and> B \<noteq> {}\<close> is_f_many_def)   
   have B90:"\<forall>b \<in> B. (b=\<Inter>(f b))"
        by (metis (mono_tags, lifting) \<open>(f::'a set \<Rightarrow> 'a set set) = (\<lambda>x::'a set. SOME t::'a set set. is_f_many t (C::'a set set) \<and> x = \<Inter> t)\<close> \<open>\<forall>b::'a set\<in>B::'a set set. \<exists>t::'a set set. is_f_many t (C::'a set set) \<and> b = \<Inter> t\<close> someI)
   have B90:"\<forall>b \<in> B. (is_f_many (f b) C)"
     by (metis (mono_tags, lifting) B80 \<open>(f::'a set \<Rightarrow> 'a set set) = (\<lambda>x::'a set. SOME t::'a set set. is_f_many t (C::'a set set) \<and> x = \<Inter> t)\<close> someI)
   have B100:"\<forall>b \<in> B. (finite (f b))"
     using B90 is_f_many_def by blast
   have B110:"finite B"
     by (simp add: \<open>(B::'a set set) \<in> Pow (fmeetclosure_in (C::'a set set) (X::'a set)) \<and> finite B \<and> (a::'a set) = \<Inter> B \<and> B \<noteq> {}\<close>)    
   let ?D="\<Union>b \<in> B. (f b)"
   have B120:"finite ?D"
     using B100 B110 by blast
   have B130:"?D \<in> Pow C"
     by (meson B90 PowI UN_least is_f_many_def)
   have B140:"?D \<noteq> {}"
     using B90 \<open>(B::'a set set) \<in> Pow (fmeetclosure_in (C::'a set set) (X::'a set)) \<and> finite B \<and> (a::'a set) = \<Inter> B \<and> B \<noteq> {}\<close> is_f_many_def by fastforce
   have B150:"a=\<Inter>B"
     by (simp add: \<open>(B::'a set set) \<in> Pow (fmeetclosure_in (C::'a set set) (X::'a set)) \<and> finite B \<and> (a::'a set) = \<Inter> B \<and> B \<noteq> {}\<close>)
   have B160:"a=(\<Inter>b\<in>B. b)"
     by (simp add: B150)
   have B170:"\<forall>b \<in> B. (b=(\<Inter>(f b)))"
     by (metis (mono_tags, lifting) B80 \<open>(f::'a set \<Rightarrow> 'a set set) = (\<lambda>x::'a set. SOME t::'a set set. is_f_many t (C::'a set set) \<and> x = \<Inter> t)\<close> someI_ex)
   have B180:"a=(\<Inter>b\<in>B. (\<Inter>(f b)))"
     using B160 B170 by auto
  have B190:"a=\<Inter>?D"
    using B180 by blast
  with B120 B130 B140 B190 have B200:"a \<in> ?C1"
    using B30 by blast
  show "a \<in> ?C1"
    by (simp add: B200)
  qed
  have B3:"?C1 = ?C2"
    by (simp add: B1 B2 subset_antisym)
  with B3 show ?thesis
    by simp
qed

lemma bozowatch1:
  assumes A0:"PiSystem A" and A1:"A \<noteq> {}" and A2:"A \<in> Pow(Pow(X))"
  shows "\<forall>E \<in> Pow A. E \<noteq> {} \<longrightarrow> finite E \<longrightarrow> \<Inter>E \<in> A"
  by (metis A0 A2 PiSystem_def PowD finite_intersections_in_set)

lemma bozowatch2:
  assumes A0:"PiSystem A" and A1:"A \<noteq> {}" and A2:"A \<in> Pow(Pow(X))"
  shows "A = fmeetclosure_in A X"
proof-
  have L:"A \<subseteq> fmeetclosure_in A X"
    by (meson A1 A2 fmc_monotone)
  have R:"fmeetclosure_in A X \<subseteq> A"
  proof
    fix a assume "a \<in> fmeetclosure_in A X"
    have R0:"(a \<in> Pow X)"
      by (metis (no_types, lifting) CollectD \<open>a \<in> fmeetclosure_in A X\<close> fmeetclosure_in_def)
    have R1:"\<exists>B\<in>(Pow A). (finite B) \<and> (a=\<Inter>B) \<and> (B \<noteq> {})"
      using \<open>a \<in> fmeetclosure_in A X\<close> fmeetclosure_in_def by auto
    show "a \<in> A"
      by (metis A0 A1 A2 R1 bozowatch1)
  qed
  with L R show ?thesis by simp
qed

lemma bozowatch3:
  assumes A0:"FilterOfSetsIn F X" and A1:"F \<in> Pow (Pow X)"
  shows "F = fmeetclosure_in F X"
  by (metis A0 A1 FilterOfSetsIn_def bozowatch2)

lemma fsubbase1712:
  assumes A0:"X \<noteq> {}" and A1:"C \<in> Pow (Pow X)" and A2:"FilterSubbaseIn C X"
  shows "F \<in> (FilUpSets C X) \<longrightarrow>  (filter_generated_by_in C X) \<preceq> F "
proof-
  let ?BF="(fmeetclosure_in C X)" 
  let ?EF="upclosure_in ?BF X "
  have B0:"C \<preceq> ?BF"
    by (metis A1 empty_subsetI fmc_monotone subseteq_imp_preceq)
  have B1:"?BF \<preceq> ?EF"
    by (smt (verit, del_insts) CollectD CollectI fmeetclosure_in_def preceq_def preceq_reflexive upclosure_in_def)
  have B2:"Fp \<in> FilUpSets C X \<longrightarrow> C \<preceq> Fp"
    by (simp add: FilUpSets_def)
  have B3:"Fp \<in> FilUpSets C X \<longrightarrow> ?BF \<preceq> Fp "


end
