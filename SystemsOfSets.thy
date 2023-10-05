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


subsection RelationsAndOperations

definition preceq:: "'X set set \<Rightarrow> 'X set set \<Rightarrow> bool" (infix "\<preceq>" 50) where
  "\<A> \<preceq> \<B>  \<longleftrightarrow> (\<forall>A\<in>\<A>. (\<exists>B\<in>\<B>. (A \<supseteq> B)))"

definition fequiv:: "'X set set \<Rightarrow> 'X set set \<Rightarrow> bool" (infix "~" 50) where
  "\<A> ~ \<B>  \<longleftrightarrow> ((\<A> \<preceq> \<B>) \<and> ( \<B> \<preceq>  \<A>))"

definition upclosure:: "'X set set \<Rightarrow> 'X set set" where
  "upclosure \<A>  = {E. (\<exists>A \<in>\<A>.( A \<subseteq> E)) }"

definition fmeetclosure:: "'X set set \<Rightarrow> 'X set set" where
  "fmeetclosure \<A> = {A. (\<exists>\<B>\<in>(Pow \<A>). (finite \<B>) \<and> ( A=\<Inter>\<B>) \<and> (\<B> \<noteq> {}))}"

definition meshes:: "'X set set \<Rightarrow> 'X set set \<Rightarrow> bool" where
  "meshes \<A> \<B> \<equiv> \<forall>A \<in> \<A>. \<forall>B \<in>\<B>. (A \<inter> B \<noteq> {})"

definition grill_of::"'X set set \<Rightarrow> 'X set  \<Rightarrow> 'X set set" where
  "grill_of \<A> X =  {E \<in> Pow X. meshes {E} \<A> } "

subsection SyntaxForFC

definition is_f_many::"'X set \<Rightarrow>'X set \<Rightarrow> bool" where
  "is_f_many \<B> \<A> \<equiv>  (\<B> \<subseteq> \<A>) \<and> (finite \<B>) \<and> (\<B> \<noteq> {}) "

definition f_many::"'X set \<Rightarrow> 'X set set" where
  "f_many \<A> = {\<B>. is_f_many \<B> \<A> }"


section Lemmas

subsection PropertiesOfRelations

lemma preceq_transitive:
   "\<forall>\<A> \<B> \<C>. (\<A> \<preceq> \<B> \<and>  \<B> \<preceq> \<C>) \<longrightarrow> (\<A> \<preceq> \<C>)"
  by (meson dual_order.trans preceq_def)

lemma preceq_reflexive:
  "\<forall>\<A>. \<A> \<preceq> \<A>"
  using preceq_def by auto

lemma subseteq_imp_preceq:
  " \<forall>\<A> \<B>. \<A> \<subseteq> \<B>\<longrightarrow>\<A> \<preceq> \<B>"
  by (meson dual_order.refl in_mono preceq_def)

lemma preceq_trns2:
  "\<forall>\<A> \<B> \<C>. \<A> \<subseteq> \<B> \<and> \<B> \<preceq> \<C> \<longrightarrow> \<A> \<preceq> \<C>  "
  using preceq_transitive subseteq_imp_preceq by blast

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

lemma upclosed_equiv_then_equal:
  assumes A0:"UpClosed  \<A> \<and> UpClosed \<B> " and
          A1:"\<A> ~ \<B>"
 shows  "\<A>=\<B>"
  by (meson A0 A1 UpClosed_def fequiv_def preceq_def subsetI subset_antisym)

lemma upclosure_is_upclosed1:
  assumes "\<A>=upclosure \<B>"
  shows "UpClosed \<A>"
  by (smt (verit, ccfv_SIG) CollectD CollectI UpClosed_def assms dual_order.trans upclosure_def)

lemma upclosure_is_upclosed2:
  assumes "\<A>=upclosure \<B>"
  shows "\<A> ~ \<B>"
  by (smt (verit, ccfv_threshold) assms dual_order.refl fequiv_def mem_Collect_eq preceq_def upclosure_def)

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

lemma fbase_condition:
  assumes A0: "(Proper B)" and
          A1: "FilterOfSets F"
  shows "(F=upclosure B) \<longleftrightarrow> (F \<preceq> B) \<and> (B \<subseteq> F)"
  by (metis A0 A1 FilterOfSets_def UpClosed_def empty_iff fequiv_def fequiv_iff_upclosure_equal subseteq_imp_preceq upclosed_equiv_then_equal upclosed_then_preceq_imp_subseteq upclosure_is_upclosed1 upclosure_is_upclosed2)

lemma upprop_fip:
  assumes A0:"Centered B" and
          A1: "A \<preceq> B"
  shows"Centered A"
  by (metis (no_types, lifting) A0 A1 Centered_def inf_mono preceq_def subset_empty)



lemma union_inter_c:
  "\<Inter>(\<A> \<union> \<B>) = (\<Inter>\<A>)\<inter>(\<Inter>\<B> )"
  by blast

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



lemma sup_subbase2:
  assumes A0:"FilterSubbase \<C>"
  shows "PiSystem (fmeetclosure \<C>)"
  by (simp add: PiSystem_def assms sup_subbase1)


lemma sup_subbase3:
  assumes A0: "PiSystem \<A>"
  shows "DownDirected \<A>"
  by (meson DownDirected_def PiSystem_def assms subsetI)


lemma sup_subbase5:
  assumes A0:"FilterSubbase \<C>"
  shows "( fmeetclosure \<C>) \<noteq> {}"
  by (metis CollectI FilterSubbase_def assms bot.extremum ex_in_conv f_many_def finite.emptyI finite.insertI insert_subset is_f_many_def union_fiter0)

lemma sup_subbase4:
  assumes A0:"FilterSubbase \<C>"
  shows "FilterBase (fmeetclosure \<C> )"
  by (simp add: FilterBase_def assms sup_subbase0 sup_subbase2 sup_subbase3 sup_subbase5)


subsection Bases

lemma sup_base5:
  assumes A0:"FilterBase \<B>"
  shows "(upclosure \<B>) \<noteq> {}"
  using FilterOfSets_def assms fbase_gen_filter by auto

lemma sup_base6:
  assumes A0: "FilterBase \<B>"
  shows "Proper ( upclosure( \<B> ))"
  using FilterBase_def assms upclosure_preserves_properness by auto

lemma sup_base7:
  assumes A0: "FilterBase \<B>"
  shows "PiSystem (upclosure \<B>)"
  using FilterOfSets_def assms fbase_gen_filter by auto

lemma sup_base8:
   assumes A0: "FilterBase \<B>"
   shows "UpClosed (upclosure \<B>)"
  by (simp add: upclosure_is_upclosed1)

lemma sup_base9:
  assumes A0: "FilterBase \<B>"
  shows "FilterOfSets (upclosure \<B>)"
  by (simp add: assms fbase_gen_filter)

lemma generated_filter:
  assumes A0:"FilterSubbase \<C>"
  shows "FilterOfSets( upclosure (fmeetclosure \<C>))"
  by (simp add: assms sup_base9 sup_subbase4) 




end
