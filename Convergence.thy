theory Convergence
  imports Main
begin
no_notation Cons (infixr "#" 65) 

definition preceq::"'a set set \<Rightarrow> 'a set set \<Rightarrow> bool"  (infixl "(\<preceq>)" 70) where
  "\<A> \<preceq> \<B> \<equiv> (\<forall>A. A \<in> \<A> \<longrightarrow> (\<exists>B \<in> \<B>. B \<subseteq> A))"

lemma preceqI[intro?]:
  "(\<And>A. A \<in> \<A> \<Longrightarrow>(\<exists>B \<in> \<B>. B \<subseteq> A)) \<Longrightarrow> \<A> \<preceq> \<B>"
  by(simp add:preceq_def)

lemma preceqE[elim?]:
  " \<A> \<preceq> \<B> \<Longrightarrow> (\<And>A. A \<in> \<A> \<Longrightarrow>(\<exists>B \<in> \<B>. B \<subseteq> A)) "
  by(simp add:preceq_def)

lemma preceq_refl:
  "\<A> \<preceq> \<A>" 
  by(auto simp add:preceq_def)

lemma preceq_trans[trans]:
  "\<lbrakk>\<A> \<preceq> \<B>; \<B> \<preceq> \<C>\<rbrakk> \<Longrightarrow> \<A> \<preceq> \<C>"
  by (meson order.trans preceq_def)

lemma sub_preceq:
  "\<A> \<subseteq> \<B> \<Longrightarrow>\<A> \<preceq> \<B>"
  using preceq_def by blast

definition upclosed::"'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "upclosed X \<A> \<equiv> (\<A> \<subseteq> Pow X) \<and> (\<forall>A B. A \<in> \<A> \<and> B \<in> Pow X \<and> A \<subseteq> B \<longrightarrow> B \<in> \<A>)"

definition upcl::"'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set set" where 
  "upcl X \<A> \<equiv> {E \<in> Pow X. \<exists>A \<in> \<A>. A \<subseteq>  E}"

lemma upclosedI:
  "\<lbrakk>(\<A> \<subseteq> Pow X) ;(\<And>A B. \<lbrakk>A \<in> \<A>; B \<in> Pow X; A \<subseteq> B\<rbrakk> \<Longrightarrow> B \<in> \<A>)\<rbrakk> \<Longrightarrow> upclosed X \<A>"
  by(auto simp add:upclosed_def)

lemma upclosedE:
  assumes up:"upclosed X \<A>" shows upcl_sub:"(\<A> \<subseteq> Pow X)" and upcl:"(\<And>A B. \<lbrakk>A \<in> \<A>; B \<in> Pow X; A \<subseteq> B\<rbrakk> \<Longrightarrow> B \<in> \<A>)"
  using up upclosed_def apply blast
  by (meson up upclosed_def)
  
lemma upcl_closed[simp]:
  "(upcl X \<A>) \<subseteq> (Pow X)"
  by(auto simp add:upcl_def)

lemma upcl_ext:
  assumes sub:"\<A> \<subseteq> Pow X" 
  shows "\<A> \<subseteq> upcl X \<A>"
  using sub upcl_def by fastforce 

lemma upcl_iso:
  assumes  sub1:"\<B> \<subseteq> Pow X" and sub2:"\<A> \<subseteq> \<B>"
  shows "upcl X \<A> \<subseteq> upcl X \<B>"
  using sub1 sub2 by(auto simp add:upcl_def) 


lemma upcl_ide:
  assumes sub:"\<A> \<subseteq> Pow X" 
  shows "upcl X \<A> = upcl X (upcl X \<A>)"
  using assms apply(auto simp add:upcl_def)
  by (meson dual_order.trans)

lemma upcl_upclosed:
  assumes sub:"\<A> \<subseteq> Pow X" 
  shows "upclosed X (upcl X \<A>)"
  apply(rule upclosedI)
  apply(simp add:sub)
  apply(auto simp add:upcl_def)
  by (meson order_trans)

lemma upcl_fp:
  assumes sub:"\<A> \<subseteq> Pow X" and up:"upclosed X \<A>"
  shows "upcl X \<A>=\<A>"
  using assms by(auto simp add:upcl_def upclosed_def)

lemma up_cl_preceq:
  "\<A> \<subseteq> Pow X \<Longrightarrow> \<A> \<preceq> upcl X \<A>"
  by (simp add: sub_preceq upcl_ext)

lemma up_cl_preceq2:
  "\<A> \<subseteq> Pow X \<Longrightarrow>  upcl X \<A> \<preceq> \<A>"
  by(auto simp add:preceq_def upcl_def)

lemma preceq_iff:
  assumes  sub1:"\<A> \<subseteq> Pow X" and sub2:"\<B> \<subseteq> Pow X"
  shows "\<A> \<preceq> \<B> \<longleftrightarrow> \<A> \<subseteq> upcl X \<B>" 
  using assms by(auto simp add:upcl_def preceq_def)

lemma preceq_of_iso:
  assumes sub1:"\<A> \<subseteq> Pow X"  and sub2:"\<B> \<subseteq> Pow X" and up:"upclosed X \<B>"
  shows "\<A> \<preceq>\<B> \<longleftrightarrow>\<A>  \<subseteq> \<B> "
  by (metis preceq_iff sub1 sub2 up upcl_fp)

lemma preceq_image:
  assumes map:"f`X =Y" and sub1:"\<A> \<subseteq> Pow X" and sub2:"\<B> \<subseteq> Pow Y" 
  shows "\<B> \<preceq> {h`A|A. A \<in> \<A>} \<longleftrightarrow> {vimage h B|B. B \<in> \<B>} \<preceq> \<A> " (is "?L \<longleftrightarrow> ?R")
proof
  show "?L \<Longrightarrow> ?R"
  proof-
    assume ?L 
    have "\<And>B. B \<in> \<B>  \<Longrightarrow> (\<exists>A \<in> \<A>. A \<subseteq> vimage h B)" 
    proof-
      fix B assume "B \<in> \<B>" then obtain A where "A \<in> \<A>" and "(h`A) \<subseteq> B"  using \<open>\<B> \<preceq> {h ` A |A. A \<in> \<A>}\<close> preceqE by force
      then have "A \<subseteq> vimage h (h`A)" by blast
      also have "... \<subseteq> vimage h B"   using \<open>h ` A \<subseteq> B\<close> by blast
      then show "(\<exists>A \<in> \<A>. A \<subseteq> vimage h B)"  by (meson \<open>A \<in> \<A>\<close> calculation subset_trans)
   qed
   then show ?R  using preceq_def by force
  qed
  show "?R \<Longrightarrow> ?L"
 proof-
    assume ?R
    have "\<And>B. B \<in> \<B>  \<Longrightarrow> (\<exists>A \<in> \<A>. h`A \<subseteq> B)" 
    proof-
      fix B assume "B \<in> \<B>" then obtain A where "A \<in> \<A>" and "A \<subseteq> vimage h B"
      by (metis (mono_tags, lifting) CollectI \<open>{h -` B |B. B \<in> \<B>} \<preceq> \<A>\<close> preceqE)
      then have "h`A \<subseteq> h`(vimage h B)" by blast
      also have "... \<subseteq> B" by blast
       then show "(\<exists>A \<in> \<A>. h`A \<subseteq>  B)"  by (meson \<open>A \<in> \<A>\<close> calculation subset_trans)
    qed
   then show ?L    by (simp add: preceqI setcompr_eq_image)
 qed
qed


definition fil::"'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "fil X \<F> \<equiv> \<F>  \<noteq> {} \<and> \<F> \<subseteq> Pow X \<and> (\<forall>A F. A \<in> Pow X \<and> F \<in> \<F> \<and> F \<subseteq> A \<longrightarrow> A \<in> \<F>) \<and> (\<forall>F1 F2. F1 \<in> \<F>  \<and>  F2 \<in> \<F> \<longrightarrow> F1 \<inter> F2 \<in> \<F> )"

definition pfil::"'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "pfil X \<F> \<equiv>  \<F>  \<noteq> {} \<and>  \<F> \<subseteq> Pow X \<and> (\<forall>A F. A \<in> Pow X \<and> F \<in> \<F> \<and> F \<subseteq> A \<longrightarrow> A \<in> \<F>) \<and> (\<forall>F1 F2. F1 \<in> \<F>  \<and>  F2 \<in> \<F> \<longrightarrow> F1 \<inter> F2 \<in> \<F> ) \<and>  \<F> \<noteq> Pow X"

lemma pfil_fil:
  "pfil X \<F> \<Longrightarrow> fil X \<F>"
  by (simp add: fil_def pfil_def)

lemma fil_pfil:
  "fil X \<F> \<Longrightarrow>\<F> \<noteq> Pow X \<Longrightarrow> pfil X \<F> "
  by (simp add: fil_def pfil_def)

lemma filE:
  assumes f:"fil X \<F>" 
  shows filsub:"\<F> \<subseteq> Pow X" and 
        filupc:"\<And>A F. \<lbrakk>A \<in> Pow X; F \<in>  \<F>; F \<subseteq> A\<rbrakk> \<Longrightarrow> A \<in>  \<F>" and
        filinc:"\<And>F1 F2. \<lbrakk>F1 \<in>  \<F>; F2 \<in>  \<F>\<rbrakk> \<Longrightarrow> F1 \<inter> F2 \<in>  \<F>" and
        filnem:"\<F>  \<noteq> {} " and
        filtop:"X \<in> \<F>"
 using f apply(simp add:fil_def)
 using f fil_def apply blast
 apply (metis f fil_def)
 using f fil_def apply blast
 by (metis PowD Pow_top ex_in_conv f fil_def subsetD)

lemma pfilE:
  assumes f:"pfil X \<F>" 
  shows pfilsub:"\<F> \<subseteq> Pow X" and 
        pfilupc:"\<And>A F. \<lbrakk>A \<in> Pow X; F \<in>  \<F>; F \<subseteq> A\<rbrakk> \<Longrightarrow> A \<in>  \<F>" and
        pfilinc:"\<And>F1 F2. \<lbrakk>F1 \<in>  \<F>; F2 \<in>  \<F>\<rbrakk> \<Longrightarrow> F1 \<inter> F2 \<in>  \<F>" and
        pfilnsp:"\<F> \<noteq> Pow X" and
        pfiltop:"X \<in> \<F>" and
        pfilnbt:"{} \<notin> \<F>" 
        apply (meson f fil_def pfil_fil)
        using f filupc pfil_fil apply blast
        using f filinc pfil_fil apply blast
        using f pfil_def apply blast
        apply (simp add: f filtop pfil_fil)
        by (metis empty_subsetI f pfil_def subsetI subset_antisym)
        
lemma filter_inter:
  assumes ef:"\<forall>F. F \<in> EF \<longrightarrow> fil X F" and ne:"EF \<noteq> {}"
  shows "fil X (\<Inter>EF)"
  apply(auto simp add: fil_def)
  apply (metis InterI ef empty_iff filtop)
  apply (metis IntD2 Int_commute Pow_iff all_not_in_conv ef fil_def inf.absorb_iff2 ne)
  apply (meson PowI ef filupc)
  by (meson ef filinc)


lemma pfilter_inter:
  assumes ef:"\<forall>F. F \<in> EF \<longrightarrow> pfil X F" and ne:"EF \<noteq> {}"
  shows "pfil X (\<Inter>EF)"
proof(rule fil_pfil)
  obtain "fil X (\<Inter>EF)"  by (simp add: ef filter_inter ne pfil_fil)
  then show "fil X (\<Inter> EF)" using filter_inter by auto
  then show "\<Inter> EF \<noteq> Pow X"   using ef ne pfilnbt by fastforce
qed


definition mesh::"'a set set \<Rightarrow> 'a set set \<Rightarrow> bool" (infix "(#)" 50) where
  "\<A>#\<B> \<equiv> (\<forall>A B. A \<in> \<A> \<and> B \<in> \<B> \<longrightarrow> A \<inter> B \<noteq> {})"

lemma mesh_sym:
  "\<A>#\<B> \<longleftrightarrow> \<B>#\<A>"
  by (metis Int_commute mesh_def)

lemma mesh_single[simp]:
  "{A}#\<B> \<longleftrightarrow> (\<forall>B. B \<in> \<B> \<longrightarrow> A \<inter> B \<noteq> {})"
  by (simp add: mesh_def)

lemma mesh_sub:
  "\<lbrakk>\<F> \<subseteq> Pow X; A \<in> Pow X; {A}#\<F>;A \<subseteq> B\<rbrakk> \<Longrightarrow> {B}#\<F>"
  by fastforce

lemma mesh_props1:
  assumes sub1:"\<A> \<subseteq> Pow X" and sub2:"E \<in> Pow X" and up:"upclosed X \<A>"
  shows msh1:"E \<notin> \<A> \<longleftrightarrow> {X-E}#\<A>"
  using assms apply(simp)
  by (metis Diff_disjoint Diff_eq_empty_iff Int_Diff Int_commute PowD in_mono inf.absorb2 sub2 upcl)


definition grill::"'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set set" where
  "grill X \<A> \<equiv> {E \<in> Pow X. \<forall>A. A \<in> \<A> \<longrightarrow> A \<inter> E \<noteq> {} }"

lemma grill_memI:
  "E \<in> Pow X \<Longrightarrow> (\<And>A. A \<in> \<A> \<Longrightarrow> A \<inter> E \<noteq> {}) \<Longrightarrow> E \<in> grill X \<A>" 
  by(simp add:grill_def)


lemma grill_memE:
  assumes "E \<in> grill X \<A>"
  shows grillsub:"E \<in> Pow X" and grillmesh1:"(\<And>A. A \<in> \<A> \<Longrightarrow> A \<inter> E \<noteq> {})"
  apply (metis (no_types, lifting) CollectD assms grill_def)
  by (metis (mono_tags, lifting) CollectD assms grill_def)

lemma grill_mesh:
  "grill X \<A> = {E \<in> Pow X. {E}#\<A>}"
  by(auto simp add:grill_def mesh_def)

lemma grill_sub:
  "grill X \<A> \<subseteq> Pow X"
  using grillsub by auto

lemma grill_anti:
  assumes sub1:"\<A> \<subseteq> \<B> "and  sub2:"\<B> \<subseteq> Pow X" 
  shows "grill X \<B> \<subseteq> grill X \<A>"
  by (meson grill_memI grillmesh1 grillsub in_mono sub1 subsetI)

lemma grill_mem_upcl:
  assumes sub1:"\<A> \<subseteq> Pow X" and sub2:"E \<in> Pow X" and up:"upclosed X \<A>" 
  shows "E \<in> grill X \<A> \<longleftrightarrow> (X-E) \<notin> \<A>"
  by (metis (no_types, lifting) Diff_Diff_Int Diff_subset PowD PowI grill_mesh inf.absorb2 mem_Collect_eq mesh_props1 sub1 sub2 up)

lemma grill_upcl:
  assumes sub1:"\<A> \<subseteq> Pow X "
  shows grillup:"upclosed X (grill X \<A>)" and "grill X (grill X \<A>) = upcl X \<A>"
proof-
  show "upclosed X (grill X \<A>)" 
    apply(rule upclosedI)
    apply (simp add: grill_sub)
    by (metis (no_types, lifting) CollectD CollectI grill_mesh mesh_sub sub1)
  show "grill X (grill X \<A>) = upcl X \<A>" 
  proof
    show "grill X (grill X \<A>) \<subseteq>  upcl X \<A> "


end