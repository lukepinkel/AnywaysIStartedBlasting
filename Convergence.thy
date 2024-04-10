theory Convergence
  imports Main Posets16
begin
no_notation Cons (infixr "#" 65) 

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

lemma upclosedE1:
  "upclosed X \<A> \<Longrightarrow> \<A> \<subseteq> Pow X"
   by(simp add:upclosed_def)

lemma upclosedE2:
  "upclosed X \<A> \<Longrightarrow> (\<And>A B. \<lbrakk>A \<in> \<A>; B \<in> Pow X; A \<subseteq> B\<rbrakk> \<Longrightarrow> B \<in> \<A>)"
   by(simp add:upclosed_def)

lemma upclosed_memI1:
  "\<lbrakk>upclosed X \<A>; E \<in> Pow X; (\<exists>A \<in> \<A>. A \<subseteq> E)\<rbrakk> \<Longrightarrow> E \<in> \<A>"
  using upclosedE2 by blast    
   

lemma upcl_memI:
  "\<lbrakk>E \<in> Pow X; (\<exists>A \<in> \<A>. A \<subseteq> E)\<rbrakk> \<Longrightarrow>  E \<in> upcl X \<A>"
  by (simp add: upcl_def)

lemma upcl_memI2:
  "\<lbrakk>E \<in> Pow X; A \<in> \<A>; A \<subseteq> E\<rbrakk> \<Longrightarrow>  E \<in> upcl X \<A>"
proof-
  assume A0:"E \<in> Pow X" and "A \<in> \<A>" and "A \<subseteq> E"
  then obtain  "E \<in> Pow X"  and "(\<exists>A \<in> \<A>. A \<subseteq> E)" by blast
  then show "E \<in> upcl X \<A>"  by(rule upcl_memI)
qed

lemma upcl_memE1:
   " E \<in> upcl X \<A> \<Longrightarrow> E \<in> Pow X"
   by (simp add: upcl_def) 

lemma upcl_closed:
  "(upcl X \<A>) \<subseteq> (Pow X)"
  by(auto dest:upcl_memE1)

lemma upcl_memE2:
   "E \<in> upcl X \<A> \<Longrightarrow> (\<exists>A \<in> \<A>. A \<subseteq> E)"
   by (simp add: upcl_def) 

lemma upcl_mem_iff:
  "E \<in> upcl X \<A> \<longleftrightarrow> E \<in> Pow X \<and> (\<exists>A \<in> \<A>. A \<subseteq> E)"
  by (simp add: upcl_def)
  
lemma upcl_upclosed1:
  "\<lbrakk>A \<in> upcl X \<A>; B \<in> Pow X; A \<subseteq> B\<rbrakk> \<Longrightarrow> B \<in> upcl X \<A>"
proof(rule upcl_memI, simp)
  assume A0:"A \<in> upcl X \<A>" and A1:"B \<in> Pow X" and A2:"A \<subseteq> B"
  from A0 obtain C where "C \<in> \<A>" and "C \<subseteq> A"  using upcl_memE2 by blast 
  then obtain "C \<in> \<A>" and "C \<subseteq> B" using A2 by simp
  then show "\<exists>A\<in>\<A>. A \<subseteq> B" by auto
qed

lemma upcl_ref:
  "\<A> \<subseteq> Pow X \<Longrightarrow> E \<in> \<A> \<Longrightarrow> E \<in> upcl X \<A>"
proof-
    assume "\<A> \<subseteq> Pow X" and "E \<in> \<A>"
    then obtain "(\<exists>A \<in> \<A>. A \<subseteq> E)" and "E \<in> Pow X" by blast
    then show "E \<in> upcl X \<A>"    by (simp add: upcl_memI) 
qed

lemma upcl_ext:
 "\<A> \<subseteq> Pow X \<Longrightarrow> \<A> \<subseteq> upcl X \<A>"
 by (simp add: subset_eq upcl_ref)

lemma upcl_iso:
  "\<lbrakk>\<A> \<subseteq> \<B>; \<B> \<subseteq> Pow X\<rbrakk> \<Longrightarrow> upcl X \<A> \<subseteq> upcl X \<B>"
proof-
  assume "\<A> \<subseteq> \<B>" and "\<B> \<subseteq> Pow X" then obtain "\<A> \<subseteq> Pow X" by simp
  show "upcl X \<A> \<subseteq> upcl X \<B>"
  proof
    fix E assume "E\<in> upcl X \<A>"
    then obtain "E \<in> Pow X" and " (\<exists>A \<in> \<A>. A \<subseteq> E)"   by (simp add: upcl_mem_iff)
    then obtain A where "A \<in> \<A>" and "A \<subseteq> E" by blast
    also obtain  "E \<in> Pow X" and  "A \<in> \<B>" and "A \<subseteq> E"  using \<open>E \<in> Pow X\<close> \<open>\<A> \<subseteq> \<B>\<close> calculation(1,2) by blast  
    then show "E \<in> upcl X \<B>" by(rule upcl_memI2)
  qed
qed


lemma upcl_ide:
  "\<lbrakk>\<A> \<subseteq> Pow X\<rbrakk> \<Longrightarrow> upcl X \<A> = upcl X (upcl X \<A>)"
proof-
  assume A0:"\<A> \<subseteq> Pow X"
   show "upcl X \<A> = upcl X (upcl X \<A>)"
  proof
    show "upcl X \<A>  \<subseteq> upcl X (upcl X \<A>)"
    proof
      fix E assume "E \<in>upcl X \<A>"
      then show "E \<in> upcl X (upcl X \<A>)" by (simp add: upcl_closed upcl_ref)
    qed
    show "upcl X (upcl X \<A>) \<subseteq> upcl X \<A> "
    proof
      fix E assume A1:"E \<in> upcl X (upcl X \<A>)"
      then obtain A where "A \<in> upcl X \<A>" and "A \<subseteq> E"     using upcl_memE2 by blast
      then obtain B where "B \<in> \<A>" and "B \<subseteq> A"    using upcl_memE2 by blast
      also obtain "E \<in> Pow X" and "B \<in> \<A>" and "B \<subseteq> E"   using A1 \<open>A \<subseteq> E\<close> calculation(1,2)upcl_memE1 by blast
      then show "E \<in>upcl X \<A>"  by (simp add: upcl_memI2)
    qed
  qed
qed


lemma upcl_upclosed2:
  "\<lbrakk>\<A> \<subseteq> Pow X\<rbrakk> \<Longrightarrow> upclosed X (upcl X \<A>)"
proof-
  assume A0:"\<A> \<subseteq> Pow X"
  show "upclosed X (upcl X \<A>)"
  proof(rule upclosedI)
    show "upcl X \<A> \<subseteq> Pow X" by (simp add: upcl_closed)
    show "\<And>A B. A \<in> upcl X \<A> \<Longrightarrow> B \<in> Pow X \<Longrightarrow> A \<subseteq> B \<Longrightarrow> B \<in> upcl X \<A>" using upcl_upclosed1 by blast
  qed
qed




lemma upcl_fp:
  "\<lbrakk>\<A> \<subseteq> Pow X; upclosed X \<A>\<rbrakk> \<Longrightarrow>upcl X \<A>=\<A>"
proof-
  assume sub:"\<A> \<subseteq> Pow X" and up:"upclosed X \<A>"
  show "upcl X \<A>=\<A>"
  proof
    show "upcl X \<A> \<subseteq> \<A>"
    proof
      fix E assume "E \<in> upcl X \<A>"  
      then obtain "E \<in> Pow X" and "(\<exists>A \<in> \<A>. A \<subseteq> E)" by (simp add: upcl_mem_iff)
      show "E \<in> \<A>"   using \<open>E \<in> Pow X\<close> \<open>\<exists>A\<in>\<A>. A \<subseteq> E\<close> up upclosedE2 by blast
    qed
    show " \<A>\<subseteq> upcl X \<A>" by (simp add: sub upcl_ext)
  qed
qed


lemma up_cl_preceq:
  "\<A> \<subseteq> Pow X \<Longrightarrow> \<A> \<preceq> upcl X \<A>"
  by (simp add: sub_preceq upcl_ext)

lemma up_cl_preceq2:
  "\<A> \<subseteq> Pow X \<Longrightarrow>  upcl X \<A> \<preceq> \<A>"
  by(auto simp add:preceq_def upcl_def)

lemma preceq_iff:
  "\<lbrakk>\<A> \<subseteq> Pow X; \<B> \<subseteq> Pow X\<rbrakk> \<Longrightarrow> \<A> \<preceq> \<B> \<longleftrightarrow> \<A> \<subseteq> upcl X \<B> "
proof-
  assume sub1:"\<A> \<subseteq> Pow X" and sub2:"\<B> \<subseteq> Pow X" 
  show "\<A> \<preceq> \<B> \<longleftrightarrow> \<A> \<subseteq> upcl X \<B>"
  proof
    assume L:"\<A> \<preceq> \<B>"
    show "\<A> \<subseteq> upcl X \<B>"
    proof
      fix E assume "E \<in> \<A>"
      then obtain B where "B \<in> \<B>" and "B \<subseteq> E"   using L preceqE by blast
      also obtain "E \<in> Pow X" and "B \<in> \<B>" and "B \<subseteq> E"  using \<open>E \<in> \<A>\<close> calculation(1,2) sub1 by blast 
      then show "E \<in> upcl X \<B>" by(rule upcl_memI2)
    qed
    next
    assume R:"\<A> \<subseteq> upcl X \<B>"
    show "\<A> \<preceq> \<B>"
    proof(rule preceqI)
      fix A assume "A \<in> \<A>"
      then obtain "A \<in> upcl X \<B>" using R by blast
      then show "\<exists>B\<in>\<B>. B \<subseteq> A"   by (simp add: upcl_memE2)
    qed
  qed
qed

lemma preceq_of_iso:
  assumes sub1:"\<A> \<subseteq> Pow X"  and sub2:"\<B> \<subseteq> Pow X" and up:"upclosed X \<B>"
  shows "\<A> \<preceq>\<B> \<longleftrightarrow>\<A>  \<subseteq> \<B> "
proof
  assume L:"\<A> \<preceq> \<B>"
  show "\<A>  \<subseteq> \<B>"
  proof
    fix A assume "A \<in> \<A>"
    then obtain B where "B \<in> \<B>" and "B \<subseteq> A"  using L preceqE by blast
    also obtain "A \<in> Pow X" and "B \<in> \<B>" and "B \<subseteq> A"  using \<open>A \<in> \<A>\<close> calculation(1,2) sub1 by blast 
    then show "A \<in> \<B>"  using up upclosedE2 by blast 
  qed
  next
  assume R: "\<A>  \<subseteq> \<B>"
  show "\<A> \<preceq> \<B>" by (simp add: R sub_preceq)
qed

  

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

abbreviation filters_on where
  "filters_on X \<equiv> {\<F>. fil X \<F>}"

abbreviation pfilters_on where
  "pfilters_on X \<equiv> {\<F>. pfil X \<F>}"

abbreviation filter_filters where
  "filter_filters X \<A> \<equiv> {\<F>. \<A> \<subseteq> \<F> \<and> fil X \<F>}"
           
abbreviation filter_pfilters where
  "filter_pfilters X \<A> \<equiv> {\<F>. \<A> \<subseteq> \<F> \<and> pfil X \<F>}"

lemma filI:
  "\<lbrakk>\<F>  \<noteq> {}; \<F> \<subseteq> Pow X; (\<And>A F. \<lbrakk>A \<in> Pow X; F \<in>  \<F>; F \<subseteq> A\<rbrakk> \<Longrightarrow> A \<in>  \<F>); (\<And>F1 F2. \<lbrakk>F1 \<in>  \<F>; F2 \<in>  \<F>\<rbrakk> \<Longrightarrow> F1 \<inter> F2 \<in>  \<F>)\<rbrakk> \<Longrightarrow> fil X \<F>"
  by (metis fil_def)

lemma pfilI:
  "\<lbrakk>\<F>  \<noteq> {}; \<F> \<subseteq> Pow X; (\<And>A F. \<lbrakk>A \<in> Pow X; F \<in>  \<F>; F \<subseteq> A\<rbrakk> \<Longrightarrow> A \<in>  \<F>); (\<And>F1 F2. \<lbrakk>F1 \<in>  \<F>; F2 \<in>  \<F>\<rbrakk> \<Longrightarrow> F1 \<inter> F2 \<in>  \<F>);\<F> \<noteq> Pow X\<rbrakk> \<Longrightarrow> pfil X \<F>"
  by (metis pfil_def)



lemma pfil_fil:
  "pfil X \<F> \<Longrightarrow> fil X \<F>"
  by (simp add: fil_def pfil_def)

lemma fil_pfil:
  "fil X \<F> \<Longrightarrow>\<F> \<noteq> Pow X \<Longrightarrow> pfil X \<F> "
  by (simp add: fil_def pfil_def)

lemma pfilI2:
  "\<lbrakk>fil X \<F>; {}  \<notin> \<F>\<rbrakk> \<Longrightarrow> pfil X \<F>"
proof-
  assume f:"fil X \<F>" and ne:"{} \<notin> \<F>"
  also obtain "\<F> \<noteq> Pow X"  using ne by blast
  then show "pfil X \<F>" by (simp add: f fil_pfil)
qed    

lemma filE1:
  "fil X \<F> \<Longrightarrow> \<F> \<subseteq> Pow X"
  by (simp add: fil_def)            

lemma pfilE1:
  "pfil X \<F> \<Longrightarrow> \<F> \<subseteq> Pow X"
  by (simp add: pfil_def)

lemma filE2:
  "fil X \<F> \<Longrightarrow> (\<And>A F. \<lbrakk>A \<in> Pow X; F \<in>  \<F>; F \<subseteq> A\<rbrakk> \<Longrightarrow> A \<in>  \<F>)"
  using fil_def by blast    

lemma pfilE2:
  "pfil X \<F> \<Longrightarrow> (\<And>A F. \<lbrakk>A \<in> Pow X; F \<in>  \<F>; F \<subseteq> A\<rbrakk> \<Longrightarrow> A \<in>  \<F>)"
  using filE2 pfil_fil by blast
  

lemma filE3:
  "fil X \<F> \<Longrightarrow>  (\<And>F1 F2. \<lbrakk>F1 \<in>  \<F>; F2 \<in>  \<F>\<rbrakk> \<Longrightarrow> F1 \<inter> F2 \<in>  \<F>)"
proof-
  assume f:"fil X \<F>"
  show "\<And>F1 F2. \<lbrakk>F1 \<in>  \<F>; F2 \<in>  \<F>\<rbrakk> \<Longrightarrow> F1 \<inter> F2 \<in>  \<F>"
  proof-
    fix F1 F2 assume m1:"F1 \<in>  \<F>" and m2:"F2 \<in>  \<F>"
    then obtain "F1 \<in> \<F> \<and> F2 \<in> \<F>" by auto
    then show "F1 \<inter> F2 \<in>  \<F>" using f fil_def[of X \<F>]  by auto 
  qed
qed


lemma pfilE3:
  "pfil X \<F> \<Longrightarrow>  (\<And>F1 F2. \<lbrakk>F1 \<in>  \<F>; F2 \<in>  \<F>\<rbrakk> \<Longrightarrow> F1 \<inter> F2 \<in>  \<F>)"
  using filE3 pfil_fil by blast

lemma filE4:
  "fil X \<F> \<Longrightarrow>   \<F> \<noteq> {}"
  using fil_def by blast

lemma pfilE4:
  "pfil X \<F> \<Longrightarrow>   \<F> \<noteq> {}"
  using pfil_def by blast

lemma filE5:
  "fil X \<F> \<Longrightarrow>  X \<in> \<F>"
proof-
  assume f:"fil X \<F>"
  then obtain F where "F \<in> \<F>" using filE4 by fastforce 
  then obtain "F \<subseteq> X" using f filE1 by auto
  then obtain "X \<in> Pow X" and "F \<in> \<F>" and "F \<subseteq> X"  using \<open>F \<in> \<F>\<close> by blast
  then show "X \<in> \<F>" using f filE2 by blast
qed

lemma pfilE5:
  "pfil X \<F> \<Longrightarrow>  X \<in> \<F>"
  by (simp add: filE5 pfil_fil)

lemma pfilE6:
  "pfil X \<F> \<Longrightarrow>  \<F> \<noteq> Pow X"
  by (simp add: pfil_def)

lemma pfilE7:
  "pfil X \<F> \<Longrightarrow>  {} \<notin> \<F>"
proof-
  assume f:"pfil X \<F>"
  show " {} \<notin> \<F>"
  proof(rule ccontr)
    assume "\<not> ({} \<notin> \<F>)" then obtain cont:"{} \<in> \<F>" by simp
    then have "\<F>=Pow X"
    proof-
      show "\<F> = Pow X"
      proof
        show "\<F> \<subseteq> Pow X"  using f pfilE1 by auto
        next
        show "Pow X \<subseteq> \<F> "
        proof
          fix E assume "E \<in> Pow X"
          then obtain"E \<in> Pow X" and  "{} \<in> \<F>" and "{} \<subseteq> E"        by (simp add: cont)
          then show "E \<in> \<F>"    using f pfilE2 by blast
        qed
    qed
  qed
  then show False by (simp add: f pfilE6)
  qed
qed


lemma fil_upcl:
  "fil X \<F> \<Longrightarrow> upclosed X \<F>"
proof-
  assume f:"fil X \<F>"
  show "upclosed X \<F>"
  proof(rule upclosedI)
    show "\<F> \<subseteq> Pow X"   by (simp add: f filE1)
    show "\<And>A B. A \<in> \<F> \<Longrightarrow> B \<in> Pow X \<Longrightarrow> A \<subseteq> B \<Longrightarrow> B \<in> \<F>"   using f filE2 by blast
  qed
qed
    

lemma pfil_upcl:
  "pfil X \<F> \<Longrightarrow> upclosed X \<F>"
  by (simp add: fil_upcl pfil_fil)
        
lemma filter_inter:
  assumes ef:"\<forall>F. F \<in> EF \<longrightarrow> fil X F" and ne:"EF \<noteq> {}"
  shows "fil X (\<Inter>EF)"
proof(rule filI)
  obtain "X \<in> \<Inter>EF" by (simp add: ef filE5)
  then show "\<Inter> EF \<noteq> {}" by blast
  show "\<Inter> EF \<subseteq> Pow X" by (simp add: Inf_less_eq ef filE1 ne)
  show "\<And>A F. A \<in> Pow X \<Longrightarrow> F \<in> \<Inter> EF \<Longrightarrow> F \<subseteq> A \<Longrightarrow> A \<in> \<Inter> EF"  by (meson InterE InterI ef filE2)
  show " \<And>F1 F2. F1 \<in> \<Inter> EF \<Longrightarrow> F2 \<in> \<Inter> EF \<Longrightarrow> F1 \<inter> F2 \<in> \<Inter> EF"   using ef filE3 by fastforce
qed

lemma pfilter_inter:
  assumes ef:"\<forall>F. F \<in> EF \<longrightarrow> pfil X F" and ne:"EF \<noteq> {}"
  shows "pfil X (\<Inter>EF)"
proof(rule fil_pfil)
  obtain "fil X (\<Inter>EF)"  by (simp add: ef filter_inter ne pfil_fil)
  then show "fil X (\<Inter> EF)" using filter_inter by auto
  then show "\<Inter> EF \<noteq> Pow X"  using ef ne pfilE7 by fastforce  
qed


lemma subset_simp1:
  "\<lbrakk>A \<subseteq> X; B \<subseteq> X\<rbrakk> \<Longrightarrow> A \<subseteq> B \<longleftrightarrow> A \<inter> (X-B) = {}"
  by blast

lemma subset_simp2:
  "\<lbrakk>A \<subseteq> X; B \<subseteq> X\<rbrakk> \<Longrightarrow> A \<subseteq> (X-B)\<longleftrightarrow> A \<inter> B = {}"
  by blast

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
proof
  assume L:"E \<notin> \<A>"  show "{X-E}#\<A>"
    proof(rule ccontr)
      assume "\<not>{X-E}#\<A>" then obtain cont1:"\<not>(\<forall>B. B \<in> \<A> \<longrightarrow> (X-E) \<inter> B \<noteq> {})"  using mesh_single by blast
      then obtain B where "B \<in> \<A>" and "(X-E) \<inter> B = {}"  by fastforce
      then obtain "B \<subseteq> E"   using sub1 by fastforce
      then obtain "E \<in>\<A>" using \<open>B \<in> \<A>\<close> sub2 up upclosedE2 by blast
      show False   using L \<open>E \<in> \<A>\<close> by auto
    qed
  next
  assume R:"{X-E}#\<A>" show "E \<notin> \<A>"  using R by auto
qed


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

lemma grill_mem_upcl1:
  assumes sub1:"\<A> \<subseteq> Pow X" and sub2:"E \<in> Pow X" and up:"upclosed X \<A>" 
  shows "E \<in> \<A> \<longleftrightarrow> (X-E) \<notin> grill X \<A>" 
proof-
  have " (X-E) \<notin> grill X \<A> \<longleftrightarrow> \<not>(\<forall>A \<in> \<A>. A \<inter> (X-E) \<noteq> {})" by (meson Diff_subset Pow_iff grill_memI grillmesh1) 
  also have "...           \<longleftrightarrow> (\<exists>A \<in> \<A>. A \<inter> (X-E) = {})" by simp
  also have "...           \<longleftrightarrow> (\<exists>A \<in> \<A>. A \<subseteq> E)"  using Diff_triv sub1 subset_iff by fastforce
  then have "(X-E) \<notin> grill X \<A>  \<longleftrightarrow> (\<exists>A \<in> \<A>. A \<subseteq> E)"   by (simp add: \<open>(X - E \<notin> grill X \<A>) = (\<not> (\<forall>A\<in>\<A>. A \<inter> (X - E) \<noteq> {}))\<close>)
  then have "(X-E) \<notin> grill X \<A> \<Longrightarrow> E \<in> \<A>"  using sub2 up upclosed_memI1 by blast  
  then have "E \<in> \<A> \<Longrightarrow> (X-E) \<notin> grill X \<A>"   using \<open>(X - E \<notin> grill X \<A>) = (\<exists>A\<in>\<A>. A \<subseteq> E)\<close> by blast
  then show ?thesis
  using \<open>X - E \<notin> grill X \<A> \<Longrightarrow> E \<in> \<A>\<close> by blast
qed


lemma grill_mem_upcl2:
  assumes sub1:"\<A> \<subseteq> Pow X" and sub2:"E \<in> Pow X" and up:"upclosed X \<A>" 
  shows "(X-E) \<notin> \<A> \<longleftrightarrow> E \<in> grill X \<A>"
  using grill_mem_upcl1
  by (metis Diff_Diff_Int Diff_subset Pow_iff inf.absorb2 sub1 sub2 up)
 
lemma grill_mesh2:
  assumes sub1:"\<A> \<subseteq> Pow X" and up:"upclosed X \<A>" 
  shows "grill X \<A> = {E \<in> Pow X. (X-E) \<notin> \<A>}"      
  apply(simp add:grill_def)   
  using assms mem_Collect_eq apply(auto)
  by (simp add: grill_mem_upcl2 grillmesh1) 

lemma mesh_iff_gril:
  assumes sub1:"\<A> \<subseteq> Pow X "  and sub2:" \<B> \<subseteq> Pow X "
  shows "\<A>#\<B> \<longleftrightarrow> \<A> \<subseteq> grill X \<B>"
  apply(auto simp add:grill_def mesh_def subset_eq)
  using sub1 by(auto)

lemma grill_upcl1:
  assumes sub1:"\<A> \<subseteq> Pow X "
  shows grillup:"upclosed X (grill X \<A>)" 
  apply(rule upclosedI)
  apply (simp add: grill_sub)
  by (metis (no_types, lifting) CollectD CollectI grill_mesh mesh_sub sub1)


lemma grill_upcl2:
  assumes sub1:"\<A> \<subseteq> Pow X " and sub2:"E \<in> Pow X"
  shows "E \<in> grill X (grill X \<A>)  \<longleftrightarrow> E \<in>  upcl X \<A>"
proof-
  have "E \<in>  grill X (grill X \<A>) \<longleftrightarrow> (X-E) \<notin>  (grill X \<A>)"   by (meson grill_mem_upcl2 grill_sub grill_upcl1 sub1 sub2)
  also have "...  \<longleftrightarrow> \<not> (\<forall>A \<in> \<A>. A \<inter> (X-E) \<noteq> {})" by (meson Diff_subset PowI grill_memI grillmesh1)
  also have "...  \<longleftrightarrow> (\<exists>A \<in> \<A>. A \<inter> (X-E) = {}) " by simp
  also have "...  \<longleftrightarrow>  (\<exists>A \<in> \<A>. A \<subseteq> E)" by (metis Diff_eq_empty_iff Int_Diff PowD inf.order_iff sub1 subset_iff)
  also have "... \<longleftrightarrow>  E \<in>  upcl X \<A>" using  upcl_mem_iff sub2 by blast
  then show ?thesis
  using calculation by blast
qed

lemma refined_pfil_mesh:
  assumes pf1:"pfil X \<F>" and pf2:" pfil X \<G>" and pr:" \<F> \<preceq> \<G> "
  shows  "\<F>#\<G> "
proof(rule ccontr)
  assume  "\<not> \<F>#\<G> " then obtain F G where f1:"F \<in> \<F>" and g1:"G \<in> \<G>" and fg:"F \<inter> G = {}" using mesh_def by blast
  obtain "\<F> \<subseteq> Pow X" and  "\<G> \<subseteq> Pow X" and "upclosed X \<G>" by (simp add: pf1 pf2 pfilE1 pfil_upcl)
  then have "\<F> \<subseteq> \<G>" using pr preceq_of_iso[of \<F> X \<G>] by blast
  then obtain "F \<in> \<G>"  using f1 by blast
  then have "{} \<in>  \<G>"  using fg g1 pf2 pfilE3[of X \<G> F G] by auto
  then show False  using pf2 pfilE7 by blast  
qed

lemma finer_pfilters1:
  assumes ne:"\<C> \<noteq> {}" and "subset.chain (filter_pfilters X \<F>) \<C>"
  shows "\<Union>\<C> \<in> filter_pfilters X \<F>"
proof(auto)
  let ?U="\<Union>\<C>"
  have B0:"\<And>C. C \<in> \<C> \<Longrightarrow> pfil X C \<and> \<F> \<subseteq> C" by (metis (no_types, lifting) CollectD assms(2) in_mono subset_chain_def)
  have B1:"\<And>C1 C2. \<lbrakk>C1 \<in> \<C>;C2 \<in> \<C>\<rbrakk> \<Longrightarrow> C1 \<subseteq> C2 \<or> C2 \<subseteq> C1"  by (meson assms(2) subset_chain_def)
  show "\<And>F. F \<in> \<F> \<Longrightarrow> \<exists>C\<in>\<C>. F \<in> C" using B0 ne by blast
  show "pfil X (?U)"
  proof(rule pfilI)
    show "?U \<noteq> {}"   using B0 ne pfilE4 by fastforce
    show "?U \<subseteq> Pow X"  by (simp add: B0 Sup_le_iff pfilE1)
    show "\<And>A F. A \<in> Pow X \<Longrightarrow> F \<in> ?U \<Longrightarrow> F \<subseteq> A \<Longrightarrow> A \<in> ?U"  by (meson B0 Union_iff pfilE2)
    show "\<And>F1 F2. F1 \<in> ?U \<Longrightarrow> F2 \<in> ?U\<Longrightarrow> F1 \<inter> F2 \<in>?U" 
    proof-
      fix F1 F2 assume "F1 \<in> ?U" and"F2 \<in> ?U"
      then obtain C1 C2 where "C1 \<in> \<C>" and "C2 \<in> \<C>" and "F1 \<in> C1" and "F2 \<in> C2" by blast
      then obtain "F1 \<inter> F2 \<in> C1 \<or> F1 \<inter> F2 \<in> C2" by (metis B0 B1 filE3 insert_Diff insert_subset pfil_fil) 
      then show "F1 \<inter> F2 \<in> ?U"   using \<open>C1 \<in> \<C>\<close> \<open>C2 \<in> \<C>\<close> by blast
    qed
    show "?U\<noteq> Pow X"  using B0 pfilE7 by force
 qed
qed


locale conv=
  fixes X::"'a set" and q::"('a set set \<times> 'a) set"

locale convergence=conv+
  assumes frel:"q \<subseteq> (pfilters_on X) \<times> X"
begin

lemma frel1:"fst`q \<subseteq> pfilters_on X" using frel by auto
lemma frel2:"snd`q \<subseteq> X" using frel by auto
lemma frel3:"\<forall>(\<F>, x) \<in> q. \<F> \<in> pfilters_on X \<and> x \<in> X" using frel by auto
lemma frel4:"\<forall>(\<F>, x) \<in> q. pfil X \<F> \<and> x \<in> X" using frel by auto
lemma frel5:"\<forall>(\<F>, x) \<in> q. fil X \<F> \<and> x \<in> X" using frel pfil_fil by auto


end

locale iso_conv=conv+
  assumes iso:"\<And>x F G. \<lbrakk>(F, x) \<in> q; F \<preceq> G\<rbrakk> \<Longrightarrow> (\<G>, x) \<in> q "




end