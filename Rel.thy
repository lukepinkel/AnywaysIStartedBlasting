theory Rel
  imports Main
begin

section Settings
hide_const top bot
hide_const(open) List.list.Nil
no_notation List.list.Nil ("[]")  
no_notation Cons (infixr "#" 65) 
hide_type list
hide_const rev
declare [[show_consts,show_sorts,show_types, show_results]]

definition ubd::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set"  where
  "ubd R X A \<equiv> {b \<in> X. (\<forall>x. x\<in> A \<inter> X \<longrightarrow> (x,b)\<in>R)}"

lemma ubd_memI:
  "\<lbrakk>\<And>x. x \<in> A \<Longrightarrow> (x,b)\<in>R; b \<in> X\<rbrakk> \<Longrightarrow>b \<in> ubd R X A "
  by (simp add: ubd_def)

lemma ubd_memE:
  "b \<in> ubd R X A \<Longrightarrow> (\<forall>x. x\<in> A \<inter> X \<longrightarrow> (x,b)\<in>R)  \<and> b \<in> X"
  by (simp add: ubd_def)

lemma ubd_sub_space:
  "ubd R X A \<subseteq> X"
  by (simp add: ubd_def)

lemma ubd_ant:
  "A \<subseteq> B \<Longrightarrow> ubd R X B \<subseteq> ubd R X A"
  by (simp add: subset_eq ubd_def)

lemma ubd_empty:
  "ubd R X {} = X"
  by (simp add: ubd_def)

definition lbd::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set"  where
  "lbd R X A \<equiv> {b \<in> X. (\<forall>x. x\<in> A \<inter> X \<longrightarrow> (b,x)\<in>R)}"

lemma lbd_memI:
  "\<lbrakk>\<And>x. x \<in> A \<Longrightarrow> (b,x)\<in>R; b \<in> X\<rbrakk> \<Longrightarrow>b \<in> lbd R X A "
  by (simp add: lbd_def)

lemma lbd_memE:
  "b \<in> lbd R X A \<Longrightarrow> (\<forall>x. x\<in> A \<inter> X \<longrightarrow> (b,x)\<in>R)  \<and> b \<in> X"
  by (simp add: lbd_def)

lemma lbd_sub_space:
  "lbd R X A \<subseteq> X"
  by (simp add: lbd_def)

lemma lbd_ant:
  "A \<subseteq> B \<Longrightarrow> lbd R X B \<subseteq> lbd R X A"
  by (simp add: subset_eq lbd_def)

lemma lbd_empty:
  "lbd R X {} = X"
  by (simp add: lbd_def)

abbreviation dual where "dual R \<equiv> (converse R)"

lemma upper_dual:
  "ubd (dual R) X A = lbd R X A"
  by(simp add:ubd_def lbd_def)

lemma lower_dual:
  "lbd (dual R) X A = ubd R X A"
  by(simp add:ubd_def lbd_def)

definition is_lst::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool" where
  "is_lst R A m \<equiv>  m \<in> A \<and> (\<forall>x. x\<in> A \<longrightarrow> (m,x)\<in>R)"

lemma is_lstE:
  "is_lst R A m \<Longrightarrow> m \<in> A \<and> (\<forall>x. x \<in> A \<longrightarrow> (m,x)\<in>R)"
  by(simp add:is_lst_def)

definition is_grt::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool" where
  "is_grt R A m \<equiv>  m \<in> A \<and> (\<forall>x. x\<in> A \<longrightarrow> (x,m)\<in>R)"

lemma is_grtE:
  "is_grt R A m \<Longrightarrow> m \<in> A \<and> (\<forall>x. x \<in> A \<longrightarrow> (x,m)\<in>R)"
  by(simp add:is_grt_def)




end
