theory Rel
  imports Main
begin


locale map = 
  fixes R X Y
  assumes graph[intro, simp]:"R \<subseteq> X \<times> Y"
begin

lemma graph_closed1:
  "(x, y) \<in> R \<Longrightarrow> x \<in> X \<and> y \<in> Y"
  using graph by blast

lemma graph_closed2:
  "y \<in> R``{x} \<Longrightarrow> x \<in> X \<and> y \<in> Y"
  using graph by blast

lemma image1:
  "R``X \<subseteq> Y"
  using graph_closed1 by force

lemma vimage1:
  "(converse R)``Y \<subseteq> X"
  using graph_closed1 by force

end

locale injective= map+
   assumes inj:"\<lbrakk>y \<in> R``{x1}; y \<in> R``{x2}\<rbrakk> \<Longrightarrow> x1=x2 "
begin

lemma inj2:
  "\<lbrakk>(x1, y)\<in> R; (x2, y)\<in> R\<rbrakk> \<Longrightarrow> x1=x2"
  by (simp add: inj)

lemma inj_contrapos:
  "\<lbrakk>x1 \<noteq> x2; y1 \<in> R``{x1}; y2 \<in> R``{x2}\<rbrakk> \<Longrightarrow> y1 \<noteq> y2"
  using inj by blast

lemma inj_contrapos2:
  "\<lbrakk>x1 \<noteq> x2; (x1, y1) \<in> R; (x2, y2) \<in> R\<rbrakk> \<Longrightarrow> y1 \<noteq> y2"
  using inj by blast

end
  
locale surjective = map +
  assumes sur:"\<forall>y \<in> Y. \<exists>x \<in> X. y \<in> R``{x}"
begin

lemma sur2:
  "\<forall>y \<in> Y. \<exists>x \<in> X. (x, y) \<in> R"
  using sur by auto

lemma sur_codomain:
  "R``X=Y"
  using image1 sur2 by auto

end

locale coinjective=map+
  assumes coinj:"\<lbrakk>y1 \<in> R``{x}; y2 \<in> R``{x}\<rbrakk>\<Longrightarrow>y1=y2"
begin

lemma coinj2:
  "\<lbrakk>(x, y1) \<in> R; (x, y2)\<in>R \<rbrakk>\<Longrightarrow> y1=y2"
  by (simp add: coinj)

lemma coinj_contrapos:
  "\<lbrakk>y1 \<noteq> y2; y1 \<in> R``{x1}; y2 \<in> R``{x2} \<rbrakk>\<Longrightarrow> x1 \<noteq> x2 "
  using coinj by blast

lemma coinj_contrapos2:
  "\<lbrakk>y1 \<noteq> y2; (x1, y1) \<in> R; (x2, y2) \<in> R\<rbrakk> \<Longrightarrow> x1 \<noteq> x2"
  using coinj2 by blast

end

locale cosurj=map+
  assumes cosurj:"\<forall>x \<in> X. \<exists>y \<in> Y. y \<in> R``{x}"
begin

lemma cosurj2:
  "\<forall>x \<in> X. \<exists>y \<in> Y. (x, y)\<in>R"
  using cosurj by auto

end

end