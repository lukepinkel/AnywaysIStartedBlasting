theory Prod
  imports Main "HOL-Library.Nat_Bijection" "HOL-Library.FuncSet" "HOL-Library.Countable_Set"
begin

declare [[show_types]]

definition CartesianProduct::"'I set \<Rightarrow> ('I \<Rightarrow> 'X set) \<Rightarrow> ('I \<Rightarrow> 'X) set" where
  "CartesianProduct I X = {f::('I \<Rightarrow> 'X). \<forall>i \<in> I. (f i) \<in> (X i)}"

abbreviation Prod::"'I set \<Rightarrow> ('I \<Rightarrow> 'X set) \<Rightarrow> ('I \<Rightarrow> 'X) set" where
  "Prod I X \<equiv> CartesianProduct I X"

lemma prod_mem:
  "f \<in> Prod I X \<longleftrightarrow> (\<forall>i \<in> I. (f i) \<in> (X i))"
  by (simp add: CartesianProduct_def)


lemma axiom_of_choice_lol:
  fixes I::"'I set"
  fixes X::"'I \<Rightarrow> 'X set"
  assumes A0:"I \<noteq> {}" and A1:"\<forall>i \<in> I. X i \<noteq> {}"
  shows "Prod I X \<noteq> {}"
proof-
  define f where "f=(\<lambda>i. SOME x. (x \<in> (X i)))"
  have "f \<in> Prod I X"
    by (metis A1 equals0I f_def prod_mem verit_sko_ex')
  show ?thesis
    using \<open>(f::'I \<Rightarrow> 'X) \<in> Prod.Prod (I::'I set) (X::'I \<Rightarrow> 'X set)\<close> by auto
qed

lemma projection_is_surjective:
  fixes I::"'I set"
  fixes X::"'I \<Rightarrow> 'X set"
  assumes A0:"I \<noteq> {}" and 
          A1:"\<forall>i \<in> I. X i \<noteq> {}" 
  shows "\<forall>i \<in> I. \<forall>x \<in> (X i). \<exists>f \<in> (Prod I X). (f i) = x"
proof-
  have B0:"Prod I X \<noteq> {}"
    by (simp add: A0 A1 axiom_of_choice_lol)
  have B1:"\<forall>i \<in> I. \<forall>x \<in> (X i). \<exists>f \<in> (Prod I X). (f i) = x"
  proof
    fix i assume A2:"i \<in> I"
    show B2:"\<forall>x \<in> (X i). \<exists>f \<in> (Prod I X). (f i) = x"
    proof
      fix x assume A3:"x \<in> (X i)"
      obtain f0 where B3:"f0 \<in> Prod I X"
        using B0 by blast
      define f where "f=(\<lambda>j. if j=i then x else (f0 j))"
      have B4:"f \<in> Prod I X"
        by (metis A3 B3 f_def prod_mem)
      have B5:"f i = x"
        by (simp add: f_def)
      show "\<exists>f \<in> (Prod I X). (f i) = x"
        using B4 B5 by blast
      qed
    qed
  show ?thesis
    using B1 by blast
qed

lemma comp_inverse:
  "UNIV-(UNIV-X) = X"
  by (simp add: Diff_Diff_Int)

lemma union_of_intersections:
  fixes I::"'I set"
  fixes J::"'I \<Rightarrow> 'J set"
  fixes X::"'I \<Rightarrow> 'J \<Rightarrow> 'X set"
  assumes A0:"I \<noteq> {}" 
  shows "(\<Union>i\<in>I. (\<Inter>j\<in>(J i). (X i j))) = (\<Inter>f\<in>(Prod I J). (\<Union>i \<in> I. (X i (f i))))"
proof-
  let ?S="\<Union>i \<in> I. J i"
  let ?P="Prod I J"
  have B0:"\<forall>f. f \<in> ?P \<longleftrightarrow> (\<forall>i \<in> I. (f i) \<in> (J i))"
    by (simp add: prod_mem)
  have B1:"\<forall>x. x \<in> (\<Union>i\<in>I. (\<Inter>j\<in>(J i). (X i j))) \<longleftrightarrow> (\<exists>i \<in>I. x \<in>  (\<Inter>j\<in>(J i). (X i j)))"
    by blast
  have B2:"\<forall>x. x \<in> (\<Union>i\<in>I. (\<Inter>j\<in>(J i). (X i j))) \<longleftrightarrow> (\<exists>i \<in> I. \<forall>j \<in> (J i). x \<in> (X i j))"
    by simp
  have B3:"\<forall>x \<in> (\<Union>i\<in>I. (\<Inter>j\<in>(J i). (X i j))). (\<exists>i \<in> I. \<forall>f \<in> ?P. x \<in> (X i (f i)))"
  proof
    fix x assume B3A0:"x \<in> (\<Union>i\<in>I. (\<Inter>j\<in>(J i). (X i j)))"
    obtain i where "i \<in>I \<and>  x \<in>  (\<Inter>j\<in>(J i). (X i j))"
      using B3A0 by blast
    have B30:"\<forall>f \<in> ?P. \<forall>i \<in> I. ((f i) \<in> (J i))"
      by (simp add: prod_mem)  
    show "(\<exists>i \<in> I. \<forall>f \<in> ?P. x \<in> (X i (f i) ))"
      using B30 B3A0 by auto
  qed
  have B4:"\<forall>x. x \<in> (\<Union>i\<in>I. (\<Inter>j\<in>(J i). (X i j))) \<longrightarrow>  ( \<forall>f \<in> ?P. \<exists>i \<in> I.  x \<in> (X i (f i)))"
    using B0 by blast
  have B5:"\<forall>x. x \<in> (\<Union>i\<in>I. (\<Inter>j\<in>(J i). (X i j))) \<longrightarrow> (\<forall>f \<in> ?P. x \<in> (\<Union>i \<in> I. (X i (f i))))"
    by (simp add: B4)
  have B6:" (\<Union>i\<in>I. (\<Inter>j\<in>(J i). (X i j))) \<subseteq> (\<Inter>f\<in>?P. (\<Union>i \<in> I. (X i (f i))))"
    using B5 by blast
  have B7:"\<And>x. x \<notin> (\<Union>i\<in>I. (\<Inter>j\<in>(J i). (X i j))) \<longrightarrow> x \<notin> (\<Inter>f\<in>?P. (\<Union>i \<in> I. (X i (f i))))"
  proof
    fix x assume B7A0:"x \<notin> (\<Union>i\<in>I. (\<Inter>j\<in>(J i). (X i j)))"
    have B70:"\<forall>i \<in> I. x \<notin>(\<Inter>j\<in>(J i). (X i j))"
      using B7A0 by blast
    have B71:"\<forall>i \<in> I. {j. j\<in> (J i) \<and> (x \<notin> (X i j))} \<noteq> {}"
      using B70 by fastforce
    define K where "K=(\<lambda>(i::('I)).  {j. j\<in> (J i) \<and> (x \<notin> (X i j))})"
    define f where "f=( \<lambda>(i::('I)). SOME j. j \<in> (K i))"
    have B72:"f \<in> ?P"
      by (metis (mono_tags, lifting) B0 B71 Collect_empty_eq K_def f_def mem_Collect_eq verit_sko_ex')
    have B73:"\<forall>i \<in> I. x \<notin> (X i (f i))"
      by (metis (mono_tags, lifting) B71 Collect_empty_eq K_def f_def mem_Collect_eq someI_ex)
    have B74:"x \<notin>  (\<Union>i \<in> I. (X i (f i)))"
      using B73 by blast
    show "x \<notin> (\<Inter>f\<in>?P. (\<Union>i \<in> I. (X i (f i))))"
      using B72 B74 by blast
  qed
  have B8:"\<forall>x. x \<notin> (\<Union>i\<in>I. (\<Inter>j\<in>(J i). (X i j))) \<longrightarrow> x \<notin> (\<Inter>f\<in>?P. (\<Union>i \<in> I. (X i (f i))))"
    using B7 by blast
  have B9:"(\<Inter>f\<in>?P. (\<Union>i \<in> I. (X i (f i)))) \<subseteq>  (\<Union>i\<in>I. (\<Inter>j\<in>(J i). (X i j)))"
    using B8 by blast
  with B6 B9 show ?thesis
    by blast
qed
   


lemma intersection_of_unions:
  fixes I::"'I set"
  fixes J::"'I \<Rightarrow> 'J set"
  fixes X::"'I \<Rightarrow> 'J \<Rightarrow> 'X set"
  assumes A0:"I \<noteq> {}" 
  shows "(\<Inter>i \<in> I. (\<Union>j \<in> (J i). (X i j))) = (\<Union>f\<in>(Prod I J). (\<Inter>i\<in> I. (X i (f i))))"
proof-
  define Z where "Z= (\<lambda>(i::('I)) (j::('J)). (UNIV-(X i j)))"
  have B0:"(\<Union>i \<in> I. (\<Inter>j \<in> (J i). (Z i j))) = (\<Inter>f \<in> (Prod I J). (\<Union>i \<in> I. (Z i (f i))))"
    by (simp add: assms union_of_intersections)
  have B1:"UNIV-(\<Union>i \<in> I. (\<Inter>j \<in> (J i). (Z i j))) = UNIV-(\<Inter>f \<in> (Prod I J). (\<Union>i \<in> I. (Z i (f i))))"
    using B0 by presburger
  have B2:"(\<Inter>i \<in> I. (UNIV -  (\<Inter>j \<in> (J i). (Z i j)))) = (\<Union>f \<in> (Prod I J). UNIV-(\<Union>i \<in> I. (Z i (f i))))"
    using B1 by force
  have B3:"(\<Inter>i \<in> I. (\<Union>j \<in> (J i). (UNIV-(Z i j)))) =  (\<Union>f \<in> (Prod I J). (\<Inter>i \<in> I. UNIV-(Z i (f i))))"
    using B1 by auto
  have B4:"(\<Inter>i \<in> I. (\<Union>j \<in> (J i). UNIV-(UNIV-(X i j)))) = (\<Union>f\<in>(Prod I J). (\<Inter>i\<in> I. UNIV-(UNIV-(X i (f i)))))"
    using B3 Z_def by blast
  have B5:"(\<Inter>i \<in> I. (\<Union>j \<in> (J i). (X i j))) = (\<Union>f\<in>(Prod I J). (\<Inter>i\<in> I. (X i (f i))))"
    proof -
      have "\<forall>X. (UNIV::'X set) - (UNIV - X) = X"
        by (simp add: comp_inverse)
      then show ?thesis
        using B4 by presburger
    qed
   with B5 show ?thesis
     by simp
qed

lemma cartesian_product_union_intersection:
  fixes I::"'I set"
  fixes J::"'I \<Rightarrow> 'J set"
  fixes X::"'I \<Rightarrow> 'J \<Rightarrow> 'X set"
  assumes A0:"I \<noteq> {}" and A1:"\<forall>i \<in> I. J i \<noteq> {}"
  shows "Prod I (\<lambda>i. (\<Union>j \<in> (J i). (X i j))) = (\<Union>f \<in> (Prod I J). (Prod I (\<lambda>i. (X i (f i)))))"
proof-
  define G where A2:"G=(\<lambda>i. (\<Union>j \<in> (J i). (X i j)))"
  define F where A3:"F=(\<lambda>f i. (X i (f i)))"
  let ?PIJ="Prod I J"
  let ?L="Prod I G"
  let ?R="(\<Union>f \<in>?PIJ. (Prod I (F f)))"
  have LR:"?L \<subseteq> ?R"
    proof-
      have LR0:"\<And>g. g \<in> ?L \<longrightarrow> g \<in> ?R"
        proof
          fix g assume LR0A0:"g \<in> ?L"
          have B0:"\<forall>i \<in> I. \<exists>j \<in> (J i). (g i) \<in> (X i j)"
            by (metis A2 LR0A0 UN_iff prod_mem)
          define H where A3:"H=(\<lambda>i. {j \<in> (J i). (g i) \<in> (X i j)})"
          have B1:"\<forall>i \<in> I. (H i) \<noteq> {}"
            using A3 B0 by auto
          define f where A4:"f=(\<lambda>i. SOME j. j \<in> (H i))"
          have B2:"\<forall>i \<in> I. (f i) \<in> (H i)"
            using A4 B1 some_in_eq by blast
          have B3:"f \<in> ?PIJ"
            using A3 B2 prod_mem by fastforce
          have B4:"g \<in> (Prod I (F f))"
            using A3 B2 \<open>F::('I \<Rightarrow> 'J) \<Rightarrow> 'I \<Rightarrow> 'X set \<equiv> \<lambda>(f::'I \<Rightarrow> 'J) i::'I. (X::'I \<Rightarrow> 'J \<Rightarrow> 'X set) i (f i)\<close> prod_mem by fastforce
          show "g \<in> ?R"
            using B3 B4 by blast
          qed
       show ?thesis
         using LR0 by blast
      qed
  have RL:"?R \<subseteq> ?L"
   proof-
      have RL0:"\<And>g. g \<in> ?R \<longrightarrow> g \<in> ?L"
        proof
          fix g assume A5:"g \<in> ?R"
          obtain f where A6:"f \<in> ?PIJ \<and> (\<forall>i \<in> I. (g i) \<in> (X i ((f i))))"
            using A3 A5 prod_mem by force
          have B5:"\<forall>i \<in> I. (\<exists>j \<in> (J i). (f i) = j)"
            by (meson A6 prod_mem)
          have B6:"\<forall>i \<in> I. (\<exists>j \<in> (J i). (g i) \<in> (X i j))"
            using A6 B5 by blast
          show "g \<in> ?L"
            by (simp add: A2 B6 prod_mem)
          qed
      show ?thesis
        using RL0 by blast
    qed
  show ?thesis
    using A2 A3 LR RL by fastforce
qed      
  

lemma cartesian_product_intersection_union:
  fixes I::"'I set"
  fixes J::"'I \<Rightarrow> 'J set"
  fixes X::"'I \<Rightarrow> 'J \<Rightarrow> 'X set"
  assumes A0:"I \<noteq> {}" and A1:"\<forall>i \<in> I. J i \<noteq> {}"
  shows "Prod I (\<lambda>i. (\<Inter>j \<in> (J i). (X i j))) = (\<Inter>f \<in> (Prod I J). (Prod I (\<lambda>i. (X i (f i)))))"
proof-
  define G where A2:"G=(\<lambda>i. (\<Inter>j \<in> (J i). (X i j)))"
  define F where A3:"F=(\<lambda>f i. (X i (f i)))"
  let ?PIJ="Prod I J"
  let ?L="Prod I G"
  let ?R="(\<Inter>f \<in>?PIJ. (Prod I (F f)))"
  have B0:"\<forall>g. g \<in> ?L \<longleftrightarrow> (\<forall>i \<in> I. \<forall>j \<in> (J i). (g i) \<in> (X i j))"
    by (simp add: \<open>G::'I \<Rightarrow> 'X set \<equiv> \<lambda>i::'I. \<Inter> ((X::'I \<Rightarrow> 'J \<Rightarrow> 'X set) i ` (J::'I \<Rightarrow> 'J set) i)\<close> prod_mem)
  have B1:"\<forall>g. g \<in> ?R \<longleftrightarrow> (\<forall>f \<in> ?PIJ. \<forall>i \<in> I. (g i) \<in> (X i (f i)))"
    by (simp add: A3 prod_mem)
  have B2:"\<forall>f. f \<in> ?PIJ \<longleftrightarrow> (\<forall>i \<in> I. (f i) \<in> (J i))"
    by (simp add: prod_mem)
  have LR:"?L \<subseteq> ?R"
    proof-
      have LR0:"\<And>g. g \<in> ?L \<longrightarrow> g \<in> ?R"
        proof
          fix g assume LR0A0:"g \<in> ?L"
          show "g \<in> ?R"
            by (metis B0 B1 LR0A0 prod_mem)
        qed
      show ?thesis
        using LR0 by blast
   qed
  have RL:"?R \<subseteq> ?L"
   proof-
      have RL0:"\<And>g. g \<in> ?R \<longrightarrow> g \<in> ?L"
        proof
          fix g assume A5:"g \<in> ?R"
          have RL0B0:"\<forall>f. f \<in> ?PIJ \<longrightarrow> (\<forall>i\<in>I. (g i) \<in> (X i (f i)))"
            by (meson A5 B1)
          have RL0B1:"\<forall>f \<in> ?PIJ. (\<forall>i \<in> I. (f i) \<in> (J i))"
            using B2 by fastforce
          have RL0B2:"(\<forall>i \<in> I. \<forall>j \<in> (J i). (g i) \<in> (X i j))"
          proof
            fix k assume "k \<in> I"
            show "\<forall>h \<in> (J k). (g k) \<in> (X k h)"
            proof
              fix h assume "h \<in> (J k)"
              show "(g k) \<in> (X k h)"
                by (metis A0 A1 RL0B0 \<open>(h::'J) \<in> (J::'I \<Rightarrow> 'J set) (k::'I)\<close> \<open>(k::'I) \<in> (I::'I set)\<close> projection_is_surjective)
            qed
          qed
          show "g \<in> ?L"
            using B0 RL0B2 by blast
      qed
      show ?thesis
        using RL0 by blast
  qed
  show ?thesis
    using A2 A3 LR RL by blast
qed

definition is_right_inv_of_on::"('b \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b set \<Rightarrow> bool" where
  "is_right_inv_of_on h f Y \<equiv> (\<forall>y. y \<in> Y \<longrightarrow> (f (h y) =y))"

definition cardlt::"'a set \<Rightarrow> 'b set \<Rightarrow> bool" where 
  "cardlt A B \<equiv> (\<exists>(f::('a \<Rightarrow> 'b)). inj_on f A \<and> f`A \<subseteq> B)"

definition cardgt::"'a set \<Rightarrow> 'b set \<Rightarrow> bool" where 
  "cardgt A B \<equiv> (A = {}) \<or> (\<exists>(f::('a \<Rightarrow> 'b)). f`A = B)"

lemma right_inv_imp_surj:
  assumes A0:"B \<noteq> {} \<and> A \<noteq> {}" and A1:"\<exists>h. (is_right_inv_of_on h f B) \<and> (range h \<subseteq> A)"
  shows "\<forall>b. b \<in>  B \<longrightarrow> (\<exists>a \<in> A. f a =b)"
  by (meson A1 is_right_inv_of_on_def range_subsetD)

lemma right_surj_imp_right_inv:
  assumes A0:"A \<noteq> {} \<and> B \<noteq> {} \<and> (\<forall>b. b \<in>  B \<longrightarrow> (\<exists>a \<in> A. f a =b))"
  shows "\<exists>h. (is_right_inv_of_on h f B) \<and> (range h \<subseteq> A)"
proof-
  have B0: "\<forall>b. b \<in> B \<longrightarrow> ((vimage f {b}) \<noteq> {})"
    using A0 by auto
  define a0 where  "a0= (SOME a. a \<in> A)"
  have B01:"a0 \<in> A"
    by (simp add: a0_def assms some_in_eq)
  define h where "h=(\<lambda>b. if b \<in> B then (SOME a. a \<in> A \<and> ((f a = b) )) else a0)"
  have B1:"\<And>b. b \<in> B \<longrightarrow> (f (h b) =b)"
  proof
    fix b assume A2:"b \<in> B" 
    show "(f (h b) =b)"
      by (smt (verit, best) A2 assms h_def verit_sko_ex')
  qed
  have B2:"(is_right_inv_of_on h f B)"
    by (simp add: B1 is_right_inv_of_on_def)
  have B3:"range h \<subseteq> A"
  proof
    fix x assume A3:"x \<in> range h"
    obtain b where B4:"h b = x"
      using A3 by blast
    have B5:"(h b) = (SOME a. (a \<in> A  \<and> ((f a = b)) )) \<or> (h b) =  a0"
      using h_def by auto
    show "x \<in> A"
    proof(cases "h b = a0")
      case True
      then show ?thesis
        by (simp add: B01 B4)
    next
      case False
      have B6:"(h b) = (SOME a. (a \<in> A \<and> (f a = b)))"
        using B5 False by auto
      then show ?thesis
        by (smt (verit, best) B4 False assms h_def someI_ex)
    qed
   qed
  show ?thesis
    using B2 B3 by blast
qed

lemma cardlt_obtains:
  assumes "cardlt A B" obtains f where "inj_on f A \<and> (f`A) \<subseteq> B"
  using assms by (meson cardlt_def)

lemma cardgt_obtains:
  assumes "A \<noteq> {}" and "cardgt A B" obtains f where "(f`A) = B"
  using assms by (meson cardgt_def)

lemma cardlt_imp_rev_cardgt:
  assumes A0:"A \<noteq> {}" and A1:"cardlt A B"
  shows "cardgt B A"
proof-
  obtain f where B0:"inj_on f A \<and> f`A \<subseteq>  B"
    by (metis A1 cardlt_def) 
  define finv where "finv=the_inv_into A f"
  define a0 where  "a0= (SOME a. a \<in> A)"
  define g where  "g=(\<lambda>y. (if y \<in> (f`A) then (finv y) else a0))"
  have B1:"\<forall>a. a \<in> A \<longrightarrow> g (f (a)) = a"
    by (simp add: B0 finv_def g_def the_inv_into_f_f)
  have B2:"(g`B) \<subseteq> A"
  proof
    fix a assume A2:"a \<in> (g`B)"
    obtain b where B3:"b \<in> B \<and> a=(g b)"
      using A2 by blast
    show "a \<in> A"
      by (simp add: A0 B0 B3 a0_def finv_def g_def some_in_eq the_inv_into_into)
  qed  
  have B4:"A \<subseteq> g`B"
    by (metis B0 B1 image_subset_iff subsetI)
  show ?thesis
    using B2 B4 cardgt_def by auto
qed

lemma cardgt_imp_rev_cardlt:
  assumes A0:"B \<noteq> {}" and A1:"cardgt B A"
  shows "cardlt A B"
proof-
  obtain g where B0:"(g`B)=A"
    by (meson A0 A1 cardgt_obtains)
  have B1:"\<forall>a. a \<in> A \<longrightarrow> (\<exists>b. b \<in> B \<and> g b = a) "
    using B0 by blast
  define b0 where "b0 = (SOME b. b \<in> B)"
  define f where "f = (\<lambda>x. if x \<in> A then (SOME y.  y \<in> B \<and> g y = x) else b0)"
  have B2:"inj_on f A"
  proof-
    have B4: "\<And>x1 x2. x1 \<in> A \<and> x2 \<in> A \<and> (f x1 = f x2) \<longrightarrow> x1 =x2"
    proof
      fix x1 x2 assume  A2:"x1 \<in> A \<and> x2 \<in> A \<and> (f x1 = f x2)"
      obtain y1 y2 where B3:"y1 \<in> B \<and> g y1 = x1 \<and> y2 \<in> B \<and> g y2 = x2"
        using A2 B1 by presburger
      show "x1 = x2"
        by (metis (mono_tags, lifting) A2 B3 f_def someI_ex)
    qed
    show ?thesis
      by (simp add: B4 inj_onI)
  qed
  have B5:"f`A \<subseteq> B"
  proof
    fix b assume A3:"b \<in> f`A"
    obtain a where B6:"a \<in> A \<and> b = f a"
      using A3 by blast
    show "b \<in> B"
      by (metis (full_types, lifting) B1 B6 f_def someI_ex)
  qed
  show ?thesis
    by (metis B2 B5 cardlt_def)
qed
  
      

definition is_countable :: "'a set \<Rightarrow> bool" where
  "is_countable I \<equiv> (\<exists>f::'a \<Rightarrow> nat. inj_on f I)"


definition is_countably_infinite :: "'a set \<Rightarrow> bool" where
  "is_countably_infinite I \<equiv> is_countable I \<and> infinite I"

definition even_odd_glue::"(nat \<Rightarrow> 'a) \<Rightarrow>  (nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a) " where
  "even_odd_glue f g  \<equiv> (\<lambda>(n::nat). (if (even n) then f(n div 2) else g((n-1) div 2)))"

lemma even_odd_glue_mem1:
  fixes f g::"(nat \<Rightarrow> 'a)" 
  assumes A0:"inj_on f (UNIV::nat set) \<and> inj_on g (UNIV::nat set)" and
           A1:"h=even_odd_glue f g" and 
           A2:"range f \<inter> range g = {}"
  shows "inj_on h (UNIV::nat set)"
proof-
  have B0:"\<And>(n1::nat) n2. h n1 = h n2 \<longrightarrow> n1 = n2"
  proof
     fix n1 n2 assume A3:"h n1 = h n2"
     show "n1=n2"
       by (smt (verit) A0 A1 A2 A3 Suc_1 Zero_not_Suc bit_eq_rec disjoint_iff even_odd_glue_def 
            injD nonzero_mult_div_cancel_left odd_two_times_div_two_nat range_eqI)
  qed
  show ?thesis
    by (simp add: B0 injI)
qed



lemma is_countably_infinite_imp:
  "is_countably_infinite I \<Longrightarrow> (is_countable I \<and> infinite I)" 
  by (simp add: is_countably_infinite_def)

lemma is_countably_infinite_if:
  " (is_countable I \<and> infinite I) \<Longrightarrow> is_countably_infinite I"
  by (simp add: is_countably_infinite_def)

lemma countable_subset:
  "is_countable A \<Longrightarrow> B \<subseteq> A \<Longrightarrow> is_countable B"
  apply(simp add: is_countable_def)
  using inj_on_subset by blast

lemma is_countable_imp_cardlt:
  assumes "is_countable I"
  shows "cardlt I (UNIV::nat set)"
  apply( simp add: cardlt_def)
  using assms is_countable_def by auto




lemma infinite_ge_countably_infinite:
  "infinite A \<longleftrightarrow> (cardlt (UNIV::nat set) A)" (is "?L \<longleftrightarrow> ?R")
proof
  assume L:?L show ?R
    by (simp add: L cardlt_def infinite_countable_subset)
  next
  assume R:?R show ?L
    by (meson R cardlt_def infinite_iff_countable_subset)
qed

lemma inj_countable_codom:
  "inj_on f A \<Longrightarrow> f`A=B \<Longrightarrow> is_countable B \<Longrightarrow> is_countable A"
  by (meson comp_inj_on is_countable_def)

lemma surj_countable_dom:
  "f`A=B \<Longrightarrow> is_countable A \<Longrightarrow> is_countable B"
  by (metis countable_subset inj_countable_codom inj_on_empty inj_on_iff_surj is_countable_def)

lemma countably_infinite_bij_nat:
  "is_countably_infinite A \<Longrightarrow> (\<exists>f. bij_betw f A (UNIV::nat set))"
  by (meson Schroeder_Bernstein infinite_iff_countable_subset is_countable_def is_countably_infinite_def subset_UNIV)

lemma countably_infinite_obtain_bij_nat:
  assumes "is_countably_infinite A"
  obtains f where "bij_betw f A (UNIV::nat set)"
  using assms countably_infinite_bij_nat by blast

lemma countably_infinite_bij_countably_infinite:
  assumes A0:"is_countably_infinite A" and A1:"bij_betw f A B"
  shows "is_countably_infinite B"
  by (metis A0 A1 bij_betw_finite bij_betw_imp_surj_on is_countably_infinite_def surj_countable_dom)


lemma disjoint_emb:
  fixes A B::"'a set" and u::"'b"
  assumes A0:"bij_betw f A B"
  shows "\<exists>g. bij_betw g A {b0. (\<exists>b \<in> B. b0=(u, b))}"
proof-
  define g where "g=(\<lambda>a. (u, f a))"
  have B0:"\<And>(x1::'a) (x2::'a). (x1 \<in> A \<and> x2 \<in> A \<and>  g x1 = g x2) \<longrightarrow> x1 = x2"
  proof
    fix x1 x2 assume A1:"(x1 \<in> A \<and> x2 \<in> A \<and>  g x1 = g x2)"
    obtain a1 a2 where B1:"g x1 = (u, (f a1)) \<and> g x2 = (u, (f a2))"
      by (simp add: g_def)
    have B1:"f a1 = f a2"
      using A1 B1 by auto
    show "x1 =x2"
      by (metis A1 Pair_inject assms bij_betw_inv_into_left g_def)
  qed
  have B1:"g ` A = {b0::'b \<times> 'a. \<exists>b::'a\<in>B. b0 = (u, b)}"
    by (smt (verit) Collect_cong assms bij_betw_iff_bijections g_def image_def)
  show ?thesis
  apply(auto simp add: bij_betw_def inj_on_def)
    using B0 B1 by blast
qed

lemma disjoint_emb_def:
  fixes A B::"'a set" and u::"'b" and f::"'a \<Rightarrow> 'a"
  defines "g \<equiv> (\<lambda>a. (u, f a))"
  assumes A0:"bij_betw f A B"
  shows "bij_betw g A {b0. (\<exists>b \<in> B. b0=(u, b))}"
proof-
  have B0:"\<And>(x1::'a) (x2::'a). (x1 \<in> A \<and> x2 \<in> A \<and>  g x1 = g x2) \<longrightarrow> x1 = x2"
  proof
    fix x1 x2 assume A1:"(x1 \<in> A \<and> x2 \<in> A \<and>  g x1 = g x2)"
    obtain a1 a2 where B1:"g x1 = (u, (f a1)) \<and> g x2 = (u, (f a2))"
      by (simp add: g_def)
    have B1:"f a1 = f a2"
      using A1 B1 by auto
    show "x1 =x2"
      by (metis A1 Pair_inject assms bij_betw_inv_into_left g_def)
  qed
  have B1:"g ` A = {b0::'b \<times> 'a. \<exists>b::'a\<in>B. b0 = (u, b)}"
    by (smt (verit) Collect_cong assms bij_betw_iff_bijections g_def image_def)
  show ?thesis
  apply(auto simp add: bij_betw_def inj_on_def)
    using B0 apply auto[1]
    using A0 bij_betwE g_def apply blast
    using B1 by blast
qed



lemma infinite_iso:
  "infinite A \<Longrightarrow> A \<subseteq> B \<Longrightarrow> infinite B"
  using finite_subset by blast

lemma is_countable_imp_countable:
  "is_countable A \<Longrightarrow> countable A"
  by (simp add: countable_def is_countable_def)

lemma is_countable_if_countable:
  "countable A \<Longrightarrow> is_countable A"
  by (simp add: countable_def is_countable_def)

lemma infinite_imp_infinite_union:
  "infinite A \<Longrightarrow> infinite B \<Longrightarrow> infinite (A \<union> B)"
  by simp

lemma cinfinite_union:
  assumes "is_countably_infinite A \<and> is_countably_infinite B"
  shows "is_countably_infinite (A \<union> B)"
proof-
  have "infinite (A \<union> B)"
    using assms is_countably_infinite_def by auto
  have "is_countable A \<and> is_countable B"
    by (simp add: assms is_countably_infinite_imp)
  have "countable A \<and> countable B"
    by (simp add: \<open>is_countable (A::'a set) \<and> is_countable (B::'a set)\<close> is_countable_imp_countable)
  have "countable (A \<union> B)"
    by (simp add: \<open>countable (A::'a set) \<and> countable (B::'a set)\<close>)
  have "is_countable (A \<union> B)"
    using \<open>countable ((A::'a set) \<union> (B::'a set))\<close> is_countable_if_countable by blast
  have "is_countably_infinite (A \<union> B)"
    using \<open>infinite ((A::'a set) \<union> (B::'a set))\<close> \<open>is_countable ((A::'a set) \<union> (B::'a set))\<close> is_countably_infinite_def by blast
  show ?thesis
    by (simp add: \<open>is_countably_infinite ((A::'a set) \<union> (B::'a set))\<close>)
qed

lemma empty_countable:
  "is_countable {}"
  by (simp add: is_countable_def)




end
