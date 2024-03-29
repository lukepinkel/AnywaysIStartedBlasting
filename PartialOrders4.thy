theory PartialOrders4
  imports Main
begin

section Prelims
subsection DeclarationsAndNotation
hide_const(open) List.list.Nil
no_notation List.list.Nil ("[]")  
no_notation Cons (infixr "#" 65) 
hide_type list
hide_const rev

declare [[show_types]]
declare [[show_sorts]]
declare [[show_consts]]

subsection Covering

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
    using \<open>(f::'I \<Rightarrow> 'X) \<in> Prod (I::'I set) (X::'I \<Rightarrow> 'X set)\<close> by auto
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

definition set_covers::"('b \<Rightarrow> 'a set) \<Rightarrow> 'b set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "set_covers X I E \<equiv> E \<subseteq> (\<Union>i \<in> I. X i)"

lemma covering_surj:
  fixes X::"'b \<Rightarrow> 'a set" and I::"'b set" and A::"'a set" and B::"'c set" and f::"'a \<Rightarrow> 'c" 
  assumes "f`A=B" and "set_covers X I A"
  shows "set_covers (\<lambda>i. f`(X i)) I B"
  apply(simp add:set_covers_def)
  by (metis assms(1) assms(2) set_covers_def image_UN image_mono)

subsection CompleteSemilatticeClass

class complete_semilattice_inf = semilattice_inf + Inf +
    assumes CInf_lower: "A \<noteq> {} \<Longrightarrow> x \<in> A \<Longrightarrow> Inf A \<le> x"
    and CInf_greatest: "A \<noteq> {} \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> z \<le> x) \<Longrightarrow> z \<le> Inf A"

class complete_semilattice_sup = semilattice_sup + Sup +
   assumes CSup_upper: "A \<noteq> {} \<Longrightarrow> x \<in> A \<Longrightarrow> x \<le>  Sup A"
    and CSup_least: "A \<noteq> {} \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> x \<le> z) \<Longrightarrow> Sup A \<le> z"


class complete_semilattice_inf_top = complete_semilattice_inf + top +
   assumes top_greatest: "a \<le> top"

class complete_semilattice_sup_bot = complete_semilattice_sup + bot +
   assumes bot_least: "bot \<le> a"


sublocale complete_semilattice_inf \<subseteq> semilattice_inf inf "(\<le>)" "(<)" ..

sublocale complete_semilattice_sup \<subseteq> semilattice_sup sup "(\<le>)" "(<)" ..

sublocale complete_lattice \<subseteq> semilattice_inf inf  "(\<le>)" "(<)" ..

sublocale complete_lattice \<subseteq> semilattice_sup sup  "(\<le>)" "(<)" ..

sublocale complete_boolean_algebra  \<subseteq> semilattice_inf inf  "(\<le>)" "(<)" ..

sublocale complete_boolean_algebra  \<subseteq> semilattice_sup sup "(\<le>)" "(<)" ..

sublocale complete_lattice \<subseteq> csls:complete_semilattice_sup
  apply unfold_locales
  apply (simp add: local.Sup_upper)
  using local.Sup_least by blast


sublocale complete_lattice \<subseteq> csli:complete_semilattice_inf
  apply unfold_locales
  apply (simp add: local.Inf_lower)
  using local.Inf_greatest by blast

sublocale complete_semilattice_inf_top \<subseteq> complete_semilattice_inf ..

sublocale complete_semilattice_sup_bot \<subseteq> complete_semilattice_sup ..

sublocale complete_lattice \<subseteq> complete_semilattice_inf_top
  apply unfold_locales
  by simp

sublocale complete_lattice \<subseteq> complete_semilattice_sup_bot
  apply unfold_locales
  by simp


subsection SemilatticeInfFinitaryOperator
(*

  Adapted from  https://isabelle.in.tum.de/library/HOL/HOL/Lattices_Big.html 

  and

  T. Nipkow, L.C. Paulson (2005), "Proof Pearl: Defining Functions over Finite Sets", 
  in J. Hurd, T. Melham (Eds.), Theorem Proving in Higher Order Logics, TPHOLs 2005, 
  LNCS, Vol. 3603, Springer, Berlin, Heidelberg. 
  Available at: https://doi.org/10.1007/11541868_25

*)

context semilattice_inf
begin


definition fInf::"'a set \<Rightarrow> 'a" where
  eq_fold1:"fInf A = the (Finite_Set.fold (\<lambda>x y. Some (case y of None \<Rightarrow> x | Some z \<Rightarrow> inf x z)) None A)"


lemma eq_fold2:
  assumes "finite A"
  shows "fInf (insert x A) = Finite_Set.fold inf x A"
  using assms eq_fold1 local.Inf_fin.eq_fold local.Inf_fin.eq_fold' by auto


lemma singleton [simp]:
  "fInf {x} = x"
  using eq_fold1 local.Inf_fin.eq_fold' local.Inf_fin.singleton by presburger

lemma insert_not_elem:
  assumes "finite A" and "x \<notin> A" and "A \<noteq> {}"
  shows "fInf (insert x A) = inf x (fInf A)"
  using assms(1) assms(3) eq_fold1 local.Inf_fin.eq_fold' local.Inf_fin.insert by presburger

lemma in_idem:
  assumes "finite A" and "x \<in> A"
  shows "inf x (fInf A) = fInf A"
  using assms(1) assms(2) eq_fold1 local.Inf_fin.eq_fold' local.Inf_fin.in_idem by presburger

lemma insert [simp]:
  assumes "finite A" and "A \<noteq> {}"
  shows "fInf (insert x A) = inf x (fInf A)"
  using assms by (cases "x \<in> A") (simp_all add: insert_absorb in_idem insert_not_elem)

lemma union:
  assumes "finite A" "A \<noteq> {}" and "finite B" "B \<noteq> {}"
  shows "fInf(A \<union> B) = inf (fInf A) (fInf B)"
  using assms by (induct A rule: finite_ne_induct) (simp_all add: ac_simps)

lemma remove:
  assumes "finite A" and "x \<in> A"
  shows "fInf A = (if A - {x} = {} then x else inf x (fInf(A - {x})))"
proof -
  from assms obtain B where "A = insert x B" and "x \<notin> B" by (blast dest: mk_disjoint_insert)
  with assms show ?thesis by simp
qed

lemma insert_remove:
  assumes "finite A"
  shows "fInf (insert x A) = (if A - {x} = {} then x else inf x (fInf(A - {x})))"
  using assms by (cases "x \<in> A") (simp_all add: insert_absorb remove)

lemma subset:
  assumes "finite A" "B \<noteq> {}" and "B \<subseteq> A"
  shows "inf (fInf B) (fInf A) = fInf A"
proof -
  from assms have "A \<noteq> {}" and "finite B" by (auto dest: finite_subset)
  with assms show ?thesis by (simp add: union [symmetric] Un_absorb1)
qed

lemma closed:
  assumes "finite A" "A \<noteq> {}" and elem: "\<And>x y. inf x y \<in> {x, y}"
  shows "fInf A \<in> A"
using \<open>finite A\<close> \<open>A \<noteq> {}\<close> proof (induct rule: finite_ne_induct)
  case singleton then show ?case by simp
next
  case insert with elem show ?case by force
qed

lemma hom_commute:
  assumes hom: "\<And>x y. h (inf x y) = inf (h x) (h y)"
  and N: "finite N" "N \<noteq> {}"
  shows "h (fInf N) = fInf (h ` N)"
using N proof (induct rule: finite_ne_induct)
  case singleton thus ?case by simp
next
  case (insert n N)
  then have "h (fInf (insert n N)) = h (inf n (fInf N))" by simp
  also have "\<dots> = inf (h n) (h (fInf N))" by (rule hom)
  also have "h (fInf N) = fInf (h ` N)" by (rule insert)
  also have "inf (h n) \<dots> = fInf (insert (h n) (h ` N))"
    using insert by simp
  also have "insert (h n) (h ` N) = h ` insert n N" by simp
  finally show ?case .
qed

lemma infinite: "\<not> finite A \<Longrightarrow> fInf A = the None"
  unfolding eq_fold1 by (cases "finite (UNIV::'a set)") (auto intro: finite_subset fold_infinite)

lemma lower_bounded_iff:
  assumes "finite A" and "A \<noteq> {}"
  shows "x \<le> fInf A \<longleftrightarrow> (\<forall>a\<in>A. x \<le> a)"
  using assms by (induct rule: finite_ne_induct) simp_all

lemma boundedI:
  assumes "finite A"
  assumes "A \<noteq> {}"
  assumes "\<And>a. a \<in> A \<Longrightarrow> x \<le> a"
  shows "x \<le> fInf A"
  using assms by (simp add: lower_bounded_iff)

lemma boundedE:
  assumes "finite A" and "A \<noteq> {}" and "x \<le> fInf A"
  obtains "\<And>a. a \<in> A \<Longrightarrow> x \<le> a"
  using assms by (simp add: lower_bounded_iff)

lemma coboundedI:
  assumes "finite A"
    and "a \<in> A"
  shows "fInf A \<le> a"
proof -
  from assms have "A \<noteq> {}" by auto
  from \<open>finite A\<close> \<open>A \<noteq> {}\<close> \<open>a \<in> A\<close> show ?thesis
  proof (induct rule: finite_ne_induct)
    case singleton thus ?case by (simp add: refl)
  next
    case (insert x B)
    from insert have "a = x \<or> a \<in> B" by simp
    then show ?case
      by (simp add: in_idem insert.hyps(1) local.inf.absorb_iff2)
  qed
qed

lemma subset_imp:
  assumes "A \<subseteq> B" and "A \<noteq> {}" and "finite B"
  shows "fInf B \<le> fInf A"
proof (cases "A = B")
  case True then show ?thesis by (simp add: refl)
next
  case False
  have B: "B = A \<union> (B - A)" using \<open>A \<subseteq> B\<close> by blast
  then have "fInf B = fInf (A \<union> (B - A))" by simp
  also have "\<dots> = inf (fInf A) (fInf (B - A))" using False assms by (subst union) (auto intro: finite_subset)
  also have "\<dots> \<le> fInf A" by simp
  finally show ?thesis .
qed

lemma finite_inf_greatest:
  "\<And>z A. A \<noteq> {} \<Longrightarrow> finite A \<Longrightarrow> ((\<And>x. x \<in> A \<Longrightarrow> z \<le> x) \<Longrightarrow> z \<le> fInf A)"
  by (simp add: lower_bounded_iff)
end

subsection SemilatticeSupFinitaryOperator
context semilattice_sup
begin

definition fSup::"'a set \<Rightarrow> 'a" where
  eq_fold1:"fSup A = the (Finite_Set.fold (\<lambda>x y. Some (case y of None \<Rightarrow> x | Some z \<Rightarrow> sup x z)) None A)"


lemma eq_fold2:
  assumes "finite A"
  shows "fSup (insert x A) = Finite_Set.fold sup x A"
  using assms local.Sup_fin.eq_fold local.Sup_fin.eq_fold' local.eq_fold1 by auto

lemma singleton [simp]:
  "fSup {x} = x"
  using local.Sup_fin.eq_fold' local.Sup_fin.singleton local.eq_fold1 by presburger


lemma insert_not_elem:
  assumes "finite A" and "x \<notin> A" and "A \<noteq> {}"
  shows "fSup (insert x A) = sup x (fSup A)"
  using assms(1) assms(3) local.Sup_fin.eq_fold' local.Sup_fin.insert local.eq_fold1 by presburger


lemma in_idem:
  assumes "finite A" and "x \<in> A"
  shows "sup x (fSup A) = fSup A"
  using assms(1) assms(2) local.Sup_fin.eq_fold' local.Sup_fin.in_idem local.eq_fold1 by presburger


lemma insert [simp]:
  assumes "finite A" and "A \<noteq> {}"
  shows "fSup (insert x A) = sup x (fSup A)"
  using assms by (cases "x \<in> A") (simp_all add: insert_absorb in_idem insert_not_elem)

lemma union:
  assumes "finite A" "A \<noteq> {}" and "finite B" "B \<noteq> {}"
  shows "fSup(A \<union> B) = sup (fSup A) (fSup B)"
  using assms by (induct A rule: finite_ne_induct) (simp_all add: ac_simps)

lemma remove:
  assumes "finite A" and "x \<in> A"
  shows "fSup A = (if A - {x} = {} then x else sup x (fSup(A - {x})))"
proof -
  from assms obtain B where "A = insert x B" and "x \<notin> B" by (blast dest: mk_disjoint_insert)
  with assms show ?thesis by simp
qed

lemma insert_remove:
  assumes "finite A"
  shows "fSup (insert x A) = (if A - {x} = {} then x else sup x (fSup(A - {x})))"
  using assms by (cases "x \<in> A") (simp_all add: insert_absorb remove)

lemma subset:
  assumes "finite A" "B \<noteq> {}" and "B \<subseteq> A"
  shows "sup (fSup B) (fSup A) = fSup A"
proof -
  from assms have "A \<noteq> {}" and "finite B" by (auto dest: finite_subset)
  with assms show ?thesis by (simp add: union [symmetric] Un_absorb1)
qed

lemma closed:
  assumes "finite A" "A \<noteq> {}" and elem: "\<And>x y. sup x y \<in> {x, y}"
  shows "fSup A \<in> A"
using \<open>finite A\<close> \<open>A \<noteq> {}\<close> proof (induct rule: finite_ne_induct)
  case singleton then show ?case by simp
next
  case insert with elem show ?case by force
qed

lemma hom_commute:
  assumes hom: "\<And>x y. h (sup x y) = sup (h x) (h y)"
  and N: "finite N" "N \<noteq> {}"
  shows "h (fSup N) = fSup (h ` N)"
using N proof (induct rule: finite_ne_induct)
  case singleton thus ?case by simp
next
  case (insert n N)
  then have "h (fSup (insert n N)) = h (sup n (fSup N))" by simp
  also have "\<dots> = sup (h n) (h (fSup N))" by (rule hom)
  also have "h (fSup N) = fSup (h ` N)" by (rule insert)
  also have "sup (h n) \<dots> = fSup (insert (h n) (h ` N))"
    using insert by simp
  also have "insert (h n) (h ` N) = h ` insert n N" by simp
  finally show ?case .
qed

lemma infinite: "\<not> finite A \<Longrightarrow> fSup A = the None"
  unfolding eq_fold1 by (cases "finite (UNIV::'a set)") (auto intro: finite_subset fold_infinite)

lemma upper_bounded_iff:
  assumes "finite A" and "A \<noteq> {}"
  shows "fSup A \<le> x \<longleftrightarrow> (\<forall>a\<in>A. a \<le> x)"
  using assms by (induct rule: finite_ne_induct) simp_all

lemma boundedI:
  assumes "finite A"
  assumes "A \<noteq> {}"
  assumes "\<And>a. a \<in> A \<Longrightarrow> a \<le> x"
  shows "fSup A \<le> x"
  using assms(1) assms(2) assms(3) upper_bounded_iff by auto

lemma boundedE:
  assumes "finite A" and "A \<noteq> {}" and "fSup A \<le> x"
  obtains "\<And>a. a \<in> A \<Longrightarrow> a \<le> x"
  using assms by (simp add: upper_bounded_iff)

lemma coboundedI:
  assumes "finite A"
    and "a \<in> A"
  shows "a \<le> fSup A"
proof -
  from assms have "A \<noteq> {}" by auto
  from \<open>finite A\<close> \<open>A \<noteq> {}\<close> \<open>a \<in> A\<close> show ?thesis
  proof (induct rule: finite_ne_induct)
    case singleton thus ?case by (simp add: refl)
  next
    case (insert x B)
    from insert have "a = x \<or> a \<in> B" by simp
    then show ?case
      by (simp add: insert.hyps(1) local.in_idem local.le_iff_sup)
  qed
qed

lemma subset_imp:
  assumes "A \<subseteq> B" and "A \<noteq> {}" and "finite B"
  shows "fSup A \<le> fSup B"
proof (cases "A = B")
  case True then show ?thesis by (simp add: refl)
next
  case False
  have B: "B = A \<union> (B - A)" using \<open>A \<subseteq> B\<close> by blast
  then have "fSup B = fSup (A \<union> (B - A))" by simp
  also have "\<dots> = sup (fSup A) (fSup (B - A))" using False assms by (subst union) (auto intro: finite_subset)
  also have "\<dots> \<ge> fSup A" by simp
  finally show ?thesis .
qed

lemma finite_sup_greatest:
  "\<And>z A. A \<noteq> {} \<Longrightarrow> finite A \<Longrightarrow> ((\<And>x. x \<in> A \<Longrightarrow> x \<le> z) \<Longrightarrow> fSup A \<le> z)"
  by (simp add: upper_bounded_iff)

end


abbreviation Fpow_ne::"'a set \<Rightarrow> 'a set set" where
  "Fpow_ne A \<equiv> (Fpow A)-{{}}"

abbreviation Dpow::"'a set \<Rightarrow> 'a set set set" where
  "Dpow A \<equiv> (Pow (Pow A))"

abbreviation Pow_ne::"'a set \<Rightarrow> 'a set set" where
  "Pow_ne A \<equiv> (Pow A) - {{}}"

lemma in_dpow_iff:
  "a \<in> Dpow A \<longleftrightarrow> (\<forall>x  \<in> a. x \<in> Pow A)"
  by blast

section Bounds
subsection Upper
definition ub_set_in::"'a::ord set \<Rightarrow> 'a::ord set  \<Rightarrow> 'a::ord set" where
  "ub_set_in A B \<equiv> {u. (\<forall>x. x \<in> A \<longrightarrow> x \<le> u) \<and> u \<in> B}"

definition ub_set::"'a::ord set  \<Rightarrow> 'a::ord set" where
  "ub_set A \<equiv> {u. (\<forall>x. x \<in> A \<longrightarrow> x \<le> u)}"

subsection Lower
definition lb_set_in::"'a::ord set \<Rightarrow> 'a::ord set  \<Rightarrow> 'a::ord set" where
  "lb_set_in A B \<equiv> {l. (\<forall>x. x \<in> A \<longrightarrow> l \<le> x) \<and> l \<in> B}"

definition lb_set::"'a::ord set  \<Rightarrow> 'a::ord set" where
  "lb_set A \<equiv> {l. (\<forall>x. x \<in> A \<longrightarrow> l \<le> x)}"

section Predicates
subsection GreatestLeastPredicates
definition is_max::"'a::ord \<Rightarrow> 'a::ord set \<Rightarrow> bool" where
  "is_max m A \<equiv> (m \<in> A \<inter> (ub_set_in A UNIV))"

definition is_min::"'a::ord \<Rightarrow> 'a::ord set \<Rightarrow> bool" where
  "is_min m A \<equiv> (m \<in> A \<inter> (lb_set_in A UNIV))"

definition has_max::"'a::ord set \<Rightarrow> bool" where
  "has_max A \<equiv> (\<exists>m. is_max m A)"

definition has_min::"'a::ord set \<Rightarrow> bool" where
  "has_min A \<equiv> (\<exists>m. is_min m A)"

subsection SupInfPredicates
definition is_sup_in::"'a::ord \<Rightarrow> 'a::ord set \<Rightarrow> 'a::ord set \<Rightarrow> bool" where
  "is_sup_in s A X \<equiv>  (is_min s (ub_set_in A X))"

definition is_inf_in::"'a::ord \<Rightarrow> 'a::ord set \<Rightarrow> 'a::ord set \<Rightarrow> bool" where
  "is_inf_in i A X \<equiv>  (is_max i (lb_set_in A X))"

definition is_sup::"'a::order \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "is_sup s A \<equiv>  (is_min s (ub_set A))"

definition is_inf::"'a::order \<Rightarrow>  'a::order set \<Rightarrow> bool" where
  "is_inf i A \<equiv>  (is_max i (lb_set A))"

definition has_sup_in::" 'a::ord set \<Rightarrow> 'a::ord set \<Rightarrow> bool" where
  "has_sup_in A X \<equiv>  (has_min (ub_set_in A X))"

definition has_inf_in::" 'a::ord set \<Rightarrow> 'a::ord set \<Rightarrow> bool" where
  "has_inf_in A X \<equiv>  (has_max (lb_set_in A X))"

definition has_sup::" 'a::order set \<Rightarrow> bool" where
  "has_sup A \<equiv>  (has_min (ub_set A))"

definition has_inf::" 'a::order set  \<Rightarrow> bool" where
  "has_inf A \<equiv>  (has_max (lb_set A))"

section Operators
subsection GreatestLeastOperators
definition max::"'a::ord set \<Rightarrow> 'a::ord" where
  "max A \<equiv> (THE m. is_max m A)"

definition min::"'a::ord set \<Rightarrow> 'a::ord" where
  "min A \<equiv> (THE m. is_min m A)"

subsection SupInfOperators
definition SupIn::"'a::ord set \<Rightarrow>'a::ord set \<Rightarrow> 'a::ord" where
  "SupIn A X = (THE s. is_sup_in s A X)"

definition InfIn::"'a::ord set \<Rightarrow>'a::ord set \<Rightarrow> 'a::ord" where
  "InfIn A X = (THE i. is_inf_in i A X)"


definition SupUn::"'a::order set \<Rightarrow> 'a::order" where
  "SupUn A = (THE s. is_sup s A)"

definition InfUn::"'a::order set \<Rightarrow> 'a::order" where
  "InfUn A = (THE i. is_inf i A)"

subsection PropertiesOfFunctions
definition is_extensive::"('a::ord \<Rightarrow> 'a::ord) \<Rightarrow> bool" where
  "is_extensive f \<equiv> (\<forall>x. (x \<le> (f x)))"

definition is_isotone::"('a::ord \<Rightarrow> 'b::ord) \<Rightarrow> bool" where
  "is_isotone f \<equiv> (\<forall>x1 x2. x1 \<le> x2 \<longrightarrow> (f x1) \<le> (f x2))"

definition is_idempotent::"('a::ord \<Rightarrow> 'a::ord) \<Rightarrow> bool" where
  "is_idempotent f \<equiv> (\<forall>x.  (f x)= f (f x))"

definition is_closure::"('a::ord \<Rightarrow> 'a::ord) \<Rightarrow> bool" where
  "is_closure f \<equiv> (is_extensive f) \<and> (is_isotone f) \<and> (is_idempotent f)"

definition pointwise_less_eq::"('a::ord \<Rightarrow> 'b::ord) \<Rightarrow>('a::ord \<Rightarrow> 'b::ord) \<Rightarrow> bool" where
  "pointwise_less_eq f g \<equiv> (\<forall>x. (f x) \<le> (g x))"

definition pointwise_less::"('a::ord \<Rightarrow> 'b::ord) \<Rightarrow>('a::ord \<Rightarrow> 'b::ord) \<Rightarrow> bool" where
  "pointwise_less f g \<equiv> (pointwise_less_eq f g) \<and> (f \<noteq> g)"

definition antitone :: "('a::ord \<Rightarrow> 'b::ord) \<Rightarrow> bool" where
"antitone f \<longleftrightarrow> (\<forall>x y. x \<le> y \<longrightarrow> f y \<le> f x)"

definition comp_extensive :: "('a::ord \<Rightarrow> 'b::ord) \<Rightarrow> ('b::ord \<Rightarrow> 'a::ord) \<Rightarrow> bool" where
"comp_extensive f g \<longleftrightarrow> (\<forall>x. x \<le> g (f x)) \<and> (\<forall>y. y \<le> f (g y))"

subsection GaloisConnections
definition relation_to_fgc::"('a \<times> 'b) set \<Rightarrow> (('a set) \<Rightarrow> ('b set))" where
  "relation_to_fgc R = (\<lambda>(A::('a set)). {(y::'b). \<forall>x \<in> A. (x, y) \<in> R}) "

definition relation_to_ggc::"('a \<times> 'b) set \<Rightarrow> (('b set) \<Rightarrow> ('a set))" where
  "relation_to_ggc R = (\<lambda>(B::('b set)). {(x::'a). \<forall>y \<in> B. (x, y) \<in> R}) "

definition fgc_to_relation::"(('a set) \<Rightarrow> ('b set)) \<Rightarrow> ('a \<times> 'b) set" where
  "fgc_to_relation f = {(x, y). y \<in> f({x}) }"

definition ggc_to_relation::"(('b set) \<Rightarrow> ('a set)) \<Rightarrow> ('a \<times> 'b) set" where
  "ggc_to_relation g = {(x, y). x \<in> g({y}) }"

definition is_gc2::"('a::ord \<Rightarrow> 'b::ord) \<Rightarrow> ('b::ord \<Rightarrow> 'a::ord) \<Rightarrow> bool" where
  "is_gc2 f g \<equiv> (comp_extensive f g) \<and> (antitone f) \<and> (antitone g)"

definition is_gc4::"('a::ord \<Rightarrow> 'b::ord) \<Rightarrow> ('b::ord \<Rightarrow> 'a::ord) \<Rightarrow> bool" where
  "is_gc4 f g \<equiv> \<forall>(x::('a::ord)). \<forall>(y::('b::ord)). y \<le> (f x) \<longleftrightarrow> x \<le> (g y)"

definition binf::"'a::order  \<Rightarrow> 'a::order \<Rightarrow> 'a::order" where
  "binf a b \<equiv> InfUn {a,b}"

definition bsup::"'a::order \<Rightarrow> 'a::order \<Rightarrow> 'a::order" where
  "bsup a b \<equiv> SupUn {a, b}"

definition is_join_dual::"('a::order \<Rightarrow> 'b::order) \<Rightarrow> bool" where
  "is_join_dual f \<equiv> (\<forall>A. ( (f (SupUn A)) = (InfUn (f`(A))) ))"

definition join_dual_partner::"('a::order \<Rightarrow> 'b::order) \<Rightarrow> ('b::order \<Rightarrow> 'a::order)" where
  "join_dual_partner f = (\<lambda>y::('b::order). SupUn {x::'a::order. y \<le> (f x)})"

subsection SpecialSets

definition is_cofinal_in::"'a::ord set \<Rightarrow> 'a::ord set \<Rightarrow> bool" (infix "is'_cofinal'_in" 50) where
  "A is_cofinal_in B \<equiv> (\<forall>a. a \<in> A \<longrightarrow> (\<exists>b \<in> B. b \<ge> a))"

definition is_inf_complete::"'a::ord set \<Rightarrow> bool" where 
  "is_inf_complete X \<equiv> (\<forall>A. A \<in> Pow_ne X \<longrightarrow> has_inf_in A X)"

definition is_sup_complete::"'a::ord set \<Rightarrow> bool" where 
  "is_sup_complete X \<equiv> (\<forall>A. A \<in> Pow_ne X \<longrightarrow> has_sup_in A X)"

definition is_inf_closed::"'a::ord set \<Rightarrow> bool" where 
  "is_inf_closed X \<equiv> (\<forall>A. A \<in> Pow_ne X \<longrightarrow> InfIn A X \<in> X)"

definition is_sup_closed::"'a::ord set \<Rightarrow> bool" where 
  "is_sup_closed X \<equiv> (\<forall>A. A \<in> Pow_ne X  \<longrightarrow> SupIn A X \<in> X)"

definition is_inhabited::"'a set  \<Rightarrow> bool" where
   "is_inhabited X \<equiv> (X \<noteq> {})"

definition is_downdir::"'a::ord set  \<Rightarrow> bool" where
   "is_downdir A \<equiv> (\<forall>a b. (a \<in> A \<and> b \<in> A) \<longrightarrow> (\<exists>c  \<in> A. (c \<le> a) \<and>  (c \<le> b)))"

definition is_updir::"'a::ord set  \<Rightarrow> bool" where
   "is_updir A \<equiv> (\<forall>a b. (a \<in> A \<and> b \<in> A) \<longrightarrow> (\<exists>c  \<in> A. (c \<ge> a) \<and>  (c \<ge> b)))"

definition is_upclosed_in::"'a::ord set \<Rightarrow>'a::ord set  \<Rightarrow> bool" where
   "is_upclosed_in A X \<equiv> (\<forall>a b. (a \<le> b \<and>  a \<in> A \<and> b \<in> X) \<longrightarrow>  b \<in> A)"

definition is_upclosed::"'a::ord set \<Rightarrow> bool" where
   "is_upclosed A \<equiv> is_upclosed_in A UNIV"

definition is_downclosed_in::"'a::ord set \<Rightarrow> 'a::ord set \<Rightarrow> bool" where
   "is_downclosed_in A X \<equiv> (\<forall>a b. (a \<ge> b \<and>  a \<in> A \<and> b \<in> X) \<longrightarrow>  b \<in> A)"

definition is_downclosed::"'a::ord set  \<Rightarrow> bool" where
   "is_downclosed A \<equiv> is_downclosed_in A  UNIV"

definition is_pisystem::"'a::order set \<Rightarrow> bool" where
   "is_pisystem X \<equiv> (\<forall>a b. a \<in> X  \<longrightarrow> b \<in> X \<longrightarrow> (binf a b)  \<in> X)"

definition is_filter_in::"'a::ord set \<Rightarrow> 'a::ord set \<Rightarrow> bool" where 
  "is_filter_in F X \<equiv> (F \<subseteq> X \<and> is_downdir F \<and> is_upclosed_in F X \<and> is_inhabited F)"

definition is_ideal_in::"'a::ord set \<Rightarrow> 'a::ord set \<Rightarrow> bool" where 
  "is_ideal_in F X \<equiv> (F \<subseteq> X \<and> is_updir F \<and> is_downclosed_in F X \<and> is_inhabited F)"

definition is_filter::"'a::ord set \<Rightarrow> bool" where 
  "is_filter F \<equiv> is_filter_in F UNIV"

definition is_ideal::"'a::ord set \<Rightarrow> bool" where 
  "is_ideal I \<equiv> is_ideal_in I UNIV"

definition covers::"'a::ord set \<Rightarrow> 'a::ord \<Rightarrow> bool" where
  "covers A b \<equiv> (b \<in> lb_set A) \<and> (A \<noteq> {}) "

definition is_finite_subcover::"'a::ord set \<Rightarrow> 'a::ord set \<Rightarrow>   'a::ord \<Rightarrow>  bool" where
 "is_finite_subcover S A b \<equiv> (S \<in> Fpow_ne A)  \<and> (b \<in> lb_set S)"

definition is_compact::"'a::ord \<Rightarrow> bool" where
  "is_compact b \<equiv> (\<forall>A. (covers A b) \<longrightarrow> (\<exists>S. is_finite_subcover S A b))"

definition is_directed::"'a::ord set \<Rightarrow> bool" where 
  "is_directed D \<equiv> (D \<noteq> {}) \<and> (\<forall>A. A  \<in> Fpow_ne D \<longrightarrow> (\<exists>u \<in> D. u \<in> ub_set A))"

definition directed_covering::"'a::ord \<Rightarrow> 'a::ord set \<Rightarrow> bool" where
  "directed_covering a D \<equiv> (covers D a) \<and> is_directed D"

definition is_compactly_generated::"'a::order set  \<Rightarrow> bool" where
  "is_compactly_generated X \<equiv> (\<forall>x \<in> X. (\<exists>Cx. (\<forall>c \<in> Cx. is_compact c) \<and> (is_sup x Cx)))"

definition is_meet_reducible::"'a::order \<Rightarrow> bool" where
  "is_meet_reducible x \<equiv> (\<exists>A. (A \<noteq> {}) \<and> (x \<notin> A) \<and> (is_inf x A))"

definition is_join_reducible::"'a::order \<Rightarrow> bool" where
  "is_join_reducible x \<equiv> (\<exists>A. (A \<noteq> {}) \<and> (x \<notin> A) \<and> (is_sup x A))"

definition is_moore_family::"'a::order set \<Rightarrow> bool" where
  "is_moore_family C \<equiv> (C \<noteq> {}) \<and> (\<forall>(a::'a). has_min (ub_set_in {a} C))"

definition moore_to_closure::"'a::order set \<Rightarrow> ('a::order \<Rightarrow> 'a::order)" where
  "moore_to_closure C \<equiv> (\<lambda>x. InfUn(ub_set_in {x} C))"

definition filter_closure::"'a::order set \<Rightarrow> 'a::order set" where
  "filter_closure A \<equiv> {a. \<exists>S\<in>Fpow_ne(A). InfUn S \<le> a}"

definition filter_closure_in::"'a::order set \<Rightarrow>'a::order \<Rightarrow> 'a::order set" where
  "filter_closure_in A x \<equiv> {a. a \<le> x \<and> (\<exists>S\<in>Fpow_ne(A). InfUn S \<le> a)}"

definition up_closure_in::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> 'a::order set" where
  "up_closure_in A X \<equiv> {x. x \<in> X \<and>  (\<exists>a \<in> A. a \<le> x)}"

definition up_closure::"'a::order set \<Rightarrow> 'a::order set" where
  "up_closure A \<equiv> up_closure_in A UNIV"

definition down_closure_in::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> 'a::order set" where
  "down_closure_in A X \<equiv> {x. x \<in> X \<and>  (\<exists>a \<in> A. a \<ge> x)}"

definition down_closure::"'a::order set \<Rightarrow> 'a::order set" where
  "down_closure A \<equiv> down_closure_in A UNIV"

definition is_prime::"'a::{order, sup} set \<Rightarrow> bool" where
  "is_prime A \<equiv> (\<forall>a. \<forall>b. (sup a b) \<in> A \<longrightarrow> (a \<in> A \<or> b \<in> A))"

definition is_prime_alt::"'a::{boolean_algebra,order_bot} set \<Rightarrow> bool" where
  "is_prime_alt U \<equiv> (\<forall>a. ((a \<in> U) \<and> \<not>((-a) \<in> U)) \<or> (\<not>(a \<in> U) \<and> ((-a) \<in> U)))"

definition binary_filter_sup::"'a::semilattice_inf set \<Rightarrow> 'a::semilattice_inf set \<Rightarrow> 'a::semilattice_inf set" where
  "binary_filter_sup A B = {x. \<exists>a \<in> A. \<exists>b \<in> B. inf a b \<le> x}"

definition filter_sup::"'a::order set set \<Rightarrow> 'a::order set" where
  "filter_sup EF \<equiv> filter_closure(Sup(EF))"

definition filter_inf::"'a::bounded_semilattice_inf_top set set \<Rightarrow> 'a::bounded_semilattice_inf_top set" where
  "filter_inf EF \<equiv> (if EF={} then {top} else \<Inter>EF)"

definition is_proper_in::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "is_proper_in F X \<equiv> F \<noteq> X"

definition is_proper::"'a::order set \<Rightarrow> bool" where
  "is_proper F \<equiv> (is_proper_in F UNIV)"

definition is_pfilter_in::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "is_pfilter_in F X \<equiv> (is_filter_in F X) \<and> (is_proper_in F X) "

definition is_complete_inf_semilattice::"'a::order set \<Rightarrow> bool" where
  "is_complete_inf_semilattice X \<equiv> (is_inhabited X) \<and> (\<forall>A. A \<in> Pow_ne X \<longrightarrow> has_inf_in A X)"

definition is_complete_sup_semilattice::"'a::order set \<Rightarrow> bool" where
  "is_complete_sup_semilattice X \<equiv> (is_inhabited X) \<and> (\<forall>A. A \<in> Pow_ne X \<longrightarrow> has_sup_in A X)"

 
lemma is_pfilter_in_imp:
  "\<And>F X. is_pfilter_in F X \<Longrightarrow>  (is_filter_in F X) \<and> (is_proper_in F X)"
  by (simp add:is_pfilter_in_def)

lemma is_pfilter_in_if:
  "\<And>F X.  (is_filter_in F X) \<and> (is_proper_in F X) \<Longrightarrow> is_pfilter_in F X "
  by (simp add:is_pfilter_in_def)

lemma is_pfilter_in_imp2:
  "\<And>F X. is_pfilter_in F X \<Longrightarrow>  (is_proper_in F X \<and> F \<subseteq> X \<and> is_downdir F \<and> is_upclosed_in F X \<and> is_inhabited F)"
  by (simp add: is_filter_in_def is_pfilter_in_def)

lemma is_pfilter_in_if2:
  "\<And>F X.  (is_proper_in F X \<and> F \<subseteq> X \<and> is_downdir F \<and> is_upclosed_in F X \<and> is_inhabited F) \<Longrightarrow> is_pfilter_in F X "
  by (simp add: is_filter_in_def is_pfilter_in_def)

definition is_pfilter::"'a::order set \<Rightarrow>  bool" where
  "is_pfilter F \<equiv> is_pfilter_in F UNIV"


lemma is_pfilter_imp1:
  "\<And>F. is_pfilter F \<Longrightarrow>  (is_filter_in F UNIV) \<and> (is_proper_in F UNIV)"
  by(simp add:is_pfilter_def is_pfilter_in_def)

lemma is_pfilter_imp2:
  "\<And>F. is_pfilter F \<Longrightarrow>  (is_filter F) \<and> (is_proper F)"
  by (simp add: is_filter_def is_pfilter_imp1 is_proper_def)



lemma is_pfilter_if1:
  "\<And>F X.  (is_filter_in F UNIV) \<and> (is_proper_in F UNIV) \<Longrightarrow> is_pfilter F "
  by (simp add:is_pfilter_in_def is_pfilter_def)    

lemma is_pfilter_if2:
  "\<And>F X.  (is_filter F) \<and> (is_proper F) \<Longrightarrow> is_pfilter F "
  by (simp add: is_filter_def is_pfilter_def is_pfilter_in_if is_proper_def)

definition is_ultrafilter::"'a::order set  \<Rightarrow> bool" where
  "is_ultrafilter U \<equiv> (is_pfilter U  \<and> (\<forall>F .  (is_pfilter F \<and> U \<subseteq> F) \<longrightarrow> U=F))"

definition upsets_in::"'a::order set \<Rightarrow> 'a::order set set" where
  "upsets_in X = {U. U \<subseteq> X \<and> is_upclosed_in U X}"

definition downsets_in::"'a::order set \<Rightarrow> 'a::order set set" where
  "downsets_in X = {D. D \<subseteq> X \<and> is_downclosed_in D X}"


definition filters_in::"'a::order set \<Rightarrow> 'a::order set set" where
  "filters_in A = {F. (is_filter F) \<and> (F \<in> (Pow A))}"

definition pfilters_in::"'a::order set \<Rightarrow> 'a::order set set" where
  "pfilters_in A = {F. (is_pfilter F) \<and> (F \<in> (Pow A))}"

definition ultrafilters_in::"'a::order set \<Rightarrow> 'a::order set set" where
  "ultrafilters_in A = {U. (is_ultrafilter U) \<and> (U \<in> (Pow A))}"

definition finer_pfilters::"'a::order set \<Rightarrow> 'a::order set set" where
  "finer_pfilters F = {U. is_pfilter U \<and> (F \<subseteq> U)}"
    
definition finer_ultrafilters::"'a::order set \<Rightarrow> 'a::order set set" where
  "finer_ultrafilters F = {U. is_ultrafilter U \<and> (F \<subseteq> U)}"

definition coarser_ultrafilters::"'a::order set \<Rightarrow> 'a::order set set" where
  "coarser_ultrafilters F = {U. is_ultrafilter U \<and> (F \<supseteq> U)}"

definition finer_upsets::"'a::order set \<Rightarrow> 'a::order set set" where
  "finer_upsets A = {U. is_upclosed U \<and> (A \<subseteq> U)}"

definition is_chain::"'X::order set \<Rightarrow> bool" where
  "is_chain A \<equiv> (\<forall>a1 \<in> A. \<forall>a2 \<in> A. (a1 \<le> a2 \<or> a2 \<le> a1))"

definition meshes::"('a::{lattice,order_bot} set) \<Rightarrow> ('a::{lattice,order_bot} set) \<Rightarrow> bool"  (infixl "#" 50)  where
   "(A # B) \<equiv> (\<forall>a \<in> A. \<forall>b \<in> B.  ((inf a b) \<noteq> bot))"

definition grill::"'a::{lattice,order_bot} set \<Rightarrow> 'a::{lattice,order_bot} set" where
  "grill A = {x::('a::{lattice,order_bot}). {x}#A}"  

abbreviation principal_filter_in::"'a::order \<Rightarrow> 'a::order set \<Rightarrow> 'a::order set" where
  "principal_filter_in x A \<equiv> ub_set_in {x} A"



section FiniteExtrema
subsection Lattices
context lattice
begin
(*Existence of finite inf and sup in lattice*)
lemma finf_lattice:
  "\<And>A. (finite A \<and> A \<noteq> {}) \<longrightarrow> (\<exists>i. fInf A=i)"
  by simp
lemma fsup_lattice:
  "\<And>A. (finite A \<and> A \<noteq> {}) \<longrightarrow> (\<exists>s. fSup A=s)"
  by simp
end

subsubsection CompleteSemilattices
context complete_semilattice_sup
begin
(*finite inf and sup agree with inf and sup in complete lattice*)
lemma fsup_complete_lattice:
  "\<And>A. (finite A \<and> A \<noteq> {}) \<longrightarrow> (fSup A = Sup A)"
  using local.CSup_least local.CSup_upper local.Sup_fin.boundedI local.Sup_fin.coboundedI
         local.Sup_fin.eq_fold' local.dual_order.antisym local.eq_fold1 by auto

end

context complete_semilattice_inf
begin
(*finite inf and sup agree with inf and sup in complete lattice*)
lemma finf_complete_lattice:
  "\<And>A. (finite A \<and> A \<noteq> {}) \<longrightarrow> (fInf A = Inf A)"
  using local.CInf_greatest local.CInf_lower local.Inf_fin.bounded_iff 
          local.Inf_fin.coboundedI local.Inf_fin.eq_fold' local.dual_order.antisym local.eq_fold1
           by auto
end

subsubsection CompleteLattices
context complete_lattice
begin
(*finite inf and sup agree with inf and sup in complete lattice*)
lemma finf_complete_lattice:
  "\<And>A. (finite A \<and> A \<noteq> {}) \<longrightarrow> (fInf A = Inf A)"
  by (simp add: local.csli.finf_complete_lattice)


lemma fsup_complete_lattice:
  "\<And>A. (finite A \<and> A \<noteq> {}) \<longrightarrow> (fSup A = Sup A)"
  using local.csls.fsup_complete_lattice by blast

end
section Bounds
subsection UpperBounds
subsubsection Relative

lemma ub_set_in_mem:
  "\<And>(A::'a::order set) X x u. (u \<in> ub_set_in A X  \<and> x \<in> A) \<Longrightarrow> (x \<le> u \<and> u \<in> X) "
  by (simp add: ub_set_in_def)

lemma ub_set_in_subset:
  "ub_set_in A X \<subseteq> X"
  by (simp add: Collect_conj_eq ub_set_in_def)

lemma ub_set_in_imp:
  "\<And>(A::'a::order set) X u. (u \<in> ub_set_in A X) \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> x \<le> u)"
  by (simp add: ub_set_in_def)

lemma ub_set_in_elm:
  "\<And>(A::'a::order set) X u. (\<And>a. a \<in> A \<Longrightarrow> a \<le> u) \<Longrightarrow> u \<in> X \<Longrightarrow> u \<in> ub_set_in A X"
  by (simp add: ub_set_in_def)

lemma ub_set_in_mem_iff:
  "\<forall>x. x \<in> ub_set_in A B \<longleftrightarrow> (x \<in> B) \<and> (\<forall>a. a \<in> A \<longrightarrow> a \<le> x )"
  using ub_set_in_def by auto


lemma ub_set_in_antitone1:
  "\<And>A B X. A \<subseteq> B \<Longrightarrow>  ub_set_in B X \<subseteq> ub_set_in A X"
  by (simp add: subset_eq ub_set_in_def)

lemma ub_set_in_isotone2:
  "\<And>A  B X. B \<subseteq> X \<Longrightarrow>  ub_set_in A B \<subseteq> ub_set_in A X"
  by (simp add: subset_eq ub_set_in_def)

lemma ub_set_in_degenerate:
  "ub_set_in {} X = X"
  by (simp add: ub_set_in_def)

lemma ub_set_in_ub_inter:
  "(ub_set A) \<inter> B = ub_set_in A B"
  by (simp add: Collect_conj_eq ub_set_def ub_set_in_def)

lemma ub_set_in_ub_univ:
  "ub_set A = ub_set_in A UNIV"
  using ub_set_in_ub_inter by auto

lemma ub_set_in_univ_absorb:
  "ub_set_in A UNIV = ub_set A"
  using ub_set_in_ub_univ by blast

lemma ub_set_in_singleton:
  "ub_set_in {x} C  = {y \<in> C. x \<le> y}"
  by (simp add: set_eq_iff ub_set_in_mem_iff)

lemma ub_set_in_from_principal:
  assumes "A \<noteq> {}"
  shows "ub_set_in A X = (\<Inter>a \<in> A. ub_set_in {a} X)"
  apply(auto simp add:ub_set_in_def)
  using assms by auto

subsubsection Absolute

lemma ub_set_mem:
  "\<And>(A::'a::order set) x u. (u \<in> ub_set A  \<and> x \<in> A) \<Longrightarrow> (x \<le> u) "
  by (simp add: ub_set_def)

lemma ub_set_imp:
  "\<And>(A::'a::order set) u. (u \<in> ub_set A) \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> x \<le> u) "
  by (simp add: ub_set_def)

lemma ub_set_if:
  "\<And>(A::'a::order set) u. (\<And>x. x \<in> A \<Longrightarrow> x \<le> u) \<Longrightarrow> u \<in> ub_set A"
  by (simp add: ub_set_def)

lemma ub_set_elm:
  "\<And>(A::'a::order set) u. (\<And>a. a \<in> A \<Longrightarrow> a \<le> u)  \<Longrightarrow> u \<in> ub_set A"
  by (simp add: ub_set_def)

lemma ub_set_mem_iff:
  "\<forall>x. x \<in> ub_set A \<longleftrightarrow> (\<forall>a. a \<in> A \<longrightarrow> a \<le> x )"
  using ub_set_def by auto

lemma imp_in_upper_bounds:
  "\<And>u A.  (\<forall>a \<in> A. a \<le> u) \<Longrightarrow> u \<in> ub_set A"
  using ub_set_mem_iff by blast

lemma ub_set_antitone1:
  "\<And>A B. A \<subseteq> B \<Longrightarrow>  ub_set B \<subseteq> ub_set A"
  by (simp add: subset_eq ub_set_def)

lemma ub_set_degenerate:
  "ub_set {} = UNIV"
  by (simp add: ub_set_def)

lemma ub_set_singleton:
  "ub_set {x}  = {y. x \<le> y}"
  by (simp add: set_eq_iff ub_set_mem_iff)

subsection LowerBounds
subsubsection Relative
lemma lb_set_in_mem:
  "\<And>(A::'a::order set) X x l. (l \<in> lb_set_in A X  \<and> x \<in> A) \<Longrightarrow> (l \<le> x \<and> l \<in> X) "
  by (simp add: lb_set_in_def)

lemma lb_set_in_imp:
  "\<And>(A::'a::order set) X l. (l \<in> lb_set_in A X) \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> l \<le> x)"
  by (simp add: lb_set_in_def)

lemma lb_set_in_subset:
  "lb_set_in A X \<subseteq> X"
  by (simp add: Collect_conj_eq lb_set_in_def)

lemma lb_set_in_elm:
  "\<And>(A::'a::order set) X l. (\<And>a. a \<in> A \<Longrightarrow> l \<le> a) \<Longrightarrow> l \<in> X \<Longrightarrow> l \<in> lb_set_in A X"
  by (simp add: lb_set_in_def)

lemma lb_set_in_mem_iff:
  "\<forall>x. x \<in> lb_set_in A B \<longleftrightarrow> (x \<in> B) \<and> (\<forall>a. a \<in> A \<longrightarrow> x \<le> a )"
  using lb_set_in_def by auto

lemma lb_set_in_antitone1:
  "\<And>A  B X. A \<subseteq> B \<Longrightarrow>  lb_set_in B X \<subseteq> lb_set_in A X"
  by (simp add: subset_eq lb_set_in_def)
                                 
lemma lb_set_in_isotone2:
  "\<And>A B X. B \<subseteq> X \<Longrightarrow>  lb_set_in A B \<subseteq> lb_set_in A X"
  by (simp add: subset_eq lb_set_in_def)

lemma lb_set_in_degenerate:
  "lb_set_in {} X = X"
  by (simp add: lb_set_in_def)
  
lemma lb_set_in_lb_inter:
  "(lb_set A) \<inter> B = lb_set_in A B"
  by (simp add: Collect_conj_eq lb_set_def lb_set_in_def)

lemma lb_set_in_lb_univ:
  "lb_set A = lb_set_in A UNIV"
  using lb_set_in_lb_inter by auto

lemma lb_set_in_univ_absorb:
  "lb_set_in A UNIV = lb_set A"
  using lb_set_in_lb_univ by blast

lemma lb_set_in_singleton:
  "lb_set_in {x} C  = {y \<in> C. x \<ge> y}"
  by (simp add: set_eq_iff lb_set_in_mem_iff)


lemma lb_set_in_from_principal:
  assumes "A \<noteq> {}"
  shows "lb_set_in A X = (\<Inter>a \<in> A. lb_set_in {a} X)"
  apply(auto simp add:lb_set_in_def)
  using assms by auto



subsubsection Absolute

lemma lb_set_mem:
  "\<And>(A::'a::order set) x l. (l \<in> lb_set A  \<and> x \<in> A) \<Longrightarrow> (l \<le> x) "
  by (simp add: lb_set_def)

lemma lb_set_imp:
  "\<And>(A::'a::order set) l. (l \<in> lb_set A) \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> l \<le> x)"
  by (simp add: lb_set_def)

lemma lb_set_if:
  "\<And>(A::'a::order set) l. (\<And>x. x \<in> A \<Longrightarrow> l \<le> x) \<Longrightarrow> l \<in> lb_set A"
  by (simp add: lb_set_def)

lemma lb_set_elm:
  "\<And>(A::'a::order set) l. (\<And>a. a \<in> A \<Longrightarrow> l \<le> a)  \<Longrightarrow> l \<in> lb_set A"
  by (simp add: lb_set_def)

lemma lb_set_mem_iff:
  "\<forall>x. x \<in> lb_set A \<longleftrightarrow> (\<forall>a. a \<in> A \<longrightarrow> x \<le> a )"
  using lb_set_def by auto

lemma imp_in_lower_bounds:
  "\<And>l A.  (\<forall>a \<in> A. l \<le> a) \<Longrightarrow> l \<in> lb_set A"
  using lb_set_mem_iff by blast

lemma lb_set_antitone1:
  "\<And>A B. A \<subseteq> B \<Longrightarrow>  lb_set B \<subseteq> lb_set A"
  by (simp add: subset_eq lb_set_def)
      
lemma lb_set_degenerate:
  "lb_set {} = UNIV"
  by (simp add: lb_set_def)
         
lemma lb_set_singleton:
  "lb_set {x} = {y. x \<ge> y}"
  by (simp add: set_eq_iff lb_set_mem_iff)

subsection Misc

lemma ub_lb_extensive:
  fixes A X::"'a::ord set"
  assumes "A \<subseteq> X"
  shows "A \<subseteq> (ub_set_in (lb_set_in A X) X)"
  by (meson assms lb_set_in_mem_iff subset_iff ub_set_in_mem_iff)

lemma ub_lb_isotone:
  "\<And>A B X.  A \<subseteq> B \<Longrightarrow>  (ub_set_in (lb_set_in A X) X) \<subseteq> (ub_set_in (lb_set_in B X) X)"
  by (simp add: lb_set_in_antitone1 ub_set_in_antitone1)

lemma lb_ub_extensive:
  fixes A X::"'a::ord set"
  assumes "A \<subseteq> X"
  shows "A \<subseteq> (lb_set_in (ub_set_in A X) X)"
  by (meson assms ub_set_in_mem_iff subset_iff lb_set_in_mem_iff)

lemma lb_ub_isotone:
  "\<And>A B X.  A \<subseteq> B \<Longrightarrow>  (lb_set_in (ub_set_in A X) X) \<subseteq> (lb_set_in (ub_set_in B X) X)"
  by (simp add: lb_set_in_antitone1 ub_set_in_antitone1)


section MaxMin      
subsection Max
subsubsection Predicate                                  
lemma is_max_imp:
  "\<And>A x. is_max x A \<Longrightarrow> (x \<in> A \<and> x \<in> ub_set A)"
  by (simp add: is_max_def ub_set_in_ub_univ)

lemma is_max_if1:
  "\<And>A x.  (x \<in> A \<and> x \<in> ub_set A) \<Longrightarrow> is_max x A"
  by (simp add: is_max_def ub_set_in_ub_univ)
                                   
lemma is_max_if2:
  "\<And>A x.  x \<in> A \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> a \<le> x) \<Longrightarrow> is_max x A"
  by (simp add: is_max_if1 ub_set_mem_iff)
           
lemma is_max_imp_has_max:
  "\<And>A m. is_max m A \<Longrightarrow> has_max A"
  using has_max_def by auto
     
lemma is_max_iff:
  "is_max m A \<longleftrightarrow> m \<in> A \<and> (\<forall>a. a \<in> A \<longrightarrow> a \<le> m )"
  by (simp add: is_max_def ub_set_in_mem_iff)

lemma max_imp_ne:
  assumes "\<exists>m. is_max m A"
  shows "A \<noteq> {}"
  using assms is_max_def by auto

lemma max_isotone1:
  "\<And>A B ma mb. A \<subseteq> B \<and> (is_max ma A) \<and> ( is_max mb B) \<longrightarrow>  ma \<le> mb"
  using is_max_iff by blast

lemma is_max_top:
  fixes top::"'a::ord"
  assumes is_top:"\<forall>x. x \<le> top"
  shows "is_max top UNIV"
  by (simp add: is_max_iff is_top)
     
lemma is_max_singleton:
  "is_max (x::'a::order) {x}"
  by (simp add: is_max_iff)

subsubsection Existential                                  

lemma has_max_iff:
  "has_max A \<longleftrightarrow> (\<exists>m.  m \<in> A \<and> (\<forall>a. a \<in> A \<longrightarrow> a \<le> m ))"
  by (simp add: has_max_def is_max_iff)

lemma has_max_iff2:
  "has_max A \<longleftrightarrow> (\<exists>m. is_max m A)"
  by (simp add: has_max_def is_max_iff)

lemma max_unique:
  "\<And>(A::'a::order set) m1 m2. is_max m1 A \<Longrightarrow> is_max m2 A \<Longrightarrow> m1=m2"
  by (meson Orderings.order_eq_iff is_max_iff)  

lemma if_has_max_max_unique:
  assumes "has_max (A::'a::order set)"
  shows "\<exists>!m. is_max m A"
  using assms has_max_iff2 max_unique by blast

lemma has_max_singleton:
  "has_max {x::'a::order}"
  using has_max_def is_max_singleton by auto

lemma max_top:
  fixes top::"'a::ord"
  assumes is_top:"\<forall>x. x \<le> top"
  shows "has_max (UNIV::'a::ord set)"
proof-
  have B0:"is_max top UNIV"
    by (simp add: is_max_top is_top)
  have B1:"\<exists>(m::'a::ord). is_max m UNIV"
    using B0 by auto
  show ?thesis
    by (simp add: B1 has_max_def)
qed

subsubsection Operator        

lemma max_if:
  "\<And>(A::'a::order set) m. is_max m A \<Longrightarrow> m = max A"
  by (simp add: max_def max_unique the_equality)
 
lemma max_if2:
  "\<And>(A::'a::order set) x.  x \<in> A \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> a \<le> x) \<Longrightarrow>  x = max A"
  by (simp add: is_max_if2 max_if)
           
lemma max_isotone2:
  "\<And>(A::'a::order set) B. A \<subseteq> B \<and> (has_max A) \<and> ( has_max B) \<longrightarrow>  max A \<le> max B"
  by (metis if_has_max_max_unique max_if max_isotone1)

lemma max_singleton:
  "max {x::'a::order} = x"
  by(simp add: max_def is_max_def ub_set_in_def)

subsection Min
subsubsection Predicate
lemma is_min_imp:
  "\<And>A x. is_min x A \<Longrightarrow> (x \<in> A \<and> x \<in> lb_set A)"
  by (simp add: is_min_def lb_set_in_lb_univ)  
                                         
lemma is_min_if1:
  "\<And>A x.  (x \<in> A \<and> x \<in> lb_set A) \<Longrightarrow> is_min x A "
  by (simp add: is_min_def lb_set_in_lb_univ)  
       
lemma is_min_if2:
  "\<And>A x.  x \<in> A \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> x \<le> a) \<Longrightarrow> is_min x A"
  by (simp add: is_min_if1 lb_set_mem_iff)
  
lemma is_min_imp_has_min:
  "\<And>A m. is_min m A \<Longrightarrow> has_min A"
  using has_min_def by auto

lemma is_min_iff:
  "is_min m A \<longleftrightarrow> m \<in> A \<and> (\<forall>a. a \<in> A \<longrightarrow> m \<le> a )"
  by (simp add: is_min_def lb_set_in_mem_iff)

lemma min_imp_ne:
  assumes "\<exists>m. is_min m A"
  shows "A \<noteq> {}"
  using assms is_min_def by auto

lemma min_antitone1:
  "\<And>A B ma mb. A \<subseteq> B \<and> (is_min ma A) \<and> ( is_min mb B) \<longrightarrow>  mb \<le> ma"
  using is_min_iff by blast

lemma is_min_bot:
  fixes bot::"'a::ord"
  assumes is_bot:"\<forall>x. bot \<le> x"
  shows "is_min bot UNIV"
  by (simp add: is_min_iff is_bot)

lemma is_min_singleton:
  "is_min (x::'a::order) {x}"
  by (simp add: is_min_iff)

subsubsection Existential

lemma has_min_iff:
  "has_min A \<longleftrightarrow> (\<exists>m.  m \<in> A \<and> (\<forall>a. a \<in> A \<longrightarrow> m \<le> a ))"
  by (simp add: has_min_def is_min_iff)

lemma has_min_iff2:
  "has_min A \<longleftrightarrow> (\<exists>m. is_min m A)"
  by (simp add: has_min_def)

lemma min_unique:
  "\<And>(A::'a::order set) m1 m2. is_min m1 A \<Longrightarrow> is_min m2 A \<Longrightarrow> m1=m2"
  by (meson Orderings.order_eq_iff is_min_iff)  

lemma if_has_min_min_unique:
  assumes "has_min (A::'a::order set)"
  shows "\<exists>!m. is_min m A"
  using assms has_min_iff2 min_unique by blast

lemma min_bot:
  fixes bot::"'a::ord"
  assumes is_bot:"\<forall>x. bot \<le> x"
  shows "has_min (UNIV::'a::ord set)"
proof-
  have B0:"is_min bot UNIV"
    by (simp add: is_min_bot is_bot)
  have B1:"\<exists>(m::'a::ord). is_min m UNIV"
    using B0 by auto
  show ?thesis
    by (simp add: B1 has_min_def)
qed

lemma has_min_singleton:
  "has_min {x::'a::order}"
  using has_min_def is_min_singleton by auto

subsubsection Operator

lemma min_if:
  "\<And>(A::'a::order set) m. is_min m A \<Longrightarrow> m = min A"
  by (simp add: min_def min_unique the_equality)
          
lemma min_if2:
  "\<And>(A::'a::order set) x.  x \<in> A \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> x \<le> a) \<Longrightarrow>  x = min A"
  by (simp add: is_min_if2 min_if)
  
lemma min_antitone2:
  "\<And>(A::'a::order set) B. A \<subseteq> B \<and> (has_min A) \<and> ( has_min B) \<longrightarrow>  min B \<le> min A"
  by (metis has_min_def is_min_iff min_if subset_iff)

lemma min_singleton:
  "min {x::'a::order} = x"  
  by(simp add: min_def is_min_def lb_set_in_def)


section RelativeExtrema
subsection Suprema

lemma is_sup_in_iff:
  "is_sup_in m A X \<longleftrightarrow> (is_min m ( ub_set_in A X))"
  by (simp add: is_sup_in_def)

lemma is_sup_in_imp1:
  "\<And>m A X. is_sup_in m A X  \<Longrightarrow>  (m \<in>( ub_set_in A X) \<and> is_min m (ub_set_in A X))"
  by (simp add: is_min_imp is_sup_in_iff)

lemma is_sup_in_imp2:
  "\<And>m A X. is_sup_in m A X  \<Longrightarrow>   (\<And>a. a \<in> A \<Longrightarrow> a \<le> m)"
  by (simp add:  is_sup_in_def is_min_def ub_set_in_def)

lemma is_sup_in_imp3:
  "\<And>m A X. is_sup_in m A X  \<Longrightarrow>  (\<And>u. u \<in> X \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> a \<le> u) \<Longrightarrow> m \<le> u)"
  by (simp add: is_min_iff is_sup_in_def ub_set_in_mem_iff)

lemma is_sup_in_in_set:
  "\<And>m A X. is_sup_in m A X \<Longrightarrow> m \<in> X"
  by (simp add: is_sup_in_def is_sup_in_imp1 is_min_iff ub_set_in_mem_iff)

lemma is_sup_in_if1:
  "\<And>m A X. m \<in> X \<Longrightarrow>  (m \<in>( ub_set_in A X) \<and> is_min m (ub_set_in A X)) \<Longrightarrow> is_sup_in m A X "
  by (simp add: is_sup_in_def)

lemma is_sup_in_if2:
  "\<And>m A X. m \<in> X \<Longrightarrow>  (\<And>a. a \<in> A \<Longrightarrow> a \<le> m) \<Longrightarrow> is_min m (ub_set_in A X) \<Longrightarrow> is_sup_in m A X "
  by (simp add: is_sup_in_def)

lemma is_sup_in_if3:
  "\<And>m A X. m \<in> X \<Longrightarrow>  (\<And>a. a \<in> A \<Longrightarrow> a \<le> m) \<Longrightarrow>  (\<And>u. u \<in> X \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> a \<le> u) \<Longrightarrow> m \<le> u) \<Longrightarrow> is_sup_in m A X "
  by (simp add: is_min_iff is_sup_in_def ub_set_in_mem_iff)

lemma sup_in_unique:
  "\<And>(A::'a::order set) X m1 m2. is_sup_in m1 A X \<Longrightarrow> is_sup_in m2 A X \<Longrightarrow> m1=m2"
  by (simp add: is_sup_in_def min_unique)

lemma if_has_sup_in_unique:
  assumes "has_sup_in (A::'a::order set) X"
  shows "\<exists>!m. is_sup_in m A X"
  using assms has_sup_in_def if_has_min_min_unique is_sup_in_def by blast

lemma has_sup_in_has_lub:
  "\<And>A B.  has_sup_in A B \<Longrightarrow> has_min(ub_set_in A B)"
  by (simp add: has_sup_in_def)

lemma supin_is_sup_obtain:
  fixes A B::"'a::order set"
  assumes A0:"has_sup_in A B"
  obtains s where "is_sup_in s A B"
  using assms if_has_sup_in_unique by blast

lemma supin_is_sup:
  fixes A B::"'a::order set"
  assumes A0:"has_sup_in A B"
  shows "is_sup_in (SupIn A B) A B"
  by (metis SupIn_def assms if_has_sup_in_unique the_equality)

lemma has_sup_in_imp1:
  "\<And>(A::'a::order set) X. has_sup_in A X  \<Longrightarrow>  ((SupIn A X) \<in>( ub_set_in A X) \<and> is_min (SupIn A X) (ub_set_in A X))"
  using is_sup_in_imp1 supin_is_sup by blast

lemma has_sup_in_imp2:
  "\<And>(A::'a::order set) X. has_sup_in A X  \<Longrightarrow>  (\<And>a. a \<in> A \<Longrightarrow> a \<le> (SupIn A X))"
  using is_sup_in_imp2 supin_is_sup by blast

lemma has_sup_in_imp3:
  "\<And>(A::'a::order set) X. has_sup_in A X  \<Longrightarrow> (\<And>u. u \<in> X \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> a \<le> u) \<Longrightarrow> (SupIn A X) \<le> u)"
  using is_sup_in_imp3 supin_is_sup by blast

lemma has_sup_in_in_set:
  "\<And>(A::'a::order set) X. has_sup_in A X \<Longrightarrow> (SupIn A X) \<in> X"
  using is_sup_in_in_set supin_is_sup by blast

lemma sup_in_degenerate:  
  assumes A0:"has_min (X::'a::order set)"
  shows "SupIn {} X = min X"
  by (simp add: min_def SupIn_def is_sup_in_iff ub_set_in_degenerate)

lemma is_supin_singleton:
  "is_sup_in (x::'a::order) {x} UNIV"
  by(simp add:is_sup_in_def ub_set_in_def is_min_def lb_set_in_def)

lemma is_supin_singleton2:
  "(x::'a::order) \<in> X \<Longrightarrow> is_sup_in x {x} X"
  by (simp add: is_sup_in_def ub_set_in_def is_min_def lb_set_in_def)

lemma has_supin_singleton2:
  "(x::'a::order) \<in> X \<Longrightarrow> has_sup_in {x} X"
  using has_sup_in_def is_min_imp_has_min is_sup_in_def is_supin_singleton2 by blast

lemma supin_singleton:
  "SupIn {x::'a::order} UNIV = x"
  apply(simp add: SupIn_def)
  using is_supin_singleton sup_in_unique by blast

lemma supin_singleton2:
  "(x::'a::order) \<in> X \<Longrightarrow> SupIn {x} X = x"
  by (meson has_supin_singleton2 sup_in_unique supin_is_sup is_supin_singleton2)

lemma sup_in_max:
  fixes X::"'a::order set"
  assumes "has_sup_in X X"
  shows "is_max (SupIn X X) X"
  by (simp add: assms has_sup_in_imp2 has_sup_in_in_set is_max_if2)

lemma sup_in_isotone1:
  "\<And>(A::'a::order set) B X. has_sup_in A X \<Longrightarrow> has_sup_in B X \<Longrightarrow> A \<subseteq> B \<Longrightarrow> SupIn A X \<le> SupIn B X"
  by (meson  supin_is_sup is_sup_in_imp1 is_min_iff ub_set_in_antitone1 subsetD)

lemma sup_in_antitone2:
  "\<And>(A::'a::order set) B X. has_sup_in A X \<Longrightarrow> has_sup_in A B \<Longrightarrow> B \<subseteq> X \<Longrightarrow> SupIn A X \<le> SupIn A B"
  by (meson is_sup_in_def min_antitone1 supin_is_sup ub_set_in_isotone2)

lemma is_sup_in_sup_eq:
  "\<And>(s::'a::order) A X. is_sup_in s A X \<Longrightarrow> (s = SupIn A X)"
  by (simp add: SupIn_def sup_in_unique the_equality)

context   
fixes A B C::"'a::order set"
  assumes A0:"A \<noteq> {} \<and> A \<subseteq> B \<and> B \<subseteq> C" and
          A1:"has_sup_in A C" and
          A2:"has_sup_in A B"
begin

lemma sup_geq_rsup:
  "SupIn A C \<le> SupIn A B"
  by (simp add: A0 A1 A2 sup_in_antitone2)

lemma sup_leq_rsup_if:
  "SupIn A C \<ge> SupIn A B \<longleftrightarrow> (SupIn A C \<in> B)" (is "?L \<longleftrightarrow> ?R")
proof
  assume L:?L show ?R
    by (metis A0 A1 A2 L dual_order.antisym has_sup_in_in_set sup_in_antitone2)
  next
  assume R:?R show ?L
    by (simp add: A1 A2 R has_sup_in_imp2 has_sup_in_imp3)
qed

end

(*
lemma sup_geq_rsup:
  fixes A B C::"'a::order set"
  assumes A0:"A \<noteq> {} \<and> A \<subseteq> B \<and> B \<subseteq> C" and
          A1:"has_sup_in A C" and
          A2:"has_sup_in A B"
  shows "SupIn A C \<le> SupIn A B"
  by (simp add: A0 A1 A2 sup_in_antitone2)

lemma sup_leq_rsup_if:
  fixes A B C::"'a::order set"
  assumes A0:"A \<noteq> {} \<and> A \<subseteq> B \<and> B \<subseteq> C" and
          A1:"has_sup_in A C" and
          A2:"has_sup_in A B"
  shows "SupIn A C \<ge> SupIn A B \<longleftrightarrow> (SupIn A C \<in> B)" (is "?L \<longleftrightarrow> ?R")
proof
  assume L:?L show ?R
    by (metis A0 A1 A2 L dual_order.antisym has_sup_in_in_set sup_in_antitone2)
  next
  assume R:?R show ?L
    by (simp add: A1 A2 R has_sup_in_imp2 has_sup_in_imp3)
qed
*)

(*
  this is more familiar if we take B=Y and C=UNIV so that 
  Sup A \<in> Y then Sup_{Y} A exists and equals Sup A
*)
lemma sup_subset_eq:
  fixes A B C::"'a::order set"
  assumes A0:"A \<subseteq> B" and A1:"B \<subseteq> C" and A2:"has_sup_in A C" and A3:"SupIn A C \<in> B"
  shows "has_sup_in A B \<and> SupIn A B = SupIn A C"
proof-
  let ?sc="SupIn A C"
  have B0:"is_sup_in ?sc A C"
    by (simp add: A2 supin_is_sup)
  have B1:"ub_set_in A B \<subseteq> ub_set_in A C"
    by (simp add: A1 ub_set_in_isotone2)
  have B2:"\<forall>u \<in> ub_set_in A C. ?sc \<le> u"
    by (simp add: A2 has_sup_in_imp3 ub_set_in_mem_iff)
  have B3:"\<forall>u \<in> ub_set_in A B. ?sc \<le> u"
    using B1 B2 by blast
  have B4:"?sc \<in> ub_set_in A B"
    by (simp add: A2 A3 has_sup_in_imp2 ub_set_in_elm)
  have B5:"is_min ?sc (ub_set_in A B)"
    by (simp add: B3 B4 is_min_if2)
  have B6:"is_sup_in ?sc A B"
    by (simp add: B5 is_sup_in_def)
  have B7:"has_sup_in A B"
    using B5 has_sup_in_def is_min_imp_has_min by auto
  show ?thesis
    using B6 B7 is_sup_in_sup_eq by force
qed

lemma sup_in_expression:
  "is_sup_in m A X \<longleftrightarrow> m \<in> (lb_set_in (ub_set_in A X) X) \<inter> (ub_set_in A X)" (is "?L \<longleftrightarrow> ?R")
proof
  assume L:"?L" show "?R"
  by (metis IntI L is_min_imp is_sup_in_imp1 lb_set_in_lb_inter ub_set_in_mem_iff)
  next
  assume R:"?R" show "?L"
    by (metis IntD2 R inf_commute is_min_if1 is_sup_in_def lb_set_in_lb_inter)
qed

lemma sup_in_lbub_:
  "is_sup_in m A X \<Longrightarrow>  m \<in> (lb_set_in (ub_set_in A X) X)"
  by (simp add: sup_in_expression)

lemma sup_in_lbub_super:
  "is_sup_in m A X \<Longrightarrow> A \<subseteq> B \<Longrightarrow>  m \<in> (lb_set_in (ub_set_in B X) X)"
  by (simp add: is_sup_in_imp3 is_sup_in_in_set lb_set_in_mem_iff subsetD ub_set_in_mem_iff)

lemma sup_complete_has_max:
  "\<And>(X::'a::order set). X \<noteq> {} \<Longrightarrow> is_sup_complete X \<Longrightarrow> (is_max (SupIn X X) X)"
  by (simp add: is_sup_complete_def sup_in_max)

lemma sup_complete_bounded_inf:
  fixes X::"'a::order set"
  assumes A0:"is_sup_complete X"
  shows "\<And>A. (A \<subseteq> X \<and>  lb_set_in A X \<noteq> {}) \<longrightarrow> (has_inf_in A X)"
proof
  fix A
  assume  A1:"A \<subseteq> X \<and>  (lb_set_in A X \<noteq> {})" 
  let ?L="lb_set_in A X"
  have B0:"?L \<subseteq> X"
    by (simp add: lb_set_in_subset)
  have B1:"has_sup_in ?L X"
    using A1 B0 assms is_sup_complete_def by blast
  have B2:"(SupIn ?L X) \<in> ?L"
    by (meson A1 B1 has_sup_in_imp3 has_sup_in_in_set lb_set_in_elm lb_set_in_imp subsetD)
  show "has_inf_in A X"
  proof(cases "A = {}")
    case True
    then show ?thesis
      by (metis B1 has_inf_in_def has_max_iff2 lb_set_in_degenerate sup_in_max)
  next
    case False
    then show ?thesis
      by (meson B1 B2 has_inf_in_def has_max_iff has_sup_in_imp2)
  qed
qed


lemma sup_in_comp_un_ind:
  fixes F::"'b \<Rightarrow> 'a::order set" and I::"'b set" and X::"'a::order set"
  defines "SupX \<equiv> (\<lambda>A. SupIn A X)"
  assumes A0:"I \<noteq> {}" and
          A1:"\<And>i. i \<in> I  \<Longrightarrow> has_sup_in (F i) X" and
          A2:"has_sup_in (SupX`(F`I)) X"
  shows "(has_sup_in (\<Union>i \<in> I. F i)) X \<and> SupIn (SupX`(F`I)) X = SupIn (\<Union>i \<in> I. F i) X"
proof-
  define A where A3:"A=(\<Union>i \<in> I. F i)"
  define G where A4:"G= SupX`(F`I)"
  have B0:"\<And>i. i \<in> I \<longrightarrow> (F i) \<subseteq> A"
    by (simp add: A3 SUP_upper)
  have B1:"\<And>i. i \<in> I \<longrightarrow> (\<forall>u. u \<in>(ub_set_in A X) \<longrightarrow> SupIn (F i) X \<le> u)"
    using A1 B0 has_sup_in_imp3 ub_set_in_mem_iff by fastforce
  have B2:"\<And>i. i \<in> I \<longrightarrow> ub_set_in A X \<subseteq> ub_set_in {(SupIn (F i) X)} X"
    by (simp add: B1 ub_set_in_mem_iff subset_eq)
  have B3:"ub_set_in A X \<subseteq> ub_set_in G X"
    apply(simp add:A3 A4 SupX_def)
    by (smt (verit, del_insts) A3 B1 imageE ub_set_in_mem_iff subset_eq)
  have B4:"\<And>u. u \<in> ub_set_in A X \<longrightarrow>  SupIn G X \<le> u" 
    using A2 A4 B3 has_sup_in_imp1 is_min_iff by blast
  have B5:"\<And>a. a \<in> A \<longrightarrow> a \<le> SupIn G X"
  proof
    fix a assume A5:"a \<in> A"
    obtain i where A6:"i \<in> I \<and> a \<in> F i"
      using A3 A5 by blast
    have B6:"a \<le> SupIn (F i) X "
      by (simp add: A1 A6 has_sup_in_imp2)
    show " a \<le> SupIn G X "
      by (metis A2 A4 A6 B6 SupX_def dual_order.trans has_sup_in_imp2 image_eqI)
  qed
  have B8:"is_sup_in (SupIn G X) A X"
    by (metis A2 A4 B4 B5 has_sup_in_in_set is_sup_in_def is_min_iff ub_set_in_elm)
  have B9:"has_sup_in A X"
    using B8 has_sup_in_def is_sup_in_imp1 is_min_imp_has_min by blast
  have B10:"SupIn G X = SupIn A X"
    by (simp add: B8 is_sup_in_sup_eq)
  show ?thesis
    using A3 A4 B10 B9 by blast
qed


lemma sup_in_comp_un_ind2:
  fixes B::"'b \<Rightarrow> 'a::order set" and I::"'b set" and X::"'a::order set"
  defines "S \<equiv> {bi. \<exists>i \<in> I. bi =(SupIn (B i) X)}" and  "A \<equiv> (\<Union>i \<in> I. B i)"
  assumes A0:"I \<noteq> {}" and
          A1:"\<forall>i \<in> I.  has_sup_in (B i) X \<and> (B i \<noteq> {})" and
          A2:"has_sup_in S X"
  shows "has_sup_in A X \<and> SupIn S X = SupIn A X"
proof-
  let ?b="SupIn S X"
  have B0:"\<forall>x \<in> A. x \<le> ?b"
  proof
    fix x assume A3:"x \<in> A"
    obtain i where B01:"i \<in> I \<and> x \<in> (B i)"
      using A3 A_def by blast
    have B02:"x \<le> (SupIn (B i) X)"
      by (simp add: A1 B01 has_sup_in_imp2)
    have B03:"(SupIn (B i) X) \<in> S"
      using B01 S_def by blast
    have B03:"(SupIn (B i) X) \<le> ?b"
      by (simp add: A2 B03 has_sup_in_imp2)
    show "x \<le> ?b"
      using B02 B03 by auto
  qed
  have B1:"\<And>u bi. u \<in> ub_set_in A X \<and> bi \<in> S \<longrightarrow> bi \<le> u "
  proof
    fix u bi assume A4:"u \<in> ub_set_in A X \<and> bi \<in> S"
    have B10:"\<forall>i \<in> I. \<forall>x \<in> (B i). x \<le> u"
      by (metis A4 A_def UN_I ub_set_in_imp)
    obtain i where B11:"i \<in> I \<and> (bi = SupIn (B i) X)"
      using A4 S_def by blast
    show "bi \<le> u"
      by (metis A1 A4 B10 B11 has_sup_in_imp3 ub_set_in_mem_iff)
  qed
  have B2:"?b \<in> ub_set_in A X"
    by (simp add: A2 B0 has_sup_in_in_set ub_set_in_elm)
  have B3:"is_min ?b ( ub_set_in A X)"
    by (meson A2 B1 B2 has_sup_in_imp3 in_mono is_min_if2 ub_set_in_subset)
  have B4:"is_sup_in ?b A X  \<and> has_sup_in A X"
    using B3 has_sup_in_def is_min_imp_has_min is_sup_in_def by blast
  have B5:"SupIn S X = SupIn A X"
    by (simp add: B4 is_sup_in_sup_eq)
  show ?thesis
    by (simp add: B4 B5)
qed

lemma sup_in_comp_un:
  fixes F::"'a::order set set" and  X::"'a::order set"
  defines "SupX \<equiv> (\<lambda>A. SupIn A X)"
  assumes A0:"F \<noteq> {}" and A1:"\<And>A. A \<in> F \<Longrightarrow> has_sup_in A X" and A2:"has_sup_in (SupX`(F)) X"
  shows "(has_sup_in (\<Union>F) X) \<and> (SupIn (SupX`(F)) X = SupIn (\<Union>F) X)"
proof-
  define A where A3:"A=\<Union>F"
  define G where A4:"G=SupX`(F)"
  have B0:"\<And>E. E \<in> F \<Longrightarrow> E \<subseteq> A"
    by (simp add: A3 Union_upper)
  have B1:"\<And>E. E \<in> F \<Longrightarrow> (\<forall>u. u \<in>(ub_set_in A X) \<longrightarrow> SupIn E X \<le> u)"
    using A1 B0 has_sup_in_imp3 ub_set_in_mem_iff by fastforce
  have B2:"\<And>E. E \<in> F \<Longrightarrow> ub_set_in A X \<subseteq> ub_set_in {(SupIn E X)} X"
    by (simp add: B1 subset_eq ub_set_in_mem_iff)
  have B3:"ub_set_in A X \<subseteq> ub_set_in G X"
    apply(simp add:A3 A4 SupX_def)
    by (smt (verit, del_insts) A3 B1 imageE subset_eq ub_set_in_mem_iff)
  have B4:"\<And>u. u \<in> ub_set_in A X \<longrightarrow> SupIn G X \<le> u"
    using A2 A4 B3 has_sup_in_imp1 is_min_iff by blast
  have B5:"\<And>a. a \<in> A \<longrightarrow> a \<le> SupIn G X"
  proof
    fix a assume A5:"a \<in> A"
    obtain E  where A6:"E \<in> F \<and> a \<in> E"
      using A3 A5 by blast
    have B6:"a \<le> SupIn E X"
      using A1 A6 is_sup_in_imp2 supin_is_sup by blast
    show "a \<le> SupIn G X"
      by (metis A2 A4 A6 B6 SupX_def has_sup_in_imp2 imageI order.trans)
  qed
  have B8:"is_sup_in (SupIn G X) A X"
    by (metis A2 A4 B4 B5 has_sup_in_in_set is_sup_in_if3 ub_set_in_elm)
  have B9:"has_sup_in A X"
    using B8 has_sup_in_def is_min_imp_has_min is_sup_in_def by blast
  have B10:"SupIn G X = SupIn A X"
    by (simp add: B8 is_sup_in_sup_eq)
  show ?thesis
    using A3 A4 B9 B10 by blast
qed


lemma is_sup_in_if4:
  "m \<in> X \<Longrightarrow>  (\<And>a. a \<in> A \<Longrightarrow> a \<le> m) \<Longrightarrow>  (\<And>u. u \<in> X \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> a \<le> u) \<Longrightarrow> m \<le> u) \<Longrightarrow> is_sup_in m A X "
  by (simp add: is_min_iff is_sup_in_def ub_set_in_mem_iff)

lemma is_sup_in_im:
  "is_sup_in s (g`(f`A)) X \<longleftrightarrow>  is_sup_in s ((g \<circ> f)`A) X"
  by (simp add: image_comp)             

lemma is_sup_in_im_ex1:
  "has_sup_in  (g`(f`A)) X \<Longrightarrow>  has_sup_in  ((g \<circ> f)`A) X"
  by (simp add: image_comp)   

lemma is_sup_in_im_ex2:
  "has_sup_in  ((g \<circ> f)`A) X \<Longrightarrow> has_sup_in  (g`(f`A)) X "
  by (simp add: image_comp)  

lemma sup_in_im:
  assumes "has_sup_in  (g`(f`A)) X \<or> has_sup_in  ((g \<circ> f)`A) X "
  shows "SupIn (g`(f`A)) X \<longleftrightarrow>  SupIn ((g \<circ> f)`A) X"
  by (simp add: image_comp)                  

lemma is_sup_in_id_im:
  "is_sup_in s ((id::'a::ord set \<Rightarrow> 'a::ord set)`A)  X \<longleftrightarrow>  is_sup_in s A X"
  by simp

lemma is_sup_in_cong:
  "A = B \<Longrightarrow> (\<And>x. x \<in> B \<Longrightarrow> C x = D x) \<Longrightarrow> (is_sup_in s (C`A) X \<longleftrightarrow> is_sup_in s (D`B) X)"
  by force

lemma sup_in_eqI:
  fixes f::"'b \<Rightarrow> 'a::order" and X::"'a::order set" and I::"'b set"
  shows "(m::'a::order) \<in> X \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> (f i) \<le> m) \<Longrightarrow> (\<And>u. u \<in> X \<Longrightarrow>  (\<And>i. i \<in> I \<Longrightarrow> f i \<le> u) \<Longrightarrow> m \<le> u) \<Longrightarrow>  is_sup_in m (f`I) X"
  apply (simp add: is_min_iff is_sup_in_def ub_set_in_mem_iff)
  by blast

lemma sup_in_eq2:
  fixes f::"'b \<Rightarrow> 'a::order" and X::"'a::order set" and I::"'b set"
  shows "(m::'a::order) \<in> X \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> (f i) \<le> m) \<Longrightarrow> (\<And>u. u \<in> X \<Longrightarrow>  (\<And>i. i \<in> I \<Longrightarrow> f i \<le> u) \<Longrightarrow> m \<le> u) \<Longrightarrow> m = SupIn (f`I) X"
  by (simp add: sup_in_eqI is_sup_in_sup_eq)



subsection Infima

lemma is_inf_in_iff:
  "is_inf_in m A X \<longleftrightarrow> (is_max m (lb_set_in A X))"
  by (simp add: is_inf_in_def)

lemma is_inf_in_imp1:
  "\<And>m A X. is_inf_in m A X  \<Longrightarrow>  (m \<in>(lb_set_in A X) \<and> is_max m (lb_set_in A X))"
  by (simp add: is_max_imp is_inf_in_iff)

lemma is_inf_in_imp2:
  "\<And>m A X. is_inf_in m A X  \<Longrightarrow>   (\<And>a. a \<in> A \<Longrightarrow> m \<le> a)"
  by (simp add:  is_inf_in_def is_max_def lb_set_in_def)

lemma is_inf_in_imp3:
  "\<And>m A X. is_inf_in m A X  \<Longrightarrow>  (\<And>l. l \<in> X \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> l \<le> a) \<Longrightarrow> l \<le> m)"
  by (simp add: is_max_iff is_inf_in_def lb_set_in_mem_iff)

lemma is_inf_in_in_set:
  "\<And>m A X. is_inf_in m A X \<Longrightarrow> m \<in> X"
  by (simp add: is_inf_in_def is_inf_in_imp1 is_max_iff lb_set_in_mem_iff)


lemma is_inf_in_if1:
  "\<And>m A X. m \<in> X \<Longrightarrow>  (m \<in>( lb_set_in A X) \<and> is_max m (lb_set_in A X)) \<Longrightarrow> is_inf_in m A X "
  by (simp add: is_inf_in_def)

lemma is_inf_in_if2:
  "\<And>m A X. m \<in> X \<Longrightarrow>  (\<And>a. a \<in> A \<Longrightarrow> m \<le> a) \<Longrightarrow> is_max m (lb_set_in A X) \<Longrightarrow> is_inf_in m A X "
  by (simp add: is_inf_in_def)

lemma is_inf_in_if3:
  "\<And>m A X. m \<in> X \<Longrightarrow>  (\<And>a. a \<in> A \<Longrightarrow> m \<le> a) \<Longrightarrow>  (\<And>l. l \<in> X \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> l \<le> a) \<Longrightarrow> l \<le> m) \<Longrightarrow> is_inf_in m A X "
  by (simp add: is_max_iff is_inf_in_def lb_set_in_mem_iff)

lemma inf_in_unique:
  "\<And>(A::'a::order set) X m1 m2. is_inf_in m1 A X \<Longrightarrow> is_inf_in m2 A X \<Longrightarrow> m1=m2"  
  by (simp add: is_inf_in_def max_unique)

lemma if_has_inf_in_unique:
  assumes "has_inf_in (A::'a::order set) X"
  shows "\<exists>!m. is_inf_in m A X"
  using assms has_inf_in_def if_has_max_max_unique is_inf_in_def by blast

lemma has_inf_in_has_glb:
  "\<And>A B.  has_inf_in A B \<Longrightarrow> has_max (lb_set_in A B)"
  by (simp add: has_inf_in_def)

lemma infin_is_inf_obtain:
  fixes A B::"'a::order set"
  assumes A0:"has_inf_in A B"
  obtains i where "is_inf_in i A B"
  using assms if_has_inf_in_unique by blast

lemma infin_is_inf:
  fixes A B::"'a::order set"
  assumes A0:"has_inf_in A B"
  shows "is_inf_in (InfIn A B) A B"
  by (metis InfIn_def assms if_has_inf_in_unique the_equality)



lemma has_inf_in_imp1:
  "\<And>(A::'a::order set) X. has_inf_in A X  \<Longrightarrow>  ((InfIn A X) \<in>(lb_set_in A X) \<and> is_max (InfIn A X) (lb_set_in A X))"
  using is_inf_in_imp1 infin_is_inf by blast

lemma has_inf_in_imp2:
  "\<And>(A::'a::order set) X. has_inf_in A X  \<Longrightarrow>  (\<And>a. a \<in> A \<Longrightarrow> a \<ge> (InfIn A X))"
  using is_inf_in_imp2 infin_is_inf by blast

lemma has_inf_in_imp3:
  "\<And>(A::'a::order set) X. has_inf_in A X  \<Longrightarrow> (\<And>u. u \<in> X \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> a \<ge> u) \<Longrightarrow> (InfIn A X) \<ge> u)"
  using is_inf_in_imp3 infin_is_inf by blast

lemma has_inf_in_in_set:
  "\<And>(A::'a::order set) X. has_inf_in A X \<Longrightarrow> (InfIn A X) \<in> X"
  using is_inf_in_in_set infin_is_inf by blast


lemma inf_in_degenerate:  
  assumes A0:"has_max (X::'a::order set)"
  shows "InfIn {} X = max X"
  by (simp add: max_def InfIn_def is_inf_in_iff lb_set_in_degenerate)

lemma is_infin_singleton:
  "is_inf_in (x::'a::order) {x} UNIV"
  by(simp add: is_inf_in_def lb_set_in_def is_max_def ub_set_in_def)

lemma is_infin_singleton2:
  "(x::'a::order) \<in> X \<Longrightarrow> is_inf_in x {x} X"
  by (simp add: is_inf_in_def lb_set_in_def is_max_def ub_set_in_def)

lemma has_infin_singleton2:
  "(x::'a::order) \<in> X \<Longrightarrow> has_inf_in {x} X"
  by (meson has_inf_in_def is_inf_in_imp1 is_infin_singleton2 is_max_imp_has_max)


lemma infin_singleton:
  "InfIn {x::'a::order} UNIV = x"
  apply(simp add: InfIn_def)
  using is_infin_singleton inf_in_unique by blast

lemma infin_singleton2:
  "(x::'a::order) \<in> X \<Longrightarrow> InfIn {x} X = x"
  by (meson has_infin_singleton2 inf_in_unique infin_is_inf is_infin_singleton2)

lemma infin_eq_infun:
  assumes A0:"has_inf_in (A::'a::order set) UNIV"
  shows "InfIn A UNIV = InfUn A"
  by (simp add: InfIn_def InfUn_def is_inf_in_def is_inf_def lb_set_in_univ_absorb)

lemma inf_in_min:
  fixes X::"'a::order set"
  assumes "has_inf_in X X"
  shows "is_min (InfIn X X) X"
  by (simp add: assms has_inf_in_imp2 has_inf_in_in_set is_min_if2)

lemma inf_in_antitone1:
  "\<And>(A::'a::order set) B X. has_inf_in A X \<Longrightarrow> has_inf_in B X \<Longrightarrow> A \<subseteq> B \<Longrightarrow> InfIn B X \<le> InfIn A X"
  by (meson  infin_is_inf is_inf_in_imp1 is_max_iff lb_set_in_antitone1 subsetD)

lemma inf_in_isotone2:
  "\<And>(A::'a::order set) B X. has_inf_in A X \<Longrightarrow> has_inf_in A B \<Longrightarrow> B \<subseteq> X \<Longrightarrow> InfIn A B \<le> InfIn A X"
  by (meson in_mono infin_is_inf is_inf_in_imp1 is_max_iff lb_set_in_isotone2)

lemma is_inf_in_inf_eq:
  "\<And>(i::'a::order) A X. is_inf_in i A X \<Longrightarrow> (i = InfIn A X)"
  by (simp add: InfIn_def Uniq_def inf_in_unique the1_equality')

lemma inf_leq_rinf:
  fixes A B C::"'a::order set"
  assumes A0:"A \<noteq> {} \<and> A \<subseteq> B \<and> B \<subseteq> C" and
          A1:"has_inf_in A C" and
          A2:"has_inf_in A B"
  shows "InfIn A B \<le> InfIn A C"
  by (simp add: A0 A1 A2 inf_in_isotone2)

lemma inf_leq_rinf_if:
  fixes A B C::"'a::order set"
  assumes A0:"A \<noteq> {} \<and> A \<subseteq> B \<and> B \<subseteq> C" and
          A1:"has_inf_in A C" and
          A2:"has_inf_in A B"
  shows "InfIn A B \<ge> InfIn A C \<longleftrightarrow> (InfIn A C \<in> B)" (is "?L \<longleftrightarrow> ?R")
proof
  assume L:?L show ?R
    by (metis A0 A1 A2 L dual_order.antisym has_inf_in_in_set inf_in_isotone2)
  next
  assume R:?R show ?L
    by (simp add: A1 A2 R has_inf_in_imp2 has_inf_in_imp3)
qed

lemma inf_subset_eq:
  fixes A B C::"'a::order set"
  assumes A0:"A \<subseteq> B" and A1:"B \<subseteq> C" and A2:"has_inf_in A C" and A3:"InfIn A C \<in> B"
  shows "InfIn A B = InfIn A C"
proof-
  define ic where "ic =InfIn A C"
  have B0:"is_inf_in ic A C"
    by (simp add: A2 ic_def infin_is_inf)
  have B1:"ic \<in> lb_set_in A B"
    by (metis A3 B0 is_inf_in_imp1 ic_def lb_set_in_mem_iff)
  have B2:"lb_set_in A B \<subseteq> lb_set_in A C"
    by (simp add: A1 lb_set_in_isotone2)
  have B3:"is_max ic (lb_set_in A B)"
    by (meson B0 B1 B2 is_max_iff is_inf_in_def subset_eq)
  have B4:"is_inf_in ic A B"
    by (simp add: B3 is_inf_in_def)
  show ?thesis
    using B4 is_inf_in_inf_eq ic_def by force
qed

lemma inf_in_expression:
  "is_inf_in m A X \<longleftrightarrow> m \<in> (ub_set_in (lb_set_in A X) X) \<inter> (lb_set_in A X)" (is "?L \<longleftrightarrow> ?R")
proof
  assume L:"?L" show "?R"
  by (metis IntI L is_max_imp is_inf_in_imp1 ub_set_in_ub_inter lb_set_in_mem_iff)
  next
  assume R:"?R" show "?L"
    by (metis IntD2 R inf_commute is_inf_in_def is_max_if1 ub_set_in_ub_inter)
qed

lemma inf_in_ublb_:
  "is_inf_in m A X \<Longrightarrow>  m \<in> (ub_set_in (lb_set_in A X) X)"
  by (simp add: inf_in_expression)

lemma inf_in_lbub_super:
  "is_inf_in m A X \<Longrightarrow> A \<subseteq> B \<Longrightarrow>  m \<in> (ub_set_in (lb_set_in B X) X)"
  by (simp add: is_inf_in_imp3 is_inf_in_in_set ub_set_in_mem_iff subsetD lb_set_in_mem_iff)


lemma inf_complete_has_min:
  "\<And>(X::'a::order set). X \<noteq> {} \<Longrightarrow> is_inf_complete X \<Longrightarrow> (is_min (InfIn X X) X)"
  by (simp add: is_inf_complete_def inf_in_min)


lemma inf_complete_bounded_sup:
  fixes X::"'a::order set"
  assumes A0:"is_inf_complete X"
  shows "\<And>A. (A \<subseteq> X \<and>  ub_set_in A X \<noteq> {}) \<longrightarrow> (has_sup_in A X)"
proof
  fix A
  assume  A1:"A \<subseteq> X \<and>  (ub_set_in A X \<noteq> {})" 
  let ?U="ub_set_in A X"
  have B0:"?U \<subseteq> X"
    by (simp add: ub_set_in_subset)
  have B1:"has_inf_in ?U X"
    using A1 B0 assms is_inf_complete_def by blast
  have B2:"(InfIn ?U X) \<in> ?U"
    by (meson A1 B1 has_inf_in_imp3 has_inf_in_in_set ub_set_in_elm ub_set_in_imp subsetD)
  show "has_sup_in A X"
  proof(cases "A = {}")
    case True
    then show ?thesis
      by (metis B1 has_sup_in_def has_min_iff2 ub_set_in_degenerate inf_in_min)
  next
    case False
    then show ?thesis
      by (meson B1 B2 has_inf_in_imp2 has_min_iff has_sup_in_def)
  qed
qed



lemma inf_in_comp_un_ind:
  fixes F::"'b \<Rightarrow> 'a::order set" and I::"'b set" and X::"'a set"
  assumes A0:"I \<noteq> {}" and
          A1:"\<And>i. i \<in> I  \<Longrightarrow> has_inf_in (F i) X" and
          A2:"has_inf_in ((\<lambda>A. InfIn A X)`(F`I)) X"
  shows "(has_inf_in (\<Union>i \<in> I. F i)) X \<and> InfIn ((\<lambda>A. InfIn A X)`(F`I)) X = InfIn (\<Union>i \<in> I. F i) X"
proof-
  let ?A="(\<Union>i \<in> I. F i)"
  let ?G="(\<lambda>A. InfIn A X)`(F`I)"
  have B0:"\<And>i. i \<in> I \<longrightarrow> (F i) \<subseteq> ?A"
    by (simp add: SUP_upper)
  have B1:"\<And>i. i \<in> I \<longrightarrow> (\<forall>l. l \<in>(lb_set_in ?A X) \<longrightarrow> l \<le> InfIn (F i) X)"
    using A1 B0 has_inf_in_imp3 lb_set_in_mem_iff by fastforce
  have B3:"lb_set_in ?A X \<subseteq> lb_set_in ?G X"
    by (smt (verit, del_insts) B1 imageE lb_set_in_mem_iff subset_eq)
  have B4:"\<And>l. l \<in> lb_set_in ?A X \<longrightarrow> l  \<le> InfIn ?G X"
    using A2 B3 has_inf_in_imp1 is_max_iff by blast
  have B5:"\<And>a. a \<in> ?A \<longrightarrow> InfIn ?G X \<le> a"
  proof
    fix a assume A5:"a \<in> ?A"
    obtain i where A6:"i \<in> I \<and> a \<in> F i"
      using A5 by blast
    have B6:"InfIn (F i) X \<le> a"
      by (simp add: A1 A6 has_inf_in_imp2)
    show "InfIn ?G X \<le> a"
      by (metis A2 A6 B6 dual_order.trans has_inf_in_imp2 image_eqI)
  qed
  have B8:"is_inf_in (InfIn ?G X) ?A X"
    by (metis (no_types, lifting) A2 B4 B5 has_inf_in_in_set is_inf_in_def is_max_iff lb_set_in_elm)
  have B9:"has_inf_in ?A X"
    using B8 has_inf_in_def is_inf_in_imp1 is_max_imp_has_max by blast
  have B10:"InfIn ?G X = InfIn ?A X"
    by (simp add: B8 is_inf_in_inf_eq)
  show ?thesis
    using B4 B10 B9 by blast
qed



lemma inf_in_comp_un0:
  fixes F::"'a::order set set" and  X::"'a::order set"
  assumes A0:"F \<noteq> {}" and A1:"\<And>A. A \<in> F \<Longrightarrow> has_inf_in A X" and A2:"has_inf_in ((\<lambda>A. InfIn A X)`(F)) X"
  shows "lb_set_in (\<Union>F) X  \<subseteq>  lb_set_in ((\<lambda>A. InfIn A X)`(F)) X"
proof
  fix l assume A3:"l \<in> lb_set_in (\<Union>F) X "
  have B0:"l \<in> X \<and> (\<forall>x xa. x \<in> xa \<and> xa \<in> F \<longrightarrow> l \<le> x)"
    using A3 lb_set_in_mem_iff by fastforce
  have B1:"\<forall>A \<in> F. l \<le> InfIn A X"
  proof
    fix A assume A4:"A \<in> F"
    show "l \<le> InfIn A X"
      by (meson A1 A4 B0 has_inf_in_imp3)
  qed
  show "l \<in> lb_set_in ((\<lambda>A. InfIn A X)`(F)) X"
  apply(simp add: lb_set_in_def)
    using B0 B1 by blast
qed

lemma inf_in_comp_un1:
  fixes F::"'a::order set set" and  X::"'a::order set"
  assumes A0:"F \<noteq> {}" and A1:"\<And>A. A \<in> F \<Longrightarrow> has_inf_in A X" and A2:"has_inf_in ((\<lambda>A. InfIn A X)`(F)) X"
  shows "InfIn ((\<lambda>A. InfIn A X)`(F)) X \<in> (lb_set_in (\<Union>F) X)"
proof-
  let ?A="(\<Union>F)" let ?IA="(\<lambda>A. InfIn A X)`(F)" let ?I="InfIn ?IA X"
  have B1:"\<And>x xa. x \<in> xa \<and> xa \<in> F \<longrightarrow> ?I \<le> x"
    by (metis A1 A2 dual_order.trans has_inf_in_imp2 imageI)
  show "?I \<in> (lb_set_in ?A X)"
    apply(auto simp add: lb_set_in_def B1)
    using A2 has_inf_in_in_set by blast
qed

lemma inf_in_comp_un2:
  fixes F::"'a::order set set" and  X::"'a::order set"
  assumes A0:"F \<noteq> {}" and
          A1:"\<forall>A \<in> F.  has_inf_in A X" and 
          A2:"has_inf_in ((\<lambda>A. InfIn A X)`(F)) X"
  shows "(has_inf_in (\<Union>F) X) \<and> (InfIn ((\<lambda>A. InfIn A X)`(F)) X = InfIn (\<Union>F) X)"
  proof-
  let ?A="(\<Union>F)" let ?IA="(\<lambda>A. InfIn A X)`(F)" let ?I="InfIn ?IA X"
  have B0:"?I \<in> (lb_set_in ?A X)"
    using A0 A1 A2 inf_in_comp_un1 by blast
  have B1:"lb_set_in ?A X  \<subseteq>  lb_set_in ?IA X"
    by (simp add: A0 A1 A2 inf_in_comp_un0)
  have B2:"is_inf_in ?I ?A X"
    by (metis (mono_tags, lifting) A2 B0 B1 has_inf_in_imp1 has_inf_in_in_set in_mono is_inf_in_if1 is_max_iff)
  have B3:"has_inf_in ?A X"
    using B2 has_inf_in_def is_max_imp_has_max is_inf_in_def by blast
  have B4:"?I = InfIn ?A X"
    by (simp add: B2 is_inf_in_inf_eq)
  show ?thesis
    using B3 B4 by blast
qed


lemma inf_in_comp_un:
  fixes F::"'a::order set set" and  X::"'a::order set"
  assumes A0:"F \<noteq> {}" and A1:"\<And>A. A \<in> F \<Longrightarrow> has_inf_in A X" and A2:"has_inf_in ((\<lambda>A. InfIn A X)`(F)) X"
  shows "(has_inf_in (\<Union>F) X) \<and> (InfIn ((\<lambda>A. InfIn A X)`(F)) X = InfIn (\<Union>F) X)"
proof-
  let ?A="(\<Union>F)"
  let ?G="(\<lambda>A. InfIn A X)`(F)"
  have B0:"\<And>E. E \<in> F \<Longrightarrow> E \<subseteq> ?A"
    by (simp add: Union_upper)
  have B1:"\<And>E. E \<in> F \<Longrightarrow> (\<forall>l. l \<in>(lb_set_in ?A X) \<longrightarrow> l \<le> InfIn E X)"
    using A1 B0 has_inf_in_imp3 lb_set_in_mem_iff by fastforce
  have B2:"\<And>E. E \<in> F \<Longrightarrow> lb_set_in ?A X \<subseteq> lb_set_in {(InfIn E X)} X"
    by (simp add: B1 subset_eq lb_set_in_mem_iff)
  have B3:"lb_set_in ?A X \<subseteq> lb_set_in ?G X"
    using A0 A1 A2 inf_in_comp_un0 by blast
  have B4:"\<And>l. l \<in> lb_set_in ?A X \<longrightarrow>l \<le>  InfIn ?G X"
    using A2 B3 has_inf_in_imp1 is_max_iff by blast
  have B5:"\<And>a. a \<in> ?A \<longrightarrow> InfIn ?G X \<le> a"
  proof
    fix a assume A5:"a \<in> ?A"
    obtain E  where A6:"E \<in> F \<and> a \<in> E"
      using A5 by blast
    have B6:"InfIn E X \<le> a"
      using A1 A6 is_inf_in_imp2 infin_is_inf by blast
    show "InfIn ?G X \<le> a"
      by (metis A2 A6 B6 has_inf_in_imp2 imageI order.trans)
  qed
  have B8:"is_inf_in (InfIn ?G X) ?A X"
    by (metis A2 B4 B5 has_inf_in_in_set is_inf_in_if3 lb_set_in_elm)
  have B9:"has_inf_in ?A X"
    using B8 has_inf_in_def is_max_imp_has_max is_inf_in_def by blast
  have B10:"InfIn ?G X = InfIn ?A X"
    by (simp add: B8 is_inf_in_inf_eq)
  show ?thesis
    using  B9 B10 by blast
qed

lemma is_inf_in_if4:
  "m \<in> X \<Longrightarrow>  (\<And>a. a \<in> A \<Longrightarrow> m \<le> a) \<Longrightarrow>  (\<And>l. l \<in> X \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> l \<le> a) \<Longrightarrow> l \<le> m) \<Longrightarrow> is_inf_in m A X "
  by (simp add: is_max_iff is_inf_in_def lb_set_in_mem_iff)

lemma is_inf_in_im:
  "is_inf_in s (g`(f`A)) X \<longleftrightarrow>  is_inf_in s ((g \<circ> f)`A) X"
  by (simp add: image_comp)             

lemma is_inf_in_im_ex1:
  "has_inf_in  (g`(f`A)) X \<Longrightarrow>  has_inf_in  ((g \<circ> f)`A) X"
  by (simp add: image_comp)   

lemma is_inf_in_im_ex2:
  "has_inf_in  ((g \<circ> f)`A) X \<Longrightarrow> has_inf_in  (g`(f`A)) X "
  by (simp add: image_comp)  

lemma inf_in_im:
  assumes "has_inf_in  (g`(f`A)) X \<or> has_inf_in  ((g \<circ> f)`A) X "
  shows "InfIn (g`(f`A)) X \<longleftrightarrow>  InfIn ((g \<circ> f)`A) X"
  by (simp add: image_comp)                  

lemma is_inf_in_id_im:
  "is_inf_in s ((id::'a::ord set \<Rightarrow> 'a::ord set)`A)  X \<longleftrightarrow>  is_inf_in s A X"
  by simp

lemma is_inf_in_cong:
  "A = B \<Longrightarrow> (\<And>x. x \<in> B \<Longrightarrow> C x = D x) \<Longrightarrow> (is_inf_in s (C`A) X \<longleftrightarrow> is_inf_in s (D`B) X)"
  by force

lemma inf_in_eqI:
  fixes f::"'b \<Rightarrow> 'a::order" and X::"'a::order set" and I::"'b set"
  shows "(m::'a::order) \<in> X \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> m \<le> (f i)) \<Longrightarrow> (\<And>l. l \<in> X \<Longrightarrow>  (\<And>i. i \<in> I \<Longrightarrow> l \<le>  f i) \<Longrightarrow> l \<le> m) \<Longrightarrow>  is_inf_in m (f`I) X"
  apply (simp add: is_max_iff is_inf_in_def lb_set_in_mem_iff)
  by blast

lemma inf_in_eq2:
  fixes f::"'b \<Rightarrow> 'a::order" and X::"'a::order set" and I::"'b set"
  shows "(m::'a::order) \<in> X \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> m \<le> (f i)) \<Longrightarrow> (\<And>l. l \<in> X \<Longrightarrow>  (\<And>i. i \<in> I \<Longrightarrow> l \<le>  f i) \<Longrightarrow> l \<le> m) \<Longrightarrow> m = InfIn (f`I) X"
  by (simp add: inf_in_eqI is_inf_in_inf_eq)

lemma lb_set_inf_from_principal:
  fixes A X::"'a::order set"
  assumes A0:"A \<noteq> {}" and A1:"has_inf_in A X" and A2:"A \<subseteq> X"
  shows "lb_set_in {(InfIn A X)} X = (\<Inter>a \<in> A. lb_set_in {a} X)"
proof-
  obtain i where B0:"i = InfIn A X"
    by simp
  show "lb_set_in { InfIn A X} X = (\<Inter>a \<in> A. lb_set_in {a} X)"
     apply(auto simp add:lb_set_in_def)
    apply (metis A1 B0 dual_order.trans infin_is_inf is_inf_in_imp2)
    apply (metis A0 A1 B0 equals0I has_inf_in_imp3)
    using A0 by blast
qed

subsection ExtremaFromDual

lemma sup_in_eq_inf_in_ub:
  fixes A X::"'a::order set"
  assumes A0:"A \<subseteq> X" and A1:"has_inf_in (ub_set_in A X) X"
  shows "has_sup_in A X \<and> SupIn A X = InfIn(ub_set_in A X) X"
proof-
  let ?U="ub_set_in A X"
  let ?i="InfIn ?U X"
  have B0:"A \<subseteq> lb_set_in ?U X"
    by (simp add: A0 lb_ub_extensive)
  have B1:"\<forall>a. a \<in> A \<longrightarrow> a \<le> ?i"
    by (meson A0 A1 has_inf_in_imp3 subsetD ub_set_in_imp)
  have B2:"?i \<in> ?U"
    by (simp add: A1 B1 has_inf_in_in_set ub_set_in_elm)
  have B3:"is_min ?i ?U"
    by (simp add: A1 B2 has_inf_in_imp2 is_min_if2)
  show ?thesis
    using B3 has_sup_in_def has_sup_in_imp1 is_min_imp_has_min min_unique by blast
qed

lemma inf_in_eq_sup_in_lb:
  fixes A X::"'a::order set"
  assumes A0:"A \<subseteq> X" and A1:"has_sup_in (lb_set_in A X) X"
  shows "has_inf_in A X \<and> InfIn A X = SupIn(lb_set_in A X) X"
proof-
  let ?L="lb_set_in A X"
  let ?s="SupIn ?L X"
  have B0:"A \<subseteq> ub_set_in ?L X"
    by (meson A0 lb_set_in_imp subset_eq ub_set_in_elm)
  have B1:"?s \<in> lb_set_in A X"
    by (meson A1 B0 has_sup_in_imp1 has_sup_in_in_set is_min_iff lb_set_in_elm subset_eq)
  have B2:"is_max ?s ?L"
    by (simp add: A1 B1 has_sup_in_imp2 is_max_if2)
  show ?thesis
    by (metis B2 has_inf_in_def has_max_iff2 is_inf_in_iff is_inf_in_inf_eq)
qed
lemma inf_complete_bounded_sup_eq1:
  fixes A X::"'a::order set"
  assumes A0:"(A \<subseteq> X \<and> ub_set_in A X \<noteq> {})" and
          A1:"has_inf_in (ub_set_in A X) X"
  shows "SupIn A X = InfIn (ub_set_in A X) X"
proof(cases "A = {}")
  case True
  then show ?thesis
    by (metis A1 has_min_iff2 inf_in_min min_if sup_in_degenerate ub_set_in_degenerate)
next
  case False
  define U where "U=ub_set_in A X"
  define I where "I=InfIn U X"
  have B0:"I \<in> U"
  proof-
    have B00:"I \<in> X"
      by (simp add: A1 I_def U_def has_inf_in_in_set)
    have B01:"\<forall>a. a \<in> A \<longrightarrow> a \<le> I"
      by (metis A0 A1 I_def U_def has_inf_in_imp3 subsetD ub_set_in_imp)
    show ?thesis
      by (simp add: B00 B01 U_def ub_set_in_elm)
  qed
  have B1:"\<forall>u. u \<in> U \<longrightarrow> I \<le> u"
    by (simp add: A1 I_def U_def has_inf_in_imp2)
  have B2:"is_sup_in I A X"
    by (metis B0 B1 U_def is_min_if2 is_sup_in_def)
  then show ?thesis
    using I_def U_def is_sup_in_sup_eq by fastforce
qed

lemma sup_complete_bounded_inf_eq1:
  fixes A X::"'a::order set"
  assumes A0:"(A \<subseteq> X \<and>  lb_set_in A X \<noteq> {})" and
          A1:"has_sup_in (lb_set_in A X) X"
  shows "InfIn A X = SupIn (lb_set_in A X) X"
proof(cases "A = {}")
  case True
  then show ?thesis
    by (metis A1 has_max_iff2 inf_in_degenerate lb_set_in_degenerate max_if sup_in_max)
next
  case False
  define L where "L=lb_set_in A X" 
  define S where "S=SupIn L X"
  have B0:"S \<in> L"
  proof-
    have B00:"S \<in> X"
      by (simp add: A1 L_def S_def has_sup_in_in_set)
    have B01:"\<forall>a. a \<in> A \<longrightarrow> S \<le> a"
      using A0 A1 L_def S_def has_sup_in_imp3 lb_set_in_imp by blast
    show ?thesis
      by (simp add: B00 B01 L_def lb_set_in_elm)
  qed
  have B1:"\<forall>l. l \<in> L \<longrightarrow> l \<le> S"
    by (simp add: A1 L_def S_def has_sup_in_imp2)
  have B2:"is_inf_in S A X"
    using B0 B1 L_def is_inf_in_def is_max_if2 by blast
  then show ?thesis
    using L_def S_def is_inf_in_inf_eq by force
qed
  

lemma sup_complete_bounded_inf_eq2:
  fixes X::"'a::order set"
  assumes A0:"is_sup_complete X"
  shows "\<And>A. (A \<subseteq> X \<and>  lb_set_in A X \<noteq> {}) \<longrightarrow> (InfIn A X = SupIn (lb_set_in A X) X)"
  by (metis assms bot.extremum_uniqueI lb_set_in_subset lb_ub_extensive sup_complete_bounded_inf sup_complete_bounded_inf_eq1 sup_in_eq_inf_in_ub ub_set_in_subset)


lemma inf_complete_bounded_sup_eq2:
  fixes X::"'a::order set"
  assumes A0:"is_inf_complete X"
  shows "\<And>A. (A \<subseteq> X \<and>  ub_set_in A X \<noteq> {}) \<longrightarrow> (SupIn A X = InfIn (ub_set_in A X) X)"
  by (metis assms bot.extremum_uniqueI inf_complete_bounded_sup inf_complete_bounded_sup_eq1 inf_in_eq_sup_in_lb lb_set_in_subset ub_lb_extensive ub_set_in_subset)

lemma inf_leq_sup:
  fixes A X::"'a::order set"
  assumes A0:"A \<subseteq> X" and A1:"has_inf_in A X" and A2:"has_sup_in A X" and A3:"A \<noteq> {}"
  shows "InfIn A X \<le>  SupIn A X "
  using A1 A2 A3 has_inf_in_imp2 has_sup_in_imp2 by fastforce

lemma no_top_no_empty_inf:
  fixes X::"'a::order set"
  shows "(\<not>(has_max X) \<and> \<not>(has_inf_in {} X)) \<or> (has_inf_in {} X \<and> is_max (InfIn {} X) X)"
  by (metis has_inf_in_def has_inf_in_imp1 lb_set_in_degenerate)

lemma no_bot_no_empty_sup:
  fixes X::"'a::order set"
  shows "(\<not>(has_min X) \<and> \<not>(has_sup_in {} X)) \<or> (has_sup_in {} X \<and> is_min (SupIn {} X) X)"
  by (metis has_min_iff2 has_sup_in_def min_if sup_in_degenerate ub_set_in_degenerate)


subsection CompleteSemilatticePredicate

lemma complete_inf_semilattice_has_bot:
  assumes "is_complete_inf_semilattice X"
  shows "has_min X \<and> is_min (InfIn X X) X"
  by (metis assms has_min_def inf_complete_has_min is_complete_inf_semilattice_def is_inf_complete_def is_inhabited_def)


lemma complete_sup_semilattice_has_top:
  assumes "is_complete_sup_semilattice X"
  shows "has_max X \<and> is_max (SupIn X X) X"
  by (metis assms has_max_iff2 is_complete_sup_semilattice_def is_inhabited_def is_sup_complete_def sup_complete_has_max)


section AbsoluteExtrema
subsection Suprema

lemma is_sup_iff:
  "is_sup m A \<longleftrightarrow> (is_min m ( ub_set A))"
  by (simp add: is_sup_def)


lemma is_sup_imp1:
  "\<And>m A. is_sup m A  \<Longrightarrow>  (m \<in>( ub_set A) \<and> is_min m (ub_set A))"
  by (simp add: is_min_imp is_sup_iff)

lemma is_sup_imp2:
  "\<And>m A. is_sup m A  \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> a \<le> m)"
  by (simp add: is_sup_def is_min_def ub_set_def)

lemma is_sup_imp3:
  "\<And>m A. is_sup m A  \<Longrightarrow>  (\<And>u. (\<And>a. a \<in> A \<Longrightarrow> a \<le> u) \<Longrightarrow> m \<le> u)"
  by (simp add: is_min_iff is_sup_def ub_set_mem_iff)

lemma is_sup_if1:
  "\<And>m A. (m \<in>( ub_set A) \<and> is_min m (ub_set A)) \<Longrightarrow> is_sup m A"
  by (simp add: is_sup_def)

lemma is_sup_if2:
  "\<And>m A. (\<And>a. a \<in> A \<Longrightarrow> a \<le> m) \<Longrightarrow>  is_min m (ub_set A) \<Longrightarrow> is_sup m A"
  by (simp add: is_sup_def)

lemma is_sup_if3:
  "\<And>m A. (\<And>a. a \<in> A \<Longrightarrow> a \<le> m) \<Longrightarrow>  (\<And>u. (\<And>a. a \<in> A \<Longrightarrow> a \<le> u) \<Longrightarrow> m \<le> u) \<Longrightarrow> is_sup m A"
  by (simp add: is_min_iff is_sup_def ub_set_mem_iff)


lemma is_sup_unique:
  "\<And>(A::'a::order set)m1 m2. is_sup m1 A \<Longrightarrow> is_sup m2 A \<Longrightarrow> m1=m2"
  by (simp add: is_sup_def min_unique)


lemma if_has_sup_unique:
  assumes "has_sup (A::'a::order set)"
  shows "\<exists>!m. is_sup m A"
  using assms has_sup_def if_has_min_min_unique is_sup_def by blast

lemma is_max_is_sup:
  "\<And>A m.  is_max m A \<Longrightarrow> is_sup m A"
  by (simp add: is_max_iff is_sup_if3)

lemma has_max_has_sup:
  "\<And>A.  has_max A \<Longrightarrow> has_sup A"
  by (meson has_min_def has_sup_def if_has_max_max_unique is_max_is_sup is_sup_def)
lemma sup_is_sup:
  assumes A0:"has_sup (A::'a::order set)"
  shows "is_sup (SupUn A) A"
proof-
  obtain m where A1:"m = SupUn A"
    by simp
  have B0:"is_sup m A"
    by (metis A1 SupUn_def assms if_has_sup_unique the_equality)
  show ?thesis
    using A1 B0 by blast
qed


lemma sup_degenerate: 
  "SupUn {} =( bot::'a::order_bot)"
  by (metis min_bot SupUn_def bot.extremum has_sup_def
      if_has_sup_unique is_min_bot is_sup_def
       the_equality ub_set_in_degenerate ub_set_in_ub_univ)

lemma has_sup_in_imp_sup:
  assumes "has_sup_in A UNIV"
  shows "has_sup A"
  by (metis assms has_sup_def has_sup_in_def ub_set_in_ub_univ)

lemma has_sup_imp_sup_in:
  assumes "has_sup A"
  shows "has_sup_in A UNIV"
  by (metis assms has_sup_def has_sup_in_def ub_set_in_ub_univ)

lemma has_min_ub:
  assumes A0:"has_min (ub_set_in (A::'a::order set) B)"
  shows "is_sup_in (SupIn A B) A B"
  by (simp add: assms has_sup_in_def supin_is_sup)

lemma supin_eq_supun:
  assumes A0:"has_sup_in(A::'a::order set) UNIV"
  shows "SupIn A UNIV = SupUn A"
  by(simp add:SupIn_def SupUn_def is_sup_in_def is_sup_def ub_set_in_univ_absorb)

lemma complete_semilattice_sup_is_sup:
  "\<And>(A::'a::complete_semilattice_sup set). A \<noteq> {} \<Longrightarrow> (is_sup (Sup A) A)"
  by (simp add: CSup_least CSup_upper is_sup_if3)

lemma complete_semilattice_sup_is_sup_in:
  "\<And>(A::'a::complete_semilattice_sup set). A \<noteq> {} \<Longrightarrow> (is_sup_in (Sup A) A UNIV)"
  by (simp add: CSup_least CSup_upper is_sup_in_if3)

lemma complete_semilattice_supun_is_sup:
  "\<And>(A::'a::complete_semilattice_sup set). A \<noteq> {} \<Longrightarrow> (is_sup (SupUn A) A)"
  by (meson complete_semilattice_sup_is_sup has_min_def has_sup_def is_sup_def sup_is_sup)

lemma complete_semilattice_supin_is_sup:
  "\<And>(A::'a::complete_semilattice_sup set). A \<noteq> {} \<Longrightarrow> (is_sup (SupIn A UNIV) A)"
  by (metis complete_semilattice_sup_is_sup complete_semilattice_sup_is_sup_in is_sup_in_sup_eq)

lemma complete_semilattice_supin_is_supin:
  "\<And>(A::'a::complete_semilattice_sup set). A \<noteq> {} \<Longrightarrow> (is_sup_in (SupIn A UNIV) A UNIV)"
  by (simp add: complete_semilattice_supin_is_sup is_sup_imp1 is_sup_in_iff ub_set_in_univ_absorb)

lemma complete_semilattice_supin_existence:
  "\<And>(A::'a::complete_semilattice_sup set). A \<noteq> {} \<Longrightarrow> has_sup_in A UNIV"
  by (metis complete_semilattice_supin_is_sup has_sup_in_def is_min_imp_has_min is_sup_iff ub_set_in_univ_absorb)

lemma complete_semilattice_sup_existence:
  "\<And>(A::'a::complete_semilattice_sup set). A \<noteq> {} \<Longrightarrow> has_sup A"
  by (simp add: complete_semilattice_supin_existence has_sup_in_imp_sup)


lemma complete_semilattice_sup_least:
  fixes A::"'a::complete_semilattice_sup set"
  shows "\<forall>u \<in> ub_set A. A \<noteq> {} \<longrightarrow>  Sup A \<le> u"
  by (simp add: CSup_least ub_set_imp)

lemma complete_semilattice_supun_eq_sup:
  fixes A::"'a::complete_semilattice_sup set" 
  assumes "A \<noteq> {}"
  shows "SupUn A = Sup A"
  by (meson assms complete_semilattice_sup_is_sup complete_semilattice_supun_is_sup is_sup_unique)

lemma complete_semilattice_sup_is_sup2:
  "\<forall>(A::'X::complete_semilattice_sup set). A \<noteq> {} \<longrightarrow> SupUn A = Sup A"
  by (simp add: complete_semilattice_supun_eq_sup)

lemma has_supin_singleton:
  "has_sup_in {x::'a::order} UNIV"
  by (simp add: has_max_has_sup has_max_singleton has_sup_imp_sup_in)


lemma is_sup_singleton:
  "is_sup (x::'a::order) {x}"
  by (simp add: is_max_is_sup is_max_singleton)

lemma has_sup_singleton:
  "has_sup {x::'a::order}"
  by (simp add: has_sup_in_imp_sup has_supin_singleton)

lemma sup_singleton:
  "SupUn {x::'a::order} = x"
  using has_sup_singleton is_sup_singleton is_sup_unique sup_is_sup by blast

lemma sup_monotone1:
  "\<And>A B. has_sup A \<Longrightarrow> has_sup B \<Longrightarrow> A \<subseteq> B \<Longrightarrow> SupUn A \<le> SupUn B"
  by (meson is_sup_imp2 is_sup_imp3 subsetD sup_is_sup)

lemma is_sup_sup_eq:
  "\<And>(s::'a::order) A. has_sup A \<Longrightarrow> is_sup s A \<Longrightarrow> (s = SupUn A)"
  by (simp add: is_sup_unique sup_is_sup)

lemma complete_lattice_sup_is_sup:
  fixes A::"'a::complete_lattice set"
  assumes "A \<noteq> {}"
  shows "(is_sup (Sup A) A)"
  by (simp add: Sup_least Sup_upper is_sup_if3)

lemma has_max_imp_sup_eq_max:
  fixes A::"'a::order set"
  assumes A0:"has_max A"
  shows "SupUn A = max A"
  by (metis assms has_max_has_sup if_has_max_max_unique is_max_is_sup is_sup_unique max_if sup_is_sup)

lemma complete_lattice_sup_least:
  fixes A::"'a::complete_lattice set"
  shows "\<forall>u \<in> ub_set A. A \<noteq> {} \<longrightarrow> Sup A \<le> u"
  by (simp add: csls.CSup_least ub_set_mem)

lemma is_sup_imp_lub:
  "\<And>s A. is_sup s A \<Longrightarrow> is_min s (ub_set A)"
  by (simp add: is_sup_iff)

lemma sup_comp_un_ind:
  fixes F::"'b \<Rightarrow> 'a::order set" and I::"'b set"
  defines "SupX \<equiv> (\<lambda>(A::'a::order set). (SupIn A UNIV))"
  assumes A0:"I \<noteq> {}" and
          A1:"\<And>i. i \<in> I  \<Longrightarrow> has_sup (F i)" and
          A2:"has_sup (SupUn`(F`I))"
  shows "(has_sup (\<Union>i \<in> I. F i)) \<and> SupUn (SupUn`(F`I)) = SupUn (\<Union>i \<in> I. F i)"
proof-
  define A where A3:"A=(\<Union>i \<in> I. F i)"
  define G where A4:"G= SupUn`(F`I)"
  have B0:"\<And>i. i \<in> I \<longrightarrow> (F i) \<subseteq> A"
    by (simp add: A3 SUP_upper)
  have B1:"\<And>i. i \<in> I \<longrightarrow> (\<forall>u. u \<in>(ub_set A) \<longrightarrow> SupUn (F i) \<le> u)"
    by (meson A1 B0 in_mono is_sup_imp3 sup_is_sup ub_set_mem_iff)
  have B2:"\<And>i. i \<in> I \<longrightarrow> ub_set A \<subseteq> ub_set {(SupUn (F i))}"
    by (simp add: B1 ub_set_mem_iff subset_eq)
  have B3:"ub_set A \<subseteq> ub_set G"
    by (simp add: A4 B1 imp_in_upper_bounds subsetI)
  have B4:"\<And>u. u \<in> ub_set A \<longrightarrow> SupUn G \<le> u"
    using A2 A4 B3 sup_is_sup is_sup_imp3 ub_set_imp by blast
  have B5:"\<And>a. a \<in> A \<longrightarrow> a \<le> SupUn G"
  proof
    fix a assume A5:"a \<in> A"
    obtain i where A6:"i \<in> I \<and> a \<in> F i"
      using A3 A5 by blast
    have B6:"a \<le> SupUn (F i)"
      using A1 A6 is_sup_imp2 sup_is_sup by blast
    show "a \<le> SupUn G"
      by (metis A2 A4 A6 B6 dual_order.trans imageI is_sup_imp2 sup_is_sup)
  qed
  have B8:"is_sup (SupUn G) A"
    by (simp add: B4 B5 imp_in_upper_bounds is_sup_if3)
  have B9:"has_sup A"
    using B8 has_sup_def has_min_def is_sup_def by blast
  have B10:"SupUn G = SupUn A"
    by (simp add: B8 B9 is_sup_sup_eq)
  show ?thesis
    using A3 A4 B9 B10 by blast
qed


lemma sup_comp_un:
  fixes F::"'a::order set set"
  assumes A0:"F \<noteq> {}" and A1:"\<And>A. A \<in> F \<Longrightarrow> has_sup A" and A2:"has_sup (SupUn`(F))"
  shows "(has_sup (\<Union>F)) \<and> (SupUn (SupUn`(F)) = SupUn (\<Union>F))"
proof-
  define A where A3:"A=\<Union>F"
  define G where A4:"G=SupUn`(F)"
  have B0:"\<And>E. E \<in> F \<Longrightarrow> E \<subseteq> A"
    by (simp add: A3 Union_upper)
  have B1:"\<And>E. E \<in> F \<Longrightarrow> (\<forall>u. u \<in>(ub_set A) \<longrightarrow> SupUn (E) \<le> u)"
    by (meson A1 B0 in_mono is_sup_imp3 sup_is_sup ub_set_mem_iff)
  have B2:"\<And>E. E \<in> F \<Longrightarrow> ub_set A \<subseteq> ub_set {(SupUn E)}"
    by (simp add: B1 ub_set_mem_iff subset_eq)
  have B3:"ub_set A \<subseteq> ub_set G"
    by (simp add: A4 B1 imp_in_upper_bounds subsetI)
  have B4:"\<And>u. u \<in> ub_set A \<longrightarrow> SupUn G \<le> u"
    using A2 A4 B3 sup_is_sup is_sup_imp3 ub_set_imp by blast
  have B5:"\<And>a. a \<in> A \<longrightarrow> a \<le> SupUn G"
  proof
    fix a assume A5:"a \<in> A"
    obtain E  where A6:"E \<in> F \<and> a \<in> E"
      using A3 A5 by blast
    have B6:"a \<le> SupUn E"
      using A1 A6 is_sup_imp2 sup_is_sup by blast
    show "a \<le> SupUn G"
      by (metis A2 A4 A6 B6 dual_order.trans imageI is_sup_imp2 sup_is_sup)
  qed
  have B8:"is_sup (SupUn G) A"
    by (simp add: B4 B5 imp_in_upper_bounds is_sup_if3)
  have B9:"has_sup A"
    using B8 has_sup_def has_min_def is_sup_def by blast
  have B10:"SupUn G = SupUn A"
    by (simp add: B8 B9 is_sup_sup_eq)
  show ?thesis
    using A3 A4 B9 B10 by blast
qed

subsection Infima

lemma is_inf_iff:
  "is_inf m A \<longleftrightarrow> (is_max m (lb_set A))"
  by (simp add: is_inf_def)

lemma is_inf_imp1:
  "\<And>m A. is_inf m A  \<Longrightarrow>  (m \<in>( lb_set A) \<and> is_max m (lb_set A))"
  by (simp add: is_max_imp is_inf_iff)

lemma is_inf_imp2:
  "\<And>m A. is_inf m A  \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> m \<le> a)"
  by (simp add: is_inf_def is_max_def lb_set_def)

lemma is_inf_imp3:
  "\<And>m A. is_inf m A  \<Longrightarrow>  (\<And>l. (\<And>a. a \<in> A \<Longrightarrow> l \<le> a) \<Longrightarrow> l \<le> m)"
  by (simp add: is_max_iff is_inf_def lb_set_mem_iff)

lemma is_inf_if1:
  "\<And>m A. (is_max m (lb_set A)) \<Longrightarrow> is_inf m A"
  by (simp add: is_inf_def)

lemma is_inf_if2:
  "\<And>m A.  m \<in> (lb_set A) \<Longrightarrow>  (\<And>l. (\<And>a. a \<in> A \<Longrightarrow> l \<le> a) \<Longrightarrow> l \<le> m) \<Longrightarrow> is_inf m A"
  by (simp add: is_inf_if1 is_max_iff lb_set_mem_iff)

lemma is_inf_if3:
  "\<And>m A. (\<And>a. a \<in> A \<Longrightarrow> m \<le> a) \<Longrightarrow>  (\<And>l. (\<And>a. a \<in> A \<Longrightarrow> l \<le> a) \<Longrightarrow> l \<le> m) \<Longrightarrow> is_inf m A"
  by (simp add: is_inf_if2 lb_set_elm)

lemma is_inf_unique:
  "\<And>(A::'a::order set) m1 m2. is_inf m1 A \<Longrightarrow> is_inf m2 A \<Longrightarrow> m1=m2"  
  by (simp add: is_inf_def max_unique)

lemma if_has_inf_unique:
  assumes "has_inf (A::'a::order set)"
  shows "\<exists>!m. is_inf m A"
  using assms has_inf_def if_has_max_max_unique is_inf_def by blast

lemma is_min_is_inf:
  "\<And>A m.  is_min m A \<Longrightarrow> is_inf m A"
  by (simp add: is_inf_if2 is_min_imp)

lemma has_min_has_inf:
  "\<And>A.  has_min A \<Longrightarrow> has_inf A"
  by (meson has_inf_def has_max_iff2 if_has_min_min_unique is_inf_def is_min_is_inf)

lemma has_inf_in_imp_inf:
  assumes "has_inf_in A UNIV"
  shows "has_inf A"
  by (metis assms has_inf_def has_inf_in_def lb_set_in_lb_univ)

lemma has_inf_imp_inf_in:
  assumes "has_inf A"
  shows "has_inf_in A UNIV"
  by (metis assms has_inf_def has_inf_in_def lb_set_in_lb_univ)

lemma has_max_lb:
  assumes A0:"has_max (lb_set_in (A::'a::order set) B)"
  shows "is_inf_in (InfIn A B) A B"
  by (simp add: assms has_inf_in_def infin_is_inf)

lemma inf_is_inf:
  assumes A0:"has_inf (A::'a::order set)"
  shows "is_inf (InfUn A) A"
proof-
  obtain m where A1:"m = InfUn A"
    by simp
  have B0:"is_inf m A"
    by (metis A1 InfUn_def assms if_has_inf_unique the_equality)
  show ?thesis
    using A1 B0 by blast
qed

lemma complete_semilattice_inf_has_min:
  fixes X::"'a::order set"
  assumes "X \<noteq> {} \<and> is_inf_complete X"
  shows "has_min X \<and> (is_min (InfIn X X) X)"
  using assms inf_complete_has_min is_min_imp_has_min by blast

lemma complete_semilattice_sup_has_max:
  fixes X::"'a::order set"
  assumes "X \<noteq> {} \<and> is_sup_complete X"
  shows "has_max X \<and> (is_max (SupIn X X) X)"
  using assms is_max_imp_has_max sup_complete_has_max by blast


lemma complete_semilattice_inf_has_min2:
  "has_min (UNIV::'a::complete_semilattice_inf set)"
  by (metis CInf_lower min_bot UNIV_I empty_not_UNIV)

lemma complete_semilattice_sup_has_max2:
  "has_max (UNIV::'a::complete_semilattice_sup set)"
  by (metis CSup_upper max_top UNIV_I ex_in_conv)


lemma complete_semilattice_inf_is_inf:
  "\<And>(A::'a::complete_semilattice_inf set). A \<noteq> {} \<Longrightarrow> (is_inf (Inf A) A)"
  by (simp add: CInf_greatest CInf_lower is_inf_if3)

lemma complete_semilattice_inf_is_inf_in:
  "\<And>(A::'a::complete_semilattice_inf set). A \<noteq> {} \<Longrightarrow> (is_inf_in (Inf A) A UNIV)"
  by (simp add: CInf_greatest CInf_lower is_inf_in_if3)

lemma complete_semilattice_infun_is_inf:
  "\<And>(A::'a::complete_semilattice_inf set). A \<noteq> {} \<Longrightarrow> (is_inf (InfUn A) A)"
  by (meson complete_semilattice_inf_is_inf has_inf_def inf_is_inf is_inf_def is_max_imp_has_max)

lemma complete_semilattice_infin_is_inf:
  "\<And>(A::'a::complete_semilattice_inf set). A \<noteq> {} \<Longrightarrow> (is_inf (InfIn A UNIV) A)"
  by (metis complete_semilattice_inf_is_inf complete_semilattice_inf_is_inf_in is_inf_in_inf_eq)

lemma complete_semilattice_infin_is_infin:
  "\<And>(A::'a::complete_semilattice_inf set). A \<noteq> {} \<Longrightarrow> (is_inf_in (InfIn A UNIV) A UNIV)"
  by (simp add: complete_semilattice_infin_is_inf is_inf_imp1 is_inf_in_iff lb_set_in_univ_absorb)

lemma complete_semilattice_infin_existence:
  "\<And>(A::'a::complete_semilattice_inf set). A \<noteq> {} \<Longrightarrow> has_inf_in A UNIV"
  by (metis complete_semilattice_infun_is_inf has_inf_in_def has_max_def is_inf_def lb_set_in_lb_univ)

lemma complete_semilattice_inf_existence:
  "\<And>(A::'a::complete_semilattice_inf set). A \<noteq> {} \<Longrightarrow> has_inf A"
  by (simp add: complete_semilattice_infin_existence has_inf_in_imp_inf)

lemma complete_semilattice_inf_greatest:
  fixes A::"'a::complete_semilattice_inf set"
  shows "\<forall>l \<in> lb_set A. A \<noteq> {} \<longrightarrow> l \<le> Inf A"
  by (simp add: CInf_greatest lb_set_mem)

lemma complete_lattice_inf_is_inf:
  fixes A::"'a::complete_lattice set"
  assumes "A \<noteq> {}"
  shows "(is_inf (Inf A) A)"
  by (simp add: Inf_greatest Inf_lower is_inf_if3)

lemma complete_semilattice_infun_eq_inf:
  fixes A::"'a::complete_semilattice_inf set"
  assumes "A \<noteq> {}"
  shows "InfUn A = Inf A"
  by (meson assms complete_semilattice_inf_is_inf complete_semilattice_infun_is_inf is_inf_unique)

lemma complete_semilattice_inf_is_inf2:
  "\<forall>(A::'X::complete_semilattice_inf set). A \<noteq> {} \<longrightarrow> InfUn A = Inf A"
  using complete_semilattice_infun_eq_inf by blast


lemma has_infin_singleton:
  "has_inf_in {x::'a::order} UNIV"
  by (simp add: has_min_has_inf has_min_singleton has_inf_imp_inf_in)


lemma inf_degenerate:  
  "InfUn {} =( top::'a::order_top)"
  apply(simp add:InfUn_def is_inf_def lb_set_degenerate ub_set_in_def is_max_def)
  using top.extremum_unique by force

lemma is_inf_singleton:
  "is_inf (x::'a::order) {x}"
  by (simp add: is_min_is_inf is_min_singleton)

lemma has_inf_singleton:
  "has_inf {x::'a::order}"
  by (simp add: has_inf_in_imp_inf has_infin_singleton)

lemma inf_singleton:
  "InfUn {x::'a::order} = x"
  using has_inf_singleton is_inf_singleton is_inf_unique inf_is_inf by blast

lemma inf_antitone1:
  "\<And>A B. has_inf A \<Longrightarrow> has_inf B \<Longrightarrow> A \<subseteq> B \<Longrightarrow> InfUn B \<le> InfUn A"
  by (meson inf_is_inf is_inf_imp2 is_inf_imp3 subset_eq)

lemma is_inf_inf_eq:
  "\<And>(i::'a::order) A. has_inf A \<Longrightarrow> is_inf i A \<Longrightarrow> (i = InfUn A)"
  by (simp add: inf_is_inf is_inf_unique)


lemma inf_comp_un_ind:
  fixes F::"'b \<Rightarrow> 'a::order set" and I::"'b set"
  assumes A0:"I \<noteq> {}" and A1:"\<And>i. i \<in> I  \<Longrightarrow> has_inf (F i)" and A2:"has_inf (InfUn`(F`I))"
  shows "(has_inf (\<Union>i \<in> I. F i)) \<and> InfUn (InfUn`(F`I)) = InfUn (\<Union>i \<in> I. F i)"
proof-
  define A where A3:"A=(\<Union>i \<in> I. F i)"
  define G where A4:"G= InfUn`(F`I)"
  have B0:"\<And>i. i \<in> I \<longrightarrow> (F i) \<subseteq> A"
    by (simp add: A3 SUP_upper)
  have B1:"\<And>i. i \<in> I \<longrightarrow> (\<forall>l. l \<in>(lb_set A) \<longrightarrow> l \<le> InfUn (F i))"
    by (meson A1 B0 inf_is_inf is_inf_imp1 is_max_iff lb_set_antitone1 subsetD)
  have B2:"\<And>i. i \<in> I \<longrightarrow> lb_set A \<subseteq> lb_set {(InfUn (F i))}"
    by (simp add: B1 lb_set_mem_iff subset_eq)
  have B3:"lb_set A \<subseteq> lb_set G"
    by (simp add: A4 B1 imp_in_lower_bounds subsetI)
  have B4:"\<And>l. l \<in> lb_set A \<longrightarrow> l  \<le> InfUn G"
    using A2 A4 B3 inf_is_inf is_inf_imp3 lb_set_imp by blast
  have B5:"\<And>a. a \<in> A \<longrightarrow> InfUn G \<le> a"
  proof
    fix a assume A5:"a \<in> A"
    obtain i where A6:"i \<in> I \<and> a \<in> F i"
      using A3 A5 by blast
    have B6:"InfUn (F i) \<le> a"
      using A1 A6 inf_is_inf is_inf_imp2 by blast
    show "InfUn G \<le> a"
      by (metis A2 A4 A6 B6 imageI inf_is_inf is_inf_imp1 lb_set_mem order_trans)
  qed
  have B8:"is_inf (InfUn G) A"
    by (simp add: B4 B5 imp_in_lower_bounds is_inf_if3)
  have B9:"has_inf A"
    using B8 has_inf_def has_max_def is_inf_def by blast
  have B10:"InfUn G = InfUn A"
    by (simp add: B8 B9 is_inf_inf_eq)
  show ?thesis
    using A3 A4 B9 B10 by blast
qed
  

lemma inf_comp_un:
  fixes F::"'a::order set set"
  assumes A0:"F \<noteq> {}" and A1:"\<And>A. A \<in> F \<Longrightarrow> has_inf A" and A2:"has_inf (InfUn`(F))"
  shows "(has_inf (\<Union>F)) \<and> (InfUn (InfUn`(F)) = InfUn (\<Union>F))"
proof-
  define A where A3:"A=\<Union>F"
  define G where A4:"G=InfUn`(F)"
  have B0:"\<And>E. E \<in> F \<Longrightarrow> E \<subseteq> A"
    by (simp add: A3 Union_upper)
  have B1:"\<And>E. E \<in> F \<Longrightarrow> (\<forall>l. l \<in>(lb_set A) \<longrightarrow> l \<le> InfUn (E))"
    by (meson A1 B0 inf_is_inf is_inf_imp1 is_max_iff lb_set_antitone1 subsetD)
  have B2:"\<And>E. E \<in> F \<Longrightarrow> lb_set A \<subseteq> lb_set {(InfUn E)}"
    by (simp add: B1 lb_set_mem_iff subset_eq)
  have B3:"lb_set A \<subseteq> lb_set G"
    by (simp add: A4 B1 imp_in_lower_bounds subsetI)
  have B4:"\<And>l. l \<in> lb_set A \<longrightarrow> l  \<le> InfUn G"
    using A2 A4 B3 inf_is_inf is_inf_imp3 lb_set_imp by blast
  have B5:"\<And>a. a \<in> A \<longrightarrow> InfUn G \<le> a"
  proof
    fix a assume A5:"a \<in> A"
    obtain E  where A6:"E \<in> F \<and> a \<in> E"
      using A3 A5 by blast
    have B6:"InfUn E \<le> a"
      using A1 A6 inf_is_inf is_inf_imp2 by blast
    show "InfUn G \<le> a"
      by (metis A2 A4 A6 B6 imageI inf_is_inf is_inf_imp1 lb_set_mem order_trans)
  qed
  have B8:"is_inf (InfUn G) A"
    by (simp add: B4 B5 imp_in_lower_bounds is_inf_if3)
  have B9:"has_inf A"
    using B8 has_inf_def has_max_def is_inf_def by blast
  have B10:"InfUn G = InfUn A"
    by (simp add: B8 B9 is_inf_inf_eq)
  show ?thesis
    using A3 A4 B9 B10 by blast
qed


subsection ExtremaFromDuals

lemma sup_eq_inf_ub:
  fixes A::"'a::order set"
  assumes "has_inf (ub_set A)"
  shows "has_sup A \<and> SupUn A = InfUn(ub_set A)"
proof-
  let ?U="ub_set A"
  let ?i="InfUn ?U"
  have B0:"A \<subseteq> lb_set ?U"
    by (simp add: lb_set_elm subset_eq ub_set_imp)
  have B1:"?i \<in> ub_set A"
    by (meson B0 assms inf_is_inf is_inf_def is_max_iff subset_eq ub_set_mem_iff)
  have B2:"is_min ?i (ub_set A)"
    by (simp add: B1 assms inf_is_inf is_inf_imp1 is_min_if1)
  show ?thesis
    by (metis B2 has_min_def has_sup_def is_sup_def is_sup_sup_eq)
qed

lemma inf_eq_sup_lb:
  fixes A::"'a::order set"
  assumes "has_sup (lb_set A)"
  shows "has_inf A \<and> InfUn A = SupUn(lb_set A)"
proof-
  let ?L="lb_set A"
  let ?s="SupUn ?L"
  have B0:"A \<subseteq> ub_set ?L"
    by (simp add: ub_set_elm subset_eq lb_set_imp)
  have B1:"?s \<in> lb_set A"
    by (meson B0 assms sup_is_sup is_sup_def is_min_iff subset_eq lb_set_mem_iff)
  have B2:"is_max ?s (lb_set A)"
    by (simp add: B1 assms sup_is_sup  is_sup_imp1 is_max_if1)
  show ?thesis
    by (metis B2 has_inf_def has_max_iff2 is_inf_def is_inf_inf_eq)
qed

lemma has_least_imp_inf_eq_least:
  fixes A::"'a::order set"
  assumes A0:"has_min A"
  shows "InfUn A = min A"
  by (metis assms has_min_has_inf if_has_min_min_unique inf_is_inf is_inf_unique is_min_is_inf min_if)


lemma complete_lattice_inf_greatest:
  fixes A::"'a::complete_lattice set"
  shows "\<forall>l \<in> lb_set A. A \<noteq> {} \<longrightarrow> l \<le> Inf A"
  by (simp add: csli.CInf_greatest lb_set_imp)

lemma complete_semilattice_inf_exists_inf:
  "\<And>(A::'a::complete_semilattice_inf set). A \<noteq> {} \<Longrightarrow> has_inf A"
  by (metis complete_semilattice_infun_is_inf has_inf_def has_max_def is_inf_def)

lemma is_inf_imp_glb1:
  "\<And>i A. is_inf i A \<Longrightarrow> is_max i (lb_set A)"
  by (simp add: is_inf_iff)


lemma complete_semilattice_sup_lb_imp_inf:
  fixes A::"'a::complete_semilattice_sup set"
  assumes "lb_set A \<noteq> {}"
  shows "has_inf A \<and> InfUn A = Sup(lb_set A)"
  by (simp add: assms complete_semilattice_sup_existence complete_semilattice_supun_eq_sup inf_eq_sup_lb)

lemma complete_semilattice_sup_lb_imp_inf2:
  fixes A::"'a::complete_semilattice_sup set"
  assumes "lb_set A \<noteq> {}"
  shows "has_inf A \<and> InfUn A = SupUn(lb_set A)"
  by (simp add: assms complete_semilattice_sup_is_sup2 complete_semilattice_sup_lb_imp_inf)



section MiscResults
subsection CardinalityStuff

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

lemma infinite_imp_infinite_union:
  "infinite A \<Longrightarrow> infinite B \<Longrightarrow> infinite (A \<union> B)"
  by simp

lemma empty_countable:
  "is_countable {}"
  by (simp add: is_countable_def)

(*de Morgans for finite sup and inf in complete boolean algebra*)
subsection CompleteBooleanAlgebra
context complete_boolean_algebra
begin
lemma finf_complete_lattice_set:
  "\<And>A. (finite A \<and> A \<noteq> {}) \<longrightarrow> -(fInf A) = fSup (uminus ` A)"
  by (simp add: local.finf_complete_lattice local.fsup_complete_lattice local.uminus_Inf)


lemma fsup_complete_lattice_set:
  "\<And>A. (finite A \<and> A \<noteq> {}) \<longrightarrow> -(fSup A) = fInf (uminus ` A)"
  by (simp add: local.finf_complete_lattice local.fsup_complete_lattice local.uminus_Sup)

end

subsection SetSystems


lemma ub_set_in_ne_iff:
  "(ub_set_in {a} B) \<noteq> {} \<longleftrightarrow> (\<exists>b \<in> B. a \<le> b)"
  using ub_set_in_singleton by fastforce

lemma lb_set_in_ne_iff:
  "(lb_set_in {a} B) \<noteq> {} \<longleftrightarrow> (\<exists>b \<in> B. a \<ge> b)"
  using lb_set_in_singleton by fastforce

lemma is_cofinal_in_imp:
  "\<And>A B. A is_cofinal_in B \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> (\<exists>b \<in> B. a \<le> b))"
  by (simp add: is_cofinal_in_def)

lemma is_cofinal_in_imp_ub_in_ne:
  "\<And>A B. A is_cofinal_in B \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> (ub_set_in {a} B) \<noteq> {})"
  by (simp add: is_cofinal_in_imp ub_set_in_ne_iff)


lemma is_cofinal_in_if:
  "\<And>A B. (\<And>a. a \<in> A \<Longrightarrow> (\<exists>b \<in> B. a \<le> b)) \<Longrightarrow> A is_cofinal_in B "
  by (simp add: is_cofinal_in_def)

lemma is_cofinal_in_if_ub_in_ne:
  "\<And>A B. (\<And>a. a \<in> A \<Longrightarrow> (ub_set_in {a} B) \<noteq> {}) \<Longrightarrow> A is_cofinal_in B "
  by (simp add: is_cofinal_in_if ub_set_in_ne_iff)



lemma is_inhabited_imp:
  "\<And>X. is_inhabited X \<Longrightarrow> \<exists>x. x \<in> X"
  by (simp add: ex_in_conv is_inhabited_def)


lemma is_downdir_imp:
  assumes "is_downdir X"
  shows "\<And>a b. (a \<in> X \<and> b \<in> X) \<Longrightarrow> (\<exists>c  \<in> X. (c \<le> a) \<and>  (c \<le> b))"
  using assms is_downdir_def by blast

lemma is_updir_imp:
  assumes "is_updir X"
  shows "\<And>a b. (a \<in> X \<and> b \<in> X) \<Longrightarrow> (\<exists>c  \<in> X. (c \<ge> a) \<and>  (c \<ge> b))"
  using assms is_updir_def by blast

lemma is_upclosed_in_imp:
  assumes "is_upclosed_in A X" and "A \<subseteq> X"
  shows "\<And>a b. (a \<le> b \<and> a \<in> A \<and> b \<in> X) \<Longrightarrow> b \<in> A"
  using assms is_upclosed_in_def by blast

lemma is_upclosed_imp:
  assumes "is_upclosed A"
  shows "\<And>a b. (a \<le> b \<and> a \<in> A) \<Longrightarrow> b \<in> A"
  by (meson UNIV_I assms is_upclosed_def is_upclosed_in_def)

lemma is_downclosed_in_imp:
  assumes "is_downclosed_in A X" and "A \<subseteq> X"
  shows "\<And>a b. (a \<ge> b \<and> a \<in> A \<and> b \<in> X) \<Longrightarrow> b \<in> A"
  using assms(1) is_downclosed_in_def by auto

lemma is_downclosed_imp:
  assumes "is_downclosed A"
  shows "\<And>a b. (a \<ge> b \<and> a \<in> A) \<Longrightarrow> b \<in> A"
  by (meson assms is_downclosed_def is_downclosed_in_def iso_tuple_UNIV_I)


lemma is_pisystem_imp:
  assumes "is_pisystem X"
  shows "\<And>a b. (a \<in> X \<and> b \<in> X) \<Longrightarrow> (binf a b) \<in> X"
  using assms is_pisystem_def by blast

lemma semilattice_inf_exists_inf:
  fixes a::"'a::semilattice_inf" and b::"'a::semilattice_inf"
  shows "has_inf {a, b}"
proof-
  define c1 where "c1=inf a b"
  have B0:"c1 \<in> lb_set {a, b}"
    by (simp add: c1_def lb_set_mem_iff)
  have B1:"\<forall>l \<in> lb_set {a, b}. l \<le> c1"
    by (simp add: c1_def lb_set_mem_iff)
  have B2:"is_max  c1 (lb_set {a, b})"
    apply (simp add: B0 B1 is_max_def ub_set_mem_iff)
    by (simp add: B1 ub_set_in_elm)
  have B3:"is_inf c1 {a, b}"
    by (simp add: B2 is_inf_iff)
  have B4:"has_inf {a, b}"
    using B2 has_inf_def has_max_iff2 by auto
  show ?thesis
    by (simp add: B4)
qed


lemma semilattice_inf_has_inf:
  fixes A::"'a::semilattice_inf set"
  assumes A0:"finite A" and
          A1:"A \<noteq> {}"
  shows "has_inf A"
proof-
  define i where "i=fInf A"
  have B0:"i \<in> lb_set A"
    by (simp add: A0 i_def lb_set_mem_iff semilattice_inf_class.coboundedI)
  have B1:"\<forall>l. l \<in> lb_set A \<longrightarrow> l \<le> i"
    by (simp add: A0 A1 finite_inf_greatest i_def lb_set_mem_iff)
  have B0:"is_inf i A"
    by (simp add: B0 B1 is_inf_def is_max_iff)
  show "has_inf A"
    using B0 has_inf_def has_max_iff2 is_inf_def by blast
qed


lemma semilattice_sup_has_sup:
  fixes A::"'a::semilattice_sup set"
  assumes A0:"finite A" and
          A1:"A \<noteq> {}"
  shows "has_sup A"
proof-
  define s where "s=fSup A"
  have B0:"s \<in> ub_set A"
    by (simp add: A0 s_def semilattice_sup_class.coboundedI ub_set_elm)
  have B1:"\<forall>u. u \<in> ub_set A \<longrightarrow> s \<le> u"
    by (simp add: A0 A1 s_def ub_set_mem_iff upper_bounded_iff)
  have B0:"is_sup s A"
    by (simp add: B0 B1 is_min_if2 is_sup_if1)
  show "has_sup A"
    using B0 has_sup_def is_min_imp_has_min is_sup_imp_lub by blast
qed

lemma semilattice_inf_finf_eq:
  fixes A::"'a::semilattice_inf set"
  assumes A0:"finite A" and
          A1:"A \<noteq> {}"
  shows " InfUn A = fInf A"
proof-
  have B0:"is_inf (InfUn A) A"
    by (simp add: A0 A1 inf_is_inf semilattice_inf_has_inf)
  have B1:"is_inf (fInf A) A"
    by (simp add: A0 A1 is_inf_if3 semilattice_inf_class.boundedI semilattice_inf_class.coboundedI)
  show "InfUn A = fInf A"
    using B0 B1 is_inf_unique by blast
qed


lemma semilattice_sup_fsup_eq:
  fixes A::"'a::semilattice_sup set"
  assumes A0:"finite A" and
          A1:"A \<noteq> {}"
  shows " SupUn A = fSup A"
proof-
  have B0:"is_sup (SupUn A) A"
    by (simp add: A0 A1 semilattice_sup_has_sup sup_is_sup)
  have B1:"is_sup (fSup A) A"
    by (simp add: A0 A1 finite_sup_greatest is_sup_if3 semilattice_sup_class.coboundedI)
  show "SupUn A = fSup A"
    using B0 B1 is_sup_unique by blast
qed
  


lemma semilattice_inf_finf_eq_small_inf:
  fixes a::"'a::semilattice_inf" and b::"'a::semilattice_inf"
  shows "inf a b = InfUn {a, b}"
  by (simp add: semilattice_inf_finf_eq)

lemma semilattice_inf_binf_eq_inf:
  fixes a::"'a::semilattice_inf" and b::"'a::semilattice_inf"
  shows "inf a b = binf a b"
  by (simp add: binf_def semilattice_inf_finf_eq)


lemma semilattice_sup_fsup_eq_small_inf:
  fixes a::"'a::semilattice_sup" and b::"'a::semilattice_sup"
  shows "sup a b = SupUn {a, b}"
  by (simp add: semilattice_sup_fsup_eq)

lemma semilattice_sup_bsup_eq_sup:
  fixes a::"'a::semilattice_sup" and b::"'a::semilattice_sup"
  shows "sup a b = bsup a b"
  by (simp add: bsup_def semilattice_sup_fsup_eq)

lemma fpow_ne_imp:
  "A \<in> Fpow_ne X \<Longrightarrow> (finite A) \<and> (A \<noteq> {}) \<and> (A \<subseteq> X)"
  by (simp add: Fpow_Pow_finite)


lemma fpow_ne_if:
  " (finite A) \<and> (A \<noteq> {}) \<and> (A \<subseteq> X) \<Longrightarrow> A \<in> Fpow_ne X "
  by (simp add: Fpow_Pow_finite)

lemma finite_subcover_imp:
  "is_finite_subcover S A x \<Longrightarrow> (S \<subseteq> A) \<and> (S \<noteq> {}) \<and> (finite S)"
  using fpow_ne_imp is_finite_subcover_def by blast

lemma finite_subcover_imp2:
  "is_finite_subcover S A x \<Longrightarrow> S \<in> Fpow_ne A"
  using fpow_ne_imp is_finite_subcover_def by blast


lemma is_pi_system_imp:
  fixes X::"'a::semilattice_inf set"
  shows "is_pisystem X \<longleftrightarrow> (\<forall>a b. a \<in> X  \<longrightarrow> b \<in> X \<longrightarrow> (inf a b)  \<in> X)"
  by (simp add: is_pisystem_def semilattice_inf_binf_eq_inf)

lemma downdir_inf:
  fixes X::"'X::semilattice_inf set"
  assumes A0:"is_downdir X" and A1:"is_upclosed X"
  shows "\<And>(a::'X) b. (a \<in> X \<and> b \<in> X) \<longrightarrow> ((inf a b) \<in> X)"
proof
  fix a b assume A2:"(a \<in> X \<and> b \<in> X)"
  obtain c where A3:"c \<in> X \<and> (c \<le> a) \<and> (c \<le> b)"
    using A0 A2 is_downdir_imp by blast
  have B0:"c \<le> (inf a b)"
     by (simp add: A3)
  show "(inf a b) \<in> X"
    using A1 A3 B0 is_upclosed_imp by blast
qed

lemma updir_sup:
  fixes X::"'X::semilattice_sup set"
  assumes A0:"is_updir X" and A1:"is_downclosed X"
  shows "\<And>(a::'X) b. (a \<in> X \<and> b \<in> X) \<longrightarrow> ((sup a b) \<in> X)"
proof
  fix a b assume A2:"(a \<in> X \<and> b \<in> X)"
  obtain c where A3:"c \<in> X \<and> (c \<ge> a) \<and> (c \<ge> b)"
    using A0 A2 is_updir_imp by blast
  have B0:"c \<ge> (sup a b)"
     by (simp add: A3)
  show "(sup a b) \<in> X"
    using A1 A3 B0 is_downclosed_imp by blast
qed

lemma downdir_up_pisystem:
  fixes X::"'X::semilattice_inf set"
  assumes "is_upclosed X"
  shows "(is_downdir X) \<longleftrightarrow> (is_pisystem X)"
proof
  let ?L="(is_downdir X)" let ?R="(is_pisystem X)"
  assume AL:"?L"
  show "?R"
    by (simp add: AL assms downdir_inf is_pi_system_imp)
  next
  let ?L="(is_downdir X)" let ?R="(is_pisystem X)"
  assume AR:"?R"
  show "?L"
  proof-
    have ARB0:"\<And>a b. (a \<in> X \<and> b \<in> X) \<longrightarrow> (\<exists>c  \<in> X. (c \<le> a) \<and>  (c \<le> b))"
    proof
      fix a b assume ARA0:"(a \<in> X \<and> b \<in> X)"
      have ARB1:"(inf a b) \<in> X"
        using AR ARA0 is_pi_system_imp by auto
      have ARB2:"(inf a b) \<le> a \<and> (inf a b) \<le> b"
        by simp 
      show "(\<exists>c  \<in> X. (c \<le> a) \<and>  (c \<le> b))"
        using ARB1 ARB2 by blast
    qed
    show ?thesis
      by (simp add: ARB0 is_downdir_def)
  qed
qed

lemma infs_eq:
  assumes A0:"finite F"
  shows "inf x (fInf F) = fInf {x, fInf F}"
proof-
  let ?R="fInf {x, fInf F}"
  let ?L="inf x (fInf F)"
  have B0:"?R \<le> x \<and> ?R \<le> fInf F"
    by simp
  have B1:"?L \<le> ?R"
    by simp
  have B2:"?L \<le> x \<and> ?L \<le> fInf F"
    by simp
  have B3:"?R \<le> ?L"
    by (simp add: B0)
  have B4:"?L = ?R"
    by simp
  show ?thesis
    using B4 by blast
qed

lemma infs_insert:
  assumes "finite F \<and> F \<noteq> {}"
  shows "fInf {x, fInf F} = fInf (insert x F)"
proof-
  have B0:"\<forall>y \<in> (insert x F). fInf {x, fInf F} \<le> y"
    by (metis assms finite.insertI infs_eq semilattice_inf_class.coboundedI semilattice_inf_class.insert)
  have B1:"\<forall>y \<in>  (insert x F).  fInf (insert x F) \<le> y"
    using B0 assms by auto
  have B2:"fInf {x, fInf F} \<le> fInf (insert x F)"
    using assms semilattice_inf_class.insert by fastforce
  have B3:"finite (insert x F) \<and> (insert x F) \<noteq> {}"
    by (simp add: assms)
  have B4:" finite {x, fInf F} \<and>  {x, fInf F} \<noteq> {}"
    by simp
  have B5:"\<forall>y \<in> {x, fInf F}. (fInf (insert x F)) \<le> y"
    by (simp add: B1 assms semilattice_inf_class.finite_inf_greatest)
  have B6:"fInf (insert x F) \<le> fInf {x, fInf F}"
    by (simp add: B5)
  show ?thesis
    using B2 B6 order_antisym_conv by blast
qed
  

lemma finite_meet_in_set:
  fixes C::"'a::semilattice_inf set"
  assumes A0: "\<And>a1 a2. a1 \<in> C \<Longrightarrow> a2 \<in> C \<Longrightarrow> (inf a1 a2) \<in> C" and 
          A1:"finite E" and
          A2:"E \<noteq> {}" and
          A3:"E \<subseteq> C"
  shows "(fInf E) \<in> C"
  using A1 A2 A3 
  proof (induct E rule: finite_ne_induct)
    case (singleton x)
    then show ?case
    proof-
      have S0:"fInf {x} \<le> x"
        by simp
      have S1:"x \<le> x"
        by simp
      have S2:"x \<le> fInf {x}"
        by simp
      have S3:"fInf {x} = x"
        by simp
      show S4:"fInf {x} \<in> C"
        using S3 singleton by force
    qed
  next
    case (insert x F)
    have P0:"x \<in> C"
      using insert.prems by auto
    have P1: "F \<subseteq> C" 
      using insert.prems by auto
    have P2:"inf x (fInf F) \<in> C"
      by (simp add: A0 P0 P1 insert.hyps(4))
    have P4:"fInf (insert x F) = inf x (fInf F)"
      by (simp add: insert.hyps(1) insert.hyps(2))
    then show ?case
      by (simp add: P2 P4)
qed



lemma pi_system_then_fc:
  fixes X::"'X::semilattice_inf set"
  assumes A0:"is_pisystem X"
  shows "(\<forall>F. F \<noteq> {} \<longrightarrow> finite F \<longrightarrow> F  \<subseteq> X \<longrightarrow> (fInf F) \<in> X)"
proof-
  have B0:"\<And>a1 a2. a1 \<in> X \<Longrightarrow> a2 \<in> X \<Longrightarrow> (inf a1 a2) \<in> X"
    by (simp add: assms is_pisystem_imp semilattice_inf_binf_eq_inf)
  have B1:"\<And>F. (F \<noteq> {}) \<and> (finite F) \<and> (F \<subseteq> X) \<longrightarrow> (fInf F) \<in> X"
  proof
    fix F assume A1:"(F \<noteq> {}) \<and> (finite F) \<and> (F \<subseteq> X) "
    show "(fInf F) \<in> X"
      by (simp add: A1 B0 finite_meet_in_set)
  qed
  show ?thesis
    using B1 by presburger
qed


lemma upclosed_in_lattice_iff:
   fixes X::"'X::lattice set"
  assumes "X \<noteq> {}"
  shows "is_upclosed X \<longleftrightarrow> (\<forall>x z. x \<in> X \<longrightarrow> (sup x z) \<in> X)"
  by (metis inf_sup_ord(3) is_upclosed_def is_upclosed_imp is_upclosed_in_def sup.absorb_iff2)

lemma fpow_ne_singleton:
  "x \<in> A \<Longrightarrow> {x} \<in> Fpow_ne A"
  by (meson empty_subsetI finite.emptyI finite_insert fpow_ne_if insert_not_empty insert_subset)

lemma fpow_singleton:
  "x \<in> A \<Longrightarrow> {x} \<in> Fpow A"
  using fpow_ne_singleton by force

lemma fpow_ne_union:
  assumes "X \<noteq> {}" and "EF \<noteq> {}" and "finite EF" and "\<forall>F \<in> EF. F \<in> Fpow_ne X"
  shows "(\<Union>EF) \<in> Fpow_ne X"
  by (metis Sup_le_iff all_not_in_conv assms(2) assms(3) assms(4) empty_Union_conv finite_Union fpow_ne_if fpow_ne_imp) 


subsection Compactness

lemma covers_imp:
  "\<And>A b. covers A b \<Longrightarrow> A \<noteq> {} \<and> (\<forall>a. a \<in> A \<longrightarrow> b \<le> a)"
  by (simp add: covers_def lb_set_mem_iff)

lemma covers_if:
  "\<And>A b.  A \<noteq> {} \<and> (\<forall>a. a \<in> A \<longrightarrow> b \<le> a) \<Longrightarrow> covers A b"
  by (simp add: covers_def lb_set_mem_iff)


lemma is_finite_subcover_imp1:
  "\<And>S A b. is_finite_subcover S A b \<Longrightarrow> (\<forall>s. s \<in> S \<longrightarrow> b \<le> s)"
  by (simp add: is_finite_subcover_def lb_set_mem_iff)

lemma is_finite_subcover_imp2:
  "\<And>S A b. is_finite_subcover S A b \<Longrightarrow> (S \<subseteq> A \<and> S \<noteq> {} \<and> finite S)"
  by (simp add: finite_subcover_imp)

lemma is_finite_subcover_if:
  "\<And>S A b. (S \<subseteq> A \<and> S \<noteq> {} \<and> finite S) \<and>  (\<forall>s. s \<in> S \<longrightarrow> b \<le> s) \<Longrightarrow>  is_finite_subcover S A b"
  by (metis fpow_ne_if imp_in_lower_bounds is_finite_subcover_def)

lemma is_compact_imp:
  "\<And>A b.  is_compact b \<Longrightarrow> (covers A b) \<Longrightarrow>  (\<exists>S. is_finite_subcover S A b)"
  using is_compact_def by auto

lemma is_compact_if:
  "\<And>b.  (\<And>A.  (covers A b) \<Longrightarrow>  (\<exists>S. is_finite_subcover S A b))  \<Longrightarrow>  is_compact b"
  using is_compact_def by auto

lemma directed_imp1:
  "is_directed D \<Longrightarrow> D \<noteq> {}"
  by (simp add: is_directed_def)

lemma directed_imp2:
  "\<And>D A. is_directed D \<Longrightarrow> A \<in> Fpow_ne D \<Longrightarrow>  (\<exists>u \<in> D. u \<in> ub_set A)"
  by (simp add: is_directed_def)

lemma directed_if:
  "\<And>D. (\<And>A.  A \<in> Fpow_ne D \<Longrightarrow>  (\<exists>u \<in> D. u \<in> ub_set A)) \<Longrightarrow> D \<noteq> {} \<Longrightarrow> is_directed D"
  by (simp add: is_directed_def)


lemma directed_covering_imp:
  "\<And>a D. directed_covering a D \<Longrightarrow> (covers D a) \<and> is_directed D"
  by (simp add: directed_covering_def)

lemma directed_covering_if:
  "\<And>a D. (covers D a) \<and> is_directed D \<Longrightarrow> directed_covering a D "
  by (simp add: directed_covering_def)

lemma is_compactly_generated_imp:
  "\<And>X. is_compactly_generated  X \<Longrightarrow>  x \<in> X \<Longrightarrow> (\<exists>Cx. (\<forall>c \<in> Cx. is_compact c) \<and> (is_sup x Cx))"
  using is_compactly_generated_def by blast

lemma is_compactly_generated_if:
  "\<And>X. (\<And>x.  x \<in> X \<Longrightarrow> (\<exists>Cx. (\<forall>c \<in> Cx. is_compact c) \<and> (is_sup x Cx))) \<Longrightarrow>  is_compactly_generated  X "
  using is_compactly_generated_def by blast


lemma compact_lattice_imp:
  fixes c::"'a::order"
  assumes A0:"is_compact c"
  shows "\<And>D. directed_covering c D \<longrightarrow> (\<exists>d \<in> D. c \<le> d)"
proof
  fix D assume A1:"directed_covering c D"
  have B0:"(covers D c) "
    using A1 directed_covering_def by auto
  obtain S where A2:"is_finite_subcover S D c"
    using B0 assms is_compact_def by blast
  have B1:"(S \<subseteq> D) \<and> (S \<noteq> {}) \<and> (finite S)"
    using A2 is_finite_subcover_imp2 by blast
  obtain d where A3:"d \<in> D \<and>  d \<in> ub_set S"
    by (meson A1 A2 directed_covering_imp directed_imp2 is_finite_subcover_def)
  show "(\<exists>d \<in> D. c \<le> d)"
    by (meson A3 B0 covers_def lb_set_mem)
qed


lemma compact_lattice_if:
  fixes c::"'a::complete_lattice"
  assumes A0:"\<And>D. directed_covering c D \<longrightarrow> (\<exists>d \<in> D. c \<le> d)"
  shows "is_compact c"
proof-
  have B0:"(\<And>A. (covers A c) \<longrightarrow> (\<exists>S. is_finite_subcover S A c))"
  proof
    fix A assume A1:"covers A c"
    define B where A2:"B \<equiv> {x. (\<exists>S \<in> Fpow_ne A. (x=fSup S))}"
    have B1:"is_directed B"
    proof-
      have B2:"B \<noteq> {}"
      proof-
        have A3:"A \<noteq> {}"
          using A1 covers_def by blast
        obtain S where A4:"S \<in> Fpow_ne A"
          by (metis A3 empty_subsetI ex_in_conv finite.intros(1) finite_insert fpow_ne_if insert_subset)
        show ?thesis
          using A2 A4 by blast
      qed
      have B3:"\<And>S. (S \<in> Fpow_ne B) \<longrightarrow> (\<exists>u \<in> B.  u \<in> ub_set S)"
      proof
        fix S assume A5:"S \<in> Fpow_ne B"
        have B4:"\<forall>s \<in> S. \<exists>F. F \<in> Fpow_ne A \<and> s=fSup F"
          using A2 A5 fpow_ne_imp by auto
        define f where "f=(\<lambda>s. SOME F. (F \<in> Fpow_ne A  \<and> s=fSup F) )"
        define fS where "fS=\<Union>(f`S)"
        have B5:"\<forall>s \<in> S.  (f s) \<in> Fpow_ne A \<and> s=fSup (f s)"
          by (metis (mono_tags, lifting) B4 f_def someI_ex)
        have B50:"finite (f`S) \<and> (f`S \<noteq> {})"
          using A5 fpow_ne_imp by blast
        have B6:"fS \<in> Fpow_ne A"
          by (metis A1 B5 B50 covers_def fS_def fpow_ne_union imageE)
        have B7:"fSup fS \<in> B"
          using A2 B6 by blast
        have B8:"\<forall>s \<in> S. f s \<subseteq> fS"
          by (simp add: SUP_upper fS_def)
        have B9:"\<forall>s \<in> S. (fSup fS) \<ge> fSup (f s)"
          by (metis B5 B6 B8 fpow_ne_imp semilattice_sup_class.subset_imp)
        have B10:"\<forall>s \<in> S. s \<le> fSup fS"
        proof
          fix s assume A6:"s \<in> S"
          have B100:"(fSup fS) \<ge> fSup (f s)"
            by (simp add: A6 B9)
          have B101:"fSup (f s) = s"
            using A6 B5 by auto
           show "s \<le> fSup fS"
             using B100 B101 by auto
        qed
        show "\<exists>u \<in> B.  u \<in> ub_set S"
          by (meson B10 B7 ub_set_elm)
      qed
      show ?thesis
        by (simp add: B2 B3 is_directed_def)
    qed
    have B11:"A \<subseteq> B"
    proof
      fix x assume A7:"x \<in> A"
      have B12:"{x} \<in> Fpow_ne A  \<and> fSup {x} = x"
        using A7 fpow_ne_singleton by force
      show "x \<in> B"
        by (metis (mono_tags, lifting) A2 B12 CollectI) 
    qed
    have B13:"Sup A \<le> Sup B"
      by (simp add: B11 Sup_subset_mono)
    have B14:"c \<le> Sup B"
      by (metis A1 B13 Inf_le_Sup complete_lattice_inf_greatest covers_def dual_order.trans)
    obtain b where A8:"b \<in> B \<and> c \<le> b"
      by (metis A1 B11 covers_def lb_set_mem_iff subset_empty subset_eq)
    obtain S where A9:"S \<in> Fpow_ne A \<and>  fSup S = b"
      using A2 A8 by blast
    have B15:"c \<le> fSup S"
      by (simp add: A8 A9)
    have B16:"fSup S = Sup S"
      by (metis A9 complete_lattice_class.fsup_complete_lattice fpow_ne_imp)
    have B16:"is_finite_subcover S A c"
      by (metis A1 A9 Int_iff covers_def fpow_ne_imp inf.absorb_iff2 is_finite_subcover_if lb_set_mem_iff)
    show "(\<exists>S. is_finite_subcover S A c)"
      using B16 by blast
  qed
  show ?thesis
    by (simp add: B0 is_compact_def)
qed


lemma top_is_meet_irreducible:
  assumes A0:"\<forall>(x::'a::{order,top}). x \<le> top"
  shows "\<not>(is_meet_reducible (top::'a::{order, top}))"
proof(rule ccontr)
  assume A1:"\<not>\<not>((is_meet_reducible (top::'a::{order, top})))"
  have B1:"(\<exists>(A::('a::{order, top} set)). (A \<noteq> {}) \<and> (top \<notin> A) \<and> (is_inf top A))"
    using A1 is_meet_reducible_def by auto
  obtain A where A2:"((A::('a::{order, top} set)) \<noteq> {}) \<and> (top \<notin> A) \<and> (is_inf top A)"
    using B1 by force
  have B2:"top \<in> lb_set A"
    using A2 is_inf_def is_max_iff by auto
  show False
    by (metis A2 B2 assms dual_order.eq_iff ex_in_conv lb_set_mem_iff)
qed


lemma bot_is_meet_irreducible:
  assumes A0:"\<forall>(x::'a::{order,bot}). bot \<le> x"
  shows "\<not>(is_join_reducible (bot::'a::{order, bot}))"
proof(rule ccontr)
  assume A1:"\<not>\<not>((is_join_reducible (bot::'a::{order, bot})))"
  have B1:"(\<exists>(A::('a::{order, bot} set)). (A \<noteq> {}) \<and> (bot \<notin> A) \<and> (is_sup bot A))"
    using A1 is_join_reducible_def by auto
  obtain A where A2:"((A::('a::{order, bot} set)) \<noteq> {}) \<and> (bot \<notin> A) \<and> (is_sup bot A)"
    using B1 by force
  have B2:"bot \<in> ub_set A"
    by (meson A2 is_min_iff is_sup_iff)
  show False
    by (metis A2 B2 assms dual_order.eq_iff ex_in_conv ub_set_mem_iff)
qed

lemma meet_irreducible_in_complete_lattice_iff:
  fixes m::"'a::complete_lattice"
  assumes A0:"m \<noteq> top"
  shows "\<not>(is_meet_reducible m) \<longleftrightarrow> (m < Inf {x. m < x})"
proof
  assume A1:"\<not>(is_meet_reducible m)"
  have B0:"{x. m < x} \<noteq> {}"
    using assms top.not_eq_extremum by auto
  have B1:"m \<le> Inf {x. m < x}"
    using le_Inf_iff order_le_less by auto
  show "(m < Inf {x. m < x})"
  proof-
    let ?L="{x. m <x}"
    have B5:"\<not>(m < Inf {x. m < x}) \<longrightarrow> \<not>\<not>(is_meet_reducible m)"
    proof
    assume A2:"\<not>(m < Inf {x. m < x})"
      have B2:"m \<ge> Inf {x. m <x}"
        using A2 B1 by auto
      have B3:"m = Inf {x. m <x}"
        using A2 B1 by auto
      have B4:"m \<notin> {x. m < x}"
        by simp
      have B5:"is_inf (Inf ?L) ?L"
      proof-
        have B50:"Inf ?L \<in> lb_set ?L"
          by (meson Inf_lower imp_in_lower_bounds)
        have B51:"is_max (Inf ?L) (lb_set ?L)"
          by (meson B0 B50 complete_lattice_inf_greatest is_max_iff)
        show ?thesis
          by (simp add: B51 is_inf_if1)
      qed
      have B3:"(is_meet_reducible m)"
        by (metis B0 B3 B4 B5 is_meet_reducible_def)
      show "\<not>\<not>(is_meet_reducible m)"
        by (simp add: B3)
      qed
    show ?thesis
      using A1 B5 by auto
  qed
  next
  assume A3:"(m < Inf {x. m < x})"
  show "\<not>(is_meet_reducible m)"
  proof-
     have B6:"(is_meet_reducible m) \<longrightarrow> \<not>(m < Inf {x. m < x})"
     proof
      assume A4:"is_meet_reducible m"
      obtain A where A5:"A \<noteq> {} \<and> m \<notin> A \<and> is_inf m A"
        using A4 is_meet_reducible_def by auto
      have B7:"\<forall>x \<in> A. m < x"
        by (metis A5 complete_lattice_inf_is_inf csli.CInf_lower is_inf_unique order_le_less)
      show " \<not>(m < Inf {x. m < x})"
        by (metis A5 B7 Inf_superset_mono complete_lattice_inf_is_inf is_inf_unique leD mem_Collect_eq subsetI)
      qed
    show ?thesis
      using A3 B6 by auto
  qed 
qed




lemma kt_fixed:
  fixes f::"'a::complete_lattice \<Rightarrow> 'a::complete_lattice"
  assumes A0:"is_isotone f"
  defines "A \<equiv> {x. (f x) \<le> x}" and "P \<equiv> {x. f x = x}"
  shows "(\<exists>a. f a = a) \<and> (\<exists>l. is_min l P) "
proof-
  define a where "a = Inf A"
  have B0:"top \<in> A"
    by (simp add: A_def)
  have B1:"A \<noteq> {}"
    using B0 by auto
  have B2:"\<forall>x \<in> A. a \<le> x"
    by (simp add: Inf_lower a_def)
  have B3:"\<forall>x \<in> A. f a \<le> f x"
    using A0 B2 is_isotone_def by auto
  have B4:"\<forall>x \<in> A. f x \<le> x"
    by (simp add: A_def)
  have B5:"\<forall>x \<in> A. f a \<le> x"
    by (metis B3 B4 order_trans)
  have B6:"f a \<le> a"
    by (metis B5 Inf_greatest a_def)
  have B7:"(f \<circ> f)(a) \<le> f a"
    using A0 B6 is_isotone_def by auto
  have B8:"(f a) \<in> A"
    using A_def B7 by auto
  have B9:"a \<le> f a"
    by (simp add: B2 B8)
  have B10:"f a = a"
    by (simp add: B6 B9 dual_order.antisym)
  have B11:"P \<subseteq> A"
    by (simp add: A_def Collect_mono_iff P_def)
  have B12:"\<forall>x \<in> P. a \<le> x"
    using B11 B2 by blast
  have B13:"a \<in> A"
    using B10 B8 by auto
  show ?thesis
    by (metis (mono_tags, lifting) B10 B12 P_def is_min_iff mem_Collect_eq)
qed

lemma isotone_inf_leq_inf_isotone:
  fixes A::"'a::order set" and
        f::"'a::order \<Rightarrow> 'b::order"
  assumes A0:"is_isotone f" and
          A1:"has_inf A" and
          A2:"has_inf (f`A)"
  shows "f (InfUn A) \<le> InfUn (f`A)"
proof-
  have B0:"\<forall>x. x \<in> A \<longrightarrow> f (InfUn A) \<le> (f x)"
    using A0 A1 inf_is_inf is_inf_imp2 is_isotone_def by blast
  show ?thesis
    by (metis (mono_tags, lifting) A2 B0 image_iff inf_is_inf is_inf_imp3)
qed
    
lemma principle_filter_anti1:
  "\<And>(x1::'a::order) x2 X. x1 \<le> x2 \<Longrightarrow> (principal_filter_in x2 X) \<subseteq>  (principal_filter_in x1 X)"
  by (simp add: order_trans subset_eq ub_set_in_mem_iff)

lemma principle_filter_anti2:
  "\<And>(x1::'a::order) x2. (principal_filter_in x2 UNIV) \<subseteq>  (principal_filter_in x1 UNIV) \<Longrightarrow>  x1 \<le> x2"
  by (simp add: order_trans subset_eq ub_set_in_mem_iff)


lemma sup_equiv1:
  "is_sup_in (s::'a::order) A X \<longleftrightarrow> (s \<in> X \<and> (\<forall>u \<in> X. ((\<forall>a \<in> A. a \<le> u) \<longleftrightarrow> (s \<le> u))))" (is "?L \<longleftrightarrow> ?R")
proof
  assume L:?L  show ?R
    by (meson L is_sup_in_imp2 is_sup_in_imp3 is_sup_in_in_set order.trans)
  next
  assume R:?R  show ?L
     by (metis R dual_order.refl is_sup_in_if3)
qed
  
lemma inf_equiv1:
  "is_inf_in (i::'a::order) A X \<longleftrightarrow> (i \<in> X \<and> (\<forall>l \<in> X. ((\<forall>a \<in> A. l \<le> a) \<longleftrightarrow> (l \<le> i))))" (is "?L \<longleftrightarrow> ?R")
proof
  assume L:?L  show ?R
    by (meson L dual_order.trans is_inf_in_imp2 is_inf_in_imp3 is_inf_in_in_set)
  next
  assume R:?R  show ?L
     by (metis R dual_order.refl is_inf_in_if3)
qed



lemma inf_from_sup:
  "(InfUn A)  = (SupUn (lb_set A))"
  by (metis (full_types) Collect_empty_eq Collect_empty_eq_bot InfUn_def SupUn_def has_max_def 
      has_max_has_sup has_min_def has_sup_def inf_eq_sup_lb is_inf_def is_sup_def)

lemma sup_from_inf:
  "(SupUn A)  = (InfUn (ub_set A))"
  by (metis (no_types, lifting) Collect_empty_eq Collect_empty_eq_bot InfUn_def SupUn_def has_inf_def
       has_min_has_inf is_inf_def is_max_imp_has_max is_min_imp_has_min is_sup_iff sup_eq_inf_ub)

lemma inter_complete_lat:
  fixes A::"'a set set" and X::"'a set"
  assumes A0:"A \<subseteq> (Pow X)"
  shows "InfIn A (Pow X) = X \<inter> (\<Inter> A)"
proof-
  define I where "I=X \<inter> (\<Inter> A)"
  have B0:"I \<in> lb_set_in A (Pow X)"
    using I_def lb_set_in_mem_iff by auto
  have B1:"\<forall>l. l \<in> (lb_set_in A (Pow X)) \<longrightarrow> l \<le> I"
    by (simp add: I_def Inf_greatest lb_set_in_mem_iff)
  have B2:"is_inf_in I A (Pow X)"
    by (simp add: B0 B1 is_inf_in_def is_max_if2)
  show ?thesis
    using B2 I_def is_inf_in_inf_eq by blast
qed


lemma empty_inter_is_carrier:
  fixes X::"'a set"
  shows "InfIn {} (Pow X) = X"
  by (simp add: inter_complete_lat)


section Closures

lemma up_closure_in_restricted:
  "X \<inter> (up_closure A) = up_closure_in A X"
  apply(simp add:up_closure_def up_closure_in_def)
  by blast


lemma down_closure_in_restricted:
  "X \<inter> (down_closure A) = down_closure_in A X"
  apply(simp add:down_closure_def down_closure_in_def)
  by blast

lemma up_closure_imp:
  "\<And>A x. (\<exists>a \<in> A. a \<le> x) \<Longrightarrow> x \<in> up_closure A"
  by (simp add: up_closure_def up_closure_in_def)

lemma down_closure_imp:
  "\<And>A x. (\<exists>a \<in> A. x \<le> a) \<Longrightarrow> x \<in> down_closure A"
  by (simp add: down_closure_def down_closure_in_def)


lemma up_closure_in_imp:
  "\<And>A x. x \<in> X \<Longrightarrow> (\<exists>a \<in> A. a \<le> x) \<Longrightarrow> x \<in> up_closure_in A X"
  by (simp add: up_closure_in_def up_closure_def)

lemma down_closure_in_imp:
  "\<And>A x. x \<in> X \<Longrightarrow> (\<exists>a \<in> A. x \<le> a) \<Longrightarrow> x \<in> down_closure_in A X"
  by (simp add: down_closure_in_def)
                   
                   
lemma up_closure_in_univ_imp:
  "is_upclosed_in A UNIV \<longleftrightarrow> is_upclosed A"
  by (simp add: is_upclosed_def)
               
lemma down_closure_in_univ_imp:
  "is_downclosed_in A UNIV \<longleftrightarrow> is_downclosed A"
  by (simp add: is_downclosed_def)

lemma up_closure_if:
  "\<And>A x.  x \<in> up_closure A \<Longrightarrow> (\<exists>a \<in> A. a \<le> x)"
  by (simp add: up_closure_def up_closure_in_def)

lemma down_closure_if:
  "\<And>A x.  x \<in> down_closure A \<Longrightarrow> (\<exists>a \<in> A. x \<le> a)"
  by (simp add: down_closure_def down_closure_in_def)

lemma up_closure_in_if:
  "\<And>A x.  x \<in> X \<Longrightarrow> x \<in> up_closure_in A X \<Longrightarrow> (\<exists>a \<in> A. a \<le> x)"
  by (simp add: up_closure_in_def)

lemma down_closure_in_if:
  "\<And>A x.  x \<in> X \<Longrightarrow> x \<in> down_closure_in A X \<Longrightarrow> (\<exists>a \<in> A. x \<le> a)"
  by (simp add: down_closure_in_def)


lemma up_closure_in_in_carrier1:
  "\<And>A x.  x \<in> up_closure_in A X \<Longrightarrow> (x \<in> A \<or> x \<in> X)"
  by (simp add: up_closure_in_def)

lemma up_closure_in_in_carrier2:
  "\<And>A x.  x \<in> up_closure_in A X \<Longrightarrow> A \<subseteq> X \<Longrightarrow>  x \<in> X"
  using up_closure_in_def by auto

lemma down_closure_in_in_carrier1:
  "\<And>A x.  x \<in> down_closure_in A X \<Longrightarrow> (x \<in> A \<or> x \<in> X)"
  by (simp add: down_closure_in_def)

lemma down_closure_in_in_carrier2:
  "\<And>A x.  x \<in> down_closure_in A X \<Longrightarrow> A \<subseteq> X \<Longrightarrow>  x \<in> X"
  using down_closure_in_def by auto


lemma up_closure_obtain:
  assumes "x \<in> up_closure A"
  obtains a where "a \<in> A \<and> a \<le> x"
  using assms up_closure_if by auto

lemma up_closure_in_obtain:
  assumes "x \<in> up_closure_in A X"
  obtains a where "a \<in> A \<and> a \<le> x"
  by (metis Int_iff assms up_closure_in_if up_closure_in_restricted)


lemma down_closure_in_obtain:
  assumes "x \<in> down_closure_in A X"
  obtains a where "a \<in> A \<and> x \<le> a"
  by (metis Int_iff assms down_closure_in_if down_closure_in_restricted)

lemma down_closure_obtain:
  assumes "x \<in> down_closure A"
  obtains a where "a \<in> A \<and> x \<le> a"
  using assms down_closure_if by auto

lemma up_closure_extensive:
  "A \<subseteq> up_closure A"
  apply(simp add:up_closure_def up_closure_in_def)
  by blast

lemma up_closure_in_extensive:
 assumes "A \<subseteq> X"
 shows "A \<subseteq> up_closure_in A X"
  using assms up_closure_in_def by fastforce

lemma down_closure_in_extensive:
 assumes "A \<subseteq> X"
 shows "A \<subseteq> down_closure_in A X"
  using assms down_closure_in_def by fastforce

lemma down_closure_extensive:
  "A \<subseteq>down_closure A"
  by (simp add: down_closure_def down_closure_in_extensive)

lemma up_closure_in_isotone:
 assumes "B \<subseteq> X" and "A \<subseteq> B"
 shows "up_closure_in A X \<subseteq> up_closure_in B X"
 apply(simp add:up_closure_in_def)
 using assms(2) by force

lemma down_closure_in_isotone:
 assumes "B \<subseteq> X" and "A \<subseteq> B"
 shows "down_closure_in A X \<subseteq> down_closure_in B X"
 apply(simp add:down_closure_in_def)
 using assms(2) by force

lemma up_closure_isotone:
 assumes "A \<subseteq> B"
 shows "up_closure A \<subseteq> up_closure B"
 by (simp add: assms up_closure_def up_closure_in_isotone)

lemma down_closure_isotone:
 assumes "A \<subseteq> B"
 shows "down_closure A \<subseteq> down_closure B"
 by (simp add: assms down_closure_def down_closure_in_isotone)


lemma up_closure_on_idempotent:
 assumes "A \<subseteq> X"
 shows "up_closure_in A X = up_closure_in (up_closure_in A X) X"
 apply(simp add:up_closure_in_def)
 using order_trans by auto

lemma down_closure_in_idempotent:
 assumes "A \<subseteq> X"
 shows "down_closure_in A X = down_closure_in (down_closure_in A X) X"
 apply(simp add:down_closure_in_def)
 using order_trans by auto

lemma up_closure_idempotent:
 shows "up_closure A = up_closure (up_closure A)"
 apply(simp add:up_closure_def up_closure_in_def)
 using dual_order.trans by auto

lemma down_closure_idempotent:
 shows "down_closure A = down_closure (down_closure A)"
 apply(simp add:down_closure_def down_closure_in_def)
 using dual_order.trans by auto

lemma upset_if_eq_upclosure_on:
  assumes "A = up_closure_in A X"
  shows "is_upclosed_in A X"
  apply(simp add: is_upclosed_in_def)
  using assms up_closure_in_imp by blast

lemma downset_if_eq_downclosure_in:
  assumes "A = down_closure_in A X"
  shows "is_downclosed_in A X"
  apply(simp add: is_downclosed_in_def)
  using assms down_closure_in_imp by blast

lemma upset_if_eq_upclosure:
  assumes "A = up_closure A"
  shows "is_upclosed A"
  apply(simp add: is_upclosed_def up_closure_def)
  by (metis assms up_closure_def upset_if_eq_upclosure_on)

lemma downset_if_eq_upclosure:
  assumes "A = down_closure A"
  shows "is_downclosed A"
  apply(simp add: is_downclosed_def down_closure_def)
  by (metis assms down_closure_def downset_if_eq_downclosure_in)


lemma eq_upclosure_on_imp_upset:
  assumes "A \<subseteq> X" and "is_upclosed_in A X"
  shows "A = up_closure_in A X"
proof-
  have B0:"A \<subseteq> up_closure_in A X"
    by (simp add: assms(1) up_closure_in_extensive)
  have B1:"up_closure_in A X \<subseteq> A"
    by (meson assms(2) is_upclosed_in_def subset_eq up_closure_in_in_carrier1 up_closure_in_obtain)
  show ?thesis
    by (simp add: B0 B1 subset_antisym)
qed

lemma eq_upclosure_imp_upset:
  assumes "is_upclosed A"
  shows "A = up_closure A"
  by (simp add: assms eq_upclosure_on_imp_upset up_closure_def up_closure_in_univ_imp)


lemma eq_downclosure_on_imp_downset:
  assumes "A \<subseteq> X" and "is_downclosed_in A X"
  shows "A = down_closure_in A X"
proof-
  have B0:"A \<subseteq> down_closure_in A X"
    by (simp add: assms(1) down_closure_in_extensive)
  have B1:"down_closure_in A X \<subseteq> A"
    by (meson assms(2) is_downclosed_in_def subset_eq down_closure_in_in_carrier1 down_closure_in_obtain)
  show ?thesis
    by (simp add: B0 B1 subset_antisym)
qed

lemma eq_downclosure_imp_downset:
  assumes "is_downclosed A"
  shows "A = down_closure A"
  by (simp add: assms down_closure_def down_closure_in_univ_imp eq_downclosure_on_imp_downset)



lemma in_downsets_in_imp_subset:
  "E \<in> downsets_in X  \<Longrightarrow> E \<subseteq> X"
  by (simp add: downsets_in_def)

lemma in_upsets_in_imp_subset:
  "E \<in> upsets_in X  \<Longrightarrow> E \<subseteq> X"
  by (simp add: upsets_in_def)


lemma lb_is_downset:
  fixes A X::"'a::order set"
  assumes "A \<subseteq> X"
  shows "is_downclosed_in (lb_set_in A X) X"
  apply(simp add:is_downclosed_in_def)
  by (meson dual_order.trans lb_set_in_mem_iff)


lemma ub_is_upset:
  fixes A X::"'a::order set"
  assumes "A \<subseteq> X"
  shows "is_upclosed_in (ub_set_in A X) X"
  apply(simp add:is_upclosed_in_def)
  by (meson dual_order.trans ub_set_in_mem_iff)

lemma is_downclosed_in_imp2:
  "\<And>A X. A \<in> downsets_in X \<Longrightarrow> is_downclosed_in A X"
  by (simp add: downsets_in_def)

lemma is_upclosed_in_imp2:
  "\<And>A X. A \<in> upsets_in X \<Longrightarrow> is_upclosed_in A X"
  by (simp add: upsets_in_def)

lemma downset_transitive:
  fixes A B X::"'a::order set"
  assumes A0:"A \<in> downsets_in X" and A1:"B  \<in> downsets_in A"
  shows "B \<in> downsets_in X"
proof-
  have B0:"B \<subseteq> A \<and> A \<subseteq> X" 
    by (simp add: A0 A1 in_downsets_in_imp_subset)
  have B1:"\<forall>a \<in> A. \<forall>b \<in> B. (a \<le> b) \<longrightarrow> a \<in> B"
    using A1 is_downclosed_in_def is_downclosed_in_imp2 by blast
  have B2:"\<forall>x \<in> X. \<forall>a \<in> A. (x \<le> a) \<longrightarrow> x \<in> A"
    using B0 A0 is_downclosed_in_imp is_downclosed_in_imp2 by blast
  have B3:"is_downclosed_in B X" (*by (meson A1 B0 B2 in_mono is_downclosed_in_def is_downclosed_in_imp2)*)
  proof-
    have B30:"\<And>x b. (x \<in>X \<and> b \<in> B \<and>  x \<le> b) \<longrightarrow> x \<in> B"
    proof
      fix x b  assume A2:"x \<in>  X \<and> b \<in> B \<and> x \<le> b" 
      have B21:"b \<in> A"
        using A2 B0 by blast
      have B22:"x \<in> X \<and> b \<in> A \<and> x \<le> b"
        by (simp add: A2 B21)
      show "x \<in> B"
        using A2 B1 B2 B21 by blast
    qed
    show ?thesis
      using B30 is_downclosed_in_def by blast
  qed
  have B4:"B \<subseteq> X"
    using B0 by blast
  show ?thesis
    by (simp add: B3 B4 downsets_in_def)
qed

lemma upset_transitive:
fixes A B X::"'a::order set"
assumes A0:"A \<in> upsets_in X" and A1:"B \<in> upsets_in A"
shows "B \<in> upsets_in X"
proof-
  have B0:"B \<subseteq> A \<and> A \<subseteq> X" 
    by (simp add: A0 A1 in_upsets_in_imp_subset)
  have B1:"\<forall>a \<in> A. \<forall>b \<in> B. (b \<le> a) \<longrightarrow> a \<in> B"
    using A1 is_upclosed_in_def is_upclosed_in_imp2 by blast
  have B2:"\<forall>x \<in> X. \<forall>a \<in> A. (a \<le> x) \<longrightarrow> x \<in> A"
    using B0 A0 is_upclosed_in_imp is_upclosed_in_imp2 by blast
  have B3:"is_upclosed_in B X" (*using B0 B1 B2 is_upclosed_in_def by fastforce*)
  proof-
    have B30:"\<And>x b. (x \<in> X \<and> b \<in> B \<and> b \<le> x) \<longrightarrow> x \<in> B"
    proof
      fix x b assume A2:"x \<in> X \<and> b \<in> B \<and> b \<le> x" 
      have B21:"b \<in> A"
        using A2 B0 by blast
      have B22:"x \<in> X \<and> b \<in> A \<and> b \<le> x"
        by (simp add: A2 B21)
      show "x \<in> B"
        using A2 B1 B2 B21 by blast
    qed
    show ?thesis
      using B30 is_upclosed_in_def by blast
  qed
  have B4:"B \<subseteq> X"
    using B0 by blast
  show ?thesis
    by (simp add: B3 B4 upsets_in_def)
qed

lemma in_downsets_imp_complement_in_upsets:
  assumes "D \<in> downsets_in X"
  shows "(X - D) \<in> upsets_in X"
  apply(simp add:upsets_in_def is_upclosed_in_def)
  using assms in_downsets_in_imp_subset is_downclosed_in_imp is_downclosed_in_imp2 by blast

lemma in_downsets_if_complement_in_upsets:
  assumes  "D \<subseteq> X" and "(X - D) \<in> upsets_in X" 
  shows "D \<in> downsets_in X"
  apply(simp add:downsets_in_def is_downclosed_in_def)
  by (metis DiffD2 DiffI IntD2 assms(1) assms(2) eq_upclosure_on_imp_upset in_upsets_in_imp_subset inf.order_iff is_upclosed_in_imp2 up_closure_in_imp)
    
lemma in_downsets_iff_complement_in_upsets:
  assumes  "D \<subseteq> X"
  shows "D \<in> downsets_in X \<longleftrightarrow> (X - D) \<in> upsets_in X"
  using assms in_downsets_if_complement_in_upsets in_downsets_imp_complement_in_upsets by blast

lemma upsets_in_inter_closed:
  assumes "EF \<subseteq> upsets_in X" and "EF \<noteq> {}"
  shows "\<Inter>EF \<in> upsets_in X"
  apply(simp add:upsets_in_def is_upclosed_in_def)
  by (metis Inf_less_eq assms(1) assms(2) in_mono in_upsets_in_imp_subset is_upclosed_in_imp is_upclosed_in_imp2)


lemma upsets_in_un_closed:
  assumes "EF \<subseteq> upsets_in X" and "EF \<noteq> {}"
  shows "\<Union>EF \<in> upsets_in X"
  apply(simp add:upsets_in_def is_upclosed_in_def)
  by (metis assms(1) assms(2) csls.CSup_least in_mono in_upsets_in_imp_subset is_upclosed_in_imp is_upclosed_in_imp2)

lemma downsets_in_un_closed:
  assumes "EF \<subseteq> downsets_in X" and "EF \<noteq> {}"
  shows "\<Union>EF \<in> downsets_in X"
  apply(simp add:downsets_in_def is_downclosed_in_def)
  by (metis assms(1) assms(2) csls.CSup_least in_downsets_in_imp_subset is_downclosed_in_imp is_downclosed_in_imp2 subsetD)

lemma downsets_in_inter_closed:
  assumes "EF \<subseteq> downsets_in X" and "EF \<noteq> {}"
  shows "\<Inter>EF \<in> downsets_in X"
  apply(simp add:downsets_in_def is_downclosed_in_def)
  by (metis Inf_less_eq assms(1) assms(2) in_downsets_in_imp_subset in_mono is_downclosed_in_imp is_downclosed_in_imp2)

lemma down_closure_has_same_ub:
  assumes "A \<subseteq> X"
  shows "ub_set_in (down_closure_in A X) X = ub_set_in A X"
  apply(auto simp add:ub_set_in_def down_closure_in_def)
  using assms by blast

lemma up_closure_has_same_lb:
  assumes "A \<subseteq> X"
  shows "lb_set_in (up_closure_in A X) X = lb_set_in A X"
  apply(auto simp add:lb_set_in_def up_closure_in_def)
  using assms by blast

lemma has_sup_in_imp_downclosure_has_sup_in:
  assumes A0:"has_sup_in A X" and A1:"A \<subseteq> X"
  shows "has_sup_in (down_closure_in A X) X \<and> SupIn A X = SupIn (down_closure_in A X) X"
proof-
  obtain s where B0:"s = SupIn A X"
    by simp
  have B1:"ub_set_in (down_closure_in A X) X = ub_set_in A X"
    by (simp add: A1 down_closure_has_same_ub)
  show "has_sup_in (down_closure_in A X) X \<and>  SupIn A X = SupIn (down_closure_in A X) X"
    by (metis A0 B1 has_sup_in_def has_sup_in_imp1 min_unique)
qed


lemma has_inf_in_imp_upclosure_has_inf_in:
  assumes A0:"has_inf_in A X" and A1:"A \<subseteq> X"
  shows "has_inf_in (up_closure_in A X) X \<and> InfIn A X = InfIn (up_closure_in A X) X"
proof-
  have B1:"lb_set_in (up_closure_in A X) X = lb_set_in A X"
    by (simp add: A1 up_closure_has_same_lb)
  show "has_inf_in (up_closure_in A X) X \<and> InfIn A X = InfIn (up_closure_in A X) X"
    by (metis A0 B1 has_inf_in_def has_inf_in_imp1 max_unique)
qed

lemma is_filter_in_imp:
  "\<And>F X. is_filter_in F X \<Longrightarrow> (F \<subseteq> X \<and> is_downdir F \<and> is_upclosed_in F X \<and> is_inhabited F)"
  by(simp add:is_filter_in_def)

lemma is_filter_in_if:
  "\<And>F X. (F \<subseteq> X \<and> is_downdir F \<and> is_upclosed_in F X \<and> is_inhabited F) \<Longrightarrow> is_filter_in F X "
  by(simp add:is_filter_in_def)


lemma is_filter_imp:
  "\<And>F. is_filter F \<Longrightarrow> (F \<subseteq> UNIV \<and> is_downdir F \<and> is_upclosed_in F UNIV \<and> is_inhabited F)"
  by (simp add: is_filter_def is_filter_in_imp)

lemma is_filter_if:
  "\<And>F. (F \<subseteq> UNIV \<and> is_downdir F \<and> is_upclosed_in F UNIV \<and> is_inhabited F) \<Longrightarrow> is_filter F "
  by (simp add: is_filter_def is_filter_in_if)



lemma moore_family_imp:
  "\<And>C. is_moore_family C \<Longrightarrow>(\<And>a. has_min (principal_filter_in a C))"  
  by (simp add: is_moore_family_def)

lemma moore_family_imp_ne:
  "\<And>C. is_moore_family C \<Longrightarrow> C \<noteq> {}"
  by (simp add: is_moore_family_def)  

lemma moore_family_if_lpf:
  assumes "C \<noteq> {}"
  shows "is_moore_family C \<longleftrightarrow> (\<forall>a. has_min (principal_filter_in a C))"
  by (simp add: assms is_moore_family_def)

lemma moore_family_obtain:
  assumes "is_moore_family C" 
  obtains m where "is_min m (principal_filter_in a C)"
  by (meson assms has_min_def is_moore_family_def)  

lemma top_principal_filter:
  fixes top::"'a::order"
  assumes is_top:"\<forall>x. x \<le> top"
  shows "ub_set {top} = {top}"
  by (simp add: is_top order_antisym_conv ub_set_def)

lemma top_least_in_principal_filter:
  fixes top::"'a::order"
  assumes is_top:"\<forall>x. x \<le> top"
  shows "is_min top (ub_set {top})"
  by (simp add: is_min_singleton is_top top_principal_filter)

lemma top_eq_least_in_principal_filter:
  fixes top::"'a::order"
  assumes is_top:"\<forall>x. x \<le> top"
  shows "min (ub_set {top}) = top"
  by (simp add: is_top min_singleton top_principal_filter)



lemma moore_closure_topped:
  fixes C::"'a::order set" and
        top::"'a::order"
  assumes A0:"is_moore_family C" and 
          A1:"\<forall>x. x \<le> top"
  shows "top \<in> C"
  by (metis A0 A1 dual_order.antisym has_min_iff is_moore_family_def singletonI ub_set_in_mem)



lemma in_cl_range_idempotent:
  assumes A0:"is_closure f"
  shows "\<And>x. x \<in> (range f) \<longrightarrow> f x = x"
  by (metis assms image_iff is_closure_def is_idempotent_def)

lemma closure_range_non_increasing:
  fixes E::"'a::order set" and  f::"'a::order \<Rightarrow> 'a::order" and  i::"'a::order" 
  assumes A0:"is_closure f" and
          A1:"E \<subseteq> range f" and
          A2:"is_inf i E"  
  shows"\<And>x. x \<in> E \<longrightarrow> f i \<le> x"
proof
  fix x assume A3:"x \<in> E"
  have B00:"f i \<le> f x"
    using A0 A2 A3 is_closure_def is_inf_imp2 is_isotone_def by blast
  have B01:"... =  x"
    using A0 A1 A3 in_cl_range_idempotent by blast
  show "(f i) \<le> x"
    using B00 B01 by force
qed

lemma closure_range_inf_closed_:
  fixes E::"'a::order set" and  f::"'a::order \<Rightarrow> 'a::order" and  i::"'a::order" 
  assumes A0:"is_closure f" and
          A1:"E \<subseteq> range f" and
          A2:"is_inf i E"
  shows "i \<in> range f \<and> (f i) = i"
proof-
  have B0:"\<And>x. x \<in> E \<longrightarrow> f i \<le> x"
    using A0 A1 A2 closure_range_non_increasing by blast
  have B1:"(f i) \<in> lb_set E"
    by (simp add: B0 lb_set_elm)
  have B2:"i \<le> f i"
    using A0 is_closure_def is_extensive_def by blast
  have B3:"f i \<le> i"
    using A2 B0 is_inf_imp3 by auto
  show ?thesis
    using B2 B3 order_antisym by blast
qed


lemma moore_closure_imp:
  fixes C::"'X::order set"
  assumes A0:"is_moore_family C"
  shows "\<forall>x. (moore_to_closure C) x = InfUn (principal_filter_in x C)"
  by (simp add: moore_to_closure_def)

lemma moore_family_is_cofinal:
  fixes C::"'X::order set"
  assumes A0:"is_moore_family C"
  shows "\<forall>x. principal_filter_in x C \<noteq> {}"
  using assms has_min_iff2 is_moore_family_def min_imp_ne by auto




lemma closure_range_inf_closed:
  fixes E::"'X::complete_semilattice_inf set" and
        f::"'X::complete_semilattice_inf \<Rightarrow> 'X::complete_semilattice_inf"
  assumes A0:"is_closure f" and
          A1:"E \<subseteq> range f" and
          A2:"E \<noteq> {}"
  shows "f (Inf E) = Inf E "
proof-
  define i where "i = Inf E"
  have B0:"\<forall>x.  x\<in> E \<longrightarrow> i \<le> x"
    using CInf_lower i_def by blast
  have B1:"\<forall>x. x \<in> E \<longrightarrow> f i \<le> x"
    using A0 A1 closure_range_non_increasing complete_semilattice_inf_is_inf i_def by blast
  have B2:"f i \<in> lb_set E"
    by (simp add: B1 lb_set_elm)
  have B3:"f i \<le> i"
    using A2 B2 complete_semilattice_inf_greatest i_def by blast
  have B4:"f i \<ge> i"
    using A0 is_closure_def is_extensive_def by blast
  show ?thesis
    using B3 B4 i_def order_antisym_conv by blast
qed


lemma moore_closure_imp_csemilattice_inf:
  fixes C::"'X::complete_semilattice_inf set"
  assumes A0:"is_moore_family C"
  shows "\<forall>x. (moore_to_closure C) x = Inf(principal_filter_in x C)"
  by (simp add: assms complete_semilattice_inf_is_inf2 moore_family_is_cofinal moore_to_closure_def)



lemma moore_to_closure_is_extensive:
  fixes C::"'a::order set"
  assumes A0:"is_moore_family C" 
  shows "is_extensive (moore_to_closure C)"
proof-
  let ?f="moore_to_closure C"
  have C01:"\<forall>x. x \<le> ?f x"
    by (metis A0 IntE has_least_imp_inf_eq_least has_min_iff min_if2 moore_family_imp moore_to_closure_def singletonI ub_set_imp ub_set_in_ub_inter)
  show ?thesis
    by (simp add: C01 is_extensive_def) 
qed




lemma moore_to_closure_is_isotone:
  fixes C::"'a::order set"
  assumes A0:"is_moore_family C" 
  shows "is_isotone (moore_to_closure C)"
proof-
  let ?f="moore_to_closure C"
  have C10:"\<And>x1 x2. x1 \<le> x2 \<longrightarrow> (?f x1) \<le> (?f x2)"
    by (simp add: assms has_min_has_inf inf_antitone1 moore_family_imp moore_to_closure_def principle_filter_anti1)
  show ?thesis
    by (simp add: C10 is_isotone_def)
qed

lemma moore_to_closure_is_idempotent:
  fixes C::"'a::order set"
  assumes A0:"is_moore_family C" 
  shows "is_idempotent (moore_to_closure C)"
proof-
  let ?f="moore_to_closure C"
  have C0:"is_extensive ?f"
    by (simp add: assms moore_to_closure_is_extensive)
  have C2:"is_idempotent ?f"
  proof-
    have C20:"\<forall>x. ?f x = ?f (?f x)"
    proof 
      fix x
      let ?y1="?f x" and ?y2="?f (?f x)"
      let ?Px="principal_filter_in x C" and ?Pfx="principal_filter_in ?y1 C"
      have C2B0:"?y1 \<in> ?Px"
        by (metis assms has_min_iff2 inf_is_inf is_inf_def is_inf_unique is_max_iff is_min_iff lb_set_mem_iff has_min_has_inf moore_family_imp moore_to_closure_def)
      have C2B1:"?y2 \<in> ?Pfx"
        by (metis assms has_min_iff2 inf_is_inf is_inf_def is_inf_unique is_max_iff is_min_iff lb_set_mem_iff has_min_has_inf moore_family_imp moore_to_closure_def)
      have C2B2:"?y1 \<in> C"
        using C2B0 ub_set_in_mem_iff by auto
      have C2B3:"?y1 \<in> ?Pfx"
        by (simp add: C2B2 ub_set_in_mem_iff)
      have C2B4:"\<forall>z \<in> ?Pfx. ?y1 \<le> z"
        by (simp add: ub_set_in_mem_iff)
      have C2B3:"?y1 = InfUn ?Pfx"
        by (metis (no_types, lifting) C2B1 C2B3 assms empty_subsetI has_inf_singleton inf_antitone1 inf_singleton insert_subsetI has_min_has_inf moore_family_imp moore_to_closure_def order_antisym_conv singleton_iff ub_set_in_mem)
      show "?f x = ?f (?f x)"
        by (metis C2B3 moore_to_closure_def)
      qed
    show ?thesis
      using C20 is_idempotent_def by blast
  qed
  show ?thesis
    using C2 by auto
qed

lemma moore_to_closure_is_idempotent2:
  fixes C::"'a::order set"
  assumes A0:"is_moore_family C" 
  shows "\<forall>c \<in> C. (moore_to_closure C)(c) = c"
proof
  fix c assume A1:"c \<in> C"
  define f where "f=(moore_to_closure C)"
  have B0:"f(c) = InfUn(principal_filter_in c C)"
    by (simp add: assms f_def moore_closure_imp)
  have B1:"... = c"
    by (metis A1 B0 assms f_def inf_is_inf is_extensive_def is_inf_def is_max_iff is_max_singleton
        lb_set_mem has_min_has_inf moore_family_imp moore_to_closure_is_extensive order_antisym ub_set_in_elm)
  show "f(c) = c"
    by (simp add: B0 B1)
qed 



lemma moore_to_closure_is_idempotent3:
  fixes C::"'a::order set"
  defines"f \<equiv> (moore_to_closure C)"
  assumes A0:"is_moore_family C" 
  shows "\<And>c. (f(c) = c) \<longrightarrow> c \<in> C"
proof
  fix c 
  assume A1:"f(c) = c"
  have B0:"... = InfUn(principal_filter_in c C)"
    by (metis A1 f_def moore_to_closure_def)
  have B1:"... = min (principal_filter_in c C)"
    by (simp add: assms has_least_imp_inf_eq_least moore_family_imp)
  have B2:"c \<in> principal_filter_in c C"
    by (metis A0 B0 B1 has_sup_in_def is_min_iff is_sup_in_def moore_family_imp
         sup_in_degenerate supin_is_sup ub_set_in_degenerate)
  show "c \<in> C"
    using B2 ub_set_in_mem_iff by blast
qed

lemma moore_to_closure_iscl:
  fixes C::"'a::order set"
  assumes A0:"is_moore_family C"
  shows "is_closure (moore_to_closure C)"
proof-
  let ?f="moore_to_closure C"
  have C0:"is_extensive ?f"
    by (simp add: assms moore_to_closure_is_extensive)
  have C1:"is_isotone ?f"
    by (simp add: assms moore_to_closure_is_isotone)
  have C2:"is_idempotent ?f"
    by (simp add: assms moore_to_closure_is_idempotent)
  show ?thesis
    by (simp add: C0 C1 C2 is_closure_def)
qed


lemma moore_then_inf_closed:
  fixes C::"'a::order set" and top::"'a::order"
  assumes A0:"is_moore_family C" and
          is_top:"\<forall>(a::'a::order). a \<le> top"
  shows "\<And>A. (A \<in> (Pow C) \<and> has_inf A) \<longrightarrow> InfUn A \<in> C"
proof
  fix A assume A1:"(A \<in> (Pow C) \<and> has_inf A)"
  define i where "i = InfUn A"
  show "InfUn A \<in> C"
  proof(cases "A = {}")
    case True
    have B0:"InfUn A = top"
      by (metis A1 True has_max_iff2 if_has_max_max_unique inf_is_inf is_inf_def is_max_top is_top lb_set_degenerate)
    then show ?thesis
      by (simp add: A0 is_top moore_closure_topped)
  next
    case False
    define f where "f=(moore_to_closure C)"
    have B1:"\<forall>a \<in> A. i \<le> a \<and> a \<in> C"
      by (metis A1 Pow_iff empty_subsetI has_inf_singleton i_def inf_antitone1 inf_singleton insert_absorb insert_subset)
    have B2:"\<forall>a \<in> A. f i \<le> f a"
      using A0 B1 f_def is_isotone_def moore_to_closure_is_isotone by blast
    have B3:"\<forall>a \<in> A. f a = a"
      by (simp add: A0 B1 f_def moore_to_closure_is_idempotent2)
    have B4:"f i \<le> i"
      by (metis A1 B2 B3 i_def inf_is_inf is_inf_def is_max_iff lb_set_mem_iff)
    have B5:"f i = i"
      by (metis A0 B4 f_def is_extensive_def moore_to_closure_is_extensive order_class.order_eq_iff)
    have B6:"i \<in> C"
      using A0 B5 f_def moore_to_closure_is_idempotent3 by auto
    then show ?thesis
      by (simp add: i_def)
  qed
qed
  
lemma complete_semilattice_sup_inf_closed_then_moore:
  fixes C::"'a::complete_semilattice_sup set"
  assumes A0:"C \<noteq> {}" and A0:"\<And>E. (E \<in> Pow(C) \<and> (has_inf E)) \<Longrightarrow> (InfUn E) \<in> C"
  shows "is_moore_family C"
proof-
    have P:"\<forall>x. has_min (principal_filter_in x C)"
    proof
      fix x
      define Cx where "Cx= principal_filter_in x C"
      have B0:"x \<in> lb_set Cx"
        by (metis Cx_def lb_set_mem_iff singletonI ub_set_in_mem)
      have B1:"lb_set Cx \<noteq> {}"
        using B0 by auto
      have B3:"has_inf (Cx)"
        by (simp add: B1 complete_semilattice_sup_lb_imp_inf)
      define i where "i = InfUn Cx"
      have B4:"x \<le> i"
        by (simp add: B0 B1 CSup_upper complete_semilattice_sup_lb_imp_inf i_def)
      have B5:"i \<in> C"
        by (metis A0 B3 Cx_def Pow_iff i_def inf_le2 ub_set_in_ub_inter)
      have B6:"i \<in> Cx"
        by (metis B4 B5 Cx_def singletonD ub_set_in_elm)
      have B7:"i \<in> lb_set Cx"
        using B3 i_def inf_is_inf is_inf_def is_max_iff by blast
      have B8:"is_min i Cx"
        using B6 B7 is_min_def lb_set_in_lb_univ by fastforce
      show "has_min (principal_filter_in x C)"
        using B8 Cx_def has_min_def by blast
    qed
    show ?thesis
      by (simp add: P assms(1) is_moore_family_def)
qed

subsection ClosureRangeIsMooreFamily
lemma clrange_is_moore:
  fixes f::"'a::order \<Rightarrow> 'a::order"
  assumes A0:"is_closure f"
  shows "is_moore_family (range f)"
proof-
  let ?C="range f"
  have B0:"\<forall>x. (f x) \<in> ?C \<and> (x \<le> f x)"
    using assms is_closure_def is_extensive_def by auto
  have B1:"\<forall>x. (f x) \<in> principal_filter_in x ?C"
    by (metis B0 singletonD ub_set_in_elm)
  have B2:"\<forall>x. principal_filter_in x ?C \<noteq> {}"
    using B1 by blast
  have B3:"\<forall>x. (\<exists>m \<in> (principal_filter_in x ?C). (\<forall>y \<in> (principal_filter_in x ?C). m \<le> y))"
  proof
    fix x
    let ?Px="(principal_filter_in x ?C)"
    define m where B3A0:"m= (f x)"
    have B3B0:"m \<in> ?Px"
      by (simp add: B1 B3A0)
    have B3B1:"\<forall>y \<in> ?Px. m \<le> y"
      by (metis B3A0 assms in_cl_range_idempotent is_closure_def is_isotone_def singletonI ub_set_in_mem_iff)
    show "(\<exists>m \<in> (principal_filter_in x ?C). (\<forall>y \<in> (principal_filter_in x ?C). m \<le> y))"
      using B3B0 B3B1 by blast
    qed
  have B4:"\<forall>x. (has_min (principal_filter_in x ?C))"
    by (meson B3 has_min_iff)
  show ?thesis
    by (simp add: B4 is_moore_family_def)
qed

(*if f is a closure then f(a) is a lower bound of [a, \<rightarrow>)\<inter>(range f)  *)
lemma cl_range_inf1:
  fixes f::"'a::order \<Rightarrow> 'a::order" and
        a::"'a::order"
  assumes A0:"is_closure f" 
  shows "\<forall>y \<in> principal_filter_in a (range f). f(a) \<le> y"
proof
  fix y assume A3A0:"y \<in> principal_filter_in a (range f)"
  have A3B0:"a \<le> y \<and> (\<exists>x. y = (f x))"
    by (meson A3A0 imageE insertI1 ub_set_in_mem)
  have A3B1:"(f y) = y"
    using A3B0 assms in_cl_range_idempotent by blast
  have A3B2:"(f a) \<le> (f y)"
    using A3B0 assms is_closure_def is_isotone_def by blast
  have A3B3:"... = y"
    by (simp add: A3B1)
  show "f(a) \<le> y"
    using A3B2 A3B3 by auto
qed

(*if C is a moore family then f=f_C is such f(a) that a lower bound of [a, \<rightarrow>)\<inter>(range f)  *)
lemma cl_range_inf2:
  fixes C::"'a::order set" and
        a::"'a::order"
  assumes A0:"is_moore_family C" 
  defines "f \<equiv> moore_to_closure C" 
  shows "\<forall>y \<in> (principal_filter_in a (range f)). (f a) \<le> y"
proof
  fix y assume A0:"y \<in> principal_filter_in a (range f)"
  have B0:"is_closure f"
    by (simp add: assms moore_to_closure_iscl)
  have B0:"a \<le> y \<and> (\<exists>x. y = (f x))"
    by (metis A0 B0 in_cl_range_idempotent singletonI ub_set_in_mem)
  have B1:"(f y) = y"
    using B0 assms in_cl_range_idempotent moore_to_closure_iscl by blast
  have B2:"(f a) \<le> (f y)"
    using B0 assms(1) f_def is_isotone_def moore_to_closure_is_isotone by blast
  have B3:"... = y"
    by (simp add: B1)
  show "f(a) \<le> y"
    using B2 B3 by auto
qed


subsection DualIsomorphismBetweenMooreFamiliesAndClosures

(*
  Let X=(X, leq) be a poset and if F:Pow(X)\<rightarrow>F(X, X) be the map moore_to_closure and
  G:F(X, X)\<longrightarrow>Pow(X) be the range map, and let (\<C>, \<subseteq>) be the moore familes on X ordered by inclusion
  and  (\<F>, \<le>) be the closure operators ordered pointwise.  Then for any f \<in> \<F> or C \<in> \<C>
  F \<circ> G (f) = f
  G \<circ> F (C) = C
  for any f g \<in> \<F> 
  G(g) \<subseteq> G(f) \<longrightarrow> f \<le> g
  while for any C D \<in> \<C>
  f \<le> g \<longrightarrow> G(g) \<subseteq> G(f)
   
*)



lemma moore_cl_iso_inv1:
  fixes f::"'X::order \<Rightarrow> 'X::order"
  assumes A0:"is_closure f" 
  defines "g \<equiv> moore_to_closure (range f)"
  shows "g = f"
proof-
  have B0:"\<forall>x. (g x) =  (f x)"
  proof
    fix a
    have A0:"\<forall>x. (f x) \<in> principal_filter_in x (range f)"
      by (metis A0 is_closure_def is_extensive_def rangeI singletonD ub_set_in_elm)
    have A1:"a \<le> (f a)"
      using assms is_closure_def is_extensive_def by auto
    let ?Pfa = " principal_filter_in a (range f)" and ?fa="f a"
    have A2:"?fa\<in>?Pfa"
      by (simp add: A0)
    have A3:"\<forall>y. y \<in> ?Pfa \<longrightarrow> ?fa \<le> y"
      using assms cl_range_inf1 by blast
    have A30:"has_min (principal_filter_in a (range f))"
      by (simp add: assms(1) clrange_is_moore moore_family_imp)
    have A31:"?fa \<in> lb_set ?Pfa"
      by (simp add: A3 lb_set_elm)
    have A32:"is_min ?fa ?Pfa"
      by (simp add: A2 A3 is_min_iff)
    have A33:"min(?Pfa) = ?fa"
      using A32 min_if by force
    have A4:"f(a) = InfUn(principal_filter_in a (range f))"
      by (simp add: A30 A33 has_least_imp_inf_eq_least)
    have B1:"principal_filter_in a (range f) = (range f) \<inter> {y. a \<le> y}"
      by (simp add: Collect_conj_eq ub_set_in_singleton)
    have B2:"(g a) = InfUn(principal_filter_in a (range f))"
      by (simp add: g_def moore_to_closure_def)
    have B3:"... = InfUn{y \<in> range f. a \<le> y}"
      by (simp add: B1 Collect_conj_eq)
    have B4:"... = InfUn{y. \<exists>x. (y = f x) \<and> (a \<le> (f x))}"
      by (metis rangeE rangeI)
    have B5:"... = f a"
      using A4 B3 B4 by presburger
    show "(g a) = (f a)"
      using A4 B2 by presburger
  qed
  show ?thesis
    using B0 by auto
qed    


lemma moore_cl_iso_inv2:
  fixes C::"'X::complete_semilattice_inf set"
  assumes A0:"is_moore_family C" 
  defines "f \<equiv> moore_to_closure C"
  shows "C = range f"
proof-
  have B0:"\<And>y. (y \<in> (range f)) \<longrightarrow>  y \<in> C"
    proof
      fix y assume B0A0:"(y \<in> (range f))"
      obtain x where B0A1:"(f x) = y"
        using B0A0 by blast
      have B0B1:"y = InfUn(principal_filter_in x C)"
        using A0 B0A1 f_def moore_closure_imp by blast
      show "y \<in> C"
        using A0 B0A0 f_def in_cl_range_idempotent moore_to_closure_is_idempotent3 moore_to_closure_iscl by blast
    qed
  have B1:"\<And>y. (y \<in> C) \<longrightarrow> (y \<in> (range f))"
  proof
    fix y assume B1A0:"y \<in> C"
    have B1B0:"f y = y"
      by (simp add: A0 B1A0 f_def moore_to_closure_is_idempotent2)
    show "y \<in> range(f)"
      by (metis B1B0 rangeI) 
  qed
  show ?thesis
    using B0 B1 by blast
qed


lemma moore_cl_iso:
  fixes f1::"'a::order \<Rightarrow> 'a::order" and
        f2::"'a::order \<Rightarrow> 'a::order"
  assumes A0:"is_closure f1 \<and> is_closure f2" 
  shows "(range f2) \<subseteq> (range f1) \<longleftrightarrow> pointwise_less_eq f1 f2" (is "?L \<longleftrightarrow> ?R")
proof
  assume L:?L show ?R
  proof-
    let ?G1="range f1" and ?G2="range f2"
    have B0:"?G2 \<subseteq> ?G1"
      using L by force
    have B1:"\<forall>x.  (?G2 \<inter> (ub_set {x})) \<subseteq> (?G1 \<inter> (ub_set {x})) "
      using B0 by blast
    have B2:"\<forall>x. principal_filter_in x ?G2 \<subseteq>  principal_filter_in x ?G1"
      by (simp add: B0 ub_set_in_isotone2)
    have B3:"\<forall>x. InfUn( principal_filter_in x ?G1) \<le> InfUn( principal_filter_in x ?G2)"
      by (simp add: A0 B2 clrange_is_moore inf_antitone1 has_min_has_inf moore_family_imp)
    have B3:"\<forall>x. f1 x \<le> f2 x"
      by (metis A0 B3 moore_cl_iso_inv1 moore_to_closure_def)
    show ?thesis
      by (simp add: B3 pointwise_less_eq_def)
  qed
  next
  assume R:?R show ?L
  proof-
    let ?G1="range f1" and ?G2="range f2"
    have B0:"\<forall>x \<in> ?G2. f1 x =x"
    proof
      fix x assume B0A0:"x \<in> ?G2"
      have B0B0:"x \<le> (f1 x)"
        using A0 is_closure_def is_extensive_def by blast
      have B0B1:"... \<le> (f2 x)"
        by (meson R pointwise_less_def pointwise_less_eq_def)
      have B0B2:"... = x"
        using A0 B0A0 in_cl_range_idempotent by blast
      show "(f1 x) = x"
        using B0B0 B0B1 B0B2 by auto
    qed
    have B1:"\<forall>x \<in> ?G2. x \<in> ?G1"
      by (metis B0 range_eqI)
    show ?thesis
      using B1 by blast
  qed
qed


(*Converse is true as well that is
fix a complete semilattice inf
C is a moore family 
      \<longleftrightarrow>
C is cofinal
\<forall>x. ub_set_in {x} C \<noteq> {}
and a complete semilattice inf
 \<forall>A \<in> Pow(C)-{}. has_in_in A C \<and> InfIn A C = InfUn A

*)
lemma moore_family_is_complete_semilattice_inf:
  fixes A C::"'a::complete_semilattice_inf set"
  assumes A0:"is_moore_family C" and A1:"A \<noteq> {} \<and> A \<subseteq> C"
  shows "((has_inf_in A C) \<and> (InfIn A C = InfUn A))"
proof-
  define i where "i=Inf A"
  have B0:"is_inf i A"
    using A1 complete_semilattice_inf_is_inf i_def by blast
  have B1:"i \<in> C"
    by (metis A0 A1 B0 closure_range_inf_closed_ moore_cl_iso_inv2 moore_to_closure_iscl)
  have B2:"is_inf_in i A C"
    apply(simp add:is_inf_in_def lb_set_in_def is_max_def ub_set_in_def)
    using B0 B1 is_inf_imp2 is_inf_imp3 by blast
  have B3:"has_inf_in A C"
    using B2 has_inf_in_def has_max_def is_inf_in_def by blast
  have B4:"InfUn A = i"
    using B0 has_inf_def has_max_iff2 inf_is_inf is_inf_def is_inf_unique by blast
  have B5:"InfIn A C  = i"
    using B2 B3 inf_in_unique infin_is_inf by blast
  have B6: "InfIn A C = InfUn A"
    by (simp add: B4 B5)
  show ?thesis
    by (simp add: B3 B6)
qed

lemma cofinal_imp_nonempty_principal:
  assumes A0:"UNIV is_cofinal_in C"
  shows "\<forall>x. (principal_filter_in x C) \<noteq> {}"
  using assms is_cofinal_in_imp_ub_in_ne by blast

definition temp_condition::"'a::order set \<Rightarrow> bool" where
  "temp_condition C \<equiv> (\<forall>A. (A \<noteq> {} \<and> A \<subseteq> C) \<longrightarrow> (InfIn A C = InfUn A))"

lemma moore_family_is_complete_semilattice_inf_converse:
  fixes C::"'a::complete_semilattice_inf set"
  assumes A0:"C \<noteq> {}" and 
          A1:"UNIV is_cofinal_in C" and
          A2:"is_inf_complete C" and
          A3:"\<And>A. (A \<noteq> {} \<and> A \<subseteq> C) \<Longrightarrow>  (InfIn A C = InfUn A)"
  shows "is_moore_family C"
proof-
  have B0:"\<forall>a. has_min (principal_filter_in a C)"
  proof
    fix a::"'a::complete_semilattice_inf"
    define A where "A=(principal_filter_in a C)"
    have B1:"A \<noteq> {} \<and> A \<subseteq> C"
      by (simp add: A1 A_def cofinal_imp_nonempty_principal ub_set_in_subset)
    have B2:"has_inf_in A C"
      using A2 B1 is_inf_complete_def by auto
    have B2b:"(InfIn A C = InfUn A)"
      by (simp add: A3 B1)
    define i where "i=InfIn A C"
    have B3:"i \<in> C"
      using B2 i_def infin_is_inf is_inf_in_imp1 lb_set_in_mem_iff by blast
    have B4:"a \<in> lb_set A "
      by (simp add: A_def lb_set_mem_iff ub_set_in_imp)
    have B5:"a \<le> i"
      by (simp add: B1 B2b B4 complete_semilattice_inf_greatest complete_semilattice_infun_eq_inf i_def)
    have B6:"i \<in> A"
      by (simp add: B5 B3 A_def ub_set_in_def)
    have B7:"i \<in> lb_set A"
      by (simp add: B1 B2b complete_semilattice_infun_is_inf i_def is_inf_imp1)
    have B8:"is_min i A"
      by (simp add: B6 B7 is_min_if1)
    show "has_min (principal_filter_in a C)"
      using A_def B8 is_min_imp_has_min by blast
  qed
  show ?thesis
    by (simp add: A0 B0 is_moore_family_def)
qed

lemma moore_family_iff_cofinal_ac:
  fixes C::"'a::complete_semilattice_inf set"
  assumes A0:"C \<noteq> {}" 
  shows "is_moore_family C \<longleftrightarrow> (UNIV is_cofinal_in C) \<and> (temp_condition C) \<and> (is_inf_complete C)" (is "?L \<longleftrightarrow> ?R")
proof
  assume L:?L show ?R
    by (simp add: L is_cofinal_in_if_ub_in_ne is_inf_complete_def moore_family_is_cofinal moore_family_is_complete_semilattice_inf temp_condition_def)
  next
  assume R:?R show ?L
    by (meson R assms moore_family_is_complete_semilattice_inf_converse temp_condition_def)
qed

lemma filter_topped:
  fixes F::"'X::order_top set"
  assumes A0:"is_filter F"
   shows "top \<in> F"
proof-
  have B0:"is_inhabited F \<and> is_upclosed F"
    by (simp add: assms is_filter_imp is_upclosed_def)
  obtain x where B2:"x \<in> F"
    using B0 is_inhabited_def by fastforce
  have B3:"x \<le> top"
    by simp
  show ?thesis
    using B0 B2 B3 is_upclosed_imp by blast
qed

lemma set_filter_topped:
  assumes A0:"is_filter F" shows "UNIV \<in> F"
  by (simp add: assms filter_topped)


lemma filter_improper_iff:
  fixes F::"'X::order_bot set"
  assumes A0:"is_filter F"
  shows "bot \<in> F \<longleftrightarrow> F=UNIV"
proof
  assume L:"bot \<in> F"
  have LB0:"\<forall>x. x \<in> F"
    by (meson L assms bot.extremum is_filter_imp is_upclosed_imp up_closure_in_univ_imp)
  show "F=UNIV"
    using LB0 by blast
  next
  assume R:"F=UNIV"
  show "bot \<in> F"
    by (simp add: R)
qed
  

lemma set_filter_improper_iff:
  assumes A0:"is_filter (F::('X set set))" 
  shows "{} \<in> F \<longleftrightarrow> F=Pow(UNIV)"
  by (simp add: assms filter_improper_iff)

lemma filter_closure_obtains0:
  "\<And>x. x \<in> filter_closure A \<longleftrightarrow> (\<exists>S\<in>Fpow_ne A. InfUn S \<le> x)"
  by (simp add: filter_closure_def)

lemma fpow_ne_equiv:
  "S\<in>Fpow_ne A \<longleftrightarrow> (S \<in> Pow A \<and> finite S \<and> S \<noteq> {})"
  by (metis Pow_iff fpow_ne_if fpow_ne_imp)

lemma filter_closure_extensive:
  fixes A::"'a::semilattice_inf set"
  shows " A \<subseteq> filter_closure A"
proof-
  have B0:"\<forall>a. a \<in> A \<longrightarrow>   a \<in> lb_set {a}"
    by (simp add: lb_set_def)
  have B1:"\<forall>a \<in> A. {a} \<in> Fpow_ne A"
    by (meson fpow_ne_singleton)
  have B2:"\<forall>a \<in> A. a \<in> (filter_closure A)"
    by (metis B0 B1 DiffI Diff_insert_absorb filter_closure_obtains0 inf_singleton lb_set_mem mk_disjoint_insert)
  show ?thesis
    by (simp add: B2 subset_iff)
qed

lemma filter_closure_isotone:
  fixes A::"'a::semilattice_inf set" and  
        B::"'a::semilattice_inf set"
  assumes A0:"A \<subseteq> B"
  shows "(filter_closure A) \<subseteq> (filter_closure B)"
proof
  fix x assume A1:"x \<in> (filter_closure A)"
  obtain S1 where A2:"S1 \<in>Fpow_ne A \<and> InfUn S1 \<le> x"
    by (meson A1 filter_closure_obtains0)
  have B0:"S1 \<in> Pow  B"
    by (meson A2 PowI assms fpow_ne_imp order_trans)
  obtain S2 where A3:"S2 \<in> Fpow_ne B \<and> InfUn S2 \<le> x"
    by (metis A2 B0 PowD fpow_ne_if fpow_ne_imp)
  show "x \<in> (filter_closure B)"
    using A3 filter_closure_obtains0 by auto
qed

subsection FilterPiSystemInSemilatticeinf

lemma filter_in_semilattice_inf_iff:
 fixes X::"'X::semilattice_inf set"
  assumes "X \<noteq> {}"
  shows "is_filter X \<longleftrightarrow> (\<forall>x y. (x \<in> X \<and> y \<in> X) \<longleftrightarrow> (inf x y) \<in> X)"
proof-
  have LtR:"is_filter X \<longrightarrow> (\<forall>x y. (x \<in> X \<and> y \<in> X) \<longleftrightarrow> (inf x y) \<in> X)"
  proof
    assume LA0:"is_filter X"
    have LA1:"is_pisystem X"
      using LA0 downdir_up_pisystem is_filter_imp is_upclosed_def by blast
    have LA2:"is_upclosed X"
      by (simp add: LA0 is_filter_imp is_upclosed_def)
    show "(\<forall>x y. (x \<in> X \<and> y \<in> X) \<longleftrightarrow> (inf x y) \<in> X)"
    proof-
      have LB0:"(\<forall>x y. (x \<in> X \<and> y \<in> X) \<longrightarrow> (inf x y) \<in> X)"
        using LA1 is_pi_system_imp by blast
      have LB1:"(\<forall>x y.  (inf x y) \<in> X \<longrightarrow> (x \<in> X \<and> y \<in> X))"
        by (metis LA2 inf.cobounded1 inf.cobounded2 is_upclosed_imp)
      show ?thesis
        using LB0 LB1 by blast
    qed
  qed
  have RtL:"(\<forall>x y. (x \<in> X \<and> y \<in> X) \<longleftrightarrow> (inf x y) \<in> X) \<longrightarrow> is_filter X"
    proof
      assume RA0:"(\<forall>x y. (x \<in> X \<and> y \<in> X) \<longleftrightarrow> (inf x y) \<in> X)"
      have RB0:"is_pisystem X"
        using RA0 is_pi_system_imp by blast
      have RB1:"is_inhabited X"
        by (simp add: assms is_inhabited_def)
      have RB2:"is_upclosed X"
        by (metis RA0 inf.absorb_iff2 is_upclosed_def is_upclosed_in_def)
      show "is_filter X"
        by (simp add: RB0 RB1 RB2 downdir_up_pisystem is_filter_if up_closure_in_univ_imp)
    qed
  show ?thesis
    using LtR RtL by blast
qed




lemma filters_inf_closed:
  assumes "is_filter (F::'X::semilattice_inf set)"
  shows "\<And>E. finite E \<Longrightarrow> E \<noteq> {} \<Longrightarrow> E \<subseteq> F \<Longrightarrow> (fInf E \<in> F)"
  by (metis assms bot.extremum_uniqueI filter_in_semilattice_inf_iff finite_meet_in_set)

lemma filter_closure_idempotent:
  fixes A::"'X::semilattice_inf set"  
  shows "(filter_closure A) = (filter_closure (filter_closure A))"
proof-
  let ?A1="filter_closure A" let ?A2="filter_closure ?A1"
  have B0:"?A2 \<subseteq> ?A1"
  proof
    fix x assume A0:"x \<in>?A2"
    obtain Ex where A1:"(Ex \<in> Fpow_ne ?A1 \<and> (InfUn Ex) \<le> x)"
      by (meson A0 filter_closure_obtains0)
    have B1:"\<forall>y \<in> Ex. (\<exists>Ey\<in> Fpow_ne A. (InfUn Ey) \<le> y)"
      by (meson A1 filter_closure_obtains0 fpow_ne_imp in_mono)
    define g where "g=(\<lambda>y. SOME Ey. Ey \<in> Fpow_ne A \<and> (InfUn Ey) \<le> y)"
    have B2:"\<forall>y \<in>  Ex. ((g y) \<in> Fpow_ne A \<and> (InfUn (g y)) \<le> y)"
      by (metis (mono_tags, lifting) B1 g_def someI)
    have B20:"finite (g`Ex) \<and> (\<forall>Ey \<in> (g`Ex). Ey \<in> Fpow_ne A)"
      by (metis A1 B2 finite_imageI fpow_ne_imp imageE)
    define E where "E=(\<Union>(g`Ex))"
    have B3:"E \<in> Fpow_ne A"
      by (metis A1 B20 DiffD2 Diff_eq_empty_iff E_def Fpow_subset_Pow PowI Pow_empty finite_has_maximal fpow_ne_union image_is_empty subset_empty)
    have B4:"\<forall>y \<in> Ex. (InfUn E) \<le> (InfUn (g y))"
      by (metis B2 B3 E_def UN_upper fpow_ne_imp inf_antitone1 semilattice_inf_has_inf)
    have B5:"\<forall>y \<in> Ex. (InfUn E) \<le> y"
      using B2 B4 order.trans by blast
    have B6:"(InfUn E) \<le> (InfUn Ex)"
      by (metis A1 B5 fpow_ne_imp inf_is_inf is_inf_imp3 semilattice_inf_has_inf)
    have B7:"(InfUn E) \<le> x"
      using A1 B6 order.trans by blast
    show "x \<in> filter_closure A"
      using B3 B7 filter_closure_obtains0 by blast
  qed
  show ?thesis
    by (simp add: B0 filter_closure_extensive set_eq_subset)
qed



lemma filter_closure_is_closure:
  shows "is_closure (filter_closure::('a::semilattice_inf set \<Rightarrow> 'a::semilattice_inf set))"
proof-
  have A0:"is_extensive (filter_closure::('a::semilattice_inf set \<Rightarrow> 'a::semilattice_inf set))"
    by (metis filter_closure_obtains0 fpow_ne_singleton inf_singleton is_extensive_def order.refl subsetI)
  have A1:"is_isotone (filter_closure::('a::semilattice_inf set \<Rightarrow> 'a::semilattice_inf set))"
    by (simp add: filter_closure_isotone is_isotone_def)
  have A3:"is_idempotent (filter_closure::('a::semilattice_inf set \<Rightarrow> 'a::semilattice_inf set))"
    using filter_closure_idempotent is_idempotent_def by blast
  show ?thesis
    by (simp add: A0 A1 A3 is_closure_def)
qed


lemma filters_in_filter_cl_range:
  fixes F::"'X::semilattice_inf set"
  assumes A0:"is_filter F"
  shows "filter_closure F = F"
proof-
  have B0:"filter_closure F \<subseteq> F"
  proof-
    have B00:"filter_closure F = {a. \<exists>S\<in>Fpow_ne(F). InfUn S \<le>  a}"
      by (simp add: filter_closure_def)
    have B01:"\<And>a. (\<exists>S\<in>Fpow_ne(F). InfUn S \<le> a) \<longrightarrow> a \<in> F"
    proof
      fix a assume B01A0:"\<exists>S\<in>Fpow_ne(F). InfUn S \<le> a "
      obtain S where B01A1:"S \<in>Fpow_ne(F) \<and>  InfUn S \<le> a"
        using B01A0 by force
      have B01A1:"(InfUn S) \<in> F"
        by (metis B01A1 assms filters_inf_closed fpow_ne_imp semilattice_inf_finf_eq)
      show "a \<in> F"
        by (metis B01A0 UNIV_I assms filters_inf_closed fpow_ne_imp is_filter_imp is_upclosed_in_def semilattice_inf_finf_eq)
    qed
    show ?thesis
      by (meson B01 filter_closure_obtains0 subsetI)
  qed
  have B1:"F \<subseteq> filter_closure F"
    by (simp add: filter_closure_extensive)
  show ?thesis
    by (simp add: B0 B1 subset_antisym)
qed


lemma filter_closure_is_filter:
  fixes E::"'X::semilattice_inf set"
  assumes A0:"E \<noteq> {}"
  shows "is_filter (filter_closure E)"
proof-
  let ?F="(filter_closure E)"
  have B0:"is_downdir ?F"
  proof-
    have B01:"(\<And>a b.  (a \<in> ?F \<and> b \<in> ?F) \<longrightarrow> (\<exists>c  \<in> ?F. (c \<le> a) \<and>  (c \<le> b)))"
    proof
       fix a b assume B0A0:"a \<in> ?F \<and> b \<in> ?F"
      obtain Sa where B0A1:"Sa \<in> Fpow_ne E \<and> (InfUn Sa) \<le> a"
        using B0A0 filter_closure_obtains0 by blast
      obtain Sb where B0A2:"Sb \<in> Fpow_ne(E) \<and> (fInf Sb) \<le> b"
        by (metis B0A0 filter_closure_obtains0 fpow_ne_equiv semilattice_inf_finf_eq)
      define Sc where B0A3:"Sc=Sa \<union> Sb"
      have B0B2:"Sc \<in> Fpow_ne (E)"
        by (metis B0A1 B0A2 B0A3 finite_Un fpow_ne_if fpow_ne_imp le_sup_iff sup_eq_bot_iff)
      have B0B3:"(fInf Sc) \<le> (fInf Sa) \<and> (fInf Sc) \<le>(fInf Sb)"
        by (metis B0A1 B0A2 B0A3 B0B2 fpow_ne_imp inf_sup_ord(4) semilattice_inf_class.subset_imp sup_ge1)
      have B0B4:"(fInf Sc) \<le> a \<and> (fInf Sc) \<le> b"
        by (metis B0A1 B0A2 B0B3 dual_order.trans fpow_ne_imp semilattice_inf_finf_eq)
      show "\<exists>c  \<in> ?F. (c \<le> a) \<and>  (c \<le> b)"
        by (metis B0B2 B0B4 dual_order.refl filter_closure_obtains0 fpow_ne_equiv semilattice_inf_finf_eq)
      qed
    show ?thesis
      by (simp add: B01 is_downdir_def)
  qed
  have B1:"is_upclosed ?F"
  proof-
    have B10:"\<And>a b. (a \<le> b \<and>  a \<in> ?F) \<longrightarrow>  b \<in> ?F"
    proof 
      fix a b assume B1A0:"(a \<le> b \<and>  a \<in> ?F)" 
      obtain Sa where B1A1:"Sa \<in> Fpow_ne E \<and>  (InfUn Sa) \<le> a"
        by (meson B1A0 filter_closure_obtains0)
      have B1B1:"(InfUn Sa) \<le> b"
        using B1A0 B1A1 dual_order.trans by blast
      show "b \<in> ?F"
        using B1A1 B1B1 filter_closure_obtains0 by blast
    qed
    show ?thesis
      by (meson B10 is_upclosed_def is_upclosed_in_def)
  qed
  have B2:"is_inhabited ?F"
    using assms filter_closure_extensive is_inhabited_def by blast
  show ?thesis
    by (simp add: B0 B1 B2 is_filter_if up_closure_in_univ_imp)
qed

lemma filter_closure_is_smallest:
  fixes E::"'X::semilattice_inf set"
  assumes A0:"E \<noteq> {}"
  shows "\<And>F. (is_filter F \<and> E \<subseteq> F) \<longrightarrow> (filter_closure E) \<subseteq> F"
proof
  fix F assume A1:"(is_filter F \<and> E \<subseteq> F)"
  show "(filter_closure E) \<subseteq> F"
  proof
    fix x assume A2:"x \<in> filter_closure E"
    show "x \<in> F"
      using A1 A2 filter_closure_isotone filters_in_filter_cl_range by blast
    qed
qed

lemma filter_sup_is_ub:
  fixes EF::"'X::semilattice_inf set set"
  assumes A0: "EF \<noteq> {}" and A1:"\<forall>F \<in> EF. is_filter F"
  shows "\<forall>F \<in> EF. F \<subseteq>  (filter_sup EF)"
  by (metis Sup_le_iff filter_closure_extensive filter_sup_def)
  
lemma filter_sup_is_lub_in_filters:
  fixes EF::"'X::semilattice_inf set set"
  assumes A0: "EF \<noteq> {}" and A1:"\<forall>F \<in> EF. is_filter F"
  shows "\<And>G. is_filter G \<Longrightarrow> (\<forall>F \<in> EF. F \<subseteq> G) \<Longrightarrow> (filter_sup EF) \<subseteq> G"
  by (metis Sup_le_iff filter_closure_isotone filter_sup_def filters_in_filter_cl_range)

lemma filter_sup_is_sup_in_filters:
  fixes EF::"'a::semilattice_inf set set"
  assumes A0: "EF \<noteq> {}" and A1:"\<forall>F \<in> EF. is_filter F"
  shows "is_sup_in (filter_sup EF) EF (filters_in UNIV)"
proof-
  let ?S=" (filter_sup EF)"
  let ?X="(filters_in UNIV)"
  have B0:"?S \<in> ub_set_in EF ?X"
  proof-
    have B01:"\<And>F. F \<in> EF \<Longrightarrow> F \<le> ?S"
      by (simp add: A0 A1 filter_sup_is_ub)
    have B02:"?S \<in> ?X"
      by (metis (no_types, lifting) A0 A1 CollectI Pow_UNIV Sup_le_iff UNIV_I bot.extremum_unique ex_in_conv filter_closure_is_filter filter_sup_def filters_in_def filters_in_filter_cl_range)
    show ?thesis
      by (simp add: B01 B02 ub_set_in_mem_iff)
  qed
  have B1:"\<And>G. is_filter G \<Longrightarrow> (\<forall>F \<in> EF. F \<subseteq> G) \<Longrightarrow> (G \<in> ub_set_in EF ?X)"
    by (simp add: filters_in_def ub_set_in_elm)
  have B2:"\<And>G. (G \<in> ub_set_in EF ?X) \<Longrightarrow> ?S \<le> G"
    by (simp add: A0 A1 filter_sup_is_lub_in_filters filters_in_def ub_set_in_mem_iff)
  have B3:"is_min ?S (ub_set_in EF ?X)"
    by (simp add: B0 B2 is_min_if2)
  show ?thesis
    by (simp add: B3 is_sup_in_iff)
qed

lemma filter_inf_is_filter:
  fixes EF::"'X::bounded_semilattice_inf_top set set"
  assumes A0: "EF \<noteq> {}" and A1:"\<forall>F \<in> EF. is_filter F"
  shows "is_filter (filter_inf EF)"
proof-
  let ?I="filter_inf EF"
  have P0:"is_inhabited ?I"
    by (metis A0 A1 InterI empty_iff filter_inf_def filter_topped is_inhabited_def)
  have P1:"is_upclosed ?I"
  proof-
    have B01:"\<And>a b. b \<in> ?I \<and> b \<le> a \<longrightarrow> a \<in> ?I"
    proof
      fix a b assume A01:"b \<in> ?I \<and>  b \<le> a"
      have B02:"\<forall>F \<in> EF. b \<in> F"
        by (metis A0 A01 Inter_iff filter_inf_def)
      have B03:"\<forall>F \<in> EF. a \<in> F"
        by (metis A01 A1 B02 equals0D filter_in_semilattice_inf_iff inf.absorb_iff2)
      show "a \<in> ?I"
        by (simp add: A0 B03 filter_inf_def)
    qed
    show ?thesis
      using B01 is_upclosed_def is_upclosed_in_def by blast
  qed
  have P2:"is_downdir ?I"
    proof-
    have B20:"(\<And>a b.  (a \<in> ?I \<and> b \<in> ?I) \<longrightarrow> (\<exists>c  \<in> ?I. (c \<le> a) \<and>  (c \<le> b)))"
    proof
       fix a b assume B2A0:"a \<in> ?I \<and> b \<in> ?I" 
       have B21:"\<forall>F \<in> EF. a \<in> F \<and> b \<in> F"
         by (metis A0 B2A0 InterE filter_inf_def)
       have B22:"\<forall>F \<in> EF. inf a b \<in> F"
         by (simp add: A1 B21 downdir_inf is_filter_imp is_upclosed_def)
       have B23:"inf a b \<in> ?I"
         by (simp add: A0 B22 filter_inf_def)
        show "(\<exists>c  \<in> ?I. (c \<le> a) \<and>  (c \<le> b))"
          by (meson B23 inf.cobounded1 inf.cobounded2)
  qed
  show ?thesis
    by (simp add: B20 is_downdir_def)
  qed
  show ?thesis
    by (simp add: P0 P1 P2 is_filter_if up_closure_in_univ_imp)
qed


lemma filter_inf_is_inf_in_filters:
  fixes EF::"'a::bounded_semilattice_inf_top set set"
  assumes A0: "EF \<noteq> {}" and A1:"\<forall>F \<in> EF. is_filter F"
  shows "is_inf_in (filter_inf EF) EF (filters_in UNIV)"
proof-
  let ?I="(filter_inf EF)"
  let ?X="(filters_in UNIV)"
  have B0:"?I \<in> lb_set_in EF ?X"
    by (metis (no_types, lifting) A0 A1 Pow_UNIV UNIV_witness dual_order.refl filter_inf_def 
        filter_inf_is_filter filters_in_def lb_set_in_elm 
        le_Inf_iff mem_Collect_eq top_apply top_set_def)
  have B1:"\<And>G. is_filter G \<Longrightarrow> (\<forall>F \<in> EF. G \<le> F) \<Longrightarrow> (G \<in> lb_set_in EF ?X)"
    by (simp add: filters_in_def lb_set_in_elm)
  have B2:"\<And>G. (G \<in> lb_set_in EF ?X) \<Longrightarrow> G \<le> ?I"
    by (simp add: A0 filter_inf_def lb_set_in_mem_iff le_Inf_iff)
  have B3:"is_max ?I (lb_set_in EF ?X)"
    by (simp add: B0 B2 is_max_iff)
  show ?thesis
    by (simp add: B3 is_inf_in_iff)
qed

lemma smallest_filter1:
  "is_filter {top::('X::bounded_semilattice_inf_top)}"
proof-
    let ?S="{top::('X::bounded_semilattice_inf_top)}"
    have B0:"is_upclosed ?S"
      by (simp add: inf.absorb_iff2 is_upclosed_def is_upclosed_in_def)
    have B1:"is_downdir ?S"
      using is_downdir_def by blast
    have B2:"is_inhabited ?S"
      by (simp add: is_inhabited_def)
    show ?thesis
      by (simp add: B0 B1 B2 is_filter_if up_closure_in_univ_imp)
qed


lemma smallest_filter2:
  "\<forall>(F::('X::bounded_semilattice_inf_top set)). is_filter F \<longrightarrow>  {top::('X::bounded_semilattice_inf_top)} \<subseteq> F"
  by (simp add: filter_topped)



lemma filter_moore_family:
  "is_moore_family {F::('X::bounded_semilattice_inf_top set). is_filter F}"
proof-
  let ?EF="{F::('X::bounded_semilattice_inf_top set). is_filter F}"
  have B0:"is_filter (top::('X::bounded_semilattice_inf_top set))"
    by (simp add: filter_in_semilattice_inf_iff)
  have B1:"(top::('X::bounded_semilattice_inf_top set)) \<in> ?EF"
    by (simp add: B0)
  have B2:"\<And>(G::'X::bounded_semilattice_inf_top set). G \<noteq> {} \<longrightarrow> (\<exists>F \<in> (principal_filter_in G ?EF).
        (\<forall>H \<in> (principal_filter_in G ?EF). F \<le> H))"
  proof
    fix G::"'X::bounded_semilattice_inf_top set" assume B2A0:"G \<noteq> {}"
    have B20:"G \<subseteq> filter_closure G"
      by (simp add: filter_closure_extensive)
    have B21:"is_filter (filter_closure G)"
      by (simp add: B2A0 filter_closure_is_filter)
    have B22:" (filter_closure G) \<in> principal_filter_in G ?EF"
      by (simp add: B20 B21 ub_set_in_mem_iff)
    have B23:"(\<forall>H \<in> (principal_filter_in G ?EF). is_filter H \<and> G \<subseteq> H)"
      by (simp add: ub_set_in_mem_iff)
    have B24:"\<forall>H \<in> (principal_filter_in G ?EF). (filter_closure G) \<subseteq> H"
      by (meson B23 B2A0 filter_closure_is_smallest)
    obtain F where B25:"F \<in> (principal_filter_in G ?EF) \<and>  (\<forall>H \<in> (principal_filter_in G ?EF). F \<le> H)"
      using B22 B24 by blast
    show "(\<exists>F \<in> (principal_filter_in G ?EF). (\<forall>H \<in> (principal_filter_in G ?EF). F \<le> H))"
      using B25 by blast
  qed
  have B3:"?EF \<noteq> {}"
    using B1 by auto
  have B4:"(\<forall>(a::(('X::bounded_semilattice_inf_top set))). (\<exists>m \<in> (principal_filter_in a ?EF). (\<forall>x \<in> (principal_filter_in a ?EF). m \<le> x)))"
  proof
     fix a
     show "(\<exists>m \<in> (principal_filter_in a ?EF). (\<forall>x \<in> (principal_filter_in a ?EF). m \<le> x))"
     proof(cases "a = {}")
       case True
        have "is_filter {top::('X::bounded_semilattice_inf_top)}"
          by (simp add: smallest_filter1)
        have " (\<forall>x \<in> (principal_filter_in a ?EF). {top::('X::bounded_semilattice_inf_top)} \<le> x)"
          by (metis mem_Collect_eq smallest_filter2 ub_set_in_mem_iff)
       then show ?thesis
         by (metis Int_Collect True mem_Collect_eq singleton_insert_inj_eq smallest_filter1 ub_set_in_ub_inter ub_set_singleton)
     next
       case False
       then show ?thesis
         by (simp add: B2)
     qed
  qed
  have B5:"(\<forall>(a::(('X::bounded_semilattice_inf_top set))). has_min (principal_filter_in a ?EF))"
    by (meson B4 has_min_iff)
  show ?thesis
    using B3 B5 is_moore_family_def by auto
qed



subsection FilterOnLattice

lemma filter_inlattice_inf_closed:
  assumes "is_filter (F::'X::lattice set)"
  shows "\<And>x1 x2. (x1 \<in> F \<and> x2 \<in> F) \<Longrightarrow> (inf x1 x2 \<in> F)"
  by (metis assms empty_iff filter_in_semilattice_inf_iff)

lemma filter_on_lattice_binf_is_lb:
  assumes A0:"is_filter (F1::('X::lattice set))" and 
          A2:"is_filter (F2::('X::lattice set))"
  shows "inf F1 F2 \<le> F1 \<and> inf F1 F2 \<le> F2"
  by simp

lemma filter_on_lattice_inhabited:
  assumes A0:"is_filter (F1::('a::lattice set))" and 
          A1:"is_filter (F2::('a::lattice set))"
  shows "is_inhabited (inf F1 F2)"
proof-
  have B00:"is_inhabited F1 \<and> is_inhabited F2"
    by (simp add: A0 A1 is_filter_imp)
  obtain x1 x2 where A01:"x1 \<in> F1 \<and> x2 \<in> F2"
    using B00 is_inhabited_imp by blast
  define x where A02:"x=sup x1 x2"
  have B01:"x1 \<le> x \<and> x2 \<le> x"
    by (simp add: A02)
  have B02:"x \<in> inf F1 F2"
    by (meson A0 A01 A1 B01 IntI UNIV_I is_filter_imp is_upclosed_in_imp)
  show ?thesis
    using B02 is_inhabited_def by auto
qed

lemma filter_on_lattice_is_downdir:
  assumes A0:"is_filter (F1::('a::lattice set))" and 
          A1:"is_filter (F2::('a::lattice set))"
  shows "is_downdir (inf F1 F2)"
proof-
  have P10:"\<And>a b. (a \<in> (inf F1 F2) \<and> b \<in> (inf F1 F2)) \<longrightarrow> (\<exists>c  \<in> (inf F1 F2). (c \<le> a) \<and>  (c \<le> b))"
  proof
    fix a b assume P1A0:"a \<in> (inf F1 F2) \<and> b \<in>  (inf F1 F2)"
    show "\<exists>c \<in>  (inf F1 F2). c \<le> a \<and> c \<le> b"
      by (metis A0 A1 Int_iff P1A0 emptyE filter_in_semilattice_inf_iff inf_le1 inf_le2)
  qed
  show ?thesis
    by (simp add: P10 is_downdir_def)
qed

lemma filter_on_lattice_is_upclosed:
  assumes A0:"is_filter (F1::('a::lattice set))" and 
          A1:"is_filter (F2::('a::lattice set))"
  shows "is_upclosed (inf F1 F2)"
proof-
  have B0:"\<And>a b. a \<le> b \<and> a \<in> F1 \<and> a \<in> F2 \<longrightarrow> b \<in> F1 \<and> b \<in> F2"
  proof
    fix a b assume A2:"a \<le> b \<and> a \<in> F1 \<and> a \<in> F2"
    show "b \<in> F1 \<and> b \<in> F2"
      by (meson A0 A1 A2 UNIV_I is_filter_imp is_upclosed_in_imp)
  qed
  show ?thesis
    by (metis A0 A1 B0 Int_iff filter_on_lattice_inhabited is_inhabited_def sup_ge1 upclosed_in_lattice_iff)
qed
  

lemma filter_on_lattice_inf:
  assumes A0:"is_filter (F1::('a::lattice set))" and 
          A2:"is_filter (F2::('a::lattice set))"
  shows "is_filter (inf F1 F2)"
proof-
  let ?I="inf F1 F2"
  have P0:"is_inhabited ?I"
    by (simp add: A0 A2 filter_on_lattice_inhabited)
  have P1:"is_downdir ?I"
    by (simp add: A0 A2 filter_on_lattice_is_downdir)
  have P3:"is_upclosed ?I"
    by (simp add: A0 A2 filter_on_lattice_is_upclosed)
  show ?thesis
    by (simp add: P0 P1 P3 is_filter_if up_closure_in_univ_imp)
qed
    


lemma filter_on_lattice_glb:
  assumes A0:"is_filter (F1::('X::lattice set))" and 
          A1:"is_filter (F2::('X::lattice set))" and
          A2:"is_filter (F3::('X::lattice set))" and
          A3:"F3 \<le> F1 \<and> F3 \<le> F2"
  shows "F3 \<le> inf F1 F2"
  by (simp add: A3)

lemma filter_on_lattice_binf_is_binf:
  assumes A0:"is_filter (F1::('X::lattice set))" and 
          A1:"is_filter (F2::('X::lattice set))"
  shows "is_inf_in (inf F1 F2) {F1, F2} (filters_in UNIV)"
proof-
  let ?I="inf F1 F2"
  let ?X="filters_in UNIV"
  have B0:"?I \<le> F1 \<and> ?I \<le> F2"
    by simp
  have B1:"is_filter ?I"
    by (simp add: A0 A1 filter_on_lattice_inf)
  have B2:"?I \<in> lb_set_in {F1, F2} ?X"
    by (simp add: B1 filters_in_def lb_set_in_mem_iff)
  have B3:"\<forall>F. F \<in>  lb_set_in {F1, F2} ?X \<longrightarrow> F \<le> ?I"
    by (simp add: lb_set_in_mem_iff)
  have B4:"is_max ?I (lb_set_in {F1, F2} ?X)"
    using B2 B3 is_max_if2 by blast
  show ?thesis
    by (simp add: B4 is_inf_in_def)
qed
    


lemma filter_on_lattice_bsup:
  assumes A0:"is_filter (F1::('X::lattice set))" and 
          A2:"is_filter (F2::('X::lattice set))"
  shows "is_filter (binary_filter_sup F1 F2)"
proof-
  let ?S="binary_filter_sup F1 F2"
  have P0:"is_inhabited ?S"
  proof-
    have P00:"is_inhabited F1 \<and> is_inhabited F2"
      using A0 A2 is_filter_imp by blast
    have P01:"F1 \<noteq> {} \<and> F2 \<noteq> {}"
      using P00 is_inhabited_def by auto
    obtain x1 x2 where P0A1:"x1 \<in> F1 \<and> x2 \<in> F2"
      by (meson P00 is_inhabited_imp)
    have P02:"x1 \<le> sup x1 x2 \<and> x2 \<le> sup x1 x2"
      by simp
    show ?thesis
      using P0A1 binary_filter_sup_def is_inhabited_def by fastforce
   qed
  have P1:"is_downdir ?S"
  proof-
     have P10:"\<And>a b. (a \<in> ?S \<and> b \<in> ?S) \<longrightarrow> (\<exists>c  \<in> ?S. (c \<le> a) \<and>  (c \<le> b))"
      proof
        fix a b assume P1A0:"a \<in>?S \<and> b \<in> ?S"
        obtain a1 a2 where P1A1:"a1 \<in> F1 \<and> a2 \<in> F2 \<and> inf a1 a2 \<le> a"
          by (smt (verit, ccfv_threshold) P1A0 binary_filter_sup_def inf.coboundedI2 mem_Collect_eq)
        obtain b1 b2 where P1A2:"b1 \<in> F1 \<and> b2 \<in> F2 \<and> inf b1 b2 \<le> b"
          by (smt (verit, ccfv_threshold) P1A0 binary_filter_sup_def inf.coboundedI2 mem_Collect_eq)
        have P1B0:"inf (inf a1 b1) (inf a2 b2) \<le> a \<and> inf (inf a1 b1) (inf a2 b2) \<le> b"
          by (meson P1A1 P1A2 dual_order.trans inf_le1 inf_le2 inf_mono)
        obtain ab1 where P1A3:"ab1 \<in> F1 \<and> ab1 \<le> a1 \<and> ab1 \<le> b1"
          by (meson A0 P1A1 P1A2 filter_inlattice_inf_closed inf_le1 inf_le2)
        obtain ab2 where P1A4:"ab2 \<in> F2 \<and> ab2 \<le> a2 \<and> ab2 \<le> b2"
          by (meson A2 P1A1 P1A2 filter_inlattice_inf_closed inf_le1 inf_le2)
        have P1B1:"ab1 \<le> (inf a1 b1) \<and> ab2 \<le> (inf a2 b2)"
          by (simp add: P1A3 P1A4)
        have P1B2:"inf a1 b1 \<in> F1 \<and> inf a2 b2 \<in> F2"
          by (simp add: A0 A2 P1A1 P1A2 filter_inlattice_inf_closed)
        have P1B3:"(inf (inf a1 b1) (inf a2 b2)) \<in> ?S"
          using P1B2 binary_filter_sup_def by blast
        show "\<exists>c \<in> ?S. c \<le> a \<and> c \<le> b"
          using P1B0 P1B3 by auto
      qed
      show ?thesis
        by (simp add: P10 is_downdir_def)
    qed
  have P2:"is_upclosed ?S"
  proof-
    have P20:"\<And>a b. (a \<le> b \<and>  a \<in> ?S) \<longrightarrow>  b \<in> ?S"
    proof
      fix a b assume P20A0:"a \<le> b \<and> a \<in> ?S"
      obtain a1 a2 where P20A1:"a1 \<in> F1 \<and> a2 \<in> F2 \<and> inf a1 a2 \<le> a"
        by (smt (verit) P20A0 binary_filter_sup_def mem_Collect_eq)
      have P20B1:"inf a1 a2 \<le> b"
        using P20A0 P20A1 by auto
      show "b \<in> ?S"
        using P20A1 P20B1 binary_filter_sup_def by blast
    qed
    show ?thesis
      by (meson P20 is_upclosed_def is_upclosed_in_def)
  qed
  show ?thesis
    by (simp add: P0 P1 P2 is_filter_if up_closure_in_univ_imp)
qed

lemma filter_on_lattice_bsup_greatest:
  assumes A0:"is_filter (F1::('X::lattice set))" and 
          A1:"is_filter (F2::('X::lattice set))"
  shows "F1 \<subseteq> (binary_filter_sup F1 F2) \<and> F2 \<subseteq> (binary_filter_sup F1 F2)"
proof-
  let ?S="binary_filter_sup F1 F2"
  have B0:"\<And>x. x \<in> F1 \<Longrightarrow> x \<in> ?S"
  proof-
    fix x assume A2:"x \<in> F1"
    obtain b where A3:"b \<in> F2"
      using A1 is_filter_imp is_inhabited_imp by blast
    have B1:"inf x b \<le> x"
      by simp
    show "x \<in> ?S"
      using A2 A3 B1 binary_filter_sup_def by blast
  qed
  have B2:"\<And>x. x \<in> F2 \<Longrightarrow> x \<in> ?S"
    proof-
    fix x assume A4:"x \<in> F2"
    obtain b where A5:"b \<in> F1"
      using A0 is_filter_imp is_inhabited_imp by blast
    have B3:"inf b x \<le> x"
      by simp
    show "x \<in> ?S"
      using A4 A5 B3 binary_filter_sup_def by blast
  qed
  show ?thesis
    by (simp add: B0 B2 subsetI)
qed


lemma filter_on_lattice_bsup_least:
  assumes A0:"is_filter (F1::('X::lattice set))" and 
          A1:"is_filter (F2::('X::lattice set))"
  shows "\<And>F3. is_filter F3 \<and> F1 \<subseteq> F3 \<and> F2 \<subseteq> F3 \<longrightarrow> (binary_filter_sup F1 F2) \<subseteq> F3"
proof
  fix F3 assume A2:"is_filter F3 \<and> F1 \<subseteq> F3 \<and> F2 \<subseteq> F3"
  let ?S="(binary_filter_sup F1 F2)"
  show "?S \<subseteq> F3"
  proof
    fix x assume A3:"x \<in> ?S"
    obtain x1 x2 where A4:"x1 \<in> F1 \<and> x2 \<in> F2 \<and> inf x1 x2 \<le> x"
      by (smt (verit, best) A3 binary_filter_sup_def mem_Collect_eq)
    have B0:"x1 \<in> F3 \<and> x2 \<in> F3"
      using A2 A4 by blast
    have B1:"inf x1 x2 \<in> F3"
      by (simp add: A2 B0 filter_inlattice_inf_closed)
    show "x \<in> F3"
      by (meson A2 A4 B1 UNIV_I is_filter_imp is_upclosed_in_imp)
  qed
qed

lemma filter_on_lattice_sup:
  fixes EF::"'a::lattice set set"
  assumes A0:"EF \<noteq> {}" and A1:"\<forall>F \<in> EF. is_filter F"
  shows "is_filter (filter_sup(EF))"
proof-
  let ?S="filter_sup(EF)"
  have P0:"is_inhabited ?S"
    by (metis A0 A1 Union_upper all_not_in_conv filter_closure_extensive filter_sup_def is_filter_imp is_inhabited_def subset_empty)
  have P1:"is_downdir ?S"
    by (metis P0 filter_closure_idempotent filter_closure_is_filter filter_sup_def is_filter_imp is_inhabited_def)
  have P2:"is_upclosed ?S"
    by (metis P0 filter_closure_idempotent filter_closure_is_filter filter_sup_def is_filter_imp is_inhabited_def is_upclosed_def)
  show ?thesis
    by (simp add: P0 P1 P2 is_filter_if up_closure_in_univ_imp)
qed

lemma filter_on_lattice_sup_greater:
  fixes EF::"'a::lattice set set"
  assumes A0:"EF \<noteq> {}" and A1:"\<forall>F \<in> EF. is_filter F"
  shows "\<forall>F \<in> EF. F \<le> filter_sup(EF)"
  by (simp add: A0 A1 filter_sup_is_ub)


lemma filter_on_lattice_sup_least_upper:
  fixes EF::"'a::lattice set set"
  assumes A0:"EF \<noteq> {}" and A1:"\<forall>F \<in> EF. is_filter F"
  shows "\<And>G. (is_filter G \<and>  (\<forall>F \<in> EF. F \<le> G))\<longrightarrow>  filter_sup(EF) \<le> G"
  by (simp add: A0 A1 filter_sup_is_lub_in_filters)

lemma filter_on_lattice_sup_is_sup:
  fixes EF::"'a::lattice set set"
  assumes A0:"EF \<noteq> {}" and A1:"\<forall>F \<in> EF. is_filter F"
  shows "is_sup_in (filter_sup EF) EF  (filters_in UNIV)"
  using A0 A1 filter_sup_is_sup_in_filters by blast


lemma filter_on_lattice_finf_is_filter:
  fixes EF::"'a::lattice set set"
  assumes A0:"EF \<noteq> {}" and A1:"\<forall>F \<in> EF. is_filter F" and A2:"finite EF"
  shows "is_filter (fInf (EF))"
  by (metis A0 A1 A2 filter_on_lattice_inf finite_meet_in_set mem_Collect_eq subsetI)

lemma filter_on_lattice_finf_is_lb:
  fixes EF::"'a::lattice set set"
  assumes A0:"EF \<noteq> {}" and A1:"\<forall>F \<in> EF. is_filter F" and A2:"finite EF"
  shows "(fInf (EF)) \<in> (lb_set_in EF (filters_in UNIV))"
  by (metis (no_types, lifting) A0 A1 A2 CollectI Pow_iff complete_lattice_class.finf_complete_lattice
       csli.CInf_lower filter_on_lattice_finf_is_filter filters_in_def lb_set_in_mem_iff top_greatest)


lemma filter_on_lattice_finf_is_glb:
  fixes EF::"'a::lattice set set"
  assumes A0:"EF \<noteq> {}" and A1:"\<forall>F \<in> EF. is_filter F" and A2:"finite EF"
  shows "is_max (fInf EF) (lb_set_in EF (filters_in UNIV))"
proof-
  let ?I="(fInf EF)"  let ?X="filters_in UNIV" let ?L="(lb_set_in EF ?X)"
  have B0:"?I \<in> ?X"
    by (simp add: A0 A1 A2 filter_on_lattice_finf_is_filter filters_in_def)
  have B1:"\<forall>F. F \<in> ?L \<longrightarrow> F \<le> ?I"
    by (simp add: A0 A2 finite_inf_greatest lb_set_in_imp)
  show ?thesis
    by (simp add: A0 A1 A2 B1 filter_on_lattice_finf_is_lb is_max_iff)
qed

lemma filter_on_lattice_finf_is_inf:
  fixes EF::"'a::lattice set set"
  assumes A0:"EF \<noteq> {}" and A1:"\<forall>F \<in> EF. is_filter F" and A2:"finite EF"
  shows "is_inf_in (fInf EF) EF  (filters_in UNIV)"
  by (simp add: A0 A1 A2 filter_on_lattice_finf_is_glb is_inf_in_def)

subsection FiltersOnTopLattice
lemma filter_on_top_lattice_inf_is_filter:
  fixes EF::"'a::bounded_lattice_top set set"
  assumes A0:"EF \<noteq> {}" and A1:"\<forall>F \<in> EF. is_filter F"
  shows "is_filter (filter_inf (EF))"
  by (simp add: A0 A1 filter_inf_is_filter)


lemma filter_on_top_lattice_inf_is_lb:
  fixes EF::"'a::bounded_lattice_top set set"
  assumes A0:"EF \<noteq> {}" and A1:"\<forall>F \<in> EF. is_filter F"
  shows " (filter_inf (EF)) \<in> lb_set_in EF (filters_in UNIV)"
  by (simp add: A0 A1 filter_inf_is_inf_in_filters is_inf_in_imp1)


lemma filter_on_top_lattice_inf_is_glb:
  fixes EF::"'a::bounded_lattice_top set set"
  assumes A0:"EF \<noteq> {}" and A1:"\<forall>F \<in> EF. is_filter F"
  shows "is_max (filter_inf (EF)) (lb_set_in EF (filters_in UNIV))"
  by (simp add: A0 A1 filter_inf_is_inf_in_filters is_inf_in_imp1)

lemma filter_on_top_lattice_inf_is_inf_in_filters:
  fixes EF::"'a::bounded_lattice_top set set"
  assumes A0:"EF \<noteq> {}" and A1:"\<forall>F \<in> EF. is_filter F"
  shows "is_inf_in (filter_inf (EF)) EF (filters_in UNIV)"
  by (simp add: A0 A1 filter_inf_is_inf_in_filters)

    
section MeshingAndGrilling
subsection PropertiesOfMeshing
lemma mesh_prop1:
  assumes A0:"{a}# F" and A1:"a \<le> b"
  shows "{b}#F"
proof-
  have B0:"\<forall>f \<in> F. ((inf a f) \<noteq> bot)"
       by (meson A0 insertI1 meshes_def)
  have B1:"\<forall>f \<in> F. ((inf a f) \<le> (inf b f))" by (simp add: A1 inf.coboundedI1)
  have B2:"\<forall>f \<in> F. ((inf b f) \<noteq> bot)"
    using B0 B1 bot.extremum_uniqueI by fastforce
  with B2 show ?thesis by (simp add: meshes_def)
qed

lemma mesh_prop2:
  assumes A0:"is_upclosed (F::'X::boolean_algebra set)" and A1:"a \<in> F"
  shows "\<not>({(-a)}#F)"
proof(rule ccontr)
  assume A2:"\<not>(\<not>({(-a)}#F))"
  have B0:"{(-a)}#F"
    using A2 by blast
  have B1:"inf (-a) a = bot"
    by simp
  show "False"
    by (meson A1 B0 B1 insertCI meshes_def)
qed


lemma mesh_prop3:
  assumes A0:"is_filter (F::'X::boolean_algebra set) \<and> is_filter G" and
          A1:"bot \<notin> F \<and> bot \<notin> G"
  shows "F \<le> G \<longrightarrow> F#G"
proof
  assume A1:"F \<le> G"
  show "F#G"
  proof-
    have P0:"\<forall>f \<in>F. \<forall>g \<in> G. (inf f g) \<noteq> bot"
    proof
      fix f assume B0:"f \<in> F"
      show "\<forall>g \<in> G. inf f g \<noteq> bot"
      proof
        fix g assume B1:"g \<in> G"
        have B2:"f \<in> G" 
          using A1 B0 by auto
        have B3:"is_filter G"
          by (simp add: assms)
        have B4:"is_pisystem G"
          by (simp add: B3 filter_inlattice_inf_closed is_pi_system_imp)
        have B5:"(inf f g) \<in> G"
          by (simp add: A0 B1 B2 filter_inlattice_inf_closed)
        show "inf f g \<noteq> bot"
          using B5 assms(2) by fastforce 
      qed
    qed
    show ?thesis by (simp add: P0 meshes_def)
  qed
qed

lemma mesh_prop4:
  assumes "is_upclosed (A::'X::boolean_algebra set)"
  shows "(x \<notin> A) \<longleftrightarrow> {(- x)}#A"
proof-
  let ?cx="-x" let ?S="{?cx}"
  let ?L="x \<notin> A" let ?R="?S#A"
  have LtR:"?L \<longrightarrow> ?R"
    by (metis assms compl_le_compl_iff inf_shunt is_upclosed_imp meshes_def singletonD)  
  have RtL:"?R \<longrightarrow> ?L" using assms mesh_prop2 by auto
  with LtR RtL show ?thesis by blast
qed
  
lemma mesh_prop5:
  assumes "is_upclosed (A::'X::boolean_algebra set)"
  shows "(x \<in> A) \<longleftrightarrow> \<not>({( - x)}#A)"
  using assms mesh_prop4 by blast

lemma mesh_prop6:
  assumes "is_upclosed (A::'X::boolean_algebra set)"
  shows "((-x) \<notin> A) \<longleftrightarrow> {x}#A"
  by (simp add: Diff_Diff_Int assms mesh_prop4)

lemma mesh_prop7:
  assumes "is_upclosed (A::'X::boolean_algebra set)"
  shows "((-x) \<in> A) \<longleftrightarrow> \<not>({x}#A)"
  using assms mesh_prop6 by auto


lemma mesh_prop8:
   "A#B \<longleftrightarrow> A \<subseteq> grill B"
proof-
  have Eq0:"A#B \<longleftrightarrow> (\<forall>a \<in> A. \<forall>b \<in> B. inf a b \<noteq> bot)" by (simp add: meshes_def)
  have Eq1:"... \<longleftrightarrow> (\<forall>a \<in> A. {a}#B)" by (simp add: meshes_def)
  have Eq2:"... \<longleftrightarrow> (\<forall>a \<in> A. a \<in> grill B)" by (simp add: grill_def)
  have Eq3:"... \<longleftrightarrow> A \<subseteq> grill B " by blast
  show ?thesis using Eq0 Eq1 Eq2 Eq3 by presburger
qed

lemma mesh_prop9:
  "A#B \<longleftrightarrow> B#A"
  by (metis inf_commute meshes_def)

lemma mesh_prop10:
   "A#B \<longleftrightarrow> B \<le> grill A"
  using mesh_prop8 mesh_prop9 by blast

lemma mesh_prop11:
   "A \<le> grill B \<longleftrightarrow> B \<le> grill A"
  using mesh_prop10 mesh_prop8 by auto

lemma mesh_prop12:
  assumes "is_upclosed (A::'X::boolean_algebra set)"
  shows "x \<in> A \<longleftrightarrow> (-x) \<notin> grill A"
  by (meson assms empty_subsetI insert_subset mesh_prop4 mesh_prop8)


lemma mesh_prop13:
  assumes "is_upclosed (A::'X::boolean_algebra set)"
  shows "x \<notin> A \<longleftrightarrow> (-x) \<in>  grill A"
  using assms mesh_prop12 by blast

lemma mesh_prop14:
  assumes "is_upclosed (A::'X::boolean_algebra set)"
  shows "(-x) \<in> A \<longleftrightarrow> x \<notin> grill A"
  by (simp add: assms double_diff mesh_prop12)

lemma mesh_prop15:
  assumes "is_upclosed (A::'X::boolean_algebra set)"
  shows "(- x) \<notin>  A \<longleftrightarrow> x \<in> grill A"
  by (simp add: assms mesh_prop14)


lemma mesh_prop16:
  fixes EF::"'X::complete_boolean_algebra set set"
  assumes A0:"\<forall>F \<in> EF. (is_filter F) \<and> (bot \<notin> F)" and
          A1:"finite EF" and
          A2:"is_filter G \<and> bot \<notin> G" and
          A0b:"EF \<noteq> bot \<and> EF \<noteq> {bot}"
  shows "G#(fInf (EF)) \<longleftrightarrow> (\<exists>F \<in> EF. G#F)"
proof-
  let ?INF="\<Inter>EF" let ?L="G#?INF" let ?R=" (\<exists>F \<in> EF. G#F)"
  have A3:"is_upclosed G"
    by (simp add: A2 is_filter_imp is_upclosed_def)
  have RtL:"?R\<longrightarrow>?L"
    by (meson Inf_lower2 mesh_prop10)
  have LtR:"\<not>?R \<longrightarrow> \<not>?L"
  proof
    assume NR:"\<not>(?R)"
    have B0:"(\<forall>F \<in> EF. \<not>(G#F))"  using NR by blast
    have B1:"(\<forall>F \<in> EF. \<exists>f \<in> F. \<not>(G#{f}))"  by (meson NR insertI1 meshes_def)
    have B2:"(\<forall>F \<in> EF. \<exists>f \<in> F. f \<notin> grill G)"
      by (simp add: B1 grill_def mesh_prop9)
    have B3:"(\<forall>F \<in> EF. \<exists>f \<in> F. (-f) \<in> G)"
      by (meson A3 B2 mesh_prop15) 
    obtain u where A5:"u=(\<lambda>F. SOME f. (f \<in> F \<and> (-f)\<in>G ) )" by simp
    have B4:" (\<forall>F \<in> EF. (-(u(F))) \<in> G)"  by (metis (no_types, lifting) A5 B3 someI)
    let ?H="u`EF" let ?HC="{b. \<exists>h \<in>?H. b=-h}"
    have B5:"finite ?H" by (simp add: A1)
    have B6:"finite ?HC"  by (metis B5 finite_imageI image_def)
    have B7:"(\<forall>hc \<in> ?HC. hc \<in> G)" using B4 by blast
    have B9:"?HC \<subseteq> G"
      using B7 by blast
    have B10:"?HC \<noteq> {}"
      using A0b by blast
    have B11:"?HC \<subseteq> G \<and> is_filter G \<and> ?HC \<noteq> {}"
      using A2 B10 B9 by blast
    have B11:"(fInf ?HC) \<in> G"
      using B11 B6 filters_inf_closed by auto
    have B12:"(-(fInf ?HC)) = fSup (?H)"
      by (metis (no_types) B10 B5 B6 boolean_algebra_class.boolean_algebra.double_compl finf_complete_lattice fsup_complete_lattice image_def image_empty uminus_Sup)
    have B13:" (fInf ?HC) \<in> G  \<longrightarrow> (fSup(?H)) \<notin> grill G"
      using A3 B12 mesh_prop12 by fastforce
    have B14:"\<forall>h \<in> ?H. \<exists>F \<in> EF. h=u(F)"
         by blast
    have B15:"\<forall>F \<in> EF. (u(F) \<in> F)"
        by (metis (mono_tags, lifting) A5 B3 someI_ex)
    have B16:"\<forall>F \<in> EF. \<exists>u \<in> ?H. u \<in> F"
       using B15 by blast
    have B17:"\<forall>F \<in> EF. \<exists>u \<in> F. u \<le> (fSup(?H))"
      by (metis A1 B16 Sup_upper finite_imageI fsup_complete_lattice insert_absorb insert_not_empty)
    have B17:"(fSup(?H)) \<in> ?INF"
      by (meson A0 B17 InterI is_filter_imp is_upclosed_def is_upclosed_imp)
    show "\<not>(?L)"
      using B11 B13 B17 mesh_prop10 by blast
  qed
  with LtR RtL show ?thesis
    by (metis A0b A1 finf_complete_lattice) 
qed

subsection PropertiesOfGrilling

lemma grill_is_antitone:
  "A \<subseteq> B \<longrightarrow> grill B \<subseteq> grill A"
  by (meson equalityD1 mesh_prop11 subset_trans)

lemma grill_antitone_converse:
  assumes A0:"is_upclosed (A::'a::complete_boolean_algebra set) \<and> is_upclosed (B::'a::complete_boolean_algebra set)"
  shows " grill B \<subseteq> grill A \<longrightarrow> A \<subseteq> B "
  using assms mesh_prop13 by blast


lemma grill_maps_to_upclosed_sets:
  assumes "(A::'a::complete_boolean_algebra set) \<noteq> {}"
  shows "is_upclosed (grill A)"
  apply(simp add: grill_def is_upclosed_def is_upclosed_in_def)
  using mesh_prop1 by blast

lemma upclosure_extensive:
  "is_extensive up_closure"
  by (simp add: is_extensive_def up_closure_extensive)

lemma upc_is_idempotent:
  "up_closure (up_closure A) = up_closure A"
proof-
  let ?A1="up_closure A" let ?A2="up_closure ?A1"
  have LtR:"?A1 \<subseteq> ?A2"
    by (meson is_extensive_def upclosure_extensive)
  have RtL:"?A2 \<subseteq> ?A1"
  proof-
    have RtLB0:"\<forall>x \<in> ?A2. x \<in> ?A1"
    proof
      fix x assume As0:"x \<in> ?A2"
      obtain a2 where As1:"a2 \<in> ?A1 \<and> a2 \<le> x"
        using As0 up_closure_idempotent by blast
      obtain a1 where As2:"a1 \<in> A \<and> a1 \<le> a2"
        using As1 up_closure_obtain by blast
      have B0:"a1 \<le> x"
        using As1 As2 dual_order.trans by blast
      show "x \<in> ?A1"
        using As0 up_closure_idempotent by blast
     qed
    show ?thesis
      by (simp add: RtLB0 subsetI)
  qed
  with LtR RtL show ?thesis by fastforce
qed

lemma upclosure_is_upclosed:
  "is_upclosed (up_closure A)"
proof-
  let ?U="up_closure A"
  have B0:"(\<And>a b. (a \<le> b \<and>  a \<in> ?U) \<longrightarrow>  b \<in> ?U)"
  proof
    fix a b assume A0:"(a \<le> b \<and>  a \<in> ?U)"
    obtain c where A1:"c \<in> A \<and> c \<le> a"
      using A0 up_closure_obtain by blast
    have B01:"c \<in> A \<and> c \<le> b"
      using A0 A1 by force
    show "b \<in> ?U"
      using B01 up_closure_imp by blast
  qed
  show ?thesis
    by (simp add: upc_is_idempotent upset_if_eq_upclosure)
qed


lemma gril_is_grill_of_upclosure:
  "grill A = grill (up_closure A)"
proof-
  have B0:"A \<subseteq> up_closure A"
    by (metis is_extensive_def upclosure_extensive)
  have B1:"grill (up_closure A) \<subseteq> grill A"
    by (simp add: B0 grill_is_antitone)  
  have B2:"grill A \<subseteq> grill (up_closure A)"
  proof
    fix a assume B2_A0:"a \<in> (grill A)"
    have B2_B1:"\<forall>b \<in> A. inf a b \<noteq> bot"
      by (meson B2_A0 dual_order.refl mesh_prop8 meshes_def)
    show "a \<in> grill (up_closure A)"
    proof-
      have B2_B3:"\<forall>c \<in> up_closure A. inf a c \<noteq> bot"
      proof
        fix c assume B2_A1:"c \<in> up_closure A"
        have B2_B4:"\<exists>b \<in> A. c \<ge> b"
          by (simp add: B2_A1 up_closure_if)
        obtain b where B2_A2:"b \<in> A \<and> c \<ge> b" 
           using B2_B4 by blast
        have B2_B5:"inf a c \<ge> inf a b" 
           by (simp add: B2_A2 inf.coboundedI2)
        have B2_B6:"... \<noteq> bot"
          using B2_A2 B2_B1 B2_B5 bot.extremum_uniqueI by fastforce
        show "inf a c \<noteq> bot" 
          using B2_B6 by blast
      qed
      show ?thesis
        by (simp add: B2_B3 grill_def meshes_def)
     qed
  qed
  with B1 B2 show ?thesis by blast
qed

lemma upclosure_if:
  fixes A::"'a::complete_boolean_algebra set" and
        a::"'a::complete_boolean_algebra"
  assumes A0:"a \<in> up_closure A"
  shows "a \<in> grill( grill A)"
proof-
  have B0:"\<forall>x. x \<in> grill (grill A) \<longleftrightarrow> (\<forall>y \<in> grill A. inf x y \<noteq> bot)"
    by (simp add: grill_def meshes_def)
  have B1:"\<forall>x. x \<in> grill (grill A) \<longleftrightarrow> (\<forall>y. (\<forall>z \<in> A. inf y z \<noteq> bot) \<longrightarrow> inf x y \<noteq> bot)"
    by (simp add: grill_def meshes_def)
  have B2:"is_upclosed (up_closure A)"
    using upclosure_is_upclosed by auto
  have B3:"-a \<notin> grill (up_closure A)"
    using B2 assms mesh_prop12 by blast
  have B4:"a \<in> grill (grill (up_closure A))"
    using B3 assms grill_maps_to_upclosed_sets mesh_prop15 by auto
  have B5:"grill (up_closure A) = grill A"
    using gril_is_grill_of_upclosure by blast
  show ?thesis
    using B4 B5 by force
qed
     
lemma grill_of_grill_is_upclosure:
  "grill (grill (A::'a::complete_boolean_algebra set)) = up_closure A"
proof-
  let ?U="up_closure A" and ?G="grill (grill A)"
  have L:"?G \<subseteq> ?U"
  proof 
    fix a assume A0:"a \<in> ?G"
    show "a \<in> ?U"
      by (metis (no_types, opaque_lifting) A0 gril_is_grill_of_upclosure in_mono mesh_prop12 mesh_prop15 up_closure_extensive upclosure_is_upclosed)
  qed
  have R:"?U \<subseteq> ?G"
  proof
     fix a assume A0:"a \<in> ?U"
     obtain x where A1:"x \<in> A \<and> x \<le> a"
       using A0 up_closure_obtain by blast
     show "a \<in> ?G"
       by (simp add: A0 upclosure_if)
  qed
  show ?thesis
    by (simp add: L R dual_order.eq_iff)
qed  

lemma grill_involutory_in_upsets:
  "grill (grill (A::'a::complete_boolean_algebra set)) = A \<longleftrightarrow> is_upclosed A"
  by (metis dual_order.refl grill_antitone_converse grill_of_grill_is_upclosure mesh_prop11 subset_antisym upclosure_is_upclosed)

lemma degenerate_grill1:
  "grill (UNIV::'a::complete_boolean_algebra set) = bot"
  by (metis UNIV_I all_not_in_conv grill_of_grill_is_upclosure mesh_prop12 top.extremum_unique up_closure_extensive upclosure_is_upclosed)

lemma degenerate_grill2:
  "grill (bot) = (UNIV::'a::complete_boolean_algebra set)"
  by (simp add: mesh_prop11 top.extremum_uniqueI)

lemma grill_grill_is_extensive:
  "is_extensive (\<lambda>A. (grill (grill A)))"
  using is_extensive_def mesh_prop11 by auto

lemma grill_grill_is_isotone:
  "is_isotone (\<lambda>A. (grill (grill A)))"
  by (simp add: grill_is_antitone is_isotone_def)
 

lemma grill_grill_is_idempotent:
  "is_idempotent (\<lambda>A. (grill (grill A)))"
  by (metis (no_types, lifting) grill_grill_is_extensive grill_is_antitone is_extensive_def is_idempotent_def subset_antisym)
  
     
lemma grill_grill_is_closure:
  "is_closure  (\<lambda>A. (grill (grill A)))"
  by (simp add: grill_grill_is_extensive grill_grill_is_idempotent grill_grill_is_isotone is_closure_def)

lemma prime_upset_is_grill_of_filter:
  fixes A::"'a::complete_boolean_algebra set"
  assumes A0:"bot \<notin> A \<and> (A \<noteq>  UNIV)" and A1:"is_upclosed A" and A2:"is_prime A"
  shows "\<exists>F. (is_filter F) \<and> (A=grill F)" 
proof-
  let ?B="grill A"
  have P3:"grill(?B ) = A"
    by (simp add: A1 grill_involutory_in_upsets)
  have P4:"\<forall>a \<in> ?B. (\<forall>b \<in> ?B. (inf a b \<in> ?B))"
  proof
    fix a assume P4A0:"a \<in> ?B" show "\<forall>b \<in> ?B.  (inf a b \<in> ?B)"
    proof
        fix b assume P4A1:"b \<in> ?B" 
        have P4B0:"(-a) \<notin> A"
          by (simp add: A1 P4A0 mesh_prop15)
        have P4B1:"(-b) \<notin> A" 
          by (simp add: P4A1 A1 mesh_prop15)
        have P4B2:"sup (-a) (-b) \<notin> A" 
          using A2 P4B0 P4B1 is_prime_def by blast
        have P4B3:"inf a b \<in> ?B"
          using A1 P4B2 mesh_prop15 by fastforce  
        show " inf a b \<in> ?B"
          by (simp add: P4B3)
      qed
  qed
  have P5:"is_pisystem ?B"
    by (simp add: P4 is_pi_system_imp)
  have P6:"is_upclosed ?B"
    using P3 grill_involutory_in_upsets by fastforce
  have P7:"\<exists>F.  ((is_pisystem F) \<and> (is_upclosed F) \<and> (A = grill F))"
    using P3 P5 P6 by auto
  obtain F where P8:"((is_pisystem F) \<and> (is_upclosed F) \<and> (A = grill F))"
    using P7 by blast
  have P9:"is_inhabited F"
    using A0 P8 degenerate_grill2 is_inhabited_def by auto
  show ?thesis
    using P8 P9 downdir_up_pisystem is_filter_if is_upclosed_def by auto
qed

lemma filtergrill_then_upclosed_prime:
  fixes A::"'a::complete_boolean_algebra set"
  assumes A0:"bot \<notin> A" and A1:"A=grill F" and A2:"is_filter F"
  shows "is_upclosed A \<and> is_prime A"
proof-
  have P0:"is_upclosed A" using A1 A2 grill_maps_to_upclosed_sets
    using filter_topped by auto
  have P1:"\<forall>a. \<forall>b. (a\<notin>A\<and>b\<notin>A) \<longrightarrow> sup a b\<notin>A"
  proof-
    fix a b
    have P10:"(a \<notin> A \<and>  b \<notin>  A)\<longrightarrow>  sup a b \<notin> A"
    proof
      assume P1A0:" (a \<notin> A \<and>  b \<notin>  A)"
      obtain f where P1A1:"f \<in> F \<and> (inf f a) = bot"
        by (metis A1 A2 P1A0 boolean_algebra.conj_cancel_left is_filter_imp is_upclosed_def mesh_prop15)
      obtain g where P1A2:"g \<in> F \<and> (inf g b) = bot"
        by (metis A1 A2 P1A0 boolean_algebra.conj_cancel_left is_filter_imp is_upclosed_def mesh_prop15)
      have P1B1:"(inf f g) \<in> F"
        by (simp add: A2 P1A1 P1A2 filter_inlattice_inf_closed)
      have P1B2:"inf (sup a b) (inf f g) = bot"
        by (metis (no_types, lifting) P1A1 P1A2 boolean_algebra.conj_disj_distrib2 inf.left_commute inf_bot_right inf_commute)
      have P1B3:"\<exists>h \<in> F. inf (sup a b) h = bot" 
        using P1B1 P1B2 by auto
      have P1B4:"(sup a b)\<notin>(grill F)"
        by (meson P1B3 dual_order.refl mesh_prop8 meshes_def) 
      show "sup a b\<notin>A" by (simp add: P1B4 assms)
     qed
     with P10 show ?thesis
       by (metis A1 A2 boolean_algebra.de_Morgan_disj filter_inlattice_inf_closed is_filter_imp is_upclosed_def mesh_prop15)
  qed
  have P2:"\<forall>a. \<forall>b. sup a b\<in>A  \<longrightarrow>  (a\<in>A\<or>b\<in>A)" 
     using P1 by auto
  have P3:"is_prime A" 
    using P1 is_prime_def by blast
  show ?thesis by (simp add: P0 P3)
qed



lemma grill_extensive:
  assumes A0:"is_filter F" and
          A1:"bot \<notin> F"
  shows "F \<subseteq> (grill F)"
  by (metis A0 A1 filter_inlattice_inf_closed mesh_prop8 meshes_def)


lemma proper_filter_iff:
  fixes F::"'X::order_bot set"
  assumes "is_filter F"
  shows  "is_proper F \<longleftrightarrow> bot \<notin> F"
  by (simp add: assms filter_improper_iff is_proper_def is_proper_in_def)



lemma ultrafilter_notprime_contradiction:
  fixes a1 a2::"'a::{distrib_lattice,bot}"
  assumes A0:"is_ultrafilter U" and
          A1:"\<not>((sup a1 a2) \<in> U \<longrightarrow> (a1 \<in> U) \<or> (a2 \<in> U))" and
          order_bot:"\<forall>x. bot \<le> x"
  shows "False"
  proof-
    have P:"((sup a1 a2) \<in> U) \<and> \<not>(a1 \<in> U \<or> a2 \<in> U) \<longrightarrow> False"
    proof
    assume A0b:"((sup a1 a2) \<in> U) \<and> \<not>(a1 \<in> U \<or> a2 \<in> U)" 
    have A1:"(sup a1 a2) \<in> U \<and> (a1 \<notin> U \<and> a2 \<notin> U)" 
      using A0 A0b by auto
    let ?S="{x. (sup a1 x) \<in> U}"
    have P2:"U \<subset> ?S"
      proof-
        have P20:"sup a1 a2 \<in> U"
           using A1 by auto
        have P21:"\<forall>u \<in> U. u \<le> sup a1 u"
           by simp
        have P22:"is_upclosed U"
          by (meson A0 is_filter_imp is_pfilter_imp2 is_ultrafilter_def up_closure_in_univ_imp)
        have P23:"\<forall>u \<in> U. ((sup a1  u) \<in> U)"
          using P21 P22 is_upclosed_imp by blast
        have P24:"\<forall>u \<in> U. u \<in> ?S" 
          by (simp add: P23)
        have P25:"U \<subseteq> ?S"
          using P24 by auto
        have P26:"a2 \<in> ?S \<and> \<not>(a2 \<in> U)"
          by (simp add: A1)
        have P27:"U \<subset> ?S" 
          using P25 P26 by blast
        with P27 show ?thesis
           by simp
     qed
    have P3:"is_pfilter ?S"
      proof-
        have F1:"is_upclosed ?S"
          proof-
            have F1_0:"\<And>a b. (a \<in> ?S \<and> a \<le> b) \<longrightarrow> b \<in> ?S"
              proof
                fix a b assume A1_0:"(a \<in> ?S \<and> a \<le>  b)"
                have F1_1:"sup a1 a \<in> U"
                  using A1_0 by auto
                have F1_2:"sup a1 a \<le> sup a1 b"
                  by (simp add: A1_0 sup.coboundedI2)
                have F1_3:"is_upclosed U"
                  by (meson A0 is_filter_in_imp is_pfilter_imp1 is_ultrafilter_def is_upclosed_def)
                have F1_4:"sup a1 b \<in> U"
                  using F1_1 F1_2 F1_3 is_upclosed_imp by blast
                show "b \<in> ?S"
                  by (simp add: F1_4)
            qed
         show ?thesis
           using F1_0 is_upclosed_def is_upclosed_in_def by blast
       qed
       have F2:"is_pisystem ?S"
        proof-
          have F2_0:"\<And>f1 f2. (f1 \<in> ?S \<and> f2 \<in> ?S) \<longrightarrow> ((inf f1 f2) \<in> ?S)"
            proof
              fix f1 f2 assume A4:"f1 \<in> ?S \<and> f2 \<in> ?S"
              let ?f12="inf f1 f2"
              have F2_1:"sup a1 f1 \<in> U \<and> sup a1 f2 \<in> U"
                using A4 by auto
               have F2_2:"inf (sup a1 f1) (sup a1 f2) \<in> U"
                 using A0 F2_1 filter_inlattice_inf_closed is_pfilter_imp2 is_ultrafilter_def by blast
               have F2_3:"inf (sup a1 f1) (sup a1 f2) = sup a1 (inf f1 f2)"
                 by (simp add: sup_inf_distrib1)
               have F2_4:"sup a1 (inf f1  f2) \<in> U"
                 using F2_2 F2_3 by auto
               show "?f12 \<in> ?S"
                 by (simp add: F2_4)
           qed
           show ?thesis
             using F2_0 is_pi_system_imp by blast
         qed
      have F3:"is_inhabited ?S"
        using A1 is_inhabited_def by auto
      have F4:"is_proper ?S"
        by (metis UNIV_I assms(2) is_proper_def is_proper_in_def mem_Collect_eq sup.idem)
      show ?thesis
        using F1 F2 F3 F4 downdir_up_pisystem is_filter_if is_pfilter_if2 is_upclosed_def by auto
      qed
    have P4:"\<not>(is_ultrafilter U)"
      using P2 P3 is_ultrafilter_def by blast
    show "False"
      using P4 assms by blast
   qed
  show "False"
    using A1 P by auto
qed

lemma filter_is_ultra_iff_prime_alt:
  fixes U::"'a::{boolean_algebra, order_bot} set"
  assumes A0:"is_pfilter U"
  shows "is_ultrafilter U \<longleftrightarrow> is_prime_alt U"
proof
  assume A1:"is_ultrafilter U"
  show "is_prime_alt U"
  proof-
    have B0:"\<forall>a. (a \<in> U) \<or> (-a) \<in> U"
      by (metis A1 assms filter_topped is_pfilter_imp2 order_bot_class.bot_least sup_compl_top ultrafilter_notprime_contradiction)
    show ?thesis
      by (metis B0 assms boolean_algebra.conj_cancel_right filter_inlattice_inf_closed is_pfilter_imp2 is_prime_alt_def proper_filter_iff)
  qed
  next
  assume A2:"is_prime_alt U"
  show "is_ultrafilter U" 
  proof-
    have B1:" (\<forall>F .  (is_pfilter F \<and> U \<subseteq> F) \<longrightarrow> U=F)"
    proof (rule ccontr)
      assume A3:"\<not> (\<forall>F .  (is_pfilter F \<and> U \<subseteq> F) \<longrightarrow> U=F)"
      obtain F where  A4:"is_pfilter F \<and> U \<subset> F "
        using A3 by blast
      obtain a where A5:"a\<in> F \<and> a \<notin> U"
        using A4 by blast
      have B2:"(-a) \<in> U"
        using A2 A5 is_prime_alt_def by blast
      show "False"
        by (metis A4 A5 B2 boolean_algebra.conj_cancel_right filter_inlattice_inf_closed is_pfilter_imp2 proper_filter_iff psubsetD)
    qed
    show ?thesis
      by (simp add: B1 assms is_ultrafilter_def)
  qed
qed


lemma not_in_grill_not_in_ultrafilter:
  assumes "is_ultrafilter U"
  shows "\<forall>u.  u \<notin> (grill U) \<longrightarrow> (u \<notin> U)"
  using assms grill_extensive is_pfilter_imp2 is_ultrafilter_def proper_filter_iff by blast


lemma grill_of_ultrafilter_subset:
  assumes A0:"is_ultrafilter (U::'a::{boolean_algebra, order_bot} set)"
  shows "(grill U) \<subseteq> U"
proof
  fix a assume A1:"a \<in> grill U"
  have B0:"\<forall>x \<in> U. inf a x \<noteq> bot"
    by (meson A1 dual_order.refl mesh_prop8 meshes_def)
  show "a \<in> U"
    using B0 assms boolean_algebra.conj_cancel_right filter_is_ultra_iff_prime_alt is_prime_alt_def is_ultrafilter_def by blast
qed

lemma ultrafilters_grill_fixpoints:
  "\<forall>U. is_ultrafilter  (U::'a::{boolean_algebra, order_bot} set) \<longrightarrow> (grill U) = U"
  by (meson grill_extensive grill_of_ultrafilter_subset is_pfilter_imp2 is_ultrafilter_def proper_filter_iff subset_antisym)


lemma filter_then_prime_imp_grillid:
  assumes A0:"is_pfilter F" and A1:"is_prime_alt F"
  shows "grill F = F"
  by (simp add: A0 A1 ultrafilters_grill_fixpoints filter_is_ultra_iff_prime_alt)



(* voll vereinigungsdualer operator*)



lemma grill_intersection_union_dual:
  assumes A0:"I \<noteq> {}" and A1:"\<forall>i \<in> I. (is_upclosed (EF(i)::'a set set))"
  shows "grill ( \<Inter>i \<in> I. EF(i) ) = (\<Union>i \<in> I. grill (EF(i)))"
proof-
  have B0:"\<forall>i \<in> I. ( \<Inter>i \<in> I. EF(i) ) \<subseteq> (EF(i))" 
     by (simp add: INT_lower)
  have B1:"\<forall>i \<in> I. grill (EF(i)) \<subseteq> grill ( \<Inter>i \<in> I. EF(i) )"
    by (simp add: INF_lower grill_is_antitone)
  have B2:"(\<Union>i \<in> I. grill (EF(i))) \<subseteq>  grill ( \<Inter>i \<in> I. EF(i))"
    using B1 by blast
  have B3:"\<forall>a. a \<notin> (\<Union>i \<in> I. grill (EF(i))) \<longrightarrow> (\<forall>i \<in> I. \<exists>fi \<in> (EF(i)). fi \<inter> a = {})"
    using A1 mesh_prop15 by fastforce
  have B12:"\<And>a. (a \<notin> (\<Union>i \<in> I. grill (EF(i)))) \<longrightarrow> (a \<notin> grill(( \<Inter>i \<in> I. EF(i))))"
  proof
  fix a assume A2:"a \<notin> (\<Union>i \<in> I. grill (EF(i)))"
  have B4:"\<forall>i \<in> I. \<exists>fi \<in> (EF(i)). fi \<inter> a = {}"
    by (meson A2 B3)
  obtain f where A3:"f=(\<lambda>i. SOME fi. fi \<in> (EF(i)) \<and>  (fi \<inter> a = {}) )"
    by simp
  have B5:"\<forall>i \<in> I. (f i) \<inter> a = {}"
    by (smt (verit, best) A3 B4 someI)
  have B6:"a \<inter> (\<Union>i \<in> I. (f i)) = {}"
    using B5 by blast
  have B7:"\<forall>i \<in> I. (f i) \<in> (EF(i))"
    by (smt (verit, del_insts) A3 B4 someI_ex)
  have B8:"\<forall>i \<in> I. (f i)\<subseteq> (\<Union>i \<in> I. (f i))" by blast
  have B9:"\<forall>i \<in> I. (\<Union>i \<in> I. (f i)) \<in> (EF(i))"
    by (meson A1 B7 B8 is_upclosed_imp)
  have B10:"(\<Union>i \<in> I. (f i)) \<in>  ( \<Inter>i \<in> I. EF(i))"
    using B9 by blast
  have B11:"a \<notin> grill(( \<Inter>i \<in> I. EF(i)))"
    by (meson B10 B6 mesh_prop8 meshes_def subset_refl)
  show "a \<notin> grill(( \<Inter>i \<in> I. EF(i)))"
    using B11 by blast
  qed
  from B12 have B13:"(\<Union>i \<in> I. grill (EF(i))) \<supseteq>  grill ( \<Inter>i \<in> I. EF(i))" by blast
  with B2 B13 show ?thesis
    by blast
qed


lemma grill_union_intersection_dual:
  assumes A0:"I \<noteq> {}" and A1:"\<forall>i \<in> I. (is_upclosed (EF(i)::'a set set))"
  shows "grill ( \<Union>i \<in> I. EF(i) ) = (\<Inter>i \<in> I. grill (EF(i)))"
proof-
  have B0:"\<forall>a. a \<in> grill ( \<Union>i \<in> I. EF(i) ) \<longleftrightarrow> (\<forall>i \<in> I. \<forall>fi \<in> (EF(i)). a \<inter> fi \<noteq> {})"
    by (simp add: grill_def meshes_def)
  have B1:"\<forall>a. (\<forall>i \<in> I. \<forall>fi \<in> (EF(i)). a \<inter> fi \<noteq> {})  \<longleftrightarrow> (\<forall>i \<in> I. a \<in> grill (EF(i)))"
    by (simp add: grill_def meshes_def)
  have B2:"\<forall>a. a \<in> grill ( \<Union>i \<in> I. EF(i) ) \<longleftrightarrow>  (\<forall>i \<in> I. a \<in> grill (EF(i)))"
    using B0 B1 by presburger
  have B3:"\<forall>a. a \<in> grill ( \<Union>i \<in> I. EF(i) ) \<longleftrightarrow>  a \<in>  (\<Inter>i \<in> I. grill (EF(i)))"
    by (simp add: B2)
  with B3 show ?thesis
    by blast
qed



lemma union_fchain_is_filter3:
  fixes EF::"'X::order_bot set set"
  assumes A0: "\<forall>F \<in> EF. is_pfilter F" 
      and A1: "is_chain(EF)" 
      and A2: "EF \<noteq> {}"
  shows "is_pfilter (Sup (EF))"
proof -
  let ?F = "Sup (EF)"
  have F1: "is_upclosed ?F"
  proof -
    have F1_0: "\<And>a b. (a \<in> ?F \<and> a \<le> b) \<longrightarrow> b \<in> ?F"
    proof
      fix a b assume A3: "a \<in> ?F \<and> a \<le> b"
      then obtain F where B0: "F \<in> EF \<and> a \<in> F"
        using SUP_upper by blast
      then have "b \<in> F"
        by (meson A0 A3 UNIV_I is_filter_imp is_pfilter_imp2 is_upclosed_in_imp)
      thus "b \<in> ?F"
        using B0 SUP_upper by blast
    qed
    show ?thesis
      by (meson F1_0 is_upclosed_def is_upclosed_in_def)
  qed
  have F2: "is_downdir ?F"
  proof -
    have F2_0: "\<And>f1 f2. (f1 \<in> ?F \<and> f2 \<in> ?F) \<longrightarrow> (\<exists>f3 \<in> ?F. f3 \<le> f1 \<and> f3 \<le> f2)"
    proof
      fix f1 f2 assume A4: "f1 \<in> ?F \<and> f2 \<in> ?F"
      then obtain F1 where B0: "F1 \<in> EF \<and> f1 \<in> F1"
        by blast 
      then obtain F2 where B1: "F2 \<in> EF \<and> f2 \<in> F2"
        using A4 by blast 
      from A1 have B2:"F1 \<subseteq> F2 \<or> F2 \<subseteq> F1"
        by (simp add: B0 B1 is_chain_def)
      obtain f3 where B3:"(f3 \<in> F1 \<or> f3 \<in> F2) \<and>  (f3 \<le> f1 \<and> f3 \<le> f2)"
        by (metis A0 B0 B1 is_filter_in_def is_filter_def B2   insert_absorb insert_subset is_downdir_imp is_pfilter_imp2)
      show "(\<exists>f3 \<in> ?F. f3 \<le> f1 \<and> f3 \<le> f2)"
        using B0 B1 B3 by blast
    qed
    show ?thesis
      by (metis F2_0 is_downdir_def)
  qed
  have F3: "is_inhabited ?F"
    by (metis A0 A2 Union_upper ex_in_conv is_filter_imp is_inhabited_def is_pfilter_imp2 subset_empty)
  have F4: "is_proper ?F"
    by (metis A0 UNIV_I UnionE is_pfilter_imp2 is_proper_def is_proper_in_def proper_filter_iff)
  show ?thesis
    using F1 F2 F3 F4 is_filter_if is_pfilter_if2 is_upclosed_def by auto
qed


lemma union_of_finer_filter_chain:
  fixes F::"'X::order_bot set" and
        C::"('X::order_bot set set)" 
  assumes A0:"C \<noteq> {}" and
          A1: "C \<subseteq>  (finer_pfilters F)" and
          A2:"is_chain C"
  shows "Sup(C) \<in> (finer_pfilters F)"
proof-
  have B0:"is_pfilter (Sup(C))"
    by (metis A0 A1 A2 CollectD finer_pfilters_def subset_eq union_fchain_is_filter3)
  have B1:"\<forall>c \<in> C. F \<subseteq> c"
    using A1 finer_pfilters_def by auto
  have B2:"\<forall>c \<in> C. c \<subseteq> (Sup(C))"
    by (simp add: complete_lattice_class.Sup_upper)
  have B3:"F \<subseteq> (Sup(C))"
    by (simp add: A0 B1 less_eq_Sup)
  show ?thesis
    by (simp add: B0 B3 finer_pfilters_def)
qed

lemma superset_ultrafilter_existence:
  fixes F::"'X::order_bot set"
  assumes A0:"is_pfilter F"
    shows "\<forall>C \<in> chains(finer_pfilters F).  C \<noteq> {} \<longrightarrow> (\<Union>C) \<in> (finer_pfilters F)"
proof
  let ?U="finer_pfilters F"
  fix C::"('X::order_bot set set)" 
  assume A1:"C \<in> chains ?U"
  show "C \<noteq> {} \<longrightarrow> \<Union>C \<in> (finer_pfilters F)"
  proof
    assume A2:"C \<noteq> {} "
    show "\<Union>C \<in> (finer_pfilters F)"
      by (meson A1 A2 chainsD chainsD2 is_chain_def union_of_finer_filter_chain)
  qed
qed


lemma existence_of_union_in_finer_filters_set:
  fixes F::"'X::order_bot set"
  assumes "is_pfilter F" and "(finer_pfilters F) \<noteq> {}"
  shows "\<And>C. \<lbrakk>C\<noteq>{}; subset.chain (finer_pfilters F) C\<rbrakk> \<Longrightarrow> (Sup(C)) \<in> (finer_pfilters F)"
  by (simp add: is_chain_def subset_chain_def union_of_finer_filter_chain)


lemma exists_finer_ultrafilter:
  fixes F::"'X::order_bot set"
  assumes A0:"is_pfilter F"
    shows "\<exists>G . is_ultrafilter G \<and> F \<subseteq> G"
proof-
  let ?U="finer_pfilters F"
  have B0:"\<forall>C \<in> chains ?U .C \<noteq> {} \<longrightarrow> \<Union>C \<in> ?U"
    by (simp add: assms superset_ultrafilter_existence)
  have B1:"\<exists>S\<in>?U . \<forall>X\<in>?U . S \<subseteq> X \<longrightarrow> X = S"
    by (smt (verit, del_insts) assms empty_Collect_eq finer_pfilters_def order_refl
        subset_Zorn_nonempty existence_of_union_in_finer_filters_set)
  obtain S where B2:"S \<in> ?U \<and> (\<forall>X\<in>?U . S \<subseteq> X \<longrightarrow> X = S)" 
    using B1 by blast
  have B3:"S \<noteq> {}"
    using B2 finer_pfilters_def is_filter_imp is_inhabited_def is_pfilter_imp2 by fastforce
  have B4:"\<And>G. (is_pfilter G) \<and> (S \<subseteq> G) \<Longrightarrow> F \<subseteq> G \<Longrightarrow> S = G"
    by (metis B2 CollectI finer_pfilters_def)
  show ?thesis
    by (metis B2 B4 CollectD finer_pfilters_def is_ultrafilter_def order_trans)
qed


lemma finer_ultrafilters_notempty:
  fixes F::"'X::order_bot set"
  assumes "is_pfilter F"
  shows "\<exists>U. (is_ultrafilter U) \<and> (F \<subseteq> U)"
  by (simp add: assms exists_finer_ultrafilter)

lemma exists_finer_filter_iff:
  fixes F::"'X::{boolean_algebra,order_bot} set" and 
        a::"'X::{boolean_algebra,order_bot}"
  assumes A0:"is_pfilter F" and A1:"\<forall>f \<in> F. inf f a \<noteq> bot"
  shows "is_pfilter (filter_closure (\<Union>{F, {a}})) \<and> a \<in> (filter_closure (\<Union>{F, {a}})) \<and>  F \<subseteq> (filter_closure (\<Union>{F, {a}}))"
proof-
  define Fa where "Fa=\<Union>{F, {a}}"
  define G where "G=filter_closure Fa"
  have B0:"is_pfilter G"
  proof-
    have A01:"is_filter G"
      by (simp add: G_def Fa_def filter_closure_is_filter)
    have A02:"bot \<notin> G"
    proof-
      have A020:"a \<noteq> bot"
        using A0 A1 boolean_algebra.conj_zero_right filter_topped is_pfilter_imp2 by blast
      have A021:"bot \<notin> F"
        using A1 inf_bot_left by blast
      have A022:"bot \<notin> Fa"
        using Fa_def A020 A021 by blast
      have A024:"\<forall>S. S \<in> Fpow_ne(F) \<longrightarrow> InfUn S \<noteq> bot"
        by (metis A0 A021 filters_inf_closed fpow_ne_imp is_pfilter_imp2 semilattice_inf_finf_eq)
      have A025:"\<And>S. S \<in> Fpow_ne(Fa)  \<longrightarrow> InfUn S \<noteq> bot"
      proof
        fix S assume A0250:"S \<in> Fpow_ne(Fa) "
        show "InfUn S \<noteq> bot"
        proof(cases "a \<in> S")
          case True
          have A0251:"InfUn S = (if (S-{a}={}) then a else (inf a (InfUn(S - {a}))))"
            by (metis A0250 True finite_Diff fpow_ne_equiv semilattice_inf_class.remove semilattice_inf_finf_eq)
          have "InfUn S \<noteq> bot"
          proof(cases "S-{a}={}")
            case True
            then show ?thesis
              using A020 A0251 by presburger
          next
            case False
            have A0252:" (S - {a}) \<in> Fpow_ne F"
              by (metis A0250 Fa_def False Sup_insert True Un_insert_right ccpo_Sup_singleton finite_Diff fpow_ne_if fpow_ne_imp subset_insert_iff sup_bot.right_neutral)
            have A0253:"InfUn(S - {a}) \<noteq> bot"
              by (meson A024 A0252 PowI)
            have A0254:"(inf (InfUn(S - {a})) a) \<noteq> bot"
              by (metis A0 A0252 A1 filters_inf_closed fpow_ne_imp is_pfilter_imp2 semilattice_inf_finf_eq)
            then show ?thesis
              by (metis A0251 False inf_commute)
          qed
          then show ?thesis 
            by simp
        next
          case False
          then show ?thesis
            by (metis A024 A0250 Fa_def Sup_insert Un_insert_right ccpo_Sup_singleton fpow_ne_if fpow_ne_imp subset_insert_iff sup_bot.right_neutral)
          qed
        qed
      show ?thesis
        by (metis A025 G_def bot.extremum_uniqueI filter_closure_obtains0)
      qed
    show ?thesis
      by (simp add: A01 A02 is_pfilter_if2 proper_filter_iff)
  qed
  have B1:"F \<subseteq> G"
    using Fa_def G_def filter_closure_extensive by force
  have B2:"a \<in> G"
    using Fa_def G_def filter_closure_extensive by fastforce
  show ?thesis
    using B0 B1 B2 Fa_def G_def by fastforce
qed

lemma filter_is_intersection_of_finer_ultrafilters:
  fixes F::"'X::{boolean_algebra,order_bot} set"
  assumes A0:"is_pfilter F"
  shows "F = \<Inter>(finer_ultrafilters F)"
proof-
  define UF where "UF=finer_ultrafilters F" 
  define I where"I=\<Inter>UF"
  have B0:"\<forall>U. U \<in> UF \<longleftrightarrow> (is_ultrafilter U \<and> F \<subseteq> U)"
    by (simp add: UF_def finer_ultrafilters_def)
  have L:"F \<subseteq> I"
    using B0 I_def by blast
  have R:"I \<subseteq> F"
  proof (rule ccontr)
    assume RA0:"\<not>(F \<supseteq> I)"
    obtain a where RA1:"a \<in> I \<and> a \<notin> F"
      using RA0 by blast
    have RB1:"(-a) \<in> grill F"
      using RA1 assms is_filter_imp is_pfilter_imp2 is_upclosed_def mesh_prop12 by blast
    have RB2:"\<forall>f \<in> F. inf (-a) f \<noteq> bot"
      by (metis RB1 dual_order.refl inf_commute mesh_prop10 meshes_def)
    define G where "G=(filter_closure (\<Union>{F, {-a}}))"
    have RB2:"is_pfilter G \<and> F \<subseteq> G \<and> (-a) \<in> G"
      by (metis G_def RB2 assms exists_finer_filter_iff inf_commute)
    obtain U where RA3:"is_ultrafilter U \<and> G \<subseteq> U"
      using RB2 finer_ultrafilters_notempty by blast
    have RB3:"(-a) \<in> U \<and> U \<in>(finer_ultrafilters F)"
      using B0 RA3 RB2 UF_def by blast
    have RB4:"a \<notin> U"
      using RA3 RB3 filter_is_ultra_iff_prime_alt is_prime_alt_def is_ultrafilter_def by blast
    show "False"
      using I_def RA1 RB3 RB4 UF_def by blast
  qed
  show ?thesis
    using I_def L R UF_def by auto
qed


lemma ultrafilters_is_union_of_coarser_ultrafilters:
  fixes G::"'X::{boolean_algebra,order_bot} set"
  assumes A0:"is_prime_alt G \<and> is_pfilter G"
  shows "(G= \<Union>(coarser_ultrafilters G))"
proof-
  have "G = \<Union> {X. is_ultrafilter X \<and> X \<subseteq> G}"
    using assms filter_is_ultra_iff_prime_alt by auto
  then show ?thesis
    by (simp add: coarser_ultrafilters_def)
qed

section GaloisConnections

lemma gc2_iff_gc4:
  fixes f::"'a::order \<Rightarrow> 'b::order" and g::"'b::order \<Rightarrow> 'a::order"
  shows "is_gc2 f g \<longleftrightarrow> is_gc4 f g"
proof-
  have LtR:"is_gc2 f g \<longrightarrow> is_gc4 f g"
  proof
    assume A0:"is_gc2 f g "
    have LR:"\<And>x y.  y \<le> (f x) \<longrightarrow> x \<le> (g y)"
    proof
      fix x y assume A1:"y \<le> f x"
      have B0:"(g (f x)) \<le> g y"
        using A0 A1 antitone_def is_gc2_def by auto
      have B1:"x \<le> (g (f x))"
        using A0 comp_extensive_def is_gc2_def by blast
      have B2:"... \<le> g y"
        by (simp add: B0)
      show "x \<le> g y"
        using B1 B2 by auto
    qed
    have RL:"\<And>x y.  x \<le> (g y) \<longrightarrow> y \<le> (f x)"
    proof
      fix x y assume A2:"x \<le> g y"
      have B3:"(f (g y)) \<le> f x"
        using A0 A2 antitone_def is_gc2_def by auto
      have B4:"y \<le> (f (g y))"
        using A0 comp_extensive_def is_gc2_def by blast
      have B5:"... \<le> f x"
        by (simp add: B3)
      show "y \<le> f x"
        using B4 B5 by auto
    qed
    show "is_gc4 f g"
      by (metis LR RL is_gc4_def)
  qed
  have RtL:"is_gc4 f g \<longrightarrow> is_gc2 f g"
  proof
    assume A3:"is_gc4 f g"
    have B6:"\<forall>x. x \<le> (g (f x))"
      using A3 is_gc4_def by blast
    have B7:"\<forall>y. y \<le> (f (g y))"
      using A3 is_gc4_def by auto
    have B8:"\<And>x1 x2. x1 \<le> x2 \<longrightarrow> (f x2) \<le> (f x1)"
      by (meson B6 A3 dual_order.trans is_gc4_def)
    have B9:"\<And>y1 y2. y1 \<le> y2 \<longrightarrow> (g y2) \<le> (g y1)"
      by (meson B7 A3 dual_order.trans is_gc4_def)
    show "is_gc2 f g"
      by (simp add: B6 B7 B8 B9 antitone_def comp_extensive_def is_gc2_def)
  qed
  show ?thesis
    using LtR RtL by blast
qed


lemma complete_lattice_inf_exists:
  fixes A::"'a::complete_lattice set"
  shows "Inf A = InfUn A"
proof-
  have B0:"is_inf (Inf A) A"
    by (metis Inf_empty complete_lattice_inf_is_inf equals0D is_inf_if3 top_greatest)
  show "Inf A = InfUn A"
    using B0 has_inf_def has_max_iff2 is_inf_def is_inf_inf_eq by blast
qed

lemma complete_lattice_sup_exists:
  fixes A::"'a::complete_lattice set"
  shows "Sup A = SupUn A"
proof-
  have B0:"is_sup (Sup A) A"
    by (simp add: Sup_least Sup_upper is_sup_if3)
  show "Sup A = SupUn A"
    using B0 has_sup_def has_min_iff2 is_sup_def is_sup_sup_eq by blast
qed


lemma gc2_imp_join_dual:
  fixes f::"('X::complete_lattice \<Rightarrow> 'Y::complete_lattice)"
  fixes g::"('Y::complete_lattice \<Rightarrow> 'X::complete_lattice)"
  assumes A0:"is_gc2 f g"
  shows "is_join_dual f"
proof-
  have B0:"is_gc4 f g" using assms gc2_iff_gc4 by blast 
  have B1:"\<forall>A. (\<forall>a \<in> A. (f (Sup(A))) \<le> (f a))"
    by (meson antitone_def assms complete_lattice_class.Sup_upper is_gc2_def)
  have B2:"\<forall>A. (\<forall>a \<in> A. (f (Sup(A))) \<le> (Inf (f`A)))"
    by (simp add: B1 INF_greatest)
  have B3:"\<And>y A. y \<le> Inf(f`(A)) \<longleftrightarrow> (\<forall>a \<in> A. (y \<le> (f a)))"
    by (simp add: le_INF_iff)
  have B4:"\<And>y A. y \<le> Inf(f`(A)) \<longleftrightarrow> (\<forall>a \<in> A. (a \<le> (g y)))"
    by (meson B0 B3 is_gc4_def)
  have B5:"\<And>y A. y \<le> Inf(f`(A)) \<longleftrightarrow> ((Sup A) \<le> (g y))"
    by (simp add: B4 Sup_le_iff)
  have B6:"\<And>y A. y \<le> Inf(f`(A)) \<longleftrightarrow> (y \<le> (f (Sup A)))"
    using B0 B5 is_gc4_def by blast
  have B7:"\<And>y A. y \<le> InfUn(f`(A)) \<longleftrightarrow> (y \<le> (f (SupUn A)))"
  proof
    fix y A assume A1:"y \<le> InfUn(f`(A))"
    have B70:"... = Inf(f`(A))"
      by (simp add: complete_lattice_inf_exists)
    have B71:"SupUn A = Sup A"
      by (simp add: complete_lattice_sup_exists)
    have B72:"(f (SupUn A)) = (f((Sup A)))"
      by (simp add: B71)
    show "(y \<le> (f (SupUn A)))"
      using A1 B6 B70 B71 by fastforce
    next
    fix y A assume "(y \<le> (f (SupUn A)))"
    have B73:"SupUn A = Sup A"
      by (simp add: complete_lattice_sup_exists)
    have B74:"(f (SupUn A)) = (f((Sup A)))"
      by (simp add: B73)
    have B75:"(y \<le> (f (Sup A)))"
      using B74 \<open>(y::'Y::complete_lattice) \<le> (f::'X::complete_lattice \<Rightarrow> 'Y::complete_lattice) (SupUn (A::'X::complete_lattice set))\<close> by auto
    have B75:"y \<le> Inf(f`(A))"
      using B6 B75 by blast
    show "y \<le> InfUn(f`(A))"
      by (metis B75 complete_lattice_inf_exists)
  qed
  show ?thesis
    by (meson B7 dual_order.refl is_join_dual_def order_antisym)
qed


lemma join_dual_imp_gc2:
  fixes f::"('X::complete_lattice \<Rightarrow> 'Y::complete_lattice)"
  fixes g::"('Y::complete_lattice \<Rightarrow> 'X::complete_lattice)"
  assumes A0:"is_join_dual f"
  shows "is_gc2 f (join_dual_partner f)"
proof-
  let ?g="(join_dual_partner f)"
  have B0:"\<And>x1 x2. (x1 \<le> x2) \<longrightarrow> (f x2) \<le> (f x1)"
  proof
    fix x1 x2 assume A1:"(x1::('X::complete_lattice)) \<le> (x2::('X::complete_lattice))"
    have B00:"SupUn {x1, x2} = x2"
      by (metis A1 Sup_insert ccpo_Sup_singleton complete_lattice_sup_exists sup.absorb_iff2)
    have B01:"(f x2) = (f (SupUn {x1, x2}))"
      by (simp add: B00)
    have B01:"... = (InfUn {(f x1), (f x2)})"
      by (metis (mono_tags, lifting) assms image_insert image_is_empty is_join_dual_def)
    have B02:"... \<le> (f x1)"
      by (simp add: semilattice_inf_finf_eq)
    show "(f x2) \<le> (f x1)"
      using B00 B01 B02 by auto
  qed
  have B1:"\<And>y1 y2. (y1 \<le> y2) \<longrightarrow> (?g y2) \<le> (?g y1)"
  proof
    fix y1 y2 assume A2:"(y1::('Y::complete_lattice)) \<le> (y2::('Y::complete_lattice))" 
    let ?B2="{x::('X::complete_lattice). y2 \<le> (f x)}"
    let ?B1="{x::('X::complete_lattice). y1 \<le> (f x)}"
    have B10:"(?g y2) = SupUn ?B2"
      by (simp add: join_dual_partner_def)   
    have B11:"(?g y1) = SupUn ?B1"
      by (simp add: join_dual_partner_def)   
    have B12:"?B2 \<subseteq> ?B1"
      using A2 by force
    have B13:"is_sup (Sup ?B1) ?B1"
      by (meson Sup_least Sup_upper is_sup_if3)
    have B14:"has_sup ?B1"
      by (metis B13 has_min_iff has_sup_def is_min_iff is_sup_def)
    have B14b:"is_sup (Sup ?B2) ?B2"
      by (meson Sup_least Sup_upper is_sup_if3)
    have B14c:"has_sup ?B2"
      by (metis B14b has_min_iff has_sup_def is_min_iff is_sup_def)
    have B15:"(?g y2) \<le> (?g y1)"
      by (simp add: B10 B11 B12 B14 B14c sup_monotone1)
    show "(?g y2) \<le> (?g y1)"
      by (simp add: B15)
  qed
  have B2:"\<And>(y::('Y::complete_lattice)). y \<le> (f (?g y))"
  proof-
    fix y::"'Y::complete_lattice"
    have B20:"?g y =  SupUn {x. y \<le> (f x)}"
      by (simp add: join_dual_partner_def)
    have B21:"f (?g y) = InfUn (f`{x. (f x) \<ge> y})"
      using B20 assms is_join_dual_def by auto
    have B22:"y \<in> lb_set (f`{x. (f x) \<ge> y})"
      by (simp add: imp_in_lower_bounds)
    have B23:"y \<le>  InfUn (f`{x. (f x) \<ge> y})"
      by (metis B22 complete_lattice_inf_exists lb_set_mem_iff le_Inf_iff)
    show "y \<le> (f (?g y))"
      by (simp add: B21 B23)
  qed
  have B3:"\<forall>(x::('X::complete_lattice)). x \<le> (?g (f x))"
  proof
    fix x::"'X::complete_lattice"
    show "x \<le> (?g (f x))"
      by (metis (mono_tags) Sup_upper complete_lattice_sup_exists join_dual_partner_def mem_Collect_eq order_refl)
  qed
  have B4:"(comp_extensive f ?g)"
    by (simp add: B2 B3 comp_extensive_def)
  have B5:"(antitone f) \<and> (antitone ?g)"
    by (simp add: B0 B1 antitone_def)
  show ?thesis
    by (simp add: B4 B5 is_gc2_def)
qed
      
lemma relation_to_gc2:
  "is_gc2 (relation_to_fgc R) (relation_to_ggc R)"
  by (simp add: antitone_def comp_extensive_def is_gc2_def relation_to_fgc_def relation_to_ggc_def subset_eq)

lemma gc2_to_relation1:
  assumes "is_gc2 f g"
  shows "fgc_to_relation f = ggc_to_relation g"
proof-
  have B0:"\<forall>x. \<forall>y. x \<in> (g {y}) \<longrightarrow> y \<in> (f {x})"
    by (meson assms empty_subsetI gc2_iff_gc4 insert_subset is_gc4_def)
  have B1:"\<forall>x. \<forall>y. y \<in> (f {x}) \<longrightarrow> x \<in> (g {y})"
    by (meson assms empty_subsetI gc2_iff_gc4 insert_subset is_gc4_def)
  have B2:"\<forall>x. \<forall>y. y \<in> (f {x}) \<longleftrightarrow>  x \<in> (g {y})"
     using B0 B1 by blast
  have B3:"\<forall>x. \<forall>y. (x, y) \<in>(fgc_to_relation f) \<longleftrightarrow> (x, y) \<in> (ggc_to_relation g)"
    by (simp add: B2 fgc_to_relation_def ggc_to_relation_def)
  show ?thesis
    by (simp add: B3 set_eq_iff)
qed

lemma gc2_to_relation2:
  fixes f::"'a set \<Rightarrow> 'b set" and
        g::"'b set \<Rightarrow> 'a set"
  assumes A0:"is_gc2 f g"
  shows "(relation_to_fgc (fgc_to_relation f)) = f"
proof-
  let ?Rf="fgc_to_relation f"
  let ?f1="relation_to_fgc ?Rf"
  have B0:"is_join_dual f"
    using assms gc2_imp_join_dual by auto
  have B11:"\<And>A y. {y} \<subseteq> ?f1(A) \<longleftrightarrow> (\<forall>a \<in> A. (a, y) \<in> ?Rf)"
    by (simp add: relation_to_fgc_def)
  have B12:"\<And>A y. y \<in> ?f1(A) \<longleftrightarrow> (\<forall>a \<in> A. y \<in> (f {a}))"
    by (simp add: fgc_to_relation_def relation_to_fgc_def)
  have B13:"\<And>A y. {y} \<subseteq> ?f1(A) \<longleftrightarrow> (\<forall>a \<in> A. {y} \<subseteq> (f {a}))"
    by (simp add: B12)
  have B14:"\<And>A y.{y} \<subseteq> ?f1(A) \<longleftrightarrow> ({y} \<subseteq> (\<Inter>a \<in> A. f {a}))"
    by (simp add: B12)
  have B15:"\<forall>A. (\<Inter>a \<in> A. f {a}) = (f (\<Union>a \<in> A. {a}))"
    proof
      fix A::"'a set"
      let ?L="(\<Inter>a \<in> A. f {a})" and ?R="(f (\<Union>a \<in> A. {a}))"
      let ?fA="{y. \<exists>a \<in> A. y = f {a}}"
      let ?sA="{y. \<exists>a \<in> A. y={a}}"
      have B150:"?L=Inf ?fA"
        by (simp add: image_def)
      have B151:"... = InfUn ?fA"
        by (simp add: complete_lattice_inf_exists)
      have B152:"?R= f (Sup ?sA)"
        by (simp add: image_def)
      have B153:"... = f (SupUn ?sA)"
        by (simp add: complete_lattice_sup_exists)
      have B54:"?L=   f (Sup ?sA)"
        by (metis (no_types) B0 INT_extend_simps(10) complete_lattice_inf_exists 
            complete_lattice_sup_exists image_def is_join_dual_def)
      have LR:"?L = ?R"
        using B152 B54 by blast
      show "(\<Inter>a \<in> A. f {a}) = (f (\<Union>a \<in> A. {a}))"
        using LR by auto
    qed
  have B16:"\<And>A y. {y} \<subseteq> ?f1(A) \<longleftrightarrow> ({y} \<subseteq> (f (\<Union>a \<in> A. {a})))"
    using B14 B15 by force
  have B17:"\<And>A y. {y} \<subseteq> ?f1(A) \<longleftrightarrow> {y} \<subseteq> (f A)"
    using B16 by auto
  have B18:"\<And>A y. y \<in> ?f1(A) \<longleftrightarrow> y \<in> (f A)"
    using B17 by auto
  have B19:"\<And>A.   ?f1(A) = (f A)"
    by (simp add: B18 set_eq_iff)
  show ?thesis
    using B19 by auto
qed

lemma gc2_to_relation3:
  "fgc_to_relation (relation_to_fgc R) = R"
proof-
  let ?f1="relation_to_fgc R"
  let ?R1="fgc_to_relation ?f1"
  have LtR:"\<And>x y. (x, y) \<in> ?R1 \<longrightarrow> (x, y) \<in> R"
  proof
    fix x y assume A0:"(x, y) \<in> ?R1"
    have B0:"y \<in> ?f1({x})"
      by (metis (no_types, lifting) A0 CollectD Pair_inject case_prodE fgc_to_relation_def)
    show "(x, y) \<in> R"
      by (metis (no_types, lifting) B0 CollectD relation_to_fgc_def singletonI)
  qed
  have RtL:"\<And>x y. (x, y) \<in> R \<longrightarrow> (x, y) \<in> ?R1"
  proof
    fix x y assume A0:"(x, y) \<in>R"
    show "(x, y) \<in> ?R1"
      by (simp add: A0 fgc_to_relation_def relation_to_fgc_def)
  qed
  show ?thesis
    using LtR RtL by auto
qed

lemma gc_double_comp:
  fixes f::"'a::order \<Rightarrow> 'b::order" and g::"'b::order \<Rightarrow> 'a::order"
  assumes A0:"is_gc2 f g"
  shows "(f \<circ> g \<circ> f = f) \<and> (g \<circ> f \<circ> g = g)"
proof-
  have B0:"\<forall>x. (f x) \<le> f ( g (f (x)))"
    by (meson assms comp_extensive_def is_gc2_def)
  have B1:"\<forall>x. x \<le> g (f (x))"
    using A0 comp_extensive_def is_gc2_def by blast
  have B2:"\<forall>x. f ( g (f (x))) \<le> (f x)"
    using B1 antitone_def assms is_gc2_def by blast
  have B3:"\<forall>x. (f x) = f ( g (f (x)))"
    by (simp add: B0 B2 order_antisym)
  have B4:"\<forall>y. (g y) \<le> g ( f (g (y)))"
    using A0 gc2_iff_gc4 is_gc4_def by blast
  have B5:"\<forall>y. y \<le> f (g (y))"
    using A0 comp_extensive_def is_gc2_def by blast
  have B6:"\<forall>y. g ( f (g (y))) \<le> (g y)"
    using B5 antitone_def assms is_gc2_def by blast
  have B7:"\<forall>y. (g y) = g ( f (g (y)))"
    by (simp add: B4 B6 order_antisym)
  show ?thesis
    using B3 B7 by fastforce
qed

lemma gc_composed_idempotent1:
  fixes f::"'a::order \<Rightarrow> 'b::order" and g::"'b::order \<Rightarrow> 'a::order"
  assumes A0:"is_gc2 f g"
  shows "(f \<circ> g) \<circ> (f \<circ> g) = (f \<circ> g)"
  by (simp add: assms fun.map_comp gc_double_comp)

lemma gc_composed_idempotent2:
  fixes f::"'a::order \<Rightarrow> 'b::order" and g::"'b::order \<Rightarrow> 'a::order"
  assumes A0:"is_gc2 f g"
  shows "(g \<circ> f) \<circ> (g \<circ> f) = (g \<circ> f)"
  by (simp add: assms gc_double_comp o_assoc)


lemma idempotent_req:
  assumes "f \<circ> f = f"
  shows "is_idempotent f"
  by (metis assms comp_apply is_idempotent_def)

lemma gc_closure:
  fixes f::"'a::order \<Rightarrow> 'b::order" and g::"'b::order \<Rightarrow> 'a::order"
  assumes A0:"is_gc2 f g"
  shows "is_closure (f \<circ> g) \<and> is_closure (g \<circ> f)"
proof-
  let ?h1="f \<circ> g" and ?h2="g \<circ> f"
  have C0:"is_extensive ?h1 \<and> is_extensive ?h2"
    by (metis assms comp_apply comp_extensive_def is_extensive_def is_gc2_def)
  have C1:"is_isotone ?h1 \<and> is_isotone ?h2"
    by (metis (mono_tags, lifting) antitone_def assms comp_apply is_gc2_def is_isotone_def)
  have C20:"?h1 \<circ> ?h1 = ?h1"
    by (simp add: assms gc_composed_idempotent1)
  have C21:"?h2 \<circ> ?h2 = ?h2"
    by (simp add: assms gc_composed_idempotent2)
  have C2:"is_idempotent ?h1 \<and> is_idempotent ?h2"
    by (simp add: C20 C21 idempotent_req)
  show ?thesis
    by (simp add: C0 C1 C2 is_closure_def)
qed

lemma grill_is_galois:
  "is_gc2 grill grill"
  by (simp add: gc2_iff_gc4 is_gc4_def mesh_prop11)
     
section SomeClosures


definition fin_inf_cl::"'a::order set \<Rightarrow> 'a::order set" where
  "fin_inf_cl A \<equiv> {x. \<exists>F \<in> Fpow_ne A. has_inf F \<and> x = InfUn F}"

definition fin_inf_cl_in::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow>  'a::order set" where
  "fin_inf_cl_in A X \<equiv> {x \<in> X. \<exists>F \<in> Fpow A. has_inf_in F X \<and> x = InfIn F X}"

definition arb_sup_cl::"'a::order set \<Rightarrow> 'a::order set" where
  "arb_sup_cl A \<equiv> {x. \<exists>F \<in> Pow A. has_sup F \<and> x = SupUn F}"

definition arb_sup_cl_in::"'a::order set \<Rightarrow>'a::order set \<Rightarrow> 'a::order set" where
  "arb_sup_cl_in A X \<equiv> {x \<in> X. \<exists>F \<in> Pow A. has_sup_in F X \<and> x = SupIn F X}"

definition is_supin_closed::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow>  bool" where
  "is_supin_closed A X \<equiv> (\<forall>B \<in> Pow_ne A. has_sup_in B X \<longrightarrow> SupIn B X \<in> A)"

definition is_infin_closed::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow>  bool" where
  "is_infin_closed A X \<equiv> (\<forall>B \<in> Pow_ne A. has_inf_in B X \<longrightarrow> InfIn B X \<in> A)"

lemma up_closed_supin_closed:
  assumes A0:"is_upclosed_in A X"
  shows "is_supin_closed A X"
  unfolding is_supin_closed_def
proof
  fix B assume A1:"B \<in> Pow_ne A"
  show "has_sup_in B X \<longrightarrow> SupIn B X \<in> A"
  proof
    assume A2:"has_sup_in B X"
    have B0:"\<exists>x \<in> B. x \<in> A \<and> x \<le> SupIn B X"
      using A1 A2 has_sup_in_imp2 by fastforce
   show "SupIn B X \<in> A"
     using A2 B0 assms has_sup_in_in_set is_upclosed_in_def by blast
  qed
qed


lemma down_closed_infin_closed:
  assumes A0:"is_downclosed_in A X"
  shows "is_infin_closed A X"
  unfolding is_infin_closed_def
proof
  fix B assume A1: "B \<in> Pow_ne A"
  show "has_inf_in B X \<longrightarrow> InfIn B X \<in> A"
  proof
    assume A2: "has_inf_in B X"
    have B0: "\<exists>x \<in> B. x \<in> A \<and> InfIn B X \<le> x"
      using A1 A2 has_inf_in_imp2 by fastforce
    show "InfIn B X \<in> A"
      using A2 B0 assms has_inf_in_in_set is_downclosed_in_def by blast
  qed
qed

lemma sup_un_sets:
  "SupUn (A::'a set set) = \<Union>A"
  by (simp add: complete_lattice_sup_exists)

lemma has_sup_un_sets:
  "has_sup (A::'a set set)"
  by (metis UNIV_I bot.extremum complete_lattice_sup_is_sup has_min_iff has_sup_def is_min_imp_has_min is_sup_def ub_set_degenerate)

lemma arb_sup_cl_sets:
  "arb_sup_cl (A::'a set set) = {x. \<exists>F \<in> Pow A. x=\<Union> F }"
  apply(simp add:arb_sup_cl_def)
  by (simp add: has_sup_un_sets sup_un_sets)
  

lemma fin_inf_cl_imp0:
  "\<And>A x. x \<in>  fin_inf_cl A \<Longrightarrow> (\<exists>F \<in>  Fpow_ne A. has_inf F \<and> x = InfUn F)"
  using fin_inf_cl_def by blast

lemma fin_inf_cl_in_imp0:
  "\<And>A X x. x \<in>  fin_inf_cl_in A X \<Longrightarrow> (\<exists>F \<in>  Fpow A. has_inf_in F X \<and> x = InfIn F X)"
  using fin_inf_cl_in_def by blast

lemma arb_sup_cl_imp0:
  "\<And>A x. x \<in>  arb_sup_cl A \<Longrightarrow> (\<exists>F \<in>  Pow A. has_sup F \<and> x = SupUn F)"
  using arb_sup_cl_def by blast

lemma arb_sup_cl_in_imp0:
  "\<And>A X x. x \<in>  arb_sup_cl_in A X \<Longrightarrow> (\<exists>F \<in>  Pow A. has_sup_in F X \<and> x = SupIn F X)"
  using arb_sup_cl_in_def by blast

lemma fin_inf_cl_imp1:
  "\<And>A x. x \<in>  fin_inf_cl A \<Longrightarrow> (\<exists>F. F \<subseteq> A \<and> finite F \<and> F \<noteq> {} \<and> has_inf F \<and>  x = InfUn F)"
  by (metis fin_inf_cl_imp0 fpow_ne_imp)

lemma fin_inf_cl_in_imp1:
  "\<And>A X x. x \<in>  fin_inf_cl_in A X \<Longrightarrow> (\<exists>F. F \<subseteq> A \<and> finite F \<and> has_inf_in F X \<and>  x = InfIn F X)"
   by (metis DiffI fin_inf_cl_in_imp0 finite.emptyI fpow_ne_imp order_bot_class.bot_least singletonD)

lemma arb_sup_cl_imp1:
  "\<And>A x. x \<in>  arb_sup_cl A \<Longrightarrow> (\<exists>F. F \<subseteq> A  \<and> has_sup F \<and> x = SupUn F)"
  using arb_sup_cl_imp0 by auto

lemma arb_sup_cl_in_imp1:
  "\<And>A X x. x \<in>  arb_sup_cl_in A X \<Longrightarrow> (\<exists>F. F \<subseteq> A \<and> has_sup_in F X \<and>  x = SupIn F X)"
  by (meson PowD arb_sup_cl_in_imp0)

lemma arb_sup_cl_in_imp2:
  "\<And>A X x. x \<in>  arb_sup_cl_in A X \<Longrightarrow> x \<in> X"
  using arb_sup_cl_in_def by blast

lemma fin_inf_cl_if1:
  "\<And>A x.  (\<exists>F \<in>  Fpow_ne A. has_inf F \<and> x = InfUn F) \<Longrightarrow> x \<in> fin_inf_cl A"
  by (simp add: fin_inf_cl_def)

lemma fin_inf_cl_in_if1:
  "\<And>A X x.  (\<exists>F \<in>  Fpow A. has_inf_in F X \<and> x = InfIn F X) \<Longrightarrow> x \<in> fin_inf_cl_in A X"
  using fin_inf_cl_in_def has_inf_in_in_set by blast

lemma arb_sup_cl_if1:
  "\<And>A x.  (\<exists>F \<in>  Pow A. has_sup F \<and> x = SupUn F) \<Longrightarrow> x \<in> arb_sup_cl A"
  by (simp add: arb_sup_cl_def)

lemma arb_sup_cl_in_if1:
  "\<And>A X x.  (\<exists>F \<in> Pow A. has_sup_in F X \<and> x = SupIn F X) \<Longrightarrow> x \<in> arb_sup_cl_in A X"
  using arb_sup_cl_in_def has_sup_in_in_set by blast


lemma fin_inf_cl_mem_iff:
  "x \<in> fin_inf_cl A \<longleftrightarrow> (\<exists>F \<in>  Fpow_ne A. has_inf F \<and> x = InfUn F)"
  by (simp add: fin_inf_cl_def)

lemma fin_inf_cl_in_mem_iff:
  "x \<in> fin_inf_cl_in A X \<longleftrightarrow> (\<exists>F \<in>  Fpow A. has_inf_in F X \<and> x = InfIn F X)"
  using fin_inf_cl_in_if1 fin_inf_cl_in_imp0 by blast

lemma  arb_sup_cl_mem_iff:
  "x \<in> arb_sup_cl A \<longleftrightarrow> (\<exists>F \<in>  Pow A. has_sup F \<and> x = SupUn F)"
  by (simp add: arb_sup_cl_def)

lemma arb_sup_cl_in_mem_iff:
  "x \<in> arb_sup_cl_in A X \<longleftrightarrow> (\<exists>F \<in>  Pow A. has_sup_in F X \<and> x = SupIn F X)"
  using arb_sup_cl_in_if1 arb_sup_cl_in_imp0
  by metis


lemma fpow_ne_iso:
  "A \<subseteq> B \<Longrightarrow> Fpow_ne A \<subseteq> Fpow_ne B"
  by (simp add: Diff_mono Fpow_mono)

lemma fpow_iso:
  "A \<subseteq> B \<Longrightarrow> Fpow A \<subseteq> Fpow B"
  by (simp add: Diff_mono Fpow_mono)

lemma fpow_ne_finite_union:
  assumes A0:"EF \<in> Fpow_ne (Fpow_ne A)"
  shows "(\<Union>EF) \<in> Fpow_ne A"
  by (metis DiffD2 Pow_empty Pow_iff assms fpow_ne_equiv fpow_ne_union subset_eq)

lemma fpow_finite_union:
  assumes A0:"EF \<in> Fpow (Fpow A)"
  shows "(\<Union>EF) \<in> Fpow A"
  by (smt (verit, ccfv_threshold) Fpow_def Sup_least assms finite_Union mem_Collect_eq subset_eq)


lemma arb_sup_cl_extensive:
  "A \<subseteq> arb_sup_cl A"
proof
  fix a assume A0:"a \<in> A"
  have B0:"{a} \<in> Pow A \<and> has_sup {a} \<and> a = SupUn {a}"
    by (simp add: A0 has_sup_singleton sup_singleton)
  show "a \<in> arb_sup_cl A"
    using B0 arb_sup_cl_def by blast
qed

lemma fin_inf_cl_extensive:
  "A \<subseteq> fin_inf_cl A"
proof
  fix a assume A0:"a \<in> A"
  have B0:"{a} \<in> Fpow_ne A \<and> has_inf {a} \<and> a = InfUn {a}"
    by (metis A0 fpow_ne_singleton has_inf_singleton inf_singleton)
  show "a \<in> fin_inf_cl A"
    using B0 fin_inf_cl_def by blast
qed


lemma fin_inf_cl_in_range:
  "fin_inf_cl_in A X \<subseteq> X"
  by (simp add: fin_inf_cl_in_def)

lemma arb_sup_cl_in_range:
  "arb_sup_cl_in A X \<subseteq> X"
  by (simp add: arb_sup_cl_in_def)

lemma fin_inf_cl_in_extensive:
  "A \<inter> X \<subseteq> fin_inf_cl_in A X"
proof
  fix a assume A0:"a \<in> A \<inter> X"
  have B0:"{a} \<in> Fpow A \<and> has_inf_in {a} X \<and> a = InfIn {a} X"
    by (metis A0 IntD2 Int_commute fpow_singleton has_infin_singleton2 infin_singleton2)
  show "a \<in> fin_inf_cl_in A X"
    using B0 fin_inf_cl_in_if1 by blast
qed

lemma arb_sup_cl_in_extensive:
  "A \<inter> X \<subseteq> arb_sup_cl_in A X"
proof
  fix a assume A0:"a \<in> A \<inter> X"
  have B0:"{a} \<in> Pow A \<and> has_sup_in {a} X \<and> a = SupIn {a} X"
    by (metis A0 IntD1 IntD2 fpow_ne_equiv fpow_ne_singleton has_supin_singleton2 supin_singleton2)
  show "a \<in> arb_sup_cl_in A X"
    using B0 arb_sup_cl_in_if1 by blast
qed


lemma arb_sup_cl_iso:
  assumes "A \<subseteq> B"
  shows "arb_sup_cl A  \<subseteq> arb_sup_cl B"
proof
  fix a assume A0:"a \<in> arb_sup_cl A"
  obtain F where A1:"F \<in> Pow A \<and> has_sup F \<and> a = SupUn F"
    using A0 arb_sup_cl_imp0 by auto
  have B0:"F \<in> Pow B \<and> has_sup F \<and>  a = SupUn F"
    using A1 assms fpow_ne_iso by blast
  show "a \<in> arb_sup_cl B"
    using B0 arb_sup_cl_def by blast
qed

lemma fin_inf_cl_iso:
  assumes "A \<subseteq> B"
  shows "fin_inf_cl A  \<subseteq> fin_inf_cl B"
proof
  fix a assume A0:"a \<in> fin_inf_cl A"
  obtain F where A1:"F \<in> Fpow_ne A \<and> has_inf F \<and> a = InfUn F"
    using A0 fin_inf_cl_def by auto
  have B0:"F \<in> Fpow_ne B \<and> has_inf F \<and>  a = InfUn F"
    using A1 assms fpow_ne_iso by blast
  show "a \<in> fin_inf_cl B"
    using B0 fin_inf_cl_def by blast
qed

lemma fin_inf_in_cl_iso:
  assumes "A \<subseteq> B"
  shows "fin_inf_cl_in A X  \<subseteq> fin_inf_cl_in B X"
proof
  fix a assume A0:"a \<in> fin_inf_cl_in A X"
  obtain F where A1:"F \<in> Fpow A \<and> has_inf_in F X \<and> a = InfIn F X"
    using A0 fin_inf_cl_in_imp0 by blast
  have B0:"F \<in> Fpow B \<and> has_inf_in F X \<and>  a = InfIn F X"
    using A1 assms fpow_iso by blast
  show "a \<in> fin_inf_cl_in B X"
    using B0 fin_inf_cl_in_if1 by blast
qed

lemma arb_sup_cl_in_iso:
  assumes "A \<subseteq> B"
  shows "arb_sup_cl_in A X  \<subseteq> arb_sup_cl_in B X"
proof
  fix a assume A0:"a \<in> arb_sup_cl_in A X"
  obtain F where A1:"F \<in> Pow A \<and> has_sup_in F X \<and> a = SupIn F X"
    using A0 arb_sup_cl_in_imp0 by blast
  have B0:"F \<in> Pow B \<and> has_sup_in F X \<and>  a = SupIn F X"
    using A1 assms by blast
  show "a \<in> arb_sup_cl_in B X"
    using B0 arb_sup_cl_in_if1 has_sup_in_in_set by blast
qed





(*these got out of hand and are just FUBAR*)
lemma fin_inf_cl_idemp:
    "fin_inf_cl A = fin_inf_cl (fin_inf_cl A)"
proof-
  define C where "C=(fin_inf_cl A)"
  have L:"C \<subseteq> fin_inf_cl C"
    by (simp add: fin_inf_cl_extensive)
  have R:"fin_inf_cl C \<subseteq> C"
  proof
    fix x assume A0:"x \<in> fin_inf_cl C"
    obtain Fx where A1:"Fx \<in> Fpow_ne C \<and> has_inf Fx \<and> x = InfUn Fx"
      using A0 C_def fin_inf_cl_def by blast
    have B0:"\<forall>y. y \<in> Fx \<longrightarrow> (\<exists>Fy \<in> Fpow_ne A. has_inf Fy \<and>  y = InfUn Fy)"
      using A1 C_def fin_inf_cl_def fpow_ne_imp by blast
    (*define Fxy where "Fxy={Fy \<in> Fpow_ne A. has_inf Fy \<and> (\<exists>y \<in> Fx. y = InfUn Fy)}" something something injection*)
    define F where "F=(\<lambda>y. SOME Fy. Fy \<in> Fpow_ne A \<and> has_inf Fy \<and>  y= InfUn Fy)"
    define FFx where "FFx=F`Fx"
    have B1:"\<And>y. y \<in> Fx  \<longrightarrow>  has_inf (F y)" 
    proof
      fix y assume A2:"y \<in> Fx"
      obtain Fy where A3:"Fy \<in> Fpow_ne A \<and> has_inf Fy \<and>  y= InfUn Fy"
        by (meson A2 B0)
      show "has_inf (F y)"
        by (metis (mono_tags, lifting) A3 F_def someI_ex)
     qed
    have B2:"Fx = (InfUn`FFx)"
    proof-
      have B3:"Fx \<subseteq> InfUn`FFx"
      proof
        fix y assume A4:"y \<in> Fx"
        have B4:"(InfUn (F y) = y)"
          by (metis (mono_tags, lifting) A4 B0 F_def someI_ex)
        show "y \<in> (InfUn`FFx)"
          by (metis A4 B4 FFx_def imageI)
      qed
      have B4:"InfUn`FFx \<subseteq> Fx"
        by (metis A1 B3 FFx_def card_seteq dual_order.eq_iff finite_imageI fpow_ne_imp surj_card_le)
      show ?thesis
        using B3 B4 by blast
    qed
   define G where "G=\<Union>FFx"
    have B6:"has_inf (InfUn`FFx)"
      using A1 B2 by blast
    have B7:"InfUn Fx = InfUn(InfUn`FFx)"
      using B2 by blast
    have B8:"... = InfUn(G)"
      by (metis A1 B1 B6 FFx_def fpow_ne_equiv inf_comp_un_ind G_def)
    have B9:"\<And>y. y \<in> Fx  \<longrightarrow> (F y) \<in> Fpow_ne A"
      by (metis (mono_tags, lifting) B0 F_def someI)
    have B10:"\<forall>Fy \<in> FFx. Fy \<in> Fpow_ne A"
      using B9 FFx_def by auto
    have B11:"FFx \<in> Fpow_ne (Fpow_ne A)"
      by (metis A1 B10 FFx_def finite_imageI fpow_ne_equiv fpow_ne_if image_is_empty subsetI)
    define G where "G=\<Union>FFx"
    have B12:"G \<in> Fpow_ne A"
      using B11 G_def fpow_ne_finite_union by auto
    have B13:"has_inf G \<and> x = InfUn G"
      by (metis A1 B1 B6 B7 FFx_def G_def fpow_ne_equiv inf_comp_un_ind)
    show "x \<in> C"
      using B12 B13 C_def fin_inf_cl_if1 by blast
    qed
  show ?thesis
    using C_def L R by force
qed

lemma fin_inf_cl_in_idemp:
    "fin_inf_cl_in A X = fin_inf_cl_in (fin_inf_cl_in A X) X"
proof-
  define C where "C=(fin_inf_cl_in A X)"
  have L:"C \<subseteq> fin_inf_cl_in C X"
    by (metis C_def fin_inf_cl_in_extensive fin_inf_cl_in_range inf.orderE)
  have R:"fin_inf_cl_in C X \<subseteq> C"
  proof
    fix x assume A0:"x \<in> fin_inf_cl_in C X"
    obtain Fx where A1:"Fx \<in> Fpow C \<and> has_inf_in Fx X \<and> x = InfIn Fx X"
      using A0 fin_inf_cl_in_imp0 by blast
    have B0:"\<forall>y. y \<in> Fx \<longrightarrow> (\<exists>Fy \<in> Fpow A. has_inf_in Fy X \<and>  y = InfIn Fy X)"
      using A1 C_def fin_inf_cl_in_imp0 fpow_ne_imp by blast
    define F where "F=(\<lambda>y. SOME Fy. Fy \<in> Fpow A \<and> has_inf_in Fy X \<and>  y= InfIn Fy X)"
    define FFx where "FFx=F`Fx"
    have B1:"\<And>y. y \<in> Fx  \<longrightarrow>  has_inf_in (F y) X" 
    proof
      fix y assume A2:"y \<in> Fx"
      obtain Fy where A3:"Fy \<in> Fpow A \<and> has_inf_in Fy X \<and>  y= InfIn Fy X"
        by (meson A2 B0)
      show "has_inf_in (F y) X"
        by (metis (mono_tags, lifting) A3 F_def someI_ex)
     qed
    define InfX where "InfX \<equiv> (\<lambda>A. InfIn A X)"
    have B2:"Fx = (InfX`FFx)"
    proof-
      have B3:"Fx \<subseteq> InfX`FFx"
      proof
        fix y assume A4:"y \<in> Fx"
        have B4:"(InfIn (F y) X = y)"
        apply(simp add:F_def)
          by (smt (verit, best) A4 B0 someI_ex)
        show "y \<in> (InfX`FFx)"
          by (metis A4 B4 FFx_def InfX_def image_eqI)
      qed
      have B4:"InfX`FFx \<subseteq> Fx"
        by (smt (verit, del_insts) A1 B3 CollectD FFx_def Fpow_def card_image_le card_seteq finite_imageI order.trans)
      show ?thesis
        using B3 B4 by blast
    qed
   define G where "G=\<Union>FFx"
    have B6:"has_inf_in (InfX`FFx) X"
      using A1 B2 by blast
    have B7:"InfIn Fx X  = InfX(InfX`FFx)"
      using B2 InfX_def by blast
    have B8:"... = InfX G"
      apply(simp add:InfX_def)
      by (metis B1 B6 FFx_def G_def InfX_def Union_empty image_cong image_empty inf_in_comp_un_ind)
    have B9:"\<And>y. y \<in> Fx  \<longrightarrow> (F y) \<in> Fpow A"
      by (smt (verit, ccfv_threshold) B0 F_def someI_ex)
    have B10:"\<forall>Fy \<in> FFx. Fy \<in> Fpow A"
      using B9 FFx_def by auto
    have B11:"FFx \<in> Fpow (Fpow A)"
      by (metis (no_types, lifting) A1 B10 FFx_def Fpow_def finite_imageI mem_Collect_eq subsetI)
    have B12:"G \<in> Fpow A"
      by (simp add: B11 G_def fpow_finite_union)
    have B13:"has_inf_in G X \<and> x = InfIn G X"
      by (metis A1 B1 B2 FFx_def G_def InfX_def Union_empty image_cong image_empty inf_in_comp_un_ind)
    show "x \<in> C"
      using B12 B13 C_def fin_inf_cl_in_if1 by blast
    qed
  show ?thesis
    using C_def L R by force
qed




lemma arb_sup_cl_idemp:
    "arb_sup_cl A = arb_sup_cl (arb_sup_cl A)"
proof-
  define C where "C=(arb_sup_cl A)"
  have L:"C \<subseteq> arb_sup_cl C"
    by (simp add: arb_sup_cl_extensive)
  have R:"arb_sup_cl C \<subseteq> C"
  proof
    fix x assume A0:"x \<in> arb_sup_cl C"
    obtain Fx where A1:"Fx \<in> Pow C \<and> has_sup Fx \<and> x = SupUn Fx"
      using A0 arb_sup_cl_imp0 by auto
    have B0:"\<forall>y. y \<in> Fx \<longrightarrow> (\<exists>Fy \<in> Pow A. has_sup Fy \<and>  y = SupUn Fy)"
      using A1 C_def arb_sup_cl_def by blast
    define F where "F=(\<lambda>y. SOME Fy. Fy \<in> Pow A \<and> has_sup Fy \<and>  y= SupUn Fy)"
    have B00:"\<And>x1 x2. x1 \<in> Fx \<and> x2 \<in> Fx  \<and> (SupUn \<circ> F) x1 = (SupUn \<circ> F) x2 \<longrightarrow> x1 =x2"
    proof
      fix x1 x2 assume B00A0:"x1 \<in> Fx \<and> x2 \<in> Fx  \<and> (SupUn \<circ> F) x1 = (SupUn \<circ> F) x2" 
      have B00B0:"(F x1) \<in> Pow A \<and> has_sup (F x1) \<and>  x1 = SupUn (F x1)"
        by (metis (mono_tags, lifting) B0 B00A0 F_def someI)
      have B00B1:"(F x2) \<in> Pow A \<and> has_sup (F x2) \<and>  x2 = SupUn (F x2)"
        by (metis (mono_tags, lifting) B0 B00A0 F_def someI)
      have B00B2:"SupUn (F x1) = SupUn (F x2)"
        using B00A0 by fastforce
      show "x1 = x2"
        using B00B0 B00B1 B00B2 by presburger
    qed
    define FFx where "FFx=F`Fx"
    have B1:"\<And>y. y \<in> Fx  \<longrightarrow>  has_sup (F y)" 
    proof
      fix y assume A2:"y \<in> Fx"
      obtain Fy where A3:"Fy \<in> Pow A \<and> has_sup Fy \<and>  y= SupUn Fy"
        by (meson A2 B0)
      show "has_sup (F y)"
        by (metis (mono_tags, lifting) A3 F_def someI_ex)
     qed
    have B2:"Fx = (SupUn`FFx)"
    proof-
      have B3:"Fx \<subseteq> SupUn`FFx"
      proof
        fix y assume A4:"y \<in> Fx"
        have B4:"(SupUn (F y) = y)"
          by (metis (mono_tags, lifting) A4 B0 F_def someI_ex)
        show "y \<in> (SupUn`FFx)"
          by (metis A4 B4 FFx_def imageI)
      qed
      have B4:"SupUn`FFx \<subseteq> Fx"
      proof
        fix z assume B4A0:"z \<in> SupUn`FFx"
        obtain w where B4A1:"w \<in> Fx \<and> z = (SupUn \<circ> F) w "
          using B4A0 FFx_def by auto
        obtain Fw where B4A2:"Fw = (F w) \<and> w = SupUn Fw \<and> Fw \<in> Pow A \<and> has_sup Fw"
          by (metis (mono_tags, lifting) B0 B4A1 F_def someI_ex)
        have B4B0:"SupUn Fw = SupUn (F w)"
          using B4A2 by force
        have B4B1:"... =  (SupUn \<circ> F) w "
          by simp
        have B4B2:"... = z"
          using B4A1 by force
        show "z \<in> Fx"
          using B4A1 B4A2 by fastforce
      qed
      show ?thesis
        using B3 B4 by blast
    qed
   define G where "G=\<Union>FFx"
    have B6:"has_sup (SupUn`FFx)"
      using A1 B2 by blast
    have B7:"SupUn Fx = SupUn(SupUn`FFx)"
      using B2 by blast
    have B8:"... = SupUn(G)"
      by (metis B1 B6 FFx_def G_def Union_empty image_empty sup_comp_un_ind)
    have B9:"\<And>y. y \<in> Fx  \<longrightarrow> (F y) \<in> Pow A"
      by (metis (mono_tags, lifting) B0 F_def someI)
    have B10:"\<forall>Fy \<in> FFx. Fy \<in> Pow A"
      using B9 FFx_def by auto
    have B11:"FFx \<in> Pow (Pow A)"
      using B10 by blast
    have B12:"G \<in> Pow A"
      using B11 G_def fpow_ne_finite_union by auto
    have B13:"has_sup G \<and> x = SupUn G"
      by (metis A1 B1 B2 FFx_def G_def Sup_empty image_empty sup_comp_un_ind)
    show "x \<in> C"
      using B12 B13 C_def arb_sup_cl_def by blast
    qed
  show ?thesis
    using C_def L R by force
qed

lemma f_inf_cl_idemp2:
  "\<forall>A. fin_inf_cl A = fin_inf_cl (fin_inf_cl A)"
  using fin_inf_cl_idemp by blast

lemma f_inf_cl_in_idemp2:
  "\<forall>A. fin_inf_cl_in A X = fin_inf_cl_in (fin_inf_cl_in A X) X"
  using fin_inf_cl_in_idemp by blast

lemma arb_sup_cl_idemp2:
  "\<forall>A. arb_sup_cl A = arb_sup_cl (arb_sup_cl A)"
  using arb_sup_cl_idemp by blast


lemma arb_sup_cl_idemp3:
  "\<And>E. E \<subseteq> arb_sup_cl (A::'a set set) \<longrightarrow> \<Union>E \<in>  arb_sup_cl A "
proof
   fix E assume A0:"E \<subseteq> arb_sup_cl (A::'a set set)" 
   show" \<Union>E \<in>  arb_sup_cl A"
   by (metis A0 PowI arb_sup_cl_idemp arb_sup_cl_if1 complete_lattice_sup_exists has_sup_un_sets)
qed



lemma fin_inf_cl_is_cl:
  "is_closure fin_inf_cl"
  unfolding is_closure_def
  apply(simp add: is_extensive_def fin_inf_cl_extensive is_isotone_def fin_inf_cl_iso)
  apply(simp add:is_idempotent_def)
  using f_inf_cl_idemp2 by blast


lemma arb_sup_cl_is_cl:
  "is_closure arb_sup_cl"
  unfolding is_closure_def
  apply(simp add: is_extensive_def arb_sup_cl_extensive is_isotone_def arb_sup_cl_iso)
  apply(simp add:is_idempotent_def)
  using arb_sup_cl_idemp2 by blast

lemma fin_inf_cl_in_top:
  "X \<in> fin_inf_cl_in A (Pow X)"
proof-
  have B0:"{} \<in> Fpow A"
    by (simp add: empty_in_Fpow)
  have B1:"(InfIn {} (Pow X)) = X"
    by (simp add: empty_inter_is_carrier)
   have B2:"has_inf_in {} (Pow X)"
     by (metis Pow_top Sup_upper Union_Pow_eq has_inf_in_def has_max_iff lb_set_in_degenerate)
    show ?thesis
      using B0 B1 B2 fin_inf_cl_in_if1 by blast
qed

lemma comp_extensive:
  fixes f1 f2::"'a::order \<Rightarrow> 'a::order" 
  assumes "is_extensive f1 \<and> is_extensive f2"
  shows " is_extensive (f1 \<circ> f2)"
  by (metis assms comp_apply is_extensive_def order_trans)

lemma comp_isotone:
  fixes f1 f2::"'a::order \<Rightarrow> 'a::order" 
  assumes "is_isotone f1 \<and> is_isotone f2"
  shows " is_isotone (f1 \<circ> f2)"
  by (metis assms comp_apply is_isotone_def)

section Topology

definition top_u1::"'a set set \<Rightarrow> bool" where
  "top_u1 T \<equiv> (\<forall>E. E \<subseteq> T \<longrightarrow> \<Union>E \<in> T )"

(*top_i1 cannot work for the local definition as \<Inter>\<emptyset> is interpreted as InfIn \<emptyset> UNIV = UNIV so 
  thats one choice out of the way
*)
(*
the topology is identified with the set of open sets so thats...a choice...im not sure if its the 
right one but oh well.  
*)

(*
so being a subset of the carrier subset is NOT baked into the type info so this has to be manually
added as an assumption very often
*)

definition top_i1::"'a set set \<Rightarrow> bool" where
  "top_i1 T \<equiv> (\<forall>E. (finite E \<and> E \<subseteq> T) \<longrightarrow> \<Inter>E \<in> T )"

definition top_i2::"'a set set \<Rightarrow> bool" where
  "top_i2 T \<equiv> (\<forall>E. (finite E \<and> E \<subseteq> T \<and> E \<noteq> {}) \<longrightarrow> \<Inter>E \<in> T )"

definition top_i3::"'a set set \<Rightarrow> bool" where
  "top_i3 T \<equiv> (\<forall>a1 a2. (a1 \<in> T \<and> a2 \<in> T) \<longrightarrow> a1 \<inter> a2 \<in> T)"

definition is_base1_for_topology::"'a set set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "is_base1_for_topology B T \<equiv> B \<subseteq> T \<and> (\<forall>U \<in>T.  (\<exists>E \<in> Pow B. U=\<Union>E))"

definition is_base2_for_topology::"'a set set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "is_base2_for_topology B T \<equiv> (B \<subseteq> T) \<and> (\<forall>U \<in> T. \<forall>x \<in> U. \<exists>B \<in> B. (x \<in> B \<and> B \<subseteq> U))"

definition is_base_3_covering::"'a set set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_base_3_covering B X \<equiv>   (B \<in> Dpow X) \<and> (\<forall>x \<in> X. \<exists>U \<in> B. x \<in> U)"

definition is_base_3_intercont::"'a set set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_base_3_intercont B X \<equiv> (\<forall>U1  U2. U1 \<in> B \<and> U2 \<in> B \<longrightarrow> (\<forall>x \<in> U1 \<inter> U2. \<exists> U3\<in> B. x \<in> U3 \<and> U3 \<subseteq> U1 \<inter> U2))"

definition is_base3_for_topology::"'a set set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_base3_for_topology B X \<equiv> is_base_3_covering B X \<and> is_base_3_intercont B X"


definition basis_element_int_npt::"'a set set \<Rightarrow> 'a set \<Rightarrow> ('a set \<Rightarrow> 'a set \<Rightarrow> 'a  \<Rightarrow> 'a set)" where
  "basis_element_int_npt B X \<equiv>  \<lambda>U1 U2 x. SOME U3. x \<in> U3 \<and> U3 \<subseteq> U1 \<inter> U2 \<and>  U3 \<in> B"

definition basis_element_npt::"'a set set \<Rightarrow>  ('a set \<Rightarrow> 'a  \<Rightarrow> 'a set)" where
  "basis_element_npt B \<equiv>  \<lambda>U x. SOME B3. (x \<in> B3) \<and> (B3 \<subseteq> U) \<and>  (B3 \<in> B)"

definition basis_element_pt::"'a set set \<Rightarrow> 'a set \<Rightarrow> ('a  \<Rightarrow> 'a set)" where
  "basis_element_pt B X \<equiv>  \<lambda>x. SOME B3. x \<in> B3 \<and>  B3 \<in> B"


definition is_nhood_system_in::"('a \<Rightarrow> 'a set set) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_nhood_system_in N X \<equiv> (\<forall>x \<in> X. is_pfilter_in (N x) (Pow X) \<and>
                             (\<forall>V \<in> N x. x \<in> V \<and> 
                               (\<exists>W \<in> N x. (\<forall>y \<in> W. V \<in> N y))))"

lemma pfilter_in_powerset_simp:
  assumes "is_pfilter_in F (Pow X)"
  shows "\<forall>f \<in> F. f \<le> X"
  using assms is_filter_in_imp is_pfilter_in_def by auto

definition is_topology_on::"'a set set \<Rightarrow> 'a set \<Rightarrow> bool" where
   "is_topology_on T X \<equiv> (T \<in> Dpow X) \<and> (top_u1 T) \<and> (top_i3 T) \<and> (X \<in> T)"


definition top_from_nhoods::"('a \<Rightarrow> 'a set set) \<Rightarrow> 'a set \<Rightarrow> 'a set set" where
  "top_from_nhoods N X \<equiv> {V \<in> Pow X. (\<forall>x \<in> V. V \<in> N x)}"

definition nhoods_of::"'a \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> 'a set set" where
  "nhoods_of x T X \<equiv> {V.  (\<exists>U. U \<in> T \<and> x \<in> U \<and> U \<subseteq> V)}"

definition nhoods_of_in::"'a \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> 'a set set" where
  "nhoods_of_in x T X \<equiv> {V. V \<subseteq> X \<and> (\<exists>U. U \<in> T \<and> x \<in> U \<and> U \<subseteq> V)}"

definition topologies_on::"'a set \<Rightarrow> 'a set set set" where
  "topologies_on X \<equiv> {T. is_topology_on T X}"

definition finer_topologies::"'a set set \<Rightarrow> 'a set \<Rightarrow> 'a set set set" where
  "finer_topologies E X \<equiv> {T. is_topology_on T X \<and> E \<subseteq> T}"

definition topology_generated_in::"'a set set \<Rightarrow> 'a set \<Rightarrow> 'a set set" where
  "topology_generated_in E X \<equiv> (SupIn {E} (topologies_on X))"


definition topology_generated_by_in::"'a set set \<Rightarrow> 'a set \<Rightarrow> 'a set set" where
  "topology_generated_by_in E X \<equiv> \<Inter>(finer_topologies E X)"


definition top_sup1::"'a set set set \<Rightarrow>'a set \<Rightarrow> 'a set set" where
  "top_sup1 ET X \<equiv> topology_generated_in (\<Union>ET) X"

definition top_sup2::"'a set set set \<Rightarrow>'a set \<Rightarrow> 'a set set" where
  "top_sup2 ET X \<equiv> (\<Inter>{T. is_topology_on T X \<and> (\<Union>ET) \<subseteq> T})"


definition nhoods_from_top::"'a set set \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'a set set)" where
  "nhoods_from_top T X \<equiv> (\<lambda>x. if x \<in> X then {V \<in> Pow X. \<exists>U \<in> T. x \<in> U \<and> U \<subseteq> V} else undefined)"

definition nhood_base_from_base::"'a set set \<Rightarrow> 'a set \<Rightarrow>  ('a \<Rightarrow> 'a set set)" where
  "nhood_base_from_base B X \<equiv> (\<lambda>x. if x \<in> X then {Bx \<in> B. x \<in> Bx} else undefined)"

definition is_nhood_base::"('a \<Rightarrow> 'a set set) \<Rightarrow> ('a \<Rightarrow> 'a set set) \<Rightarrow> 'a set \<Rightarrow> bool" where
    "is_nhood_base B N X \<equiv>  (\<forall>x \<in> X. \<forall>V \<in> N x. \<exists>b\<in> B x.  x \<in> b \<and> b \<subseteq> V)"

definition cofinite_sets_in::"'a set \<Rightarrow> 'a set set" where
  "cofinite_sets_in X \<equiv> {U. U \<in> Pow X \<and>  (finite (X - U) \<or> U={})}"

definition cocountable_sets_in::"'a set \<Rightarrow> 'a set set" where
  "cocountable_sets_in X \<equiv> {U. U \<in> Pow X \<and>  (is_countable (X - U) \<or> U={})}"

definition particular_point_top::"'a \<Rightarrow> 'a set \<Rightarrow> 'a set set" where
  "particular_point_top a X \<equiv> {U. U \<in> Pow X \<and>  ((a \<in> U) \<or> U={})}"

definition excluded_point_top::"'a \<Rightarrow> 'a set \<Rightarrow> 'a set set" where
  "excluded_point_top a X \<equiv> {U. U \<in> Pow X \<and>  a \<notin>  U \<or> U=X}"

definition is_limit_point::"'a  \<Rightarrow> 'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_limit_point x A T X \<equiv> (\<forall>V. V \<in>  nhoods_of_in x T X \<longrightarrow> A \<inter> (V - {x}) \<noteq> {})"

definition limit_points::"'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "limit_points A T X \<equiv> {x \<in> X. is_limit_point x A T X}"

definition is_adherent_point::"'a \<Rightarrow> 'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_adherent_point x A T X \<equiv> (\<forall>V. V \<in> nhoods_of_in x T X \<longrightarrow> A \<inter> V \<noteq> {})"

definition adherent_points::"'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "adherent_points A T X \<equiv> {x \<in> X. is_adherent_point x A T X}"

definition is_isolated_point::"'a \<Rightarrow> 'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_isolated_point x A T X \<equiv> (\<exists>V. V \<in> nhoods_of_in x T X \<and> V \<inter> A = {x})"

definition is_interior_point::"'a \<Rightarrow> 'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_interior_point x A T X \<equiv> (A \<in> nhoods_of_in x T X)"

definition smaller_open_sets::"'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> 'a set set" where
  "smaller_open_sets E T X \<equiv> {U \<in> T. U \<subseteq> E}"

definition larger_closed_sets::"'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> 'a set set" where
  "larger_closed_sets E T X \<equiv> {F \<in> Pow X. (X - F) \<in> T \<and> E \<subseteq> F}"

definition interior1::"'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "interior1 E T X \<equiv> \<Union>{U \<in> T. U \<subseteq> E}"

definition closure1::"'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "closure1 E T X \<equiv> \<Inter>{F. F \<subseteq> X \<and> (X-F) \<in> T \<and> E \<subseteq> F}"

definition interior2::"'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "interior2 E T X \<equiv> {x \<in> X. is_interior_point x E T X}"

definition closure2::"'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "closure2 E T X \<equiv> {x \<in> X. is_adherent_point x E T X}"

definition continuous_at::"('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> 'b set set \<Rightarrow> 'b set \<Rightarrow> bool" where
  "continuous_at f x T X S Y \<equiv> (\<forall>V \<in> nhoods_of (f x) S Y. \<exists>U \<in> nhoods_of x T X. f`U \<le> V)"

lemma top_u1_imp_contains_empty:
  "\<And>T. top_u1 T \<Longrightarrow> {} \<in> T"
  by (metis Sup_empty empty_subsetI top_u1_def)

lemma top_i1_imp_contains_carrier:
  "\<And>T. top_i1 T \<Longrightarrow> UNIV \<in> T"
  using top_i1_def by force


lemma top_i3_induct:
  assumes A0:"top_i3 T" and A1:"finite E" and A2:"E \<noteq> {}" and A3:"E \<subseteq> T"
  shows "(\<Inter>E) \<in> T"
  using A1 A2 A3 
proof (induct E rule: finite_ne_induct)
  case (singleton x)
  then show ?case
    by simp 
next
  case (insert x F)
  then show ?case
    using A0 top_i3_def by auto
qed

lemma top_i3_finite_ne:
  assumes "top_i3 T"
  shows "\<And>E. E \<in> Fpow_ne T \<Longrightarrow> (\<Inter>E) \<in> T"
  by (simp add: Fpow_def assms top_i3_induct)

lemma top_i3_i2:
  "top_i3 T \<Longrightarrow> top_i2 T"
  by (simp add: top_i2_def top_i3_induct)


lemma trivial_in_top:
  "is_topology_on T X \<Longrightarrow> ({} \<in> T) \<and> (X \<in> T)"
  by (simp add: is_topology_on_def top_u1_imp_contains_empty)

lemma carrier_is_top_un:
  "is_topology_on T X \<Longrightarrow> \<Union>T = X"
  by (meson Pow_iff cSup_eq_maximum is_topology_on_def subsetD)

lemma trivial_top:
  fixes X::"'a set"
  shows "is_topology_on {{}, X} X"
proof-
  define T where "T= {{}, X}"
  have T0:"T \<in> Dpow X"
    by (simp add: T_def)
  have T1:"top_u1 T"
    using T_def top_u1_def by fastforce
  have T2:"top_i3 T"
    using T_def top_i3_def by fastforce
  have T3:"X \<in> T"
    by (simp add: T_def)
  show ?thesis
    using T1 T2 T_def is_topology_on_def by auto
qed

lemma discrete_top:
  fixes X::"'a set"
  shows "is_topology_on (Pow X) X"
proof-
  define T where "T=Pow X"
  have T0:"T \<in> Dpow X"
    by (simp add: T_def)
  have T1:"top_u1 T"
    using T_def top_u1_def by fastforce
  have T2:"top_i3 T"
    using T_def top_i3_def by fastforce
  have T3:"X \<in> T"
    by (simp add: T_def)
  show ?thesis
    using T1 T2 T_def is_topology_on_def by auto
qed


lemma trivial_is_top:
  "{{}, X} \<in> (topologies_on X)"
  by (simp add: topologies_on_def trivial_top)

lemma discrete_is_top:
  "Pow X\<in> (topologies_on X)"
  by (simp add: discrete_top topologies_on_def)

lemma discrete_greater:
  "\<And>T. T \<in> topologies_on X \<Longrightarrow> T \<le> (Pow X)"
  by (simp add: is_topology_on_def topologies_on_def)

lemma trivial_least:
  "\<And>T. T \<in> topologies_on X \<Longrightarrow> T \<ge> {{} ,X}"
  by (simp add: topologies_on_def trivial_in_top)

lemma topologies_top:
  "is_min {{}, X} (topologies_on X)"
  by (metis is_min_iff trivial_is_top trivial_least)

lemma topologies_bot:
  "is_max (Pow X) (topologies_on X)"
  by (simp add: discrete_greater discrete_is_top is_max_iff)

lemma topologies_inf_closed:
  assumes A0:"ET \<noteq> {}" and A1:"\<forall>T \<in> ET. T \<in> topologies_on X"
  shows  "(\<Inter>ET) \<in> topologies_on X \<and> is_inf_in (\<Inter>ET) ET (topologies_on X)"
 proof-
  have B0:"\<forall>T \<in> ET. is_topology_on T X"
    using A1 topologies_on_def by fastforce
  have B1:"\<forall>T \<in> ET. top_u1 T \<and> top_i3 T \<and> X \<in> T"
    using B0 is_topology_on_def by blast
  define I where  "I=(\<Inter>ET)"
  have T0:"I \<in> Dpow X"
    by (simp add: A0 A1 I_def Inf_less_eq discrete_greater)
  have T1:"top_u1 I"
  proof-
    have T13:"\<And>E. E \<subseteq> I \<longrightarrow> \<Union>E \<in> I"
    proof
      fix E assume A2:"E \<subseteq> I"
      have T10:"\<forall>x. x \<in> E \<longrightarrow> (\<forall>T \<in> ET. x \<in> T) "
        using A2 I_def by auto
      have T11:"(\<forall>T \<in> ET. E \<subseteq> T) "
        using T10 by blast
      have T12:"(\<forall>T \<in> ET. (\<Union>E) \<in> T)"
        by (meson B1 T11 top_u1_def)
      show "\<Union>E \<in> I"
        using I_def T12 by fastforce
    qed
    show ?thesis
      by (simp add: T13 top_u1_def)
  qed
  have T2:"top_i3 I"
  proof-
    have T13:"\<And>a1 a2. (a1 \<in> I \<and> a2 \<in> I) \<longrightarrow> a1 \<inter> a2 \<in> I"
    proof
      fix a1 a2  assume T13A0:"(a1 \<in> I \<and> a2 \<in> I) "
      have T13B0:"\<forall>T \<in> ET. a1 \<in> T \<and> a2 \<in> T"
        using I_def T13A0 by blast
      have T13B1:"\<forall>T \<in> ET. a1 \<inter> a2 \<in> T"
        by (meson B1 T13B0 top_i3_def)
      show "a1 \<inter> a2 \<in> I"
        by (simp add: I_def T13B1)
    qed
    show ?thesis
      by (simp add: T13 top_i3_def)
  qed
  have T3:"X \<in> I"
    by (simp add: B1 I_def)
  have B3:"I \<in> topologies_on X"
    by (metis T0 T1 T2 T3 is_topology_on_def mem_Collect_eq topologies_on_def)
  have B4:"\<forall>T. T \<in> ET \<longrightarrow> I \<le> T"
    by (simp add: I_def Inter_lower)
  have B5:"\<And>S. (\<And>T. T \<in> ET \<Longrightarrow> S\<le> T) \<Longrightarrow> S \<le> I"
    by (simp add: I_def Inter_greatest)
  have B6:"is_inf_in I ET (topologies_on X)"
    by (simp add: B3 B4 B5 is_inf_in_if3)
  show ?thesis
    using B3 B6 I_def by blast
qed

lemma generated_topology1:
  fixes E::"'a set set" and  X::"'a set"
  defines "T \<equiv> topology_generated_by_in E X"
  shows "X \<in> T"
  apply(simp add:T_def topology_generated_by_in_def finer_topologies_def)
  using is_topology_on_def by blast

lemma in_finer_top_imp:
  "Ea \<subseteq> \<Inter>(finer_topologies E X) \<Longrightarrow> T \<in> finer_topologies E X \<Longrightarrow> Ea \<subseteq> T"
  by (simp add: le_Inf_iff)

lemma in_finer_top_imp1:
  "T \<in> finer_topologies E X \<Longrightarrow> is_topology_on T X \<and> (E \<subseteq> T)"
  by (simp add: finer_topologies_def)

lemma in_finer_top_imp2:
  "T \<in> finer_topologies E X \<Longrightarrow> T \<in> Dpow X"
  by (simp add: finer_topologies_def is_topology_on_def)

lemma in_iner_top_imp3:
  "\<And>x. x \<in> \<Inter>(finer_topologies E X) \<Longrightarrow> (\<And>S. S \<in> (finer_topologies E X) \<Longrightarrow> x \<in> S)"
  using InterE by blast

lemma generated_topology2:
  fixes E::"'a set set" and  X::"'a set"
  defines "T \<equiv> topology_generated_by_in E X"
  shows "top_u1 T"
  apply(auto simp add:T_def topology_generated_by_in_def top_u1_def)
proof-
  let ?F="(finer_topologies E X)"
  fix Ea Xa::"'a set set" assume A0:"Ea \<subseteq> \<Inter>?F" assume A1:"Xa \<in> ?F"
  have B0:"Ea \<subseteq> Xa"
    using A0 A1 by blast
  have B1:"top_u1 Xa"
    using A1 in_finer_top_imp1 is_topology_on_def by blast
  show "\<Union>Ea \<in> Xa"
    using B0 B1 top_u1_def by blast
qed

lemma generated_topology3:
  fixes Xa E::"'a set set" and  a1 a2 X::"'a set"
  defines "T \<equiv> topology_generated_by_in E X"
  assumes A0:"\<And>S. S \<in> (finer_topologies E X) \<Longrightarrow> (a1 \<in> S \<and> a2 \<in> S)" and A1:"Xa \<in> (finer_topologies E X)"
  shows "a1 \<inter> a2 \<in> Xa"
proof-
  have B0:"\<And>S. S \<in> (finer_topologies E X) \<longrightarrow> (a1 \<inter> a2 \<in> S)"
    by (meson assms(2) in_finer_top_imp1 is_topology_on_def top_i3_def)
  show ?thesis
    using A1 B0 by blast
qed


lemma generated_topology4:
  fixes E::"'a set set" and  X::"'a set"
  defines "T \<equiv> topology_generated_by_in E X"
  shows "top_i3 T"
  apply(auto simp add:T_def topology_generated_by_in_def top_i3_def)
  by (meson in_finer_top_imp1 is_topology_on_def top_i3_def)

lemma generated_topology5:
  fixes E::"'a set set" and X::"'a set"
  defines "T \<equiv> topology_generated_by_in E X"
  assumes A1:"(finer_topologies E X) \<noteq> {}"
  shows "T \<in> Dpow X"
  apply(auto simp add:T_def topology_generated_by_in_def)
  by (metis A1 DiffI Diff_eq_empty_iff Union_Pow_eq Union_upper empty_iff equals0I in_finer_top_imp1 is_topology_on_def)


lemma generated_topology6:
  fixes E::"'a set set" and X::"'a set"
  defines "T \<equiv> topology_generated_by_in E X"
  assumes "E \<in> Dpow X"
  shows A1:"(finer_topologies E X) \<noteq> {}"
  using assms(2) discrete_top finer_topologies_def by fastforce

lemma generated_topology_is_topology:
  assumes A0:"E \<in> Dpow X"
  shows "is_topology_on (topology_generated_by_in E X) X"
  apply(simp add:is_topology_on_def)
  by (meson PowD assms generated_topology1 generated_topology2 generated_topology4 generated_topology5 generated_topology6)

lemma generated_topology_upper0:
  assumes A0:"E \<in> Dpow X"
  defines "T \<equiv> (topology_generated_by_in E X) "
  shows "E \<subseteq> T"
  apply(auto simp add: T_def)
  by (metis in_finer_top_imp1 le_Inf_iff subsetD topology_generated_by_in_def)

lemma generated_topology_upper1:
  assumes A0:"E \<in> Dpow X"
  defines "T \<equiv> (topology_generated_by_in E X) "
  shows "\<And>Ei. Ei \<in> {E}  \<Longrightarrow> E \<le> T"
  using A0 T_def generated_topology_upper0 by blast


lemma generated_topology_least1:
  assumes A0:"E \<in> Dpow X"
  defines "T \<equiv> (topology_generated_by_in E X) "
  assumes A0:"is_topology_on S X" and A1:"E \<subseteq> S"
  shows "T \<subseteq> S"
  by (auto simp add: T_def A0 finer_topologies_def local.A1 topology_generated_by_in_def)

lemma generated_topology_least2:
  assumes A0:"E \<in> Dpow X"
  defines "T \<equiv> (topology_generated_by_in E X) "
  shows "\<And>S. S \<in> topologies_on X \<and> E \<le> S \<Longrightarrow> T \<le> S"
  by (metis A0 T_def generated_topology_least1 mem_Collect_eq topologies_on_def)


lemma generated_topology_is_sup_in:
  assumes A0:"E \<in> Dpow X"
  defines "T \<equiv> (topology_generated_by_in E X) "
  shows "has_sup_in {E} (topologies_on X) \<and> is_sup_in T {E} (topologies_on X)"
  proof-
    have B0:"T \<in> ub_set_in {E} (topologies_on X)"
      by (metis A0 CollectI T_def generated_topology_is_topology generated_topology_upper0 singletonD topologies_on_def ub_set_in_elm)
    have B1:"\<And>S. S \<in> ub_set_in {E} (topologies_on X) \<Longrightarrow> T \<le> S"
      by (metis A0 T_def generated_topology_least2 singletonI ub_set_in_mem)
    have B2:"is_sup_in T {E} (topologies_on X)"
      by (simp add: B0 B1 is_min_iff is_sup_in_def)
    have B3:"has_sup_in {E} (topologies_on X)"
      by (meson B0 B1 has_min_iff has_sup_in_def)
    show ?thesis
      by (simp add: B2 B3)
qed

lemma generated_topology_is_sup_in2:
 assumes A0:"E \<in> Dpow X"
 shows  "(topology_generated_by_in E X) = (topology_generated_in E X)"
  by (metis assms generated_topology_is_sup_in is_sup_in_sup_eq topology_generated_in_def)


lemma topologies_sup_closed:
  assumes A0:"ET \<noteq> {}" and A1:"\<forall>T \<in> ET. T \<in> topologies_on X"
  shows "(\<Inter>{T. is_topology_on T X \<and> (\<Union>ET) \<subseteq> T}) \<in> topologies_on X \<and>
         (is_sup_in (\<Inter>{T. is_topology_on T X \<and> (\<Union>ET) \<subseteq> T}) ET (topologies_on X)) "
proof-
  define U where "U=({T. is_topology_on T X \<and> (\<Union>ET) \<subseteq> T})"
  have B0:"(Pow X) \<in> U"
    by (simp add: A1 Sup_le_iff U_def discrete_greater discrete_top)
  have B1:"U \<noteq> {}"
    using B0 by force
  have B2:"(\<Inter>U) \<in> topologies_on X"
    by (metis (no_types, lifting) B1 U_def mem_Collect_eq topologies_inf_closed topologies_on_def)
  have B3:"\<forall>T. is_topology_on T X \<and>  (\<Union>ET) \<subseteq> T \<longrightarrow> (\<Inter>U) \<subseteq> T"
    by (simp add: Inter_lower U_def)
  have B4:"\<forall>T \<in> ET. T \<subseteq> (\<Inter>U)"
    using U_def by blast
  have B5:" (is_sup_in (\<Inter>U) ET (topologies_on X))"
    by (metis B2 B3 B4 Sup_least is_sup_in_if3 mem_Collect_eq topologies_on_def)
  show ?thesis
    using B2 B5 U_def by auto
qed
  

lemma topologies_has_sup:
  assumes A0:"ET \<noteq> {}" and A1:"\<forall>T \<in> ET. T \<in> topologies_on X"
  shows "has_sup_in ET (topologies_on X)"
proof-
  have B0:"is_sup_in (top_sup2 ET X) ET (topologies_on X)"
    by (simp add: A0 A1 top_sup2_def topologies_sup_closed)
  have B1:"has_sup_in ET (topologies_on X)"
    using B0 has_sup_in_def is_min_imp_has_min is_sup_in_imp1 by blast
  show ?thesis
    by (simp add: B1)
qed  



lemma topologies_on_mem_iff:
  "\<And>T. T \<in> topologies_on X \<longleftrightarrow> is_topology_on T X"
  by (simp add: topologies_on_def)

lemma nhoods_of_mem_iff:
  "\<And>N. N \<in> nhoods_of x T X \<longleftrightarrow> (\<exists>U. U \<in> T \<and> x \<in> U \<and> U \<subseteq> N)"
  by (simp add: nhoods_of_def)

lemma nhoods_of_in_mem_iff:
  "\<And>N. N \<in> nhoods_of_in x T X \<longleftrightarrow> (N \<subseteq> X) \<and>(\<exists>U. U \<in> T \<and> x \<in> U \<and> U \<subseteq> N)"
  by (simp add: nhoods_of_in_def)

lemma nhoods_of_imp2:
  "\<And>N. N \<in> nhoods_of x T X \<Longrightarrow> x \<in> N"
  by (meson in_mono nhoods_of_mem_iff)

lemma nhoods_of_in_imp2:
  "\<And>N. N \<in> nhoods_of_in x T X \<Longrightarrow> x \<in> N"
  by (meson nhoods_of_in_mem_iff subsetD)

lemma nhoods_of_imp3:
  "\<And>N. N \<in> nhoods_of x T X \<Longrightarrow>  (\<exists>U. U \<in> T \<and> x \<in> U \<and> U \<subseteq> N)"
  by (meson in_mono nhoods_of_mem_iff)

lemma nhoods_of_in_imp3:
  "\<And>N. N \<in> nhoods_of_in x T X \<Longrightarrow>  (\<exists>U. U \<in> T \<and> x \<in> U \<and> U \<subseteq> N)"
  by (simp add: nhoods_of_in_mem_iff)

lemma top_from_nhoods_mem_imp:
  "\<And>V. V \<in> top_from_nhoods N X \<Longrightarrow>  V \<in> Pow X \<and> (\<forall>x \<in> V. V \<in> N x)"
  by (simp add: top_from_nhoods_def)


lemma nhoods_from_top_mem_imp1:
  "\<And>V x. x \<in> X \<Longrightarrow> V \<in> nhoods_from_top T X x \<Longrightarrow>  (\<exists>U \<in> T. x \<in> U \<and> U \<subseteq> V)"
  by (simp add: nhoods_from_top_def)

lemma nhood_system_imp_pfilters:
  assumes A0:"is_nhood_system_in N X"
  shows "\<And>x. x \<in> X \<Longrightarrow> is_pfilter_in (N x) (Pow X)"
  using assms is_nhood_system_in_def by fastforce 

lemma nhood_system_imp_subset:
  assumes A0:"is_nhood_system_in N X" 
  shows "\<And>x V. (x \<in> X \<and> V \<in> (N x)) \<Longrightarrow> V \<subseteq> X"
  by (meson assms is_nhood_system_in_def pfilter_in_powerset_simp)

lemma open_is_nhood:
  "\<And>V x. x \<in> X \<Longrightarrow> x \<in> V \<Longrightarrow> V \<in> T  \<Longrightarrow> V \<in> nhoods_of x T X"
  by (meson nhoods_of_mem_iff subset_refl)

lemma open_is_nhood_in:
  "\<And>V x. x \<in> X \<Longrightarrow> x \<in> V \<Longrightarrow> V \<in> T \<Longrightarrow>  V \<subseteq> X \<Longrightarrow> V \<in> nhoods_of_in x T X"
  using nhoods_of_in_def by fastforce

lemma adherent_to_self:
  assumes "is_topology_on T X" and "A \<subseteq> X" and "x \<in> A"
  shows "is_adherent_point x A T X"
  apply(simp add: is_adherent_point_def)
  using assms(3) nhoods_of_in_imp2 by fastforce

lemma nhoods_is_pfilter:
  fixes X::"'a set" and T::"'a set set" and x::"'a"
  assumes A0:"is_topology_on T X" and A1:"x \<in> X"
  shows "is_pfilter (nhoods_of x T X)"
proof-
  let ?Nx="(nhoods_of x T X)"
  have B0:"is_proper ?Nx"
    by (metis UNIV_I empty_iff is_proper_def is_proper_in_def nhoods_of_imp2)
  have B1:"is_downdir ?Nx"
  proof-
    have B10:"\<And>a b. (a \<in> ?Nx \<and> b \<in> ?Nx) \<longrightarrow> (\<exists>c  \<in> ?Nx. (c \<le> a) \<and>  (c \<le> b))"
    proof
      fix Va Vb assume A2:"(Va \<in> ?Nx \<and> Vb \<in> ?Nx)"
      obtain Ua where A3:"Ua \<in> T \<and> x \<in> Ua \<and> Ua \<subseteq> Va"
        by (meson A2 nhoods_of_imp3)
      obtain Ub where A4:"Ub \<in> T \<and> x \<in> Ub \<and> Ub \<subseteq> Vb"
        by (meson A2 nhoods_of_imp3)
      have B11:"Ua \<inter> Ub \<in> T"
        by (meson A0 A3 A4 is_topology_on_def top_i3_def)
      have B12:"Ua \<inter> Ub \<in> T \<and> x \<in> Ua \<inter> Ub \<and> Ua \<inter> Ub \<subseteq> Va \<and> Ua \<inter> Ub \<subseteq> Vb"
        by (simp add: A3 A4 B11 inf.coboundedI1 inf.coboundedI2)
      show "(\<exists>c  \<in> ?Nx. (c \<le> Va) \<and>  (c \<le> Vb))"
        by (meson A2 B12 Pow_iff nhoods_of_mem_iff order_refl subset_trans)
    qed
    show ?thesis
      by (simp add: B10 is_downdir_def)
  qed
  have B2:"is_upclosed ?Nx"
  proof-
    have B20:"\<And>a b. (a \<le> b \<and>  a \<in> ?Nx) \<longrightarrow>  b \<in> ?Nx"
    proof
      fix Va Vb assume A5:"Va \<le> Vb \<and> Va \<in> ?Nx"
      obtain Ua where A6:"Ua \<in> T \<and> x \<in> Ua \<and> Ua \<subseteq> Va"
        by (meson A5 nhoods_of_imp3)
      have B21:"Ua \<subseteq> Vb"
        using A5 A6 by auto
      show "Vb \<in> ?Nx"
        by (meson A5 dual_order.trans nhoods_of_mem_iff)
    qed
   show ?thesis
     by (meson B20 is_upclosed_def is_upclosed_in_def)
  qed
  have B3:"is_inhabited ?Nx"
    by (metis A0 A1 empty_iff is_inhabited_def is_topology_on_def nhoods_of_mem_iff order_refl)
  show ?thesis
    by (simp add: B0 B1 B2 B3 is_filter_if is_pfilter_if2 up_closure_in_univ_imp)
qed



lemma top_from_nhoods_inv:
  fixes X::"'a set" and T::"'a set set" and x::"'a"
  assumes A0:"is_topology_on T X"
  shows "top_from_nhoods (nhoods_from_top T X) X = T" (is "?L = ?R")
proof-
  define N where "N= (nhoods_from_top T X)"
  have B0:"?L \<subseteq> ?R"
  proof
    fix V assume A1:"V \<in> ?L"
    have B01:"V \<in> Pow X \<and> (\<forall>x \<in> V. V \<in> N x)"
      using A1 N_def top_from_nhoods_mem_imp by blast
    have B02:"\<forall>x \<in> V. \<exists>U \<in> T. x \<in> U \<and> U \<subseteq> V"
      by (metis A1 Pow_iff nhoods_from_top_mem_imp1 subsetD top_from_nhoods_mem_imp)
    define F where "F=(\<lambda>x. (SOME U. U \<in> T \<and> x \<in> U \<and> U \<subseteq> V))"
    have B03:"\<forall>x \<in> V. F x \<in> T \<and> x \<in> (F x) \<and> (F x) \<subseteq> V"
      by (metis (mono_tags, lifting) B02 F_def someI)
    have B04:"\<Union>(F`V) \<subseteq> V"
      using B03 by blast
    have B05:"\<Union>(F`V) \<supseteq> V"
      using B03 by blast
    have B06:"\<Union>(F`V) =V"
      using B04 B05 by blast
    have B07:"\<forall>U \<in> (F`V). U \<in> T"
      using B03 by blast
    have B08:"V \<in> T"
      by (metis A0 B06 B07 is_topology_on_def subsetI top_u1_def)
    show "V \<in> ?R"
      by (simp add: B08)
  qed
  have B1:"?R \<subseteq> ?L"
  proof
    fix V assume A1:"V \<in> ?R"
    have B10:"V \<subseteq> X"
      by (meson A1 PowD assms in_mono is_topology_on_def)
    show "V \<in> ?L"
    proof(cases "V = {}")
      case True
      then show ?thesis
        by (simp add: top_from_nhoods_def)
    next
      case False
      obtain x where A2:"x \<in> V"
        using False by blast
      have B11:"\<exists>U \<in> T. x \<in> U \<and> U \<subseteq> V"
        using A1 A2 by blast
      then show ?thesis
        by (smt (verit, ccfv_threshold) A1 B10 CollectI PowI nhoods_from_top_def subset_iff top_from_nhoods_def)
    qed
  qed
  show ?thesis
    by (simp add: B0 B1 subset_antisym)
qed

lemma nhoods_from_top_inv:
  fixes X::"'a set" and N::"('a \<Rightarrow> 'a set set)" and x::"'a"
  assumes A0:"is_nhood_system_in N X" and A1:"x \<in> X"
  shows "(nhoods_from_top (top_from_nhoods N X) X)(x) = N(x)"
proof-
  define T where A2:"T=top_from_nhoods N X"
  define L where "L=(nhoods_from_top (top_from_nhoods N X) X)"
  have B0:"\<And>V. V \<in> L x \<longrightarrow> V \<in> N x"
  proof
    fix V assume A3:"V \<in> L x"
    obtain U where B1:"U \<in> T \<and> x \<in> U \<and> U \<subseteq> V"
      by (metis A1 A2 A3 L_def nhoods_from_top_mem_imp1)
    have B2:" (\<forall>y \<in> U. U \<in> N y)"
      using A2 B1 top_from_nhoods_mem_imp by blast
    have B3:"U \<in> N x"
      by (simp add: B1 B2)
    have B4:"U \<subseteq> V \<and> V \<subseteq> X"
      by (metis (no_types, lifting) A1 A3 B1 CollectD L_def PowD nhoods_from_top_def)
    have B5:"is_pfilter_in (N x) (Pow X)"
      using A2 assms is_nhood_system_in_def by fastforce
    have B6:"is_upclosed_in (N x) (Pow X)"
      by (simp add: B5 is_filter_in_imp is_pfilter_in_imp)
    show "V \<in> N x"
      by (meson B3 B4 B6 PowI is_upclosed_in_def)
  qed
  have B7:"\<And>V. V \<in> N x \<longrightarrow> V \<in> L x"
  proof
    fix V assume A4:"V \<in> N x"
    have A40:"V \<subseteq> X"
      by (meson A0 A1 A4 nhood_system_imp_subset)
    define U where A5:"U={y \<in> X. V \<in> N y}"
    have B7:"x \<in> U"
      by (simp add: A1 A4 A5)
    have B8:"U \<subseteq> V"
      using A0 A5 is_nhood_system_in_def by fastforce
    have B9:"(\<And>y. y \<in> U \<longrightarrow> U \<in> N y)"
      proof
        fix y assume A6:"y \<in> U"
        have A61:"V \<in> N y"
          using A5 A6 by blast
        obtain W where A7:"(W \<in> N y \<and> (\<forall>z \<in> W. V \<in> N z))"
          by (metis (no_types, lifting) A0 A5 A6 CollectD is_nhood_system_in_def)
        have B10:"W \<subseteq> U"
        proof
          fix z assume A8:"z \<in> W"
          have B101:"V \<in> N z"
            by (simp add: A7 A8)
          show "z \<in> U"
            using A0 A5 A6 A7 A8 nhood_system_imp_subset by fastforce
        qed
        have B110:"W \<in> N y \<and> is_pfilter_in (N y) (Pow X) \<and> W \<subseteq> U "
          by (meson A0 A40 A6 A7 B10 B8 in_mono nhood_system_imp_pfilters)
        have B11:"U \<in> N y"
          by (meson A40 B110 B8 PowI dual_order.trans is_filter_in_imp is_pfilter_in_imp is_upclosed_in_imp)
        show "U \<in> N y"
          using B11 by force
      qed
    have B120:"U \<in> Pow X \<and> (\<forall>u \<in> U.  V \<in> N u)"
      using A5 by blast
    have B121:"U \<in> T"
      using A2 B120 B9 top_from_nhoods_def by force
    have B122:"x \<in> U \<and> U \<subseteq> V"
      by (simp add: B7 B8)
    have B12:"V \<in> Pow X \<and> U \<in> T \<and> x \<in> U \<and> U \<subseteq> V"
      by (simp add: A40 B121 B7 B8)
    show "V \<in> L x"
      by (metis (no_types, lifting) A1 A2 B12 CollectI L_def nhoods_from_top_def)
  qed
  show ?thesis
    using B0 B7 L_def by blast
qed




lemma is_base1_for_topology_imp:
   "is_base1_for_topology B T \<Longrightarrow> U \<in> T \<Longrightarrow> (\<exists>E \<in> Pow B. U=\<Union>E)"
  by (simp add: is_base1_for_topology_def)

lemma is_base2_for_topology_imp0:
  "is_base2_for_topology B T \<Longrightarrow> (B \<subseteq> T) \<and> (\<forall>U \<in> T. \<forall>x \<in> U. \<exists>B \<in> B. (x \<in> B \<and> B \<subseteq> U))"
  by (simp add: is_base2_for_topology_def)

lemma is_base2_for_topology_if0:
  "(B \<subseteq> T) \<Longrightarrow> (\<forall>U \<in> T. \<forall>x \<in> U. \<exists>B \<in> B. (x \<in> B \<and> B \<subseteq> U)) \<Longrightarrow> is_base2_for_topology B T "
  by (simp add: is_base2_for_topology_def)

lemma is_base2_for_topology_imp1:
  "is_base2_for_topology B T \<Longrightarrow>  U \<in> T \<Longrightarrow> x \<in> U \<Longrightarrow>  (\<exists>Bx \<in> B. (x \<in> Bx \<and> Bx \<subseteq> U))"
  by (simp add: is_base2_for_topology_def)

lemma is_base2_for_topology_imp2:
  assumes "is_base2_for_topology B T" "U \<in> T" "x \<in> U"
  obtains Bx where "Bx \<in> B  \<and> x \<in> Bx \<and> Bx \<subseteq> U"
  by (meson assms(1) assms(2) assms(3) is_base2_for_topology_imp1)

lemma is_base_3_covering_imp1:
  "is_base_3_covering B X \<Longrightarrow>  (B \<in> Dpow X)"
  by (simp add: is_base_3_covering_def)

lemma is_base_3_covering_imp2:
  "is_base_3_covering B X  \<Longrightarrow> (\<forall>x \<in> X. \<exists>U \<in> B. x \<in> U)"
  by (simp add: is_base_3_covering_def)

lemma is_base_3_covering_obtains:
  assumes "is_base_3_covering B X"  and "x \<in> X" obtains U where "U \<in> B \<and> x \<in> U"
  using assms(1) assms(2) is_base_3_covering_imp2 by blast


lemma is_base_3_covering_if:
  "(B \<in> Dpow X) \<Longrightarrow>  (\<forall>x \<in> X. \<exists>U \<in> B. x \<in> U) \<Longrightarrow>  is_base_3_covering B X"
  by (simp add: is_base_3_covering_def)


lemma is_base_3_intercont_imp1:
  "is_base_3_intercont B X \<Longrightarrow> (\<forall>U1  U2. U1 \<in> B \<and> U2 \<in> B \<longrightarrow> (\<forall>x \<in> U1 \<inter> U2. \<exists> U3\<in> B. x \<in> U3 \<and> U3 \<subseteq> U1 \<inter> U2))"
  by (simp add: is_base_3_intercont_def)

lemma is_base_3_intercont_if:
  " (\<forall>U1  U2. U1 \<in> B \<and> U2 \<in> B \<longrightarrow> (\<forall>x \<in> U1 \<inter> U2. \<exists> U3\<in> B. x \<in> U3 \<and> U3 \<subseteq> U1 \<inter> U2)) \<Longrightarrow> is_base_3_intercont B X "
  by (simp add: is_base_3_intercont_def)


lemma is_base_3_intercont_if2:
  "(\<And>x U1  U2. x \<in> U1 \<inter> U2 \<and> U1 \<in> B \<and> U2 \<in> B \<Longrightarrow> (\<exists> U3\<in> B. x \<in> U3 \<and> U3 \<subseteq> U1 \<inter> U2)) \<Longrightarrow> is_base_3_intercont B X "
  by (simp add: is_base_3_intercont_def)


lemma is_base_3_intercont_obtains1:
  assumes "is_base_3_intercont B X" and "U1 \<in> B \<and> U2 \<in> B" and "x \<in> U1 \<inter> U2"
  obtains U3 where "U3 \<in> B \<and> x \<in> U3 \<and> U3 \<subseteq> U1 \<inter> U2"
  by (meson assms(1) assms(2) assms(3) is_base_3_intercont_imp1)


lemma is_base3_for_topology_imp0:
  "is_base3_for_topology B X \<Longrightarrow> is_base_3_intercont B X"
  by (simp add: is_base3_for_topology_def)

lemma is_base3_for_topology_imp1:
  "is_base3_for_topology B X \<Longrightarrow> is_base_3_covering B X"
  by (simp add: is_base3_for_topology_def)

lemma is_base3_for_topology_imp2:
   "is_base3_for_topology B X \<Longrightarrow> B \<in> Dpow X"
   by (simp add: is_base3_for_topology_def is_base_3_covering_def)

lemma is_base3_for_topology_imp3:
   "is_base3_for_topology B X \<Longrightarrow> (\<forall>x \<in> X. \<exists>U \<in> B. x \<in> U)"
    by (simp add: is_base3_for_topology_def is_base_3_covering_def)

lemma is_base3_for_topology_imp3b:
  "is_base3_for_topology B X \<Longrightarrow> x \<in> X  \<Longrightarrow>  \<exists>U \<in> B. x \<in> U"
  by (simp add: is_base3_for_topology_imp3)


lemma is_base3_for_topology_imp4:
   "is_base3_for_topology B X \<Longrightarrow> (\<forall>U1  U2. U1 \<in> B \<and> U2 \<in> B \<longrightarrow> (\<forall>x \<in> U1 \<inter> U2. \<exists> U3\<in> B. x \<in> U3 \<and> U3 \<subseteq> U1 \<inter> U2))"
    by (simp add: is_base3_for_topology_def is_base_3_intercont_def)

lemma is_base3_for_topology_imp4b:
   "is_base3_for_topology B X \<Longrightarrow>  U1 \<in> B \<and> U2 \<in> B \<and> x \<in> U1 \<inter> U2 \<Longrightarrow> (\<exists>U3\<in> B. x \<in> U3 \<and> U3 \<subseteq> U1 \<inter> U2)"
    by (simp add: is_base3_for_topology_def is_base_3_intercont_def)

lemma is_base_3_intercont_imp4c:
  assumes "is_base_3_intercont B X" and "U1 \<in> B \<and> U2 \<in> B \<and> x \<in> U1 \<inter> U2"
  shows "\<exists>U3. U3 \<in> B \<and> x \<in> U3 \<and> U3 \<subseteq> U1 \<inter> U2"
  by (meson assms(1) assms(2) is_base_3_intercont_imp1)

lemma is_base3_for_topology_imp5:
  "is_base3_for_topology B X \<Longrightarrow> b \<in> B \<Longrightarrow> b \<subseteq> X"
  using is_base3_for_topology_imp2 by fastforce

lemma is_base3_for_topology_imp6:
  "is_base3_for_topology B X \<Longrightarrow> V \<in> Pow B \<Longrightarrow> (\<Union>V) \<in> Pow X"
  using is_base3_for_topology_imp2 by fastforce

lemma is_base3_for_topology_if:
   " is_base_3_covering B X \<Longrightarrow> is_base_3_intercont B X   \<Longrightarrow>is_base3_for_topology B X"
    by (simp add: is_base3_for_topology_def)

lemma base_intercont_imp_pset_downdir:
  assumes "is_base_3_intercont B X" "x \<in> X"
  shows "is_downdir (nhood_base_from_base B X x)"
  apply( simp add:is_downdir_def nhood_base_from_base_def)
  by (metis Int_iff assms(1) assms(2) is_base_3_intercont_imp1 le_infE)



lemma basis_element_pt_props:
  assumes A0:"is_base2_for_topology B T"
  defines "f \<equiv> basis_element_npt B"
  shows "\<And>U x. (U \<in> T \<and> x \<in> U) \<longrightarrow> (f U x) \<in> B \<and> x \<in> (f U x) \<and> (f U x) \<subseteq> U"
proof
    fix U x assume A1:"U \<in> T \<and> x \<in> U"
    obtain Bx where B1:"Bx \<in> B \<and> x \<in> Bx \<and> Bx \<subseteq> U"
      by (meson A0 A1 is_base2_for_topology_imp2)
    show "(f U x) \<in> B \<and> x \<in> (f U x) \<and> (f U x) \<subseteq> U"
    apply( simp add:f_def basis_element_npt_def)
      by (metis (mono_tags, lifting) \<open>\<And>thesis::bool. (\<And>Bx::'a::type set. Bx \<in> (B::'a::type set set) \<and> (x::'a::type) \<in> Bx \<and> Bx \<subseteq> (U::'a::type set) \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> someI2_ex)
qed


lemma basis_element_pt_props2:
  assumes A0:"is_base2_for_topology B T"
  defines "f \<equiv> basis_element_npt B"
  shows "\<And>U. U \<in> T \<Longrightarrow> (\<forall>x. x \<in> U \<longrightarrow> (f U x) \<in> B \<and> x \<in> (f U x) \<and> (f U x) \<subseteq> U)"
  by (metis A0 basis_element_pt_props f_def)


lemma basis_element_pt_props3:
  assumes A0:"is_base2_for_topology B T" and A1:"U \<in> T"
  defines "f \<equiv> (\<lambda>x. ((basis_element_npt B) U x))"
  shows "(\<Union>(f`U)) =U "
  using A0 A1 basis_element_pt_props f_def by fastforce


lemma basis_element_npt_props:
  assumes "is_base3_for_topology B X"
  defines "f \<equiv> basis_element_pt B X"
  shows "\<And>x. x \<in> X \<longrightarrow> (f x) \<in> B \<and> x \<in> (f x)"
proof
    fix x assume A0:"x \<in> X"
    show "(f x) \<in> B \<and> x \<in> (f x)"
    apply(simp add:f_def basis_element_pt_def)
      by (metis (no_types, lifting) A0 assms(1) is_base3_for_topology_imp3 someI_ex)
qed

lemma basis_element_int_npt_props0:
  assumes "is_base3_for_topology B X"
  defines "f \<equiv> basis_element_int_npt B X"
  shows "\<And>U1 U2 x. U1 \<in> B \<and> U2 \<in> B  \<and> x \<in> U1 \<inter> U2 \<longrightarrow> ((f U1 U2 x) \<in> B \<and> ((f U1 U2 x) \<subseteq> U1 \<inter> U2) \<and> x \<in> (f U1 U2 x))"
proof
    fix U1 U2 x assume A0:"U1 \<in> B \<and> U2 \<in> B  \<and> x \<in> U1 \<inter> U2"
    let ?U3="(f U1 U2 x)"
    have B0:"\<exists>U3. U3 \<in> B \<and> x \<in> U3 \<and> U3 \<subseteq> U1 \<inter> U2"
      by (meson A0 assms(1) is_base3_for_topology_imp4b)
    have B1:"is_base_3_intercont B X"
      by (simp add: assms(1) is_base3_for_topology_imp0)
    show "?U3 \<in> B \<and> (?U3 \<subseteq> U1 \<inter> U2) \<and> x \<in> ?U3"
    apply(simp add:f_def basis_element_int_npt_def)
      by (metis (mono_tags, lifting) B0 Int_subset_iff tfl_some)
qed

lemma un_all_pts:
  assumes "\<And>x. x \<in> U \<longrightarrow> (x \<in> V x) \<and> (V x \<subseteq> U)"
  shows "(\<Union>x \<in> U. V x) = U"
  using assms by fastforce

lemma basis_element_int_npt_props1:
  assumes "is_base3_for_topology B X" "(b1 \<in> B \<and> b2 \<in> B)"
  shows "\<exists>V \<in> Pow B.  b1 \<inter> b2 = (\<Union>V)"
proof-
  define V where A2:"V = (\<lambda>x. (basis_element_int_npt B X) b1 b2 x)"
  have B0:"\<And>x. x \<in> b1 \<inter> b2 \<longrightarrow> (x \<in> V x) \<and> (V x \<subseteq> b1 \<inter> b2)"
    by (metis A2 assms(1) assms(2) basis_element_int_npt_props0)
  have B1:"(\<Union>x \<in> b1 \<inter> b2. V x) = b1 \<inter> b2 "
    using B0 by blast
  have B2:"V`(b1 \<inter> b2) \<in> Pow B \<and>   b1 \<inter> b2 = (\<Union>(V`(b1 \<inter> b2)))"
    by (metis B1 PowI \<open>V::'a::type \<Rightarrow> 'a::type set \<equiv> basis_element_int_npt (B::'a::type set set) (X::'a::type set) (b1::'a::type set) (b2::'a::type set)\<close> assms(1) assms(2) basis_element_int_npt_props0 image_subset_iff)
  show ?thesis
    using B2 by auto
qed  

lemma is_base3_for_topology_imp7:
  assumes A0:"is_base3_for_topology B X" 
  shows "X \<in> (arb_sup_cl B)"
proof-
  define U where "U=basis_element_pt B X"
  have B0:"\<And>x. x \<in> X \<longrightarrow> x \<in> U x \<and>  U x \<in> B"
    by (simp add: U_def assms basis_element_npt_props)
  have B1:"\<And>x. x \<in> X \<longrightarrow> (U x) \<subseteq> X"
    using B0 assms is_base3_for_topology_imp5 by blast
  have B2:"(\<Union>x \<in> X. U x) = X"
    using B0 B1 by blast
  have B8:"U`X \<subseteq> B"
    using B0 by blast
  show ?thesis
    by (metis B2 B8 arb_sup_cl_extensive arb_sup_cl_idemp3 dual_order.trans)
qed
  
lemma base34_generates_top:
  assumes "is_base3_for_topology B X"
  shows " is_topology_on (arb_sup_cl B) X" 
proof-
  define T where "T=(arb_sup_cl B)"
  have T0:"X \<in> arb_sup_cl B"
    by (simp add: assms is_base3_for_topology_imp7)
  have T1:"top_u1 T"
    apply(simp add: top_u1_def)
    by (simp add: T_def arb_sup_cl_idemp3)
  have T2:"top_i3 T"
  proof-
    have T20:"\<And>a1 a2. a1 \<in> T \<and> a2 \<in> T \<longrightarrow> a1 \<inter> a2 \<in> T "
    proof
      fix a1 a2 assume A0:"a1 \<in> T \<and> a2 \<in> T" 
      obtain B1 B2 where B1:"a1 = (\<Union>B1) \<and> B1 \<subseteq> B  \<and> a2=\<Union>B2 \<and> B2 \<in> Pow B"
        by (metis A0 PowD T_def arb_sup_cl_mem_iff sup_un_sets)
      have B2:"a1 \<inter> a2 = (\<Union>b1 \<in> B1. (\<Union>b2 \<in> B2. b1 \<inter> b2 ))"
        using B1 by auto
       define f where "f= basis_element_int_npt B X"
      have B3:"\<And>b1 b2. (b1 \<in> B1 \<and> b2 \<in> B2) \<longrightarrow> (\<exists>V \<in> Pow B.  b1 \<inter> b2 = (\<Union>V))"
        by (meson B1 PowD assms basis_element_int_npt_props1 subsetD)
      have B4:"\<And>b1 b2. (b1 \<in> B1 \<and> b2 \<in> B2) \<longrightarrow> b1 \<inter> b2 \<in> arb_sup_cl B"
        by (simp add: B3 arb_sup_cl_sets)
      have B5:"a1 \<inter> a2 \<in> arb_sup_cl (arb_sup_cl B)"
        by (metis (mono_tags, lifting) B2 B4 arb_sup_cl_idemp arb_sup_cl_idemp3 image_subsetI)
      show " a1 \<inter> a2 \<in> T"
        using B5 T_def arb_sup_cl_idemp2 by blast
      qed
   show ?thesis
     by (simp add: T20 top_i3_def)
  qed
  have T4:"T \<in> Dpow X"
  apply(simp add: T_def)
    by (metis PowD PowI Sup_subset_mono T0 Union_Pow_eq arb_sup_cl_imp1 assms 
        complete_lattice_sup_exists is_base3_for_topology_imp2 subsetI subset_antisym)
  show ?thesis
    using T0 T1 T2 T4 T_def is_topology_on_def by auto
qed

  

lemma is_base1_for_topology_imp2:
   "is_base1_for_topology B T \<Longrightarrow> U \<in> T \<Longrightarrow> (\<exists>E \<in> Pow B. has_sup E \<and> U= SupUn E)"
  by (simp add: complete_lattice_sup_exists has_sup_un_sets is_base1_for_topology_def)

lemma is_base1_for_topology_if:
  "(\<And>U. U \<in> T \<Longrightarrow> (\<exists>E \<in> Pow B. U=\<Union>E)) \<Longrightarrow> B \<subseteq> T \<Longrightarrow> is_base1_for_topology B T "
  by (simp add: is_base1_for_topology_def)
    
lemma is_base1_for_topology_if_arb_sup_cl:
  assumes"is_base1_for_topology B T" and "is_topology_on T X"
  shows "T=arb_sup_cl B"        
proof-
  have L:"T \<subseteq> arb_sup_cl B"
    using arb_sup_cl_mem_iff assms is_base1_for_topology_imp2 by fastforce
  have R:"arb_sup_cl B \<subseteq> T"
  proof
    fix V assume A0:"V \<in> arb_sup_cl B"
    obtain E where B0:"E \<in> Pow B \<and> V=(\<Union>E)"
      by (metis A0 arb_sup_cl_mem_iff sup_un_sets)
    have B1:"E \<in> Pow T"
      using B0 assms(1) is_base1_for_topology_def by blast
    show "V \<in> T"
      by (metis B0 B1 PowD assms(2) is_topology_on_def top_u1_def)
  qed
  show ?thesis
    using L R by blast
qed

lemma given_top_base1_imp_base2:
  assumes A0:"is_topology_on T X" and A1:"X \<noteq> {}" and A2:"is_base1_for_topology B T "
  shows "is_base2_for_topology B T"
proof-
  have B0:"B \<subseteq> T"
    using A2 is_base1_for_topology_def by blast
  have B1:"\<forall>U \<in> T. \<forall>x \<in> U. \<exists>Bx \<in> B. x \<in> Bx \<and> Bx \<subseteq> U"
    proof
      fix U assume A3:"U \<in> T"
      obtain E where B2:"E \<subseteq> B \<and> U=Sup E"
        by (meson A2 A3 PowD is_base1_for_topology_imp)
      show "\<forall>x \<in>  U. \<exists>Bx\<in>B. x \<in> Bx \<and> Bx \<subseteq> U"
        proof
          fix x assume A4:"x \<in> U"
          obtain Ex where B3:"Ex \<in> E \<and> x \<in> Ex"
            using A4 B2 by blast
          have B4:"Ex \<subseteq> U \<and> x \<in> Ex"
            by (simp add: B2 B3 Sup_upper)
          show "\<exists>Bx \<in> B. x \<in> Bx \<and> Bx \<subseteq> U"
            using B2 B4 by blast
       qed
     qed
  show ?thesis
    by (simp add: B0 B1 is_base2_for_topology_if0)
qed

lemma given_top_base1_if_base2:
  assumes A0:"is_topology_on T X" and A1:"X \<noteq> {}" and A2:"is_base2_for_topology B T "
  shows "is_base1_for_topology B T"
proof-
  have B0:"B \<subseteq> T"
    by (simp add: A2 is_base2_for_topology_imp0)
  have B1:"\<forall>U \<in> T. \<exists>E \<in> Pow B. U = \<Union> E"
  proof
    fix U assume A3:"U \<in> T"
    define f where B2:"f \<equiv> (\<lambda>x. ((basis_element_npt B) U x))"
    have B3:"(f`U) \<in> Pow B"
      using A2 A3 B2 basis_element_pt_props by fastforce
    have B4:"\<Union>(f`U) = U "
      using A2 A3 B2 basis_element_pt_props3 by blast
    show B2:"\<exists>E \<in> Pow B. U =  \<Union> E"
      by (metis B3 B4)
  qed
  show ?thesis
    by (simp add: B0 B1 is_base1_for_topology_if)
qed
     
lemma base34_generates_by_base1:
  assumes A0:"is_base3_for_topology B X" 
  defines "T \<equiv> {U \<in> Pow X. (\<forall>x. x \<in> U \<longrightarrow> (\<exists>Bx. x \<in> Bx \<and>  Bx \<in> B \<and> Bx \<subseteq> U))}"
  shows "is_topology_on T X"
proof-
  have T0:"X \<in> T"
  apply(simp add: T_def)
    by (meson Pow_iff assms(1) in_dpow_iff is_base3_for_topology_imp2 is_base3_for_topology_imp3)
  have T1:"top_u1 T" 
     apply(simp add:top_u1_def T_def )
    by (smt (verit, best) Ball_Collect Sup_le_iff Union_upper dual_order.trans)
  have T2:"top_i3 T"
    proof-
      have B0: "\<And>a1 a2. (a1 \<in> T \<and> a2 \<in> T) \<longrightarrow> a1 \<inter> a2 \<in> T"
      proof 
         fix a1 a2 assume A1:" (a1 \<in> T \<and> a2 \<in> T)" 
         have B6:"\<And>x. x \<in> a1 \<inter> a2 \<longrightarrow> (\<exists>Bx. Bx \<in> B \<and> x \<in> Bx \<and> Bx \<subseteq> a1 \<inter> a2)"
            proof fix x
               assume A2:"x \<in> a1 \<inter> a2" 
               have B3:"(\<exists>B1. B1 \<in> B \<and> x \<in> B1 \<and> B1 \<subseteq> a1)"
                 using A1 A2 T_def by auto
               have B4:"(\<exists>B2. B2 \<in> B \<and> x \<in> B2 \<and> B2 \<subseteq> a2)"
                 using A1 A2 T_def by auto
               have B5:"\<exists>B1 B2. B1 \<in> B \<and> B2 \<in> B \<and> x \<in> B1 \<inter> B2 \<and> B1 \<inter> B2 \<subseteq> a1 \<inter> a2"
                 by (meson B3 B4 IntI Int_mono)
            show "(\<exists>Bx. Bx \<in> B \<and> x \<in> Bx \<and> Bx \<subseteq> a1 \<inter> a2)"
              by (meson A0 B5 dual_order.trans is_base3_for_topology_imp4b)
        qed
        show "a1 \<inter> a2 \<in> T"
        apply(simp add: B6 T_def)
          using A1 B6 T_def inf.absorb_iff2 by fastforce
       qed
      show ?thesis
        by (simp add: B0 top_i3_def)
  qed
    have B3:"T \<in> Dpow X"
      using T_def by blast
  show ?thesis
    using B3 T0 T1 T2 is_topology_on_def by auto
qed

lemma base2_top_then_base34:
  assumes A0:"is_base2_for_topology B T" and A1:"is_topology_on T X"
  shows "is_base3_for_topology B X"
  unfolding is_base3_for_topology_def
  proof
    show "is_base_3_covering B X"
    proof-
      have B0:"X \<in> T" 
        using A1 is_topology_on_def by blast
      have B1:"\<And>x. x \<in> X \<longrightarrow> (\<exists>Bx. Bx \<in> B \<and> x \<in> Bx \<and> Bx \<subseteq> X)"
        by (meson A0 B0 is_base2_for_topology_imp2)
      have B2:"B \<subseteq> Pow X"
        by (meson A0 A1 in_dpow_iff is_base2_for_topology_def is_topology_on_def subsetD subsetI)
      have B3:" \<forall>x \<in>X. \<exists>U\<in>B. x \<in> U"
        using B1 by auto
      show ?thesis
        by (simp add: B2 B3 is_base_3_covering_if)
    qed
    show "is_base_3_intercont B X"
    proof- 
      have B8:"\<And>x U1  U2. x \<in> U1 \<inter> U2 \<and> U1 \<in> B \<and> U2 \<in> B \<longrightarrow> (\<exists> U3\<in> B. x \<in> U3 \<and> U3 \<subseteq> U1 \<inter> U2)"
      proof
      fix x U1 U2 assume A2:"x \<in> U1 \<inter> U2 \<and> U1 \<in> B \<and> U2 \<in> B"
        have B4:"U1 \<in> T \<and> U2 \<in> T"
          using A0 A2 is_base2_for_topology_imp0 by blast
        have B5:"U1 \<inter> U2 \<in> T"
          by (meson A1 B4 is_topology_on_def top_i3_def)
        obtain U3 where B6:"x \<in> U3 \<and> U3 \<in> B \<and> U3 \<subseteq> U1 \<inter> U2"
          by (meson A0 A2 B5 is_base2_for_topology_def)
        show "\<exists>U3 \<in> B. x \<in> U3 \<and> U3 \<subseteq> U1 \<inter> U2"
          using B6 by blast
      qed
      show ?thesis
        using B8 is_base_3_intercont_if2 by blast
    qed
qed

lemma open_iff_nhp:
  assumes A0:"is_topology_on T X" and A1:"V \<in> Pow X"
  shows "V \<in> T \<longleftrightarrow> (\<forall>x. x \<in> V \<longrightarrow> (\<exists>Ux. Ux \<in> T \<and>  x \<in> Ux \<and> Ux \<subseteq> V))" (is "?L \<longleftrightarrow> ?R")
proof
  assume L:?L show ?R
    using L by blast
  next
  assume R:?R
  define f where B0:"f=(\<lambda>x. SOME Ux. Ux \<in> T \<and> x \<in> Ux \<and> Ux \<subseteq> V)"
  have B1:"\<forall>x. x \<in> V \<longrightarrow> f x \<in> T \<and> x \<in> f x \<and> f x \<subseteq> V"
    by (metis (mono_tags, lifting) R B0 someI)
  have B2:"\<Union>(f`V) \<subseteq> V"
    by (simp add: B1 un_all_pts)
  have B3:"V \<subseteq> (\<Union>(f`V))"
    using B1 by blast   
  show ?L
    by (metis A0 B1 B2 B3 image_subset_iff is_topology_on_def subset_antisym top_u1_def)
qed


lemma closed_sets_arb_inter_closed:
  assumes "is_topology_on T X" and "FF \<in> Dpow X" and "\<forall>F \<in> FF. (X - F) \<in> T"
  shows "(X-(\<Inter>FF)) \<in> T"
proof-
  have B0:"X-(\<Inter>FF) = (\<Union>F \<in> FF. (X - F))"
    by blast
  have B1:"\<forall>F \<in> FF. (X - F) \<in> T"
    by (simp add: assms(3))
  define EF where "EF = {G. \<exists>F \<in> FF. G = X - F}"
  have B2:"\<forall>G \<in> EF. G \<in> T"
    using B1 EF_def by blast
  have B3:"\<Union>EF = (\<Union>F \<in> FF. (X - F))"
    using EF_def by blast
  have B4:"\<Union>EF \<in> T"
    by (meson B2 assms(1) is_topology_on_def subsetI top_u1_def)
  have B5:"(\<Union>F \<in> FF. (X - F)) \<in> T"
    using B3 B4 by presburger
  have B6:"(X-(\<Inter>FF)) \<in> T"
    using B3 B4 by force
  show ?thesis
    by (simp add: B6)
qed
 
lemma larger_closed_sets_mem_iff:
  assumes "is_topology_on T X" and "E \<subseteq> X"
  shows "F \<in> larger_closed_sets E T X \<longleftrightarrow> (F \<in> Pow X) \<and> (X - F) \<in> T \<and> E \<subseteq> F"
  by (simp add: larger_closed_sets_def)

lemma smaller_open_sets_mem_iff:
  assumes "is_topology_on T X" and "E \<subseteq> X"
  shows "U \<in> smaller_open_sets E T X \<longleftrightarrow> U \<in> T \<and> U \<subseteq> E"
  by (simp add: smaller_open_sets_def)


lemma larger_closed_sets_complement:
  assumes "is_topology_on T X" and "E \<subseteq> X" and "U \<subseteq> X"
  shows "U \<in> smaller_open_sets E T X \<longleftrightarrow> (X-U) \<in> larger_closed_sets (X-E) T X"
  apply(simp add:smaller_open_sets_def larger_closed_sets_def)
  using assms(3) double_diff by fastforce

lemma smaller_open_arb_union_closed:
  assumes "is_topology_on T X" and "E \<subseteq> X" and "UF \<subseteq> smaller_open_sets E T X"
  shows "\<Union>UF \<in> smaller_open_sets E T X"
  by (metis Sup_le_iff assms(1) assms(2) assms(3) is_topology_on_def smaller_open_sets_mem_iff subset_eq top_u1_def)

lemma larger_closed_sets_arb_inter_closed:
  assumes "is_topology_on T X" and "E \<subseteq> X" and "FF \<subseteq> larger_closed_sets E T X" and "FF \<noteq> {}"
  shows "\<Inter>FF \<in> larger_closed_sets E T X"
proof-
  define I where "I = (\<Inter>FF)"
  have B0:"\<forall>F \<in> FF. (X - F) \<in> T"
    using assms(1) assms(2) assms(3) larger_closed_sets_mem_iff by blast
  have B1:"FF \<in> Dpow X"
    by (meson assms(1) assms(2) assms(3) in_dpow_iff larger_closed_sets_mem_iff subset_eq)
  have B2:"(X - I) \<in> T"
    using B0 B1 I_def assms(1) closed_sets_arb_inter_closed by fastforce
  have B3:"E \<subseteq> I"
    by (metis I_def Inter_greatest assms(1) assms(2) assms(3) larger_closed_sets_mem_iff subset_eq)
  have B4:"\<forall>F \<in> FF. F \<subseteq> X"
    using B1 by blast
  have B5:"I \<subseteq> X"
    using B4 I_def assms(4) by blast
  show ?thesis
    using B2 B3 B5 I_def assms(1) larger_closed_sets_mem_iff by fastforce
qed

lemma finite_inter_finite:
  fixes EF::"'a set set"
  assumes A0:"\<And>E. E \<in> EF \<Longrightarrow> finite E" and A1:"EF \<noteq> {}"
  shows "finite (\<Inter>EF)"
  using A0 A1 by blast


lemma in_cofinite_sets_in_imp1:
  "\<And>U. U \<in> cofinite_sets_in X \<Longrightarrow> U \<in> Pow X \<and> (finite (X - U) \<or> U={})"
  by (simp add: cofinite_sets_in_def)

lemma in_cocountable_sets_in_imp1:
  "\<And>U. U \<in> cocountable_sets_in X \<Longrightarrow> U \<in> Pow X \<and> (is_countable (X - U) \<or> U={})"
  by (simp add: cocountable_sets_in_def)

lemma in_cocountable_sets_in_imp2:
  "\<And>U. U \<in> cocountable_sets_in X \<Longrightarrow> U \<noteq> {} \<Longrightarrow> is_countable(X - U)"
  by (simp add: cocountable_sets_in_def)

lemma in_cofinite_iff1:
  assumes A0:"U \<in> Pow X"
  shows "U \<in> cofinite_sets_in X \<longleftrightarrow> (U \<noteq> {} \<longrightarrow> finite (X - U))"
  using A0 cofinite_sets_in_def by auto

lemma in_cocountable_iff1:
  assumes A0:"U \<in> Pow X"
  shows "U \<in> cocountable_sets_in X \<longleftrightarrow> (U \<noteq> {} \<longrightarrow> is_countable (X - U))"
  using assms cocountable_sets_in_def by auto

lemma in_cofinite_iff2:
  assumes A0:"U \<in> Pow X"
  shows "U \<in> cofinite_sets_in X \<longleftrightarrow> (U = {} \<or> finite (X - U))"
  using A0 cofinite_sets_in_def by auto

lemma imp_in_cofinite:
  "U \<in> Pow X \<Longrightarrow> U \<noteq> {} \<Longrightarrow>  finite (X - U) \<Longrightarrow> U \<in> cofinite_sets_in X"
  by (simp add: in_cofinite_iff1)

lemma cofinite_union_comp:
  assumes A0:"C \<subseteq> cofinite_sets_in X"
  shows "\<Union>C \<in> cofinite_sets_in X"
proof-
    let ?U="(\<Union>C)"
    have B0:"?U \<in> Pow X"
      using assms in_cofinite_sets_in_imp1 by fastforce
    have B1:"?U \<noteq> {} \<Longrightarrow> finite (X-?U)"
    proof-
      assume A1:"?U \<noteq> {}"
      have B2:"X-?U=(\<Inter>u \<in> C. (X-u))"
        using A1 by blast
      show "finite (X-?U)"
        by (metis A1 B2 assms empty_Union_conv finite_INT in_cofinite_sets_in_imp1 subset_iff)
    qed
  show ?thesis
    by (metis B0 B1 in_cofinite_iff1)
qed

lemma cocountable_un_closed:
  assumes A0:"C \<subseteq> cocountable_sets_in X"
  shows "\<Union>C \<in> cocountable_sets_in X"
proof-
    let ?U="(\<Union>C)"
    have B0:"?U \<in> Pow X"
      apply(auto simp add: assms cocountable_sets_in_def)
      by (smt (verit, ccfv_threshold) UnionI Union_Pow_eq assms cocountable_sets_in_def mem_Collect_eq subset_eq)
    have B1:"?U \<noteq> {} \<Longrightarrow> is_countable (X-?U)"
    proof-
      assume A1:"?U \<noteq> {}"
      have B2:"X-?U=(\<Inter>u \<in> C. (X-u))"
        using A1 by blast
      show "is_countable (X-?U)"
        by (metis A1 B2 Diff_Diff_Int Inter_lower Union_empty_conv assms image_eqI in_cocountable_sets_in_imp1 inf.absorb_iff2 inj_on_diff is_countable_def subset_eq)
    qed
  show ?thesis
    using B0 B1 cocountable_sets_in_def by blast
qed

lemma cofinite_binf_closed:
  assumes A0:"a1 \<in> cofinite_sets_in X \<and> a2 \<in> cofinite_sets_in X"
  shows "a1 \<inter> a2 \<in> cofinite_sets_in X"
proof-
  have B6:"a1 \<inter> a2 \<noteq> {} \<Longrightarrow> finite (X-(a1 \<inter> a2))"
  proof-
    assume A1:"a1 \<inter> a2 \<noteq> {}" 
     have B7:"finite (X-a1) \<and> (finite (X-a2))"
       using A1 assms in_cofinite_sets_in_imp1 by blast
    show "finite (X-(a1 \<inter> a2))"
      by (simp add: B7 Diff_Int)
  qed
  show "a1 \<inter> a2 \<in> cofinite_sets_in X"
    by (metis B6 PowD PowI assms in_cofinite_iff1 in_cofinite_sets_in_imp1 le_infI2)
qed
  

lemma countable_subset_is_countable1:
  "A \<subseteq> B \<and> is_countable B \<Longrightarrow> is_countable A"
  apply(auto simp: is_countable_def)
  using inj_on_subset by blast

lemma countable_subset_is_countable2:
  "A \<subseteq> X \<and> (is_countable X) \<Longrightarrow> is_countable (X - A)"
  apply(auto simp add: is_countable_def)
  using inj_on_diff by blast

lemma countable_then_cocountable_discrete:
  assumes "is_countable X"
  shows "cocountable_sets_in X = Pow X "
  apply(simp add: cocountable_sets_in_def)
  by (simp add: Collect_mono Pow_def assms countable_subset_is_countable2 subset_antisym)


lemma cofinite_top_is_top:
  "is_topology_on (cofinite_sets_in X) X"
proof-
  define T where "T= (cofinite_sets_in X)"
  have T0:"T \<in> Dpow X"
    by (simp add: Collect_mono Pow_def cofinite_sets_in_def T_def)
  have T1:" (top_u1 T)"
    by (simp add: T_def cofinite_union_comp top_u1_def)
  have T2:"top_i3 T"
    by (simp add: T_def cofinite_binf_closed top_i3_def)
  have T3:"X \<in> T"
    by (simp add: T_def cofinite_sets_in_def)
  show ?thesis
    using T0 T1 T2 T3 T_def is_topology_on_def by auto
qed
(*
lemma cocountable_binf_closed:
  assumes A0:"a1 \<in> cocountable_sets_in X \<and> a2 \<in> cocountable_sets_in X"
  shows "a1 \<inter> a2 \<in> cocountable_sets_in X"
proof-
  have B6:"a1 \<inter> a2 \<noteq> {} \<Longrightarrow> is_countable (X-(a1 \<inter> a2))"
  proof-
    assume A1:"a1 \<inter> a2 \<noteq> {}" 
     have B7:"is_countable (X-a1) \<and> (is_countable (X-a2))"
       using A1 assms in_cocountable_sets_in_imp2 by auto
      have B8:"is_countable ((X - a1) \<union> (X - a2))"
        by (simp add: B7 is_countable_if_countable is_countable_imp_countable)
     show "is_countable (X-(a1 \<inter> a2))"
       by (simp add: B8 Diff_Int)
  qed
  show "a1 \<inter> a2 \<in> cocountable_sets_in X"
    by (metis B6 Pow_iff assms in_cocountable_iff1 in_cocountable_sets_in_imp1 le_infI2)
qed


lemma cocountable_top_is_top:
  " is_topology_on (cocountable_sets_in X) X"
proof-
  define T where "T= (cocountable_sets_in X)"
  have T0:"T \<in> Dpow X"
    using T_def in_cocountable_sets_in_imp1 by auto
  have T1:" (top_u1 T)"
    by (simp add: T_def cocountable_un_closed top_u1_def)
  have T2:"top_i3 T"
    by (simp add: T_def cocountable_binf_closed top_i3_def)
  have T3:"X \<in> T"
    by (simp add: T_def empty_countable in_cocountable_iff1)
  show ?thesis
    using T0 T1 T2 T3 T_def is_topology_on_def by auto
qed
*)
lemma particular_point_top_is_top:
  assumes "X \<noteq> {} \<and> a \<in> X"
  shows "is_topology_on (particular_point_top a X) X"
proof-
  define T where "T= (particular_point_top a X)"
  have T0:"T \<in> Dpow X"
    apply(simp add:  particular_point_top_def T_def)
    by blast
  have T1:" (top_u1 T)"
    apply(simp add:top_u1_def T_def particular_point_top_def)
    by blast
  have T2:"top_i3 T"
    apply(simp add:top_i3_def T_def particular_point_top_def)
    by auto
  have T3:"X \<in> T"
    by (simp add: T_def assms particular_point_top_def)
  show ?thesis
    using T0 T1 T2 T3 T_def is_topology_on_def by auto
qed

lemma excluded_point_top_is_top:
   "is_topology_on (excluded_point_top a X) X"
proof-
  define T where "T= (excluded_point_top a X)"
  have T0:"T \<in> Dpow X"
    apply(simp add:  excluded_point_top_def T_def)
    by blast
  have T1:" (top_u1 T)"
    apply(simp add:top_u1_def T_def excluded_point_top_def)
    by blast
  have T2:"top_i3 T"
    apply(simp add:top_i3_def T_def excluded_point_top_def)
    by auto
  have T3:"X \<in> T"
    by (simp add: T_def excluded_point_top_def)
  show ?thesis
    using T0 T1 T2 T3 T_def is_topology_on_def by auto
qed

lemma ideal_contains_bot:
  assumes "is_ideal (I::'a set set)"
  shows "{} \<in> I"
  by (meson UNIV_I assms empty_subsetI is_downclosed_in_def is_ideal_def is_ideal_in_def is_inhabited_imp)

lemma set_ideal_bsup_closed:
  assumes "is_ideal (I::'a set set)" and "I1 \<in> I \<and> I2 \<in> I"
  shows " I1 \<union> I2 \<in> I"
  by (meson assms(1) assms(2) down_closure_in_univ_imp is_ideal_def is_ideal_in_def updir_sup)

lemma ideal_complement_top:
  fixes T I::"'a set set" and  X::"'a set" 
  assumes A0:"I \<subseteq> Pow X" and A1:"is_ideal I" and A2:"is_topology_on T X"
  defines "B \<equiv> {x \<in> Pow X.   \<exists>u \<in> T. \<exists>i \<in> I. x = u - i }" 
  shows "is_base3_for_topology B X"
  proof-
    have B0:"is_base_3_covering B X"
    proof-
      have B01:"B \<subseteq> Pow X"
        apply(simp add: B_def)
        by blast
      have B02:"(\<And>(x::'a). x\<in>X \<longrightarrow> (\<exists>U::'a set\<in>B. x \<in> U))"
      proof
        fix x assume A3:"x \<in> X"
        have B020:"{} \<in> I \<and> X \<in> T"
          using A2 ideal_contains_bot is_topology_on_def local.A1 by blast
        have B030:"X \<in> B"
          using B020 B_def by blast
        show "\<exists>U::'a set\<in>B. x \<in> U" 
          using B030 A3 by blast
      qed
      show ?thesis
        by (simp add: B01 B02 is_base_3_covering_if)
    qed
    have B1:"is_base_3_intercont B X"
    proof-  
      have B14:"\<And>B1 B2 x. (B1 \<in> B \<and> B2 \<in> B \<and> x \<in> B1 \<inter> B2) \<longrightarrow> (\<exists>B3 \<in> B.  x \<in> B3 \<and> B3 \<subseteq> B1 \<and> B3 \<subseteq> B2)"
      proof
        fix B1 B2 x assume A4:"(B1 \<in> B \<and> B2 \<in> B \<and> x \<in> B1 \<inter> B2)"
        obtain U1 I1 U2 I2 where B10:"U1 \<in> T \<and> U2 \<in> T \<and> I1 \<in> I \<and> I2 \<in> I \<and> B1=U1-I1 \<and> B2=U2-I2"
          using A4 B_def by blast
        have B11:"B1 \<inter> B2 = (U1 \<inter> U2) - (I1 \<union> I2)"
          using B10 by fastforce
        have B12:" (U1 \<inter> U2)  \<in> T \<and> (I1 \<union> I2) \<in> I"
          by (meson A2 B10 is_topology_on_def local.A1 set_ideal_bsup_closed top_i3_def)
        have B13:"(B1 \<inter> B2 \<in> B)"
          by (metis (mono_tags, lifting) A2 B11 B12 B_def CollectI Diff_subset PowI Sup_upper2 carrier_is_top_un)
        show  "(\<exists>B3 \<in> B.  x \<in> B3 \<and> B3 \<subseteq> B1 \<and> B3 \<subseteq>B2)"
          by (meson A4 B13 inf.cobounded2 inf_sup_ord(1))
      qed
    show ?thesis
      by (simp add: B14 is_base_3_intercont_if)
  qed
  show ?thesis
    by (simp add: B0 B1 is_base3_for_topology_def)
qed
   

lemma arb_sup_cl_generates_top_if_base:
  assumes "is_base3_for_topology B X"
  shows "arb_sup_cl B = topology_generated_by_in B X" (is "?L=?R")
  proof-
    have B0:"is_topology_on ?L X"
      by (simp add: assms base34_generates_top)
    have B1:"B \<subseteq> ?L"
      by (simp add: arb_sup_cl_extensive)
    have B2:"?R \<le> ?L"
      by (meson B0 arb_sup_cl_extensive assms generated_topology_least1 is_base3_for_topology_imp2)
    have B3:"?L \<le> ?R"
    proof
      fix x assume A0:"x \<in> ?L"
      obtain E where B30:"E \<subseteq> B \<and> x = \<Union> E"
        by (metis A0 arb_sup_cl_imp1 sup_un_sets)
      have B31:"E \<subseteq> ?R"
        by (meson B30 assms dual_order.trans generated_topology_upper0 is_base3_for_topology_imp2)
      show "x \<in> ?R"
        using B30 B31 generated_topology2 top_u1_def by blast
  qed
  show ?thesis
    by (simp add: B2 B3 order_class.order_eq_iff)
qed


lemma finf_cl_yields_base:
  assumes "E \<in> Dpow X" and "E \<noteq> {}"
  defines "B \<equiv> fin_inf_cl_in E (Pow X)"
  shows "is_base3_for_topology B X"
  apply(auto simp add:is_base3_for_topology_def)
  proof-
    show "is_base_3_covering B X"
    proof-
      have B0:"B \<le> Pow X"
        by (simp add: B_def fin_inf_cl_in_range)
       have B1:"X \<in> B"
         by (simp add: B_def fin_inf_cl_in_top)
       have B2:"\<forall>x \<in> X. \<exists>U \<in> B. x \<in> U"
         using B1 by blast
        show ?thesis
          by (simp add: B0 B2 is_base_3_covering_def)
    qed
    show "is_base_3_intercont B X"
    proof-
      have B0:"\<And>B1 B2 x. (B1 \<in> B) \<and> (B2 \<in> B) \<and> (x \<in> B1 \<inter> B2) \<longrightarrow> (\<exists>B3 \<in> B. x \<in> B3 \<and> B3 \<subseteq> B1 \<inter> B2)"
      proof
        fix B1 B2 x assume A0:"(B1 \<in> B) \<and> (B2 \<in> B) \<and> (x \<in> B1 \<inter> B2)"
        obtain E1 where B3:"E1 \<in> Fpow E \<and> has_inf_in E1 (Pow X) \<and> InfIn E1 (Pow X) = B1"
          using A0 B_def fin_inf_cl_in_imp0 by blast
        obtain E2 where B4:"E2 \<in> Fpow E \<and> has_inf_in E2 (Pow X) \<and> InfIn E2 (Pow X) = B2"
          using A0 B_def fin_inf_cl_in_imp0 by blast
        have B5:"E1 \<union> E2 \<in> Fpow E"
          by (metis (mono_tags, lifting) B3 B4 Fpow_def Un_subset_iff finite_Un mem_Collect_eq)
        have B6:"is_inf_in (B1 \<inter> B2) (E1 \<union> E2) (Pow X)"
          by (smt (verit, del_insts) B3 B4 PowD PowI Un_iff inf_equiv1 infin_is_inf le_infI1 le_inf_iff)
        have B7:"has_inf_in (E1 \<union> E2) (Pow X)"
          by (meson B6 has_inf_in_def has_max_iff is_inf_in_imp1 is_max_iff)
        have B8:"InfIn (E1 \<union> E2) (Pow X) = (B1 \<inter> B2)"
          using B6 is_inf_in_inf_eq by blast
        have B9:"B1 \<inter> B2 \<in> B"
        apply(simp add:B_def)
          using B5 B7 B8 fin_inf_cl_in_if1 by blast
        show "(\<exists>B3 \<in> B. x \<in> B3 \<and> B3 \<subseteq> B1 \<inter> B2)"
          by (meson A0 B9 dual_order.eq_iff)
      qed
    show ?thesis
      by (meson B0 is_base_3_intercont_if)
   qed   
qed 

lemma topology_generated_by_is_cl1:
  assumes "E \<in> Dpow X" and "E \<noteq> {}"
  shows " is_topology_on (arb_sup_cl (fin_inf_cl_in E (Pow X))) X"
  by (meson assms(1) assms(2) base34_generates_top finf_cl_yields_base)

lemma topology_generated_by_is_cl2:
  assumes "E \<in> Dpow X" and "E \<noteq> {}"
  shows " E \<le> (arb_sup_cl (fin_inf_cl_in E (Pow X)))"
  using arb_sup_cl_extensive assms(1) fin_inf_cl_in_extensive by fastforce

lemma topology_generated_by_is_cl3:
  assumes "E \<in> Dpow X" and "E \<noteq> {}"
  shows "(arb_sup_cl (fin_inf_cl_in E (Pow X))) \<ge> topology_generated_in E X"
  by (metis assms(1) assms(2) generated_topology_is_sup_in2 generated_topology_least1 topology_generated_by_is_cl1 topology_generated_by_is_cl2)

lemma topology_generated_by_is_cl4:
  assumes "E \<in> Dpow X" and "E \<noteq> {}"
  shows "(arb_sup_cl (fin_inf_cl_in E (Pow X))) \<ge> topology_generated_by_in E X"
  by (meson assms(1) assms(2) generated_topology_least1 topology_generated_by_is_cl1 topology_generated_by_is_cl2)

lemma topology_generated_by_is_cl5:
  assumes "E \<in> Dpow X" and "E \<noteq> {}"
  shows "(arb_sup_cl (fin_inf_cl_in E (Pow X))) \<le> topology_generated_by_in E X"
proof
  fix A assume A2:"A \<in> (arb_sup_cl (fin_inf_cl_in E (Pow X)))"
  show "A \<in>topology_generated_by_in E X"
  proof-
    obtain EA1 where B0:"EA1 \<subseteq> (fin_inf_cl_in E (Pow X)) \<and> A=(\<Union>EA1)"
      by (metis A2 arb_sup_cl_imp1 sup_un_sets)
    have B1:"\<And>x. x \<in> EA1 \<longrightarrow> (\<exists>Fx \<in> Fpow E. x=InfIn Fx (Pow X))"
      using B0 fin_inf_cl_in_imp0 by blast
    have B2:"\<And>Fx. Fx \<in> Fpow_ne E \<longrightarrow> InfIn Fx (Pow X) \<in>  topology_generated_by_in E X"
    proof
      fix Fx assume B2A0:"Fx \<in> Fpow_ne E"
      have B20:"\<And>x. x \<in> Fx \<longrightarrow>  \<Inter>Fx \<le> x"
        by (simp add: Inter_lower)
      have B21:"\<And>x. x \<in> Fx \<longrightarrow> x \<in> Pow X"
        using B2A0 Fpow_subset_Pow assms(1) by blast
      have B22:"\<Inter>Fx \<in> Pow X"
        using B21 B2A0 by blast
      have B23:" \<Inter>Fx \<in> lb_set_in Fx (Pow X)"
        using B22 lb_set_in_mem_iff by blast
      have B20:"InfIn Fx (Pow X) = \<Inter>Fx"
        by (metis B21 B22 Pow_iff inf.absorb_iff2 inter_complete_lat subsetI)
       show "InfIn Fx (Pow X) \<in>  topology_generated_by_in E X"
         by (metis B20 B2A0 assms(1) fpow_ne_imp generated_topology4 generated_topology_upper0 subset_trans top_i3_induct)
    qed
    have B3:"\<And>x. x \<in> EA1 \<longrightarrow> x \<in> (topology_generated_by_in E X)"
    proof
      fix x assume B3A0:"x \<in> EA1"
      obtain Fx where B30:"Fx\<in> Fpow E \<and>  x=InfIn Fx (Pow X)"
        using B1 B3A0 by blast
      show "x \<in> (topology_generated_by_in E X)"
      proof(cases "Fx = {}")
        case True
        have B31:"x=X"
          by (simp add: B30 True empty_inter_is_carrier)
        then show ?thesis
          using generated_topology1 by blast
      next
        case False
        then show ?thesis
          by (simp add: B2 B30)
      qed
    qed
    show ?thesis
      by (metis B0 B3 generated_topology2 subsetI top_u1_def)
  qed
qed

lemma topology_generated_by_is_cl6:
  assumes "E \<in> Dpow X" and "E \<noteq> {}"
  shows "(arb_sup_cl (fin_inf_cl_in E (Pow X))) = topology_generated_by_in E X"
  by (meson assms(1) assms(2) subset_antisym topology_generated_by_is_cl4 topology_generated_by_is_cl5)

lemma topology_generated_by_is_cl7:
  assumes "E \<in> Dpow X" and "E \<noteq> {}"
  shows "(arb_sup_cl (fin_inf_cl_in E (Pow X))) = topology_generated_in E X"
  by (metis assms(1) assms(2) generated_topology_is_sup_in2 topology_generated_by_is_cl6)


lemma interior_equiv:
  assumes "A \<subseteq> X"
  shows "interior1 A T X = interior2 A T X"
proof-
  have B0:"interior1 A T X \<le> interior2 A T X"
  apply(simp add:interior1_def interior2_def is_interior_point_def nhoods_of_in_def)
    using assms subsetD by auto
 have B1:"interior2 A T X \<le> interior1 A T X"
  apply(simp add:interior1_def interior2_def is_interior_point_def nhoods_of_in_def)
   by blast
  show ?thesis
    by (simp add: B0 B1 set_eq_subset)
qed




lemma closure_is_extensive:
  assumes "is_topology_on T X"
  shows "is_extensive (\<lambda>A. closure1 A T X)"
  by (metis (no_types, lifting) Inter_greatest closure1_def is_extensive_def mem_Collect_eq)


lemma closure_is_isotone0:
  assumes "is_topology_on T X" and "A \<le> B"
  shows "closure1 A T X \<le> closure1 B T X"
  apply(simp add:closure1_def)
  using assms(2) by auto

lemma closure_is_isotone:
  assumes "is_topology_on T X"
  shows "is_isotone (\<lambda>A. closure1 A T X)"
  by (simp add: assms closure_is_isotone0 is_isotone_def)

lemma closure_is_idempotent0:
  assumes "is_topology_on T X"
  shows "closure1 (closure1 A T X) T X = closure1 A T X"
  apply(simp add:closure1_def)
  by auto

lemma closure_is_idempotent:
  assumes "is_topology_on T X"
  shows "is_idempotent (\<lambda>A. closure1 A T X)"
  by (simp add: assms closure_is_idempotent0 is_idempotent_def)

lemma closure_is_closure:
  assumes "is_topology_on T X"
  shows "is_closure (\<lambda>A. closure1 A T X)"
  by (simp add: assms closure_is_extensive closure_is_idempotent closure_is_isotone is_closure_def)


lemma closure_smallest_closed_simp:
  assumes "is_topology_on T X" and "A \<subseteq> X" and "(X - F) \<in> T" and "A \<subseteq> F" and "F \<subseteq> X"
  shows "(closure1 A T X) \<subseteq> F"
  by (simp add: Inf_lower assms(3) assms(4) assms(5) closure1_def)


lemma exists_nhood_disjoint_imp_notin_closure:
  assumes "is_topology_on T X" and "A \<le> X" and "x \<in> X" and
          "\<exists>U \<in> nhoods_of_in x T X. U \<inter> A = {}"
  shows "x \<notin> (closure1 A T X)"
proof-
  obtain V where B0:"V \<in> nhoods_of_in x T X \<and> V \<inter> A = {}"
    using assms(4) by blast
  obtain U where B1:"U \<in> T \<and> x \<in> U \<and> U \<subseteq> V"
    by (meson B0 nhoods_of_in_imp3)
  define F where "F = X - U"
  have B2:"A \<subseteq> F"
    using B0 B1 F_def assms(2) by auto
  have B3:"x \<in> U"
    by (simp add: B1)
  have B4:"x \<notin> F"
    by (simp add: B1 F_def)
  have B5:"X-F \<in> T"
    by (metis B1 F_def Union_upper assms(1) carrier_is_top_un double_diff trivial_in_top)
  have B6:"(closure1 A T X) \<subseteq> F"
    by (metis B2 B5 Diff_subset F_def assms(1) assms(2) closure_smallest_closed_simp)
  show "x \<notin> (closure1 A T X)"
    using B4 B6 by blast
qed

lemma closure_id_on_closed:
  assumes "is_topology_on T X" and "closure1 F T X = F"  and "F \<subseteq> X"
  shows "(X-F) \<in> T"
proof-
  define C where "C={K. K \<subseteq> X \<and> (X-K) \<in> T \<and> F \<subseteq> K}"
  have B0:"F=\<Inter>C"
    by (metis (mono_tags, lifting) C_def assms(2) closure1_def)
  have B1:"(X-F) = (\<Union>c \<in> C. (X - c))"
    using B0 by auto
  have B2:"\<forall>c \<in> C. (X - c) \<in> T"
    using C_def by fastforce
  have B3:"\<forall>c \<in> C. (X - c) \<subseteq> (X - F)"
    by (simp add: B0 Diff_mono Inter_lower)
  define U where "U = {U. \<exists>c \<in> C. U = X - c}"
  have B4:"U \<subseteq> T"
    using C_def U_def by blast
  have B5:"(X-F) = \<Union>U"
    by (simp add: B1 U_def image_def)
  show "(X-F) \<in> T"
    by (metis B4 B5 assms(1) is_topology_on_def top_u1_def)
qed

lemma notin_closur_imp_exists_nhood_disjoint:
  assumes "is_topology_on T X" and "A \<le> X" and "x \<in> X" and
          "x \<notin> (closure1 A T X)"
  shows "\<exists>U \<in> nhoods_of_in x T X. U \<inter> A = {}"
proof-
  define U where "U=X - (closure1 A T X)"
  have B0:"U \<in> T"
    by (metis Diff_cancel U_def assms(1) assms(2) closure_id_on_closed closure_is_idempotent0 closure_smallest_closed_simp subset_refl trivial_in_top)
  have B1:"x \<in> U"
    by (simp add: U_def assms(3) assms(4))
  have B2:"U \<in> nhoods_of_in x T X"
    by (metis B0 B1 Diff_subset U_def assms(3) open_is_nhood_in)
  have B3:"A \<subseteq> (closure1 A T X)"
    by (metis assms(1) closure_is_extensive is_extensive_def)
  have B4:"U \<inter> A = {}"
    using B3 U_def by blast
  show "\<exists>U \<in> nhoods_of_in x T X. U \<inter> A = {}"
    using B2 B4 by auto
qed


lemma closure_iff:
  assumes "is_topology_on T X" and "A \<le> X" and "x \<in> X"
  shows "x \<in> closure1 A T X \<longleftrightarrow> (\<forall>U \<in> nhoods_of_in x T X. U \<inter> A \<noteq> {})" (is "?L \<longleftrightarrow> ?R")
proof
  assume L:?L
  show ?R
    by (meson L assms(1) assms(2) assms(3) exists_nhood_disjoint_imp_notin_closure)
  next
  assume R:?R
  show ?L
    by (meson R assms(1) assms(2) assms(3) notin_closur_imp_exists_nhood_disjoint)
qed

lemma closure_equiv:
  assumes "A \<subseteq> X" and "is_topology_on T X"
  shows "closure1 A T X = closure2 A T X"
proof-
  have B0:"closure1 A T X \<le> closure2 A T X"
  apply(simp add:closure1_def closure2_def is_adherent_point_def)
  proof
    fix x assume A0:"x \<in> \<Inter> {F::'a set. F \<subseteq> X \<and> X - F \<in> T \<and> A \<subseteq> F} "
    show "x \<in> {x::'a \<in> X. \<forall>V::'a set. V \<in> nhoods_of_in x T X \<longrightarrow> A \<inter> V \<noteq> {}}"
    proof-
      have B0:"x \<in> X"
        using A0 assms(1) assms(2) trivial_in_top by force
      have B1:"\<And>V::'a set. V \<in> nhoods_of_in x T X \<longrightarrow> A \<inter> V \<noteq> {}"
        by (metis A0 B0 assms(1) assms(2) closure1_def exists_nhood_disjoint_imp_notin_closure inf_commute)
      show ?thesis
        by (simp add: B0 B1)
    qed
  qed
  have B1:"closure2 A T X \<le> closure1 A T X"
    apply(simp add:closure1_def closure2_def is_adherent_point_def)
    proof
      fix x assume A1:"x \<in> {x::'a \<in> X. \<forall>V::'a set. V \<in> nhoods_of_in x T X \<longrightarrow> A \<inter> V \<noteq> {}}"
      show "x \<in> \<Inter> {F::'a set. F \<subseteq> X \<and> X - F \<in> T \<and> A \<subseteq> F}"
      proof-
          have B0:"\<And>F. F \<subseteq> X \<and> X - F \<in> T \<and> A \<subseteq> F \<longrightarrow> x \<in> F"
          proof
           fix F assume A3:"F \<subseteq> X \<and> X - F \<in> T \<and> A \<subseteq> F"
           show "x \<in> F"
             by (smt (verit, ccfv_threshold) A3 CollectD DiffI Diff_eq_empty_iff Diff_subset Int_Diff inf.order_iff local.A1 open_is_nhood_in)
          qed
        show ?thesis
          using B0 by blast
      qed
  qed
  show ?thesis
    by (simp add: B0 B1 subset_antisym)
qed



  

lemma closure_of_closed:
  assumes "is_topology_on T X" and "(X-F) \<in> T" and "F \<subseteq> X"
  shows "closure1 F T X = F"
  apply(simp add:closure1_def)
  using assms(2) assms(3) by blast



lemma interior_of_open:
  assumes "is_topology_on T X" and "U \<in> T"
  shows "interior1 U T X = U"
  apply(simp add:interior1_def)
  using assms(2) by blast

lemma finite_closure_in_cofinite:
  assumes "finite F" and "F \<subseteq> X"
  shows "closure1 F (cofinite_sets_in X) X = F"
  by (simp add: Diff_Diff_Int assms closure_of_closed cofinite_top_is_top in_cofinite_iff1) 


lemma interior_deflationary:
  assumes "is_topology_on T X" and "A \<le> X"
  shows "interior1 A T X \<le> A"
  by (simp add: Sup_le_iff interior1_def)

lemma interior_monotone:
  assumes "is_topology_on T X" and "A \<le> X" and "B \<le> X" and "A \<le> B"
  shows "interior1 A T X \<le> interior1 B T X"
  by (smt (verit) Union_iff assms(4) dual_order.trans interior1_def mem_Collect_eq subsetI)

lemma interior_idempotent:
  assumes "is_topology_on T X" and "A \<le> X"
  shows "interior1 (interior1 A T X) T X = interior1 A T X"
  by (smt (verit) Sup_le_iff assms(1) assms(2) dual_order.refl dual_order.trans interior1_def interior_deflationary mem_Collect_eq subset_antisym)

lemma interior_id_iff:
  assumes "is_topology_on T X" and "A \<le> X"
  shows "interior1 A T X = A \<longleftrightarrow> A \<in> T" (is "?L \<longleftrightarrow> ?R")
proof
  assume L:?L
  show ?R
    by (smt (verit, best) CollectD L PowI Union_iff assms(1) assms(2) interior1_def open_iff_nhp)
  next
  assume R:?R
  show ?L
    by (simp add: R assms(1) interior_of_open)
qed
lemma interior_un_smaller_opens:
  assumes "is_topology_on T X" and "A \<le> X" 
  shows "interior1 A T X = \<Union>(smaller_open_sets A T X)"
  by (simp add:interior1_def smaller_open_sets_def)

lemma larger_closed_always_ne:
  assumes "is_topology_on T X" and "A \<le> X" 
  shows "X \<in> larger_closed_sets A T X"
  using assms(1) assms(2) larger_closed_sets_mem_iff trivial_in_top by fastforce

lemma closure_inter_larger_closed:
  assumes "is_topology_on T X" and "A \<le> X" 
  shows "closure1 A T X = \<Inter>(larger_closed_sets A T X)"
  by(simp add:closure1_def larger_closed_sets_def)

lemma smaller_open_set_iff:
  assumes "is_topology_on T X" and "A \<le> X" and "F \<subseteq> X"
  shows "F \<in> larger_closed_sets A T X \<longleftrightarrow> (X - F) \<in> smaller_open_sets (X - A) T X" (is "?L \<longleftrightarrow> ?R")
proof
  assume L:?L
  show ?R
    by (meson Diff_mono Diff_subset L assms(1) assms(2) larger_closed_sets_mem_iff order_refl smaller_open_sets_mem_iff)
  next
  assume R:?R
  show ?L
  proof-
    have B0:"(X - F) \<in> smaller_open_sets (X - A) T X"
      by (simp add: R)
    have B1:"(X - F) \<in> T \<and> (X - A) \<supseteq> (X - F)"
      using R smaller_open_sets_def by auto
    have B2:"F \<supseteq> A"
      using B1 assms(2) by auto
    show ?thesis
      by (simp add: B1 B2 assms(1) assms(2) assms(3) larger_closed_sets_mem_iff)
  qed
qed

lemma complement_of_interior_is_closure_of_complement:
  assumes "is_topology_on T X" and "A \<le> X" 
  shows "X - (interior1 A T X) = closure1 (X - A) T X"
proof-
  have B0:"\<forall>F \<in> Pow X. F \<in> (larger_closed_sets (X - A) T X) \<longleftrightarrow> (X - F) \<in> (smaller_open_sets A T X)"
    by (simp add: Diff_Diff_Int assms(1) assms(2) inf.absorb2 larger_closed_sets_complement)
  have B1:"X-(interior1 A T X) = X - (\<Union>(smaller_open_sets A T X))"
    by (simp add: interior1_def smaller_open_sets_def)
  have B2:"... = X - (\<Union>U \<in> smaller_open_sets A T X. U)"
    by simp
  have B3:"... = (\<Inter>U \<in> smaller_open_sets A T X. X - U)"
    by (smt (verit, ccfv_threshold) Diff_eq_empty_iff Diff_subset INT_extend_simps(4) Inter_lower SUP_upper Sup.SUP_cong Union_empty assms(1) assms(2) image_is_empty smaller_open_sets_mem_iff trivial_in_top)
 have B4:"closure1 (X - A) T X = (\<Inter>F \<in> larger_closed_sets (X - A) T X. F)"
   by (simp add: assms(1) closure_inter_larger_closed)
  have B5:"... = (\<Inter>U \<in> smaller_open_sets A T X. X - U)"
    by (smt (z3) B0 Diff_subset INF_eq Pow_iff Sup_upper assms(1) assms(2) carrier_is_top_un double_diff equalityE larger_closed_sets_mem_iff smaller_open_sets_mem_iff)
  show ?thesis
    using B1 B2 B3 B4 B5 by presburger
qed

lemma complement_of_closure_is_interior_of_complement:
  assumes "is_topology_on T X" and "A \<le> X" 
  shows "X - (closure1 A T X) = interior1 (X - A) T X"
  by (smt (verit) Diff_Diff_Int assms(1) assms(2) complement_of_interior_is_closure_of_complement inf.absorb_iff2 interior_deflationary subset_trans)


lemma interior_from_closure:
  assumes "is_topology_on T X" and "A \<le> X" 
  shows "interior1 A T X = X - (closure1 (X - A) T X)"
  by (metis Diff_Diff_Int assms(1) assms(2) complement_of_closure_is_interior_of_complement inf.absorb_iff2)


lemma closure_from_interior:
  assumes "is_topology_on T X" and "A \<le> X" 
  shows "closure1 A T X = X - (interior1 (X - A) T X)"
  by (metis Diff_Diff_Int assms(1) assms(2) complement_of_interior_is_closure_of_complement inf.absorb_iff2)

lemma continuous_at_imp_open_preimage:
  fixes T::"'a set set" and X::"'a set" and 
        S::"'b set set" and Y::"'b set" and
        f::"'a \<Rightarrow> 'b"
  assumes A0:"is_topology_on T X" and A1:"is_topology_on S Y" and A2:"f-`Y = X" and A3:"\<forall>x \<in> X. continuous_at f x T X S Y"  
  shows "\<forall>V \<in> S. f-`V \<in> T"
proof
  fix V assume A4:"V \<in> S"
  have B0:"\<forall>x \<in> f-`V. f x \<in> V"
    by simp
  have B1:"\<forall>x \<in> f-`V. V \<in> nhoods_of (f x) S Y"
    using A4 nhoods_of_def by fastforce
  have B2:"\<forall>x \<in> f-`V. \<exists>Vx \<in> nhoods_of x T X. f`Vx \<le> V"
    by (metis A2 A3 A4 B1 UN_I carrier_is_top_un continuous_at_def local.A1 vimage_Union)
  have B3:"\<forall>x \<in> f-`V. \<exists>Ux \<in> T. x \<in> Ux \<and> f`Ux \<le> V"
    by (meson B2 dual_order.trans image_subset_iff_subset_vimage nhoods_of_mem_iff)
  have B4:"f-`V \<in> Pow X"
    by (metis A2 A4 PowI Union_upper carrier_is_top_un local.A1 vimage_mono)
  show"f-`V \<in> T"
    by (meson A0 B3 B4 image_subset_iff_subset_vimage open_iff_nhp)
qed


lemma open_preimage_imp_continuous_at:
  fixes T::"'a set set" and X::"'a set" and 
        S::"'b set set" and Y::"'b set" and
        f::"'a \<Rightarrow> 'b"
  assumes A0:"is_topology_on T X" and A1:"is_topology_on S Y" and A2:"f-`Y = X" and A3:"\<forall>V \<in> S. f-`V \<in> T"
  shows "\<forall>x \<in> X. continuous_at f x T X S Y"
proof
  fix x assume A4:"x \<in> X"
  show "continuous_at f x T X S Y"
  apply(simp add:continuous_at_def)
    by (meson A3 image_vimage_subset nhoods_of_mem_iff vimageI2 vimage_mono)
qed

lemma continuous_at_imp_closed_preimage:
  fixes T::"'a set set" and X::"'a set" and 
        S::"'b set set" and Y::"'b set" and
        f::"'a \<Rightarrow> 'b"
  assumes A0:"is_topology_on T X" and A1:"is_topology_on S Y" and A2:"f-`Y = X" and A3:"\<forall>x \<in> X. continuous_at f x T X S Y"  
  shows "\<forall>V \<in> S. X-(f-`(Y-V)) \<in> T"
proof
  fix V assume A4:"V \<in> S"
  have B0:"X-(f-`(Y-V)) = f-`V"
    using A2 A4 carrier_is_top_un local.A1 by fastforce
  show "X-(f-`(Y-V)) \<in> T"
    using A0 A2 A3 A4 B0 continuous_at_imp_open_preimage local.A1 by force
qed

lemma closed_preimage_imp_continuous_at:
  fixes T::"'a set set" and X::"'a set" and 
        S::"'b set set" and Y::"'b set" and
        f::"'a \<Rightarrow> 'b"
  assumes A0:"is_topology_on T X" and A1:"is_topology_on S Y" and A2:"f-`Y = X" and A3:"\<forall>V \<in> S. X-(f-`(Y-V)) \<in> T"
  shows "\<forall>x \<in> X. continuous_at f x T X S Y"
proof-
  have B0:"\<forall>V \<in> S. f-`V \<in> T"
    by (metis A2 A3 Sup_upper carrier_is_top_un double_diff image_subset_iff_subset_vimage image_vimage_subset local.A1 vimage_Diff vimage_mono)
  show ?thesis
    by (simp add: A0 A2 B0 local.A1 open_preimage_imp_continuous_at)
qed

lemma continuous_then_image_closure_subseteq_closure_image:
  fixes T::"'a set set" and X::"'a set" and 
        S::"'b set set" and Y::"'b set" and
        f::"'a \<Rightarrow> 'b"
  assumes A0:"is_topology_on T X" and A1:"is_topology_on S Y" and A2:"f-`Y = X"  and A3:"\<forall>x \<in> X. continuous_at f x T X S Y"
  shows "\<forall>A \<in> Pow X. f`(closure1 A T X) \<subseteq> closure1 (f`A) S Y"
proof
  fix A assume A4:"A \<in> Pow X"
  define fA where "fA = f`A"
  define ClfA where "ClfA = closure1 fA S Y"
  define ClA where "ClA =  closure1 A T X"
  show "f`(closure1 A T X) \<subseteq> ClfA"
  proof-
    have B0:"fA \<subseteq> ClfA"
      using ClfA_def closure1_def by fastforce 
    have B1:"A \<subseteq> f-`fA"
      using fA_def by force
    have B2:"... \<subseteq>  f-`(ClfA)"
      using B0 by blast
    have B3:"X -  f-`(ClfA) \<in> T"
      by (metis A0 A2 A3 A4 ClfA_def Diff_subset PowD closure_from_interior closure_id_on_closed closure_is_idempotent0 continuous_at_imp_open_preimage fA_def image_subset_iff_subset_vimage local.A1 vimage_Diff)
    have B4:"A \<subseteq> f-`(ClfA)"
      using B1 B2 by auto
    have B5:"ClA \<subseteq>  f-`(ClfA)"
      by (metis A0 A2 A4 B3 B4 ClA_def ClfA_def Inter_lower Sup_upper Union_Pow_eq closure_inter_larger_closed closure_smallest_closed_simp fA_def image_subset_iff_subset_vimage larger_closed_always_ne local.A1 vimage_mono)
    show ?thesis
      using B5 ClA_def by blast
  qed
qed
  
(*TODO: theres another three of these to complete the cycle proof of equivalences*)


lemma continuous_then_closure_vimage_subseteq_vimage_closure:
  fixes T::"'a set set" and X::"'a set" and 
        S::"'b set set" and Y::"'b set" and
        f::"'a \<Rightarrow> 'b"
  assumes A0:"is_topology_on T X" and A1:"is_topology_on S Y" and A2:"f-`Y = X"  and A3:"\<forall>A \<in> Pow X. f`(closure1 A T X) \<subseteq> closure1 (f`A) S Y"
  shows "\<forall>B \<in> Pow Y. closure1 (f-`B) T X \<subseteq> f-`(closure1 B S Y)"
proof
  fix B assume A4:"B \<in> Pow Y"
  have B0:"f`(closure1 (f-`(B)) T X) \<subseteq> closure1 (f`(f-`B)) S Y"
    by (metis A2 A3 A4 PowD PowI vimage_mono)
  have B1:"... \<subseteq> closure1 B S Y"
    by (simp add: closure_is_isotone0 local.A1)
  show "closure1 (f-`(B)) T X \<subseteq> f-`(closure1 B S Y)"
    using B0 B1 by blast
qed


lemma continuous_then_vimage_interior_subseteq_interior_vimage:
  fixes T::"'a set set" and X::"'a set" and 
        S::"'b set set" and Y::"'b set" and
        f::"'a \<Rightarrow> 'b"
  assumes A0:"is_topology_on T X" and A1:"is_topology_on S Y" and A2:"f-`Y = X"  and A3:"\<forall>B \<in> Pow Y. closure1 (f-`B) T X \<subseteq> f-`(closure1 B S Y)"
  shows "\<forall>B \<in> Pow Y. f-`(interior1 B S Y)  \<subseteq> interior1 (f-`B) T X"
proof
  fix B assume A4:"B \<in> Pow Y"
  define YB where "YB=Y-B"
  have B0:"closure1 (f-`(YB)) T X \<subseteq>  f-`(closure1 YB S Y)"
    by (simp add: A3 YB_def)
  have B1:"X - (f-`(closure1 YB S Y)) \<subseteq> X - (closure1 (f-`(YB)) T X)"
    by (simp add: B0 Diff_mono)
  have B2:"f-`(interior1 B S Y) = (f-`(Y - (closure1 (Y - B) S Y)))"
    by (metis A4 PowD interior_from_closure local.A1)
  have B3:"... = X - (f-`(closure1 (Y - B) S Y))"
    by (simp add: A2 vimage_Diff)
  have B4:"... \<subseteq> X - (closure1 (f-`(Y - B)) T X)"
    using B1 YB_def by blast
  have B5:"... = X - (closure1 (X - (f-`B)) T X)"
    by (simp add: A2 vimage_Diff)
  have B6:"... = interior1 (f-`B) T X"
    by (metis A0 A2 A4 PowD interior_from_closure vimage_mono)
  show "f-`(interior1 B S Y)  \<subseteq> interior1 (f-`B) T X"
    using B1 B2 B3 B5 B6 YB_def by auto
qed


lemma vimage_interior_subseteq_interior_vimage_imp_open_vimage:
  fixes T::"'a set set" and X::"'a set" and 
        S::"'b set set" and Y::"'b set" and
        f::"'a \<Rightarrow> 'b"
  assumes A0:"is_topology_on T X" and A1:"is_topology_on S Y" and A2:"f-`Y = X"  and A3: "\<forall>B \<in> Pow Y. f-`(interior1 B S Y)  \<subseteq> interior1 (f-`B) T X"
  shows "\<forall>V \<in> S. f-`V \<in> T"
proof
  fix V assume A4:"V \<in> S"
  have B0:"interior1 V S Y = V"
    by (simp add: A4 interior_of_open local.A1)
  have B1:"f-`V = f-`(interior1 V S Y)"
    by (simp add: B0)
  have B2:"... \<subseteq> interior1 (f-`(V)) T X"
    using A3 A4 carrier_is_top_un local.A1 by force
  have B3:" interior1 (f-`(V)) T X \<subseteq> (f-`(V))"
    by (metis A0 A2 A4 Union_upper carrier_is_top_un interior_deflationary local.A1 vimage_mono)
  have B4:"(f-`(V)) = interior1 (f-`(V)) T X"
    using B0 B2 B3 by auto
  show "f-`V \<in> T"
    by (metis A0 A2 A4 B4 Sup_upper carrier_is_top_un interior_id_iff local.A1 vimage_mono)
qed

lemma subspace_is_top:
  assumes "is_topology_on T X" and "A \<le> X"
  defines "TA \<equiv> {UA \<in> Pow A. \<exists>U \<in> T. UA = U \<inter> A}"
  shows "is_topology_on TA A"
  proof-
    have T0:"TA \<subseteq> Pow A"
      using TA_def by fastforce
    have T1:"top_u1 TA"
    proof-
      have T10:"\<And>E. E \<subseteq> TA \<longrightarrow> \<Union> E \<in> TA"
      proof
        fix E assume A0:"E\<subseteq>TA" 
        define F where "F = (\<lambda>UA. SOME U. U \<in> T \<and> UA = U \<inter> A)"
        have B0:"\<forall>UA \<in> E.  UA \<in> Pow A \<and> (\<exists>U \<in> T. UA = U \<inter> A)"
          using A0 TA_def by blast
        have B1:"\<forall>UA \<in> E. ((F UA) \<in> T \<and>  UA = (F UA) \<inter> A)"
          by (smt (verit, best) B0 F_def someI)
        have B2:"F`E \<subseteq> T"
          using B1 by blast
        have B3:"\<Union>(F`E) \<in> T"
          by (meson B2 assms(1) is_topology_on_def top_u1_def)
        have B4:"A \<inter> (\<Union>(F`E)) = A \<inter> (\<Union>UA \<in> E. F UA)"
          by blast
        have B5:"... = (\<Union>UA \<in> E. (A \<inter> F UA))"
          by blast
        have B6:"\<forall>UA \<in> E. UA = (F UA) \<inter> A"
          by (simp add: B1)
        have B7:" (\<Union>UA \<in> E. (A \<inter> F UA)) = (\<Union>UA \<in> E. UA)"
          using B6 by blast
        have B8:"... = \<Union>E"
          by simp 
        show "(\<Union>E) \<in> TA"
          using B3 B7 B8 PowI TA_def by auto
      qed
      show ?thesis
        by (simp add: T10 top_u1_def)
    qed
  have T2:"top_i3 TA"    
  proof-  
    have T20:"\<And>a1 a2. a1 \<in> TA \<and> a2 \<in> TA \<longrightarrow> a1 \<inter> a2 \<in> TA"
    proof
      fix a1 a2 assume A1:"a1 \<in> TA \<and> a2 \<in> TA "
      obtain U1 U2 where B0:"U1 \<in> T \<and> U2 \<in> T \<and> a1 = U1 \<inter> A \<and> a2 = U2 \<inter> A"
        using TA_def local.A1 by blast
      have B1:"a1 \<inter> a2 = (U1 \<inter> U2) \<inter> A"
        using B0 by fastforce
      have B2:"U1 \<inter> U2 \<in> T"
        by (meson B0 assms(1) is_topology_on_def top_i3_def)
      show "a1 \<inter> a2 \<in> TA"
        using B1 B2 TA_def by blast
    qed
     show ?thesis
       by (simp add: T20 top_i3_def)
  qed
  have T3:"A \<in> TA"
    by (metis (mono_tags, lifting) CollectI Pow_top TA_def assms(1) assms(2) inf.absorb_iff2 trivial_in_top)
  show ?thesis
    by (simp add: T0 T1 T2 T3 is_topology_on_def)
qed



end