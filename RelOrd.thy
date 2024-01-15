theory RelOrd
  imports Main
begin

hide_const(open) List.list.Nil
no_notation List.list.Nil ("[]")  
no_notation Cons (infixr "#" 65) 


declare [[show_types]]
declare [[show_sorts]]
declare [[show_consts]]


definition L::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "L R A X Y \<equiv> (Y \<inter> (R``(X \<inter> A)))"

lemma L_imp1:
  "l \<in> L R A X Y \<Longrightarrow> l \<in> Y"
  by (simp add:L_def)

lemma L_imp2:
  "l \<in> L R A X Y \<Longrightarrow> l \<in>  R``(A \<inter> X)"
  apply (simp add:L_def)
  by blast



definition U::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "U R A X Y \<equiv> (Y \<inter> (converse(R)``(X \<inter> A)))"


lemma U_imp1:
  "u \<in> U R A X Y \<Longrightarrow> u \<in> Y"
  by (simp add:U_def)

lemma U_imp2:
  "u \<in> U R A X Y \<Longrightarrow> u \<in>  converse(R)``(A \<inter> X)"
  apply (simp add:U_def)
  by blast


abbreviation LRR::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "LRR R A X \<equiv> L R A X UNIV"

abbreviation LRD::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "LRD R A Y \<equiv> L R A UNIV Y"

abbreviation LNR::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "LNR R A \<equiv> L R A UNIV UNIV"


abbreviation URR::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "URR R A X \<equiv> U R A X UNIV"

abbreviation URD::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "URD R A Y \<equiv> U R A UNIV Y"

abbreviation UNR::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "UNR R A \<equiv> U R A UNIV UNIV"

context fixes R::"'a rel"
begin

abbreviation LCB::"'a set \<Rightarrow> 'a set" where
  "LCB A \<equiv> LNR R A"

abbreviation UCB::"'a set \<Rightarrow> 'a set" where
  "UCB A \<equiv> UNR R A"

end

definition min_set::" 'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set\<Rightarrow>  'a set" where
  "min_set R A X Y \<equiv> (L R A X Y) \<inter> A"

definition max_set::" 'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set\<Rightarrow>  'a set" where
  "max_set R A X Y \<equiv> (U R A X Y) \<inter> A"

definition is_min::"'a \<Rightarrow> 'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set\<Rightarrow> bool" where
  "is_min m R A X Y \<equiv> m \<in> (min_set R A X Y)"

definition is_max::"'a \<Rightarrow> 'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set\<Rightarrow> bool" where
  "is_max m R A X Y \<equiv> m \<in> max_set R A X Y"

definition has_min::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set\<Rightarrow> bool" where
  "has_min R A X Y \<equiv> min_set R A X Y \<noteq> {}"

definition has_max::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set\<Rightarrow> bool" where
  "has_max R A X Y \<equiv>  max_set R A X Y \<noteq> {}"

definition max::" 'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set\<Rightarrow>  'a" where
  "max R A X Y \<equiv> THE m. m \<in> max_set R A X Y"

definition min::" 'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set\<Rightarrow>  'a" where
  "min R A X Y \<equiv> THE m. m \<in> min_set R A X Y"



definition sup_set::" 'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set\<Rightarrow>  'a set" where
  "sup_set R A X Y \<equiv> (L R (U R A X Y ) X Y) \<inter> (U R A X Y )"

definition inf_set::" 'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set\<Rightarrow>  'a set" where
  "inf_set R A X Y \<equiv> (U R (L R A X Y) X Y) \<inter> (L R A X Y)"


definition is_sup::"'a \<Rightarrow> 'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set\<Rightarrow> bool" where
  "is_sup m R A X Y \<equiv> m \<in> (sup_set R A X Y)"

definition is_inf::"'a \<Rightarrow> 'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set\<Rightarrow> bool" where
  "is_inf m R A X Y \<equiv> m \<in> inf_set R A X Y"

definition has_sup::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set\<Rightarrow> bool" where
  "has_sup R A X Y \<equiv> sup_set R A X Y \<noteq> {}"

definition has_inf::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set\<Rightarrow> bool" where
  "has_inf R A X Y \<equiv>  inf_set R A X Y \<noteq> {}"

definition sup::" 'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set\<Rightarrow>  'a" where
  "sup R A X Y \<equiv> THE m. m \<in> sup_set R A X Y"

definition inf::" 'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set\<Rightarrow>  'a" where
  "inf R A X Y \<equiv> THE m. m \<in> inf_set R A X Y"


context
 fixes R::"'a rel"
 assumes is_refl:"refl R" and is_trans:"trans R" and is_asym:"asym R"
begin


lemma L_imp3:
  "l \<in> L R A X Y \<Longrightarrow> a \<in> A \<inter> X \<Longrightarrow> (l, a) \<in>  R"
  by (meson UNIV_witness asym_onD is_asym is_refl refl_onD)

lemma U_imp3:
  "u \<in> U R A X Y \<Longrightarrow> a \<in> A \<inter> X \<Longrightarrow> (a, u) \<in>  R"
  by (meson asymD is_asym is_refl reflD)

lemma L_anti2:
  "A \<subseteq> B \<Longrightarrow> L R A X Y \<subseteq> L R A X Y"
  by (meson irreflD irrefl_on_if_asym_on is_asym is_refl reflD)

lemma U_anti2:
  "A \<subseteq> B \<Longrightarrow> U R A X Y \<subseteq> U R A X Y"
  by (meson irreflD irrefl_on_if_asym_on is_asym is_refl reflD)
        
lemma L_iso3:
  "X1 \<subseteq> X2 \<Longrightarrow> L R A X1 Y \<subseteq> L R A X2 Y"
  by (meson irreflD irrefl_on_if_asym_on is_asym is_refl reflD)
      
lemma U_iso3:
  "X1 \<subseteq> X2 \<Longrightarrow> U R A X1 Y \<subseteq> U R A X2 Y"
  by (meson irreflD irrefl_on_if_asym_on is_asym is_refl reflD)

lemma L_iso4:
  "Y1 \<subseteq> Y2 \<Longrightarrow> L AR A X Y1 \<subseteq> L R A X Y2"
  by (meson irreflD irrefl_on_if_asym_on is_asym is_refl reflD)
      
lemma U_iso4:
  "Y1 \<subseteq> Y2 \<Longrightarrow> U R A X Y1 \<subseteq> U R A X Y2"
  by (meson irreflD irrefl_on_if_asym_on is_asym is_refl reflD)

lemma UL_iso:
  "A \<subseteq> U R (L R A X Y) X Y"
  by (meson irreflD irrefl_on_if_asym_on is_asym is_refl reflD)

lemma LU_iso:
  "A \<subseteq> L R (U R A X Y) X Y"
  by (meson irreflD irrefl_on_if_asym_on is_asym is_refl reflD)

lemma max_imp1:
   "has_max R A X Y \<Longrightarrow> max R A X Y \<in> max_set R A X Y"
  by (meson UNIV_witness asym_onD is_asym is_refl refl_onD)

lemma sup_imp1:
  "has_sup R A X Y \<Longrightarrow> sup R A X Y \<in> sup_set R A X Y"
  by (meson UNIV_witness asym_onD is_asym is_refl refl_onD)

lemma max_imp2:
   "has_max R A X Y \<Longrightarrow> max R A X Y \<in> U R A X Y \<and> max R A X Y \<in> A"
  by (meson UNIV_witness asym_onD is_asym is_refl refl_onD)

lemma sup_imp2:
  "has_sup R A X Y \<Longrightarrow> sup R A X Y \<in> L R (U R A X Y) X Y \<and> sup R A X Y \<in> (U R A X Y)"
  by (meson UNIV_witness asym_onD is_asym is_refl refl_onD)

lemma max_imp3:
  "max_set R A X Y \<subseteq> A"
  by (simp add: max_set_def)

lemma sup_imp3:
  "sup_set R A X Y \<subseteq> (U R A X Y)"
  by (simp add: sup_set_def)


lemma max_imp4:
  "max_set R A X Y \<subseteq> U R A X Y"
  by (simp add: max_set_def)

lemma sup_imp4:
  "sup_set R A X Y \<subseteq> L R (U R A X Y) X Y "
  by (simp add: sup_set_def)

       
lemma min_imp1:
   "has_min R A X Y \<Longrightarrow> min R A X Y \<in> min_set R A X Y"
  by (meson UNIV_witness asym_onD is_asym is_refl refl_onD)

lemma inf_imp1:
  "has_inf R A X Y \<Longrightarrow> inf R A X Y \<in> inf_set R A X Y"
  by (meson UNIV_witness asym_onD is_asym is_refl refl_onD)

lemma min_imp2:
  "has_min R A X Y \<Longrightarrow> min R A X Y \<in> L R A X Y  \<and> min R A X Y \<in> A"  
  by (meson UNIV_witness asym_onD is_asym is_refl refl_onD)

lemma inf_imp2:
  "has_inf R A X Y \<Longrightarrow> inf R A X Y \<in> U R (L R A X Y) X Y \<and> inf R A X Y \<in> (L R A X Y)"
  by (meson UNIV_witness asym_onD is_asym is_refl refl_onD)

lemma min_imp3:
  "min_set R A X Y \<subseteq> A"
  by (simp add: min_set_def)

lemma inf_imp3:
  "inf_set R A X Y \<subseteq> (L R A X Y)"
  by (simp add: inf_set_def)


lemma min_imp4:
  "min_set R A X Y \<subseteq> L R A X Y"
  by (simp add: min_set_def)

lemma inf_imp4:
  "inf_set R A X Y \<subseteq> U R (L R A X Y) X Y "
  by (simp add: inf_set_def)

lemma max_unique1:
  assumes A0:"has_max R A X Y"
  shows "m1 \<in> max_set R A X Y \<Longrightarrow> m2 \<in> max_set R A X Y \<Longrightarrow> m1 = m2"
  by (meson UNIV_I asym_onD is_asym is_refl refl_onD)

lemma min_unique1:
  assumes A0:"has_min R A X Y"
  shows "m1 \<in> min_set R A X Y \<Longrightarrow> m2 \<in> min_set R A X Y \<Longrightarrow> m1 = m2"
  by (meson UNIV_witness asym_onD is_asym is_refl refl_onD)

lemma max_unique2:
  "has_max R A X Y \<Longrightarrow> \<exists>!m. max R A X Y = m"
  by simp

lemma min_unique2:
  "has_min R A X Y \<Longrightarrow> \<exists>!m. min R A X Y = m"
  by simp

lemma sup_unique2:
  "has_sup R A X Y \<Longrightarrow> \<exists>!s. sup R A X Y = s"
  by simp

lemma inf_unique2:
  "has_inf R A X Y \<Longrightarrow> \<exists>!i. inf R A X Y = i"
  by simp

lemma sup_mayb0:
  "is_sup s R A X Y \<longleftrightarrow>  is_min s R (U R A X Y) X Y"
  by (simp add: sup_set_def is_min_def is_sup_def min_set_def)

lemma inf_mayb0:
  "is_inf i R A X Y \<longleftrightarrow>  is_max i R (L R A X Y) X Y"
  by (simp add: inf_set_def is_inf_def is_max_def max_set_def)

lemma sup_maybe1:
  "is_sup s R A X Y \<Longrightarrow> s \<in>  U R (L R (U R A X Y) X Y) X Y"
  by (meson UNIV_I asym_onD is_asym is_refl refl_onD)

lemma sup_maybe2:
  "s \<in> U R (L R (U R A X Y) X Y) X Y \<Longrightarrow> is_sup s R A X Y"
  by (meson UNIV_witness asym_onD is_asym is_refl refl_onD)

lemma inf_maybe1:
  "is_inf i R A X Y \<Longrightarrow> i \<in>  L R (U R (L R A X Y) X Y) X Y"
  by (meson UNIV_I asym_onD is_asym is_refl refl_onD)

lemma inf_maybe2:
  "i \<in> L R (U R (L R A X Y) X Y) X Y \<Longrightarrow> is_inf i R A X Y"
  by (meson asymD is_asym is_refl reflD)



end

end