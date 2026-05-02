theory Algebrah6 imports Main
begin

declare[[show_consts, show_results, show_types]]
declare[[show_abbrevs=true]]

hide_const map
hide_const partition
hide_const monoid
hide_const group
hide_const inv
hide_const bij
no_notation power (infixr "^" 80)
hide_const power
hide_const id
no_notation divide (infixl "'/" 70)
no_notation inverse_divide (infixl "'/" 70)


definition Pi ::"'a set \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> ('a \<Rightarrow> 'b) set" where "Pi A B={f. \<forall>x. x\<in>A \<longrightarrow> f x\<in>B x}"
definition set_morphisms_to::"'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<Rightarrow> 'b) set"  where "set_morphisms_to A B \<equiv> {f. (\<forall>x. x\<in>A \<longrightarrow> f x\<in>B)}"
definition set_morphisms_on::"'a set \<Rightarrow> ('a \<Rightarrow> 'b) set" where "set_morphisms_on A \<equiv> {f. (\<forall>x. x\<notin>A \<longrightarrow> f x=undefined)}"
definition "restrict" ::"('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> 'b" where "restrict f A=(\<lambda>x. if x\<in>A then f x else undefined)"
syntax "_lam" ::"pttrn \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)"  ("(3\<lambda>_\<in>_./ _)"[0,0,3] 3)
translations "\<lambda>x\<in>A. f" \<rightleftharpoons> "CONST restrict (\<lambda>x. f) A"
definition compose::"'a set \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'c)" where "compose A g f=(\<lambda>x\<in>A. g (f x))"

abbreviation "bij \<equiv> bij_betw"
abbreviation "id X \<equiv> (\<lambda>x\<in>X. x)"
lemma Pi_I[intro!]:"(\<And>x. x\<in>A\<Longrightarrow>f x\<in>B x)\<Longrightarrow>f\<in>Pi A B"  by (simp add:Pi_def)
lemma Pi_I'[simp]:"(\<And>x. x\<in>A \<longrightarrow> f x\<in>B x)\<Longrightarrow>f\<in>Pi A B"  by (simp add:Pi_def)
lemma Pi_mem:"f\<in>Pi A B\<Longrightarrow>x\<in>A\<Longrightarrow>f x\<in>B x" by (simp add:Pi_def)
lemma Pi_iff:"f\<in>Pi I X \<longleftrightarrow> (\<forall>i\<in>I. f i\<in>X i)"  unfolding Pi_def by auto
lemma PiE[elim]:"f\<in>Pi A B\<Longrightarrow>(f x\<in>B x\<Longrightarrow>Q)\<Longrightarrow>(x\<notin>A\<Longrightarrow>Q)\<Longrightarrow>Q"  by (auto simp:Pi_def)
lemma Pi_cong:"(\<And>w. w\<in>A\<Longrightarrow>f w=g w)\<Longrightarrow>f\<in>Pi A B \<longleftrightarrow> g\<in>Pi A B"  by (auto simp:Pi_def)
lemma Pi_empty[simp]:"Pi {} B=UNIV"  by (simp add:Pi_def)
lemma Pi_Int:"Pi I E\<inter>Pi I F=(Pi I (\<lambda>i. E i\<inter>F i))"  by auto
lemma Pi_split_domain[simp]:"f\<in>Pi (A \<union> B) X \<longleftrightarrow> f\<in>Pi A X \<and> f\<in>Pi B X" by (auto simp:Pi_def)
lemma Pi_split_insert_domain[simp]:"f\<in>Pi (insert a A) B \<longleftrightarrow>f\<in>Pi A B \<and> f a\<in>B a"  by (auto simp:Pi_def)

lemma set_morphisms_to_eq:"set_morphisms_to A B=Pi A (\<lambda>_. B)" by (simp add:Pi_def set_morphisms_to_def)
lemma set_morphisms_to_memI[intro!]:"(\<And>x. x\<in>A\<Longrightarrow>f x\<in>B)\<Longrightarrow>f\<in>set_morphisms_to A B"  by (simp add:set_morphisms_to_def)
lemma id_set_morphisms_to[simp]:"(\<lambda>x. x)\<in>set_morphisms_to A A" by auto
lemma set_morphisms_to_memD:"f\<in>set_morphisms_to A B\<Longrightarrow>x\<in>A\<Longrightarrow>f x\<in>B" by (simp add:set_morphisms_to_def)
lemma set_morphisms_toE[elim]:"f\<in>set_morphisms_to A B\<Longrightarrow>(f x\<in>B\<Longrightarrow>Q)\<Longrightarrow>(x\<notin>A\<Longrightarrow>Q)\<Longrightarrow>Q" by (auto simp:set_morphisms_to_def)
lemma set_morphisms_to_cong:"(\<And>w. w\<in>A\<Longrightarrow>f w=g w)\<Longrightarrow>f\<in> set_morphisms_to A B \<longleftrightarrow> g\<in> set_morphisms_to A B"  by (auto simp:set_morphisms_to_def)
lemma set_morphisms_to_empty[simp]:"set_morphisms_to {} B=UNIV"  by (simp add:set_morphisms_to_def)
lemma set_morphisms_to_int:"set_morphisms_to I E\<inter>set_morphisms_to I F=(set_morphisms_to I (E\<inter>F))" by auto
lemma set_morphisms_splits_dom[simp]:"f\<in>set_morphisms_to (A \<union> B) X \<longleftrightarrow> f\<in>set_morphisms_to A X \<and> f\<in>set_morphisms_to B X" by (auto simp:set_morphisms_to_def)
lemma set_morphisms_splits_insert_dom[simp]:"f\<in>set_morphisms_to (insert a A) B \<longleftrightarrow>f\<in>set_morphisms_to A B \<and> f a\<in>B"  by (auto simp:Pi_def)
lemma set_morphisms_to_im:"f\<in>set_morphisms_to A B\<Longrightarrow>f ` A \<subseteq> B"  by auto
definition hom::"'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<Rightarrow> 'b) set" where "hom A B \<equiv> {f. ((\<forall>x. x\<notin>A \<longrightarrow> f x=undefined) \<and> (\<forall>x. x\<in>A \<longrightarrow> f x\<in>B))}"
lemma set_morphisms_to_comp:"f\<in>set_morphisms_to A B\<Longrightarrow>g\<in>set_morphisms_to B C\<Longrightarrow>compose A g f\<in>set_morphisms_to A C"  by (simp add:set_morphisms_to_def compose_def restrict_def)
lemma compose_assoc:"f\<in>set_morphisms_to A B \<Longrightarrow>compose A h (compose A g f)=compose A (compose B h g) f "by (simp add:fun_eq_iff set_morphisms_to_def compose_def restrict_def)
lemma compose_eq:"x\<in>A\<Longrightarrow>compose A g f x=g (f x)" by (simp add:compose_def restrict_def)
lemma surj_compose:"f ` A=B\<Longrightarrow>g ` B=C\<Longrightarrow>compose A g f ` A=C"  by (auto simp add:image_def compose_eq)
lemma restrict_cong:"I=J\<Longrightarrow>(\<And>i. i\<in>J=simp=> f i=g i)\<Longrightarrow>restrict f I=restrict g J"  by (auto simp:restrict_def fun_eq_iff simp_implies_def)
lemma restrictI1[intro!]:"(\<And>x. x\<in>A\<Longrightarrow>f x\<in>B x)\<Longrightarrow>(\<lambda>x\<in>A. f x)\<in>Pi A B"  by (simp add:Pi_def restrict_def)
lemma restrictI2[intro!]:"(\<And>x. x\<in>A\<Longrightarrow>f x\<in>B)\<Longrightarrow>(\<lambda>x\<in>A. f x)\<in>set_morphisms_to A B"  by (simp add:set_morphisms_to_def restrict_def)
lemma restrict_apply[simp]:"(\<lambda>y\<in>A. f y) x=(if x\<in>A then f x else undefined)"  by (simp add:restrict_def)
lemma restrict_apply':"x\<in>A\<Longrightarrow>(\<lambda>y\<in>A. f y) x=f x" by simp
lemma restrict_ext:"(\<And>x. x\<in>A\<Longrightarrow>f x=g x)\<Longrightarrow>(\<lambda>x\<in>A. f x)=(\<lambda>x\<in>A. g x)" by (simp add:fun_eq_iff set_morphisms_to_def restrict_def)
lemma restrict_UNIV:"restrict f UNIV=f" by (simp add:restrict_def)
lemma inj_on_restrict_eq[simp]:"inj_on (restrict f A) A \<longleftrightarrow> inj_on f A"  by (simp add:inj_on_def restrict_def)
lemma inj_on_restrict_iff:"A \<subseteq> B\<Longrightarrow>inj_on (restrict f B) A \<longleftrightarrow> inj_on f A"  by (metis inj_on_cong restrict_def subset_iff)
lemma id_compose1:"f\<in>set_morphisms_to A B\<Longrightarrow>f\<in>set_morphisms_on A\<Longrightarrow>compose A (\<lambda>y\<in>B. y) f=f" by (auto simp add:fun_eq_iff compose_def set_morphisms_on_def set_morphisms_to_def)
lemma id_compose2:"f\<in>set_morphisms_to A B\<Longrightarrow>f\<in>set_morphisms_on A\<Longrightarrow>compose A f (\<lambda>x\<in>A. x)=f" by (auto simp add:fun_eq_iff compose_def set_morphisms_on_def set_morphisms_to_def)
lemma image_restrict_eq[simp]:"(restrict f A) ` A=f ` A"  by (auto simp add:restrict_def)
lemma restrict_restrict[simp]:"restrict (restrict f A) B=restrict f (A\<inter>B)"  unfolding restrict_def by (simp add:fun_eq_iff)
lemma bijI:"f\<in>set_morphisms_to A B\<Longrightarrow>g\<in>set_morphisms_to B A\<Longrightarrow>(\<And>x. x\<in>A\<Longrightarrow>g (f x)=x)\<Longrightarrow>(\<And>y. y\<in>B\<Longrightarrow>f (g y)=y)\<Longrightarrow>bij f A B" by (metis bij_betw_byWitness set_morphisms_to_im)  
lemma bijD1:"bij f A B\<Longrightarrow>f\<in>set_morphisms_to A B"  by (auto simp add:bij_betw_def)
lemma inj_compose:"bij f A B\<Longrightarrow>inj_on g B\<Longrightarrow>inj_on (compose A g f) A"   by (auto simp add:bij_betw_def inj_on_def compose_eq)
lemma bij_compose:"bij f A B\<Longrightarrow>bij g B C\<Longrightarrow>bij (compose A g f) A C"  by (simp add:inj_compose bij_betw_def surj_compose)
lemma bij_restrict_eq[simp]:"bij (restrict f A) A B=bij f A B" by (simp add:bij_betw_def)


lemma set_morphisms_on_memI[intro]:"(\<And>x. x\<notin>A\<Longrightarrow>f x=undefined)\<Longrightarrow>f\<in>set_morphisms_on A" by (simp add:set_morphisms_on_def)
lemma set_morphisms_on_memD:"f\<in>set_morphisms_on A\<Longrightarrow>x\<notin>A\<Longrightarrow>f x=undefined" by (simp add:set_morphisms_on_def)
lemma set_morphisms_on_empty[simp]:"set_morphisms_on {}={\<lambda>x. undefined}"  unfolding set_morphisms_on_def by auto
lemma set_morphisms_on_arb:"f\<in>set_morphisms_on A\<Longrightarrow>x\<notin>A\<Longrightarrow>f x=undefined"  by (simp add:set_morphisms_on_def)
lemma restrict_set_morphisms_on[simp]:"restrict f A\<in>set_morphisms_on A" by (simp add:restrict_def set_morphisms_on_def)
lemma compose_set_morphisms_on[simp]:"compose A f g\<in>set_morphisms_on A"  by (simp add:compose_def)
lemma set_morphisms_on_equalityI:"f\<in>set_morphisms_on A\<Longrightarrow>g\<in>set_morphisms_on A\<Longrightarrow>(\<And>x. x\<in>A\<Longrightarrow>f x=g x)\<Longrightarrow>f=g" by (force simp add:fun_eq_iff set_morphisms_on_def)
lemma set_morphisms_on_restrict: "f\<in>set_morphisms_on A\<Longrightarrow>restrict f A=f"  by (rule set_morphisms_on_equalityI[OF restrict_set_morphisms_on]) auto
lemma set_morphisms_on_subset:"f\<in>set_morphisms_on A\<Longrightarrow>A \<subseteq> B\<Longrightarrow>f\<in>set_morphisms_on B" unfolding set_morphisms_on_def by auto
lemma inv_set_morphism_to:"f ` A=B\<Longrightarrow>(\<lambda>x\<in>B. inv_into A f x)\<in>set_morphisms_to B A"  by (unfold inv_into_def) (fast intro:someI2)
lemma compose_inv_into_id:"bij f A B\<Longrightarrow>compose A (\<lambda>y\<in>B. inv_into A f y) f=(\<lambda>x\<in>A. x)"  by (simp add:bij_betw_def compose_def,rule restrict_ext, auto)
lemma compose_id_inv_into:"f ` A=B\<Longrightarrow>compose B f (\<lambda>y\<in>B. inv_into A f y)=(\<lambda>x\<in>B. x)"  by (simp add:compose_def,rule restrict_ext,simp add:f_inv_into_f)
lemma set_morphisms_on_Int[simp]:"set_morphisms_on I\<inter>set_morphisms_on I'=set_morphisms_on (I\<inter>I')"  unfolding set_morphisms_on_def by auto
lemma set_morphisms_on_UNIV[simp]:"set_morphisms_on UNIV=UNIV"  by (auto simp:set_morphisms_on_def)
lemma restrict_set_morphisms_on_sub[intro]:"A \<subseteq> B\<Longrightarrow>restrict f A\<in>set_morphisms_on B"  unfolding restrict_def set_morphisms_on_def by auto
lemma set_morphisms_on_insert_cancel[intro,simp]: "a\<in>set_morphisms_on I\<Longrightarrow>a\<in>set_morphisms_on (insert i I)"  unfolding set_morphisms_on_def by auto


lemma hom_memI1[intro!]:"(\<And>x. x\<notin>A\<Longrightarrow>f x=undefined)\<Longrightarrow>(\<And>x. x\<in>A\<Longrightarrow>f x\<in>B)\<Longrightarrow>f\<in>hom A B" unfolding hom_def by fast
lemma hom_memI2:"f\<in>set_morphisms_on A\<Longrightarrow>f \<in>set_morphisms_to A B\<Longrightarrow>f\<in>hom A B"   by(rule hom_memI1,auto elim:set_morphisms_on_memD)
lemma hom_memD1:"f\<in>hom A B\<Longrightarrow>f\<in>set_morphisms_on A" unfolding hom_def set_morphisms_on_def by(auto)
lemma hom_memD2:"f\<in>hom A B\<Longrightarrow>f\<in>set_morphisms_to A B" unfolding hom_def set_morphisms_to_def by(auto)
lemma id1[simp]:"id X x=(if x\<in>X then x else undefined)" by (simp add:Id_def)
lemma hom1:"hom {} Y={\<lambda>x. undefined}"  by(auto simp add:hom_def) 
lemma hom2:"f\<in>hom A B\<Longrightarrow>g\<in>hom B C\<Longrightarrow>compose A g f\<in>hom A C" by(auto simp add:hom_def compose_def)
lemma hom3:"f\<in>hom A B\<Longrightarrow>compose A h (compose A g f)=compose A (compose B h g) f" by(auto simp add:hom_def fun_eq_iff compose_def)
lemma fun_eqI:"f\<in>hom A Y\<Longrightarrow>g\<in>hom A Z\<Longrightarrow>(\<And>x. x\<in>A\<Longrightarrow>f x=g x)\<Longrightarrow>f=g"  by (meson hom_memD1 set_morphisms_on_equalityI)  

lemma hom5:"f\<in>hom A B\<Longrightarrow>compose A (id B) f=f" by(auto simp add:fun_eq_iff compose_def hom_def)
lemma hom6:"f\<in>hom A B \<Longrightarrow>compose A f (id A)=f" by(auto simp add:fun_eq_iff compose_def hom_def)
lemma hom7:"(id A)\<in>hom A A" unfolding hom_def by(auto)
lemma hom8:"A \<subseteq> B\<Longrightarrow>(id A)\<in>hom A B"  using hom_def by fastforce 
lemma hom9:"f\<in>hom A B\<Longrightarrow>x\<in>A\<Longrightarrow>f x\<in>B" unfolding hom_def by simp
lemma hom10:"f\<in>hom A B\<Longrightarrow>x\<notin>A\<Longrightarrow>f x=undefined" unfolding hom_def by simp
lemma hom11:"f\<in>hom A B\<Longrightarrow>g\<in>hom A C\<Longrightarrow>x\<notin>A\<Longrightarrow>f x=g x" unfolding hom_def by(auto)
lemma hom12[elim]:"f\<in>hom A B\<Longrightarrow>(f x\<in>B\<Longrightarrow>Q)\<Longrightarrow>(x\<notin>A\<Longrightarrow>Q)\<Longrightarrow>Q" by (auto simp:hom_def)
lemma hom13[elim]:assumes "f\<in>hom A B" obtains "x\<in>A" and "f x\<in>B" | "x\<notin>A" and "f x=undefined" using assms by(auto simp add:hom_def)

abbreviation inv_fun::"('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> ('b \<Rightarrow> 'a)" where "inv_fun f X Y \<equiv> restrict (inv_into X f) Y"
abbreviation is_inv::"('b\<Rightarrow>'a)\<Rightarrow>('a\<Rightarrow>'b)\<Rightarrow>'a set\<Rightarrow>'b set\<Rightarrow>bool" where "is_inv g f X Y \<equiv> g\<in>hom Y X \<and> compose X g f=id X \<and> compose Y f g=id Y"

locale set_morphism=fixes f::"'a \<Rightarrow> 'b" and 
                          X::"'a set" and
                          Y::"'b set"
                 assumes graph[intro,simp]:"f\<in>hom X Y"
begin
lemma set_morphism_closed[intro,simp]:"a\<in>X\<Longrightarrow>f a\<in>Y" using graph by fast
lemma set_morphism_undefined[intro]:"a\<notin>X\<Longrightarrow>f a=undefined" using graph by fast
lemma set_morphism_on:"f\<in>set_morphisms_on X " by auto
lemma set_morphism_to:"f\<in>set_morphisms_to X Y " by auto
end
locale set_epimorphism=set_morphism + assumes surjective[intro]:"f`X=Y"
locale set_monomorphism=set_morphism + assumes injective[intro,simp]:"inj_on f X"
locale bijective=fixes f and X and Y assumes bijective[intro,simp]:"bij f X Y"
locale set_isomorphism=set_morphism + bijective begin
sublocale set_epimorphism by unfold_locales (simp add:bij_betw_imp_surj_on)
sublocale set_monomorphism using bij_betw_def by unfold_locales fast
sublocale inv:set_morphism "inv_fun f X Y" Y X by (unfold_locales)  (simp add:hom_memI2 inv_set_morphism_to surjective) 
sublocale inv:bijective "inv_fun f X Y" Y X  by unfold_locales (simp add:bij_betw_inv_into surjective)
end

context set_morphism begin
lemma bij_iff_has_inv: "bij f X Y \<longleftrightarrow> (\<exists>g. is_inv g f X Y)"
proof assume "bij f X Y" then have "is_inv (inv_fun f X Y) f X Y" and "inv_fun f X Y\<in>hom Y X"   by (simp_all add:bij_betw_imp_surj_on compose_id_inv_into compose_inv_into_id  hom_memI2 inv_set_morphism_to) then show "(\<exists>g. is_inv g f X Y)"  by blast
next assume "\<exists>g. is_inv g f X Y" then obtain g where "f\<in>set_morphisms_to X Y" "g\<in>set_morphisms_to Y X" "\<And>x. x\<in>X\<Longrightarrow>g (f x)=x" "\<And>y. y\<in>Y\<Longrightarrow>f (g y)=y"  by (metis compose_eq hom_memD2 id1 set_morphism_to) then show "bij f X Y" by (simp add:bijI) 
qed
end 

locale equivalence=fixes X and R
                   assumes closed[intro,simp]:"R \<subseteq> X\<times>X" and
                           reflexive[intro,simp]:"a\<in>X\<Longrightarrow>(a, a)\<in>R" and
                           symmetric[sym]:"(a, b)\<in>R\<Longrightarrow>(b, a)\<in>R" and
                           transitive[trans]:"\<lbrakk>(a, b)\<in>R;(b, c)\<in>R\<rbrakk>\<Longrightarrow>(a, c)\<in>R"
begin
lemma left_closed[intro]:"(a, b)\<in>R\<Longrightarrow>a\<in>X" using closed by blast
lemma right_closed[intro]:"(a, b)\<in>R\<Longrightarrow>b\<in>X" using closed by blast
end 
locale partition=fixes X and P assumes subset:"P \<subseteq> Pow X"   and non_vacuous:"{}\<notin>P"   and complete:"\<Union>P=X"   and disjoint:"\<lbrakk>t\<in>P;s\<in>P;t\<noteq>s\<rbrakk>\<Longrightarrow>t\<inter>s={}"

context equivalence begin
definition "proj=(\<lambda>a\<in>X. {b\<in>X. (b, a)\<in>R})"
lemma proj_closed[dest]:"\<lbrakk>a\<in>proj b;b\<in>X\<rbrakk>\<Longrightarrow>a\<in>X"unfolding proj_def by auto
lemma proj_closed2[intro,simp]:"a\<in>X\<Longrightarrow>proj a\<subseteq>X" unfolding proj_def by auto
lemma proj_undefined[intro,simp]:"a\<notin>X\<Longrightarrow>proj a=undefined"  unfolding proj_def by simp
lemma projI[intro,simp]:"(a, b)\<in>R\<Longrightarrow>a\<in>proj b"  unfolding proj_def by (simp add:left_closed right_closed)
lemma proj_revI[intro,simp]:"(a, b)\<in>R\<Longrightarrow>b\<in>proj a" by (blast intro:symmetric)
lemma projD[dest]: "\<lbrakk>b\<in>proj a;a\<in>X\<rbrakk>\<Longrightarrow>(b, a)\<in>R" unfolding proj_def by simp
lemma proj_self[intro,simp]:  "a\<in>X\<Longrightarrow>a\<in>proj a"  unfolding proj_def by simp
lemma proj_Union[simp]:  "(\<Union>a\<in>X. proj a)=X"  by blast
lemma proj_subset:"(a, b)\<in>R\<Longrightarrow>proj a \<subseteq> proj b"  using local.transitive by blast
lemma proj_eq:  "(a, b)\<in>R\<Longrightarrow>proj a=proj b"  by (auto intro!:proj_subset intro:symmetric)
lemma proj_equivalence:"\<lbrakk>a\<in>X;b\<in>X\<rbrakk>\<Longrightarrow>proj a=proj b \<longleftrightarrow> (a, b)\<in>R"  using proj_eq by auto
lemma not_disjoint_implies_equal:"\<lbrakk>a\<in>X; b\<in>X; proj a\<inter>proj b \<noteq>{}\<rbrakk> \<Longrightarrow> proj a=proj b" by (metis disjoint_iff projD proj_eq)
lemma not_equal_implies_disjoint:"\<lbrakk>a\<in>X;b\<in>X; proj a \<noteq> proj b\<rbrakk> \<Longrightarrow> proj a\<inter>proj b={}"  by (meson not_disjoint_implies_equal)
definition "quotient_set=proj`X"
lemma proj_in_quotient_set[intro,simp]:"a\<in>X\<Longrightarrow>proj a\<in>quotient_set" unfolding quotient_set_def by fast
lemma partition:"partition X quotient_set" apply(unfold_locales) using quotient_set_def apply auto[1] using quotient_set_def apply auto[1] apply (simp add: quotient_set_def) proof-   fix t and s   assume closed:"t\<in>quotient_set" "s\<in>quotient_set" "t\<noteq>s"   then obtain a b where "a\<in>X" "b\<in>X" "t=proj a" "s= proj b"  using quotient_set_def by auto   then show "t\<inter>s={}"  by (metis closed(3) not_disjoint_implies_equal)
qed
end 

context partition begin
lemma block_exists:"a\<in>X\<Longrightarrow>\<exists>t. a\<in>t\<and>t\<in>P" using complete by blast
lemma block_unique:"\<lbrakk>a\<in>t;t\<in>P;a\<in>s;s\<in>P\<rbrakk>\<Longrightarrow>t=s" using disjoint by blast
lemma block_closed[intro]: "\<lbrakk>a\<in>t;t\<in>P\<rbrakk>\<Longrightarrow>a\<in>X" using complete by blast
lemma element_exists: "t\<in>P\<Longrightarrow>\<exists>a\<in>X. a\<in>t" by (metis Union_upper bot.extremum_uniqueI complete non_vacuous subsetD subset_emptyI)
definition "part=(\<lambda>a\<in>X. THE t. a\<in>t \<and> t\<in>P)"
lemma part_closed[intro,simp]:assumes[intro]:"a\<in>X" shows "part a\<in>P"
proof - obtain t where "a\<in>t" "t\<in>P" using block_exists by blast then show ?thesis apply (auto simp:part_def)  apply (rule theI2) apply (auto dest:block_unique) done
qed
lemma part_undefined[intro,simp]: "a\<notin>X\<Longrightarrow>part a=undefined"  unfolding part_def by simp
lemma part_self: "\<lbrakk>a\<in>t;t\<in>P\<rbrakk>\<Longrightarrow>part a=t" apply (simp add:part_def block_closed)  apply (rule the_equality) apply simp  using block_unique by blast
definition "eqr_from_part={(a, b) . \<exists>t\<in>P. a\<in>t \<and> b\<in>t}"
lemma equivalence:"equivalence X eqr_from_part"
proof show "eqr_from_part \<subseteq> X\<times>X" unfolding eqr_from_part_def using subset by auto
next fix a  assume "a\<in>X" then show "(a, a)\<in>eqr_from_part" unfolding eqr_from_part_def using complete by auto
next fix a and b assume "(a, b)\<in>eqr_from_part"  then show "(b, a)\<in>eqr_from_part" unfolding eqr_from_part_def by auto
next fix a and b and c   assume "(a, b)\<in>eqr_from_part" "(b, c)\<in>eqr_from_part"   then show "(a, c)\<in>eqr_from_part" unfolding eqr_from_part_def using disjoint by auto
qed
interpretation equivalence X eqr_from_part by (rule equivalence)
lemma proj_is_part: assumes "a\<in>X" shows "proj a=part a"
proof - from \<open>a\<in>X\<close> and block_exists obtain A where block:"a\<in>A \<and> A\<in>P" by blast show ?thesis   apply (simp add:part_def proj_def)   apply (rule theI2)     apply (rule block)    apply (metis block block_unique)   apply (auto dest:block_unique simp:eqr_from_part_def)   done
qed
lemma proj_equals_part: "proj=part"
proof fix x show "proj x=part x" by (cases "x\<in>X") (auto simp:proj_is_part)
qed

lemma partition_of_equivalence: "quotient_set=P" by (auto simp add:quotient_set_def proj_equals_part image_iff) (metis part_self element_exists)

end 

context equivalence begin
interpretation partition X quotient_set by (rule partition)
lemma equivalence_of_partition:"eqr_from_part=R" unfolding eqr_from_part_def unfolding quotient_set_def by auto (metis projD proj_closed proj_eq)
end

sublocale partition \<subseteq> equivalence X eqr_from_part  rewrites "equivalence.quotient_set X eqr_from_part=P" and "equivalence.proj X eqr_from_part=part" apply (simp add: equivalence) apply (simp add: partition_of_equivalence) by (simp add: proj_equals_part)

sublocale equivalence \<subseteq> partition X quotient_set  rewrites "partition.eqr_from_part quotient_set=R" and "partition.part X quotient_set=proj"   apply (simp add: partition)  apply (simp add: equivalence_of_partition) using equivalence_of_partition partition partition.proj_equals_part by force

notation equivalence.quotient_set (infixl "'/" 75)
context equivalence begin
lemma representant_exists[dest]:"t\<in>(equivalence.quotient_set X R)\<Longrightarrow>\<exists>a\<in>X. a\<in>t \<and> t=proj a"  by (metis part_self element_exists)
lemma quotient_projE:"t\<in>(equivalence.quotient_set X R)\<Longrightarrow>(\<And>a. a\<in>t\<Longrightarrow>P (proj a))\<Longrightarrow>P t" using representant_exists by blast
end 
sublocale equivalence \<subseteq> natural:set_epimorphism proj X "(equivalence.quotient_set X R)" by unfold_locales force+
locale fiber_relation_notation=fixes X ::"'a set" begin
definition Fiber_Relation ("R'(_')") where "Fiber_Relation f={(x, y). x\<in>X \<and> y\<in>X \<and> f x=f y}"
end 
locale fiber_relation=set_morphism begin
sublocale fiber_relation_notation .
sublocale equivalence where R="R(f)" unfolding Fiber_Relation_def by unfold_locales auto
definition "induced=(\<lambda>t\<in>X/R(f). THE b. \<exists>a\<in>t. b=f a)"
lemma Fiber_equality:"\<lbrakk>a\<in>X;b\<in>X\<rbrakk>\<Longrightarrow>proj a=proj b \<longleftrightarrow> f a=f b" unfolding proj_equivalence unfolding Fiber_Relation_def by simp
lemma induced_Fiber_simp[simp]:assumes[intro,simp]:"a\<in>X" shows "induced (proj a)=f a"
proof -  have "(THE b. \<exists>a\<in>proj a. b=f a)=f a"   by (rule the_equality) (auto simp:Fiber_equality[symmetric] part_self block_closed) then show ?thesis unfolding induced_def by simp
qed
interpretation induced:set_morphism induced "X/R(f)" Y
proof (unfold_locales, rule) fix t assume[intro,simp]:"t\<in>X/R(f)" obtain a where a:"a\<in>X" "a\<in>t" using element_exists by auto have "(THE b. \<exists>a\<in>t. b=f a)\<in>Y"   apply (rule theI2)   using a apply (auto simp:Fiber_equality[symmetric] part_self block_closed)   done then show "induced t\<in>Y" unfolding induced_def by simp
qed (simp add:induced_def)
sublocale induced:set_monomorphism induced "X/R(f)" Y
proof show "inj_on induced quotient_set"   unfolding inj_on_def   by (metis Fiber_equality part_self element_exists induced_Fiber_simp)
qed
lemma factorization_lemma:"a\<in>X\<Longrightarrow>compose X induced proj a=f a"  by (simp add:compose_eq)
lemma factorization[simp]:"compose X induced proj=f" by (rule ext) (simp add:compose_def set_morphism_undefined)
lemma uniqueness: assumes set_morphism:"h\<in>hom (X/R(f)) Y"  and factorization:"compose X h proj=f" shows "h=induced"
proof  fix t show "h t=induced t" proof (cases "t\<in>X/R(f)")   case True   then obtain a where[simp]:"t=proj a" "a\<in>X" by fast   then have "h (proj a)=f a" by (metis compose_eq factorization)   also have "\<dots>=induced (proj a)" by simp   finally show ?thesis by simp next case False then show ?thesis   using induced.set_morphism_undefined set_morphism by auto  qed
qed
end 

no_notation quotient (infixl "'/'/" 90)

locale monoid=fixes M and composition (infixl "\<cdot>" 70) and unit ("e") 
               assumes m_closed[intro,simp]:"\<lbrakk>a\<in>M;b\<in>M\<rbrakk>\<Longrightarrow>a \<cdot> b\<in>M" and 
                       one_closed[intro,simp]:"e\<in>M" and 
                       m_assoc[intro]:"\<lbrakk>a\<in>M;b\<in>M;c\<in>M\<rbrakk>\<Longrightarrow>(a \<cdot> b) \<cdot> c=a \<cdot> (b \<cdot> c)" and
                       l_one[intro,simp]:"a\<in>M\<Longrightarrow>e \<cdot> a=a" and 
                       r_one[intro,simp]:"a\<in>M\<Longrightarrow>a \<cdot> e=a"
begin
definition invertible where "u\<in>M\<Longrightarrow>invertible u \<longleftrightarrow> (\<exists>v\<in>M. u \<cdot> v=e \<and> v \<cdot> u=e)"
definition "Units={u\<in>M. invertible u}"
definition inv where "inv=(\<lambda>u\<in>M. THE v. v\<in>M \<and> u \<cdot> v=e \<and> v \<cdot> u=e)"
lemma Units_closed[dest]:"x\<in>Units \<Longrightarrow> x\<in>M"  using Units_def by blast
lemma one_unique:"u\<in>M \<Longrightarrow> (\<And>x. x\<in>M \<Longrightarrow> u\<cdot>x=x) \<Longrightarrow> u=e"  using one_closed by fastforce
lemma mem_UnitsI:"\<lbrakk>invertible u;u\<in>M\<rbrakk>\<Longrightarrow>u\<in>Units"  unfolding Units_def by clarify
lemma mem_UnitsD:"\<lbrakk>u\<in>Units\<rbrakk>\<Longrightarrow>invertible u \<and> u\<in>M" unfolding Units_def by clarify
lemma invertibleI[intro]:"\<lbrakk>u\<cdot>v=e;v\<cdot>u=e;u\<in>M;v\<in>M\<rbrakk>\<Longrightarrow>invertible u" unfolding invertible_def by fast
lemma invertibleE[elim]:"\<lbrakk>invertible u;\<And>v. \<lbrakk>u\<cdot>v=e\<and>v\<cdot>u=e;v\<in>M\<rbrakk>\<Longrightarrow>P;u\<in>M\<rbrakk>\<Longrightarrow>P" unfolding invertible_def by fast
lemma inv_unique:"\<lbrakk>u\<cdot>w=e;v\<cdot>u=e;u\<in>M;v\<in>M;w\<in>M\<rbrakk>\<Longrightarrow>v=w"by (metis m_assoc l_one r_one)
lemma inv_equality:"\<lbrakk>u\<cdot>v=e;v\<cdot>u=e;u\<in>M;v\<in>M\<rbrakk>\<Longrightarrow>inv u=v"unfolding inv_def using inv_unique by simp blast
lemma invertible_inv_closed[intro,simp]:"\<lbrakk>invertible u;u\<in>M\<rbrakk>\<Longrightarrow>inv u\<in>M"  using inv_equality by auto
lemma inv_undefined[intro,simp]: "u\<notin>M\<Longrightarrow>inv u=undefined"  by (simp add:inv_def)
lemma invertible_left_inv[simp]:"\<lbrakk>invertible u;u\<in>M\<rbrakk>\<Longrightarrow>inv u\<cdot>u=e" using inv_equality by auto
lemma invertible_right_inv[simp]:"\<lbrakk>invertible u;u\<in>M\<rbrakk>\<Longrightarrow>u\<cdot>inv u=e"  using inv_equality by auto
lemma invertible_left_cancel[simp]:"\<lbrakk>invertible x;x\<in>M;y\<in>M;z\<in>M\<rbrakk>\<Longrightarrow>x\<cdot>y=x\<cdot>z \<longleftrightarrow> y=z" by (metis m_assoc invertible_def l_one)
lemma invertible_right_cancel[simp]: "\<lbrakk>invertible x;x\<in>M;y\<in>M;z\<in>M\<rbrakk>\<Longrightarrow>y\<cdot>x=z\<cdot>x \<longleftrightarrow> y=z"  by (metis m_assoc invertible_def r_one)
lemma inv_unit[simp]:"inv e=e"  using inv_equality by blast
lemma invertible_inv_invertible[intro,simp]: "\<lbrakk>invertible u;u\<in>M\<rbrakk>\<Longrightarrow>invertible (inv u)"  using invertible_left_inv invertible_right_inv by blast
lemma invertible_inv_inv[simp]:"\<lbrakk>invertible u;u\<in>M\<rbrakk>\<Longrightarrow>inv (inv u)=u"  by (simp add:inv_equality)
lemma Units_m_closed[simp,intro]: assumes x:"x\<in>Units" and y:"y\<in>Units" shows "x\<cdot>y\<in>Units"
proof- from x obtain x' where x: "x \<in>M" "x' \<in>M" and xinv: "x\<cdot>x'=e" "x'\<cdot>x=e"   unfolding Units_def by fast from y obtain y' where y: "y \<in>M" "y' \<in>M" and yinv: "y\<cdot>y'=e" "y'\<cdot>y=e"   unfolding Units_def by fast from x y xinv yinv have "y'\<cdot>(x'\<cdot>x)\<cdot>y=e" by simp moreover from x y xinv yinv have "x\<cdot>(y\<cdot>y')\<cdot>x'=e" by simp moreover note x y ultimately show ?thesis unfolding Units_def  using invertible_def m_assoc by auto
qed
lemma Units_one_closed[intro,simp]:"e\<in> Units"by (unfold Units_def) auto
lemma Units_inv_closed[intro,simp]:"x\<in>Units \<Longrightarrow> inv x\<in>M" by (simp add: mem_UnitsD)
lemma Units_l_inv_ex:"x\<in>Units\<Longrightarrow>\<exists>y\<in>M. y\<cdot>x=e" by (unfold Units_def) auto
lemma Units_r_inv_ex:"x\<in>Units\<Longrightarrow>\<exists>y\<in>M. x\<cdot>y=e" by (unfold Units_def) auto
lemma Units_l_inv[simp]:"x\<in>Units\<Longrightarrow>inv x\<cdot>x=e" using mem_UnitsD by auto  
lemma Units_r_inv[simp]:"x\<in>Units\<Longrightarrow>x\<cdot>inv x=e" using Units_def by auto
lemma Units_inv_Units[intro,simp]:"x\<in>Units\<Longrightarrow>inv x\<in>Units" using mem_UnitsD mem_UnitsI by blast
lemma Units_l_cancel[simp]:"\<lbrakk>x\<in>Units;y\<in>M;z\<in>M\<rbrakk> \<Longrightarrow> (x\<cdot>y=x\<cdot>z)=(y=z)"  by (simp add: mem_UnitsD)
lemma Units_inv_inv[simp]:"x\<in>Units\<Longrightarrow>inv (inv x)=x" using mem_UnitsD by auto
lemma inv_inj_on_Units:"inj_on (inv) (Units)" using Units_inv_inv inj_on_inverseI by blast
lemma Units_inv_comm:"\<lbrakk>x\<cdot>y=e;x\<in>Units;y\<in>Units\<rbrakk> \<Longrightarrow> y\<cdot>x=e" by (metis Units_closed Units_inv_closed Units_r_inv inv_unique)
lemma carrier_not_empty: "M \<noteq> {}" by auto
end

lemma monoidI:fixes M and composition (infixl "\<cdot>" 70) and unit ("e")
              assumes m_closed:"\<And>a b. \<lbrakk>a\<in>M;b\<in>M\<rbrakk> \<Longrightarrow> a \<cdot> b\<in>M" and
                      one_closed:"e\<in>M" and
                      m_assoc:"\<And>a b c. \<lbrakk>a\<in>M;b\<in>M;c\<in>M\<rbrakk>\<Longrightarrow>(a \<cdot> b) \<cdot> c=a \<cdot> (b \<cdot> c)" and
                      l_one:"\<And>a. a\<in>M\<Longrightarrow>e \<cdot> a=a" and
                      r_one:"\<And>a. a\<in>M\<Longrightarrow>a \<cdot> e=a"
              shows "monoid M (\<cdot>) e"  by (fast intro!: monoid.intro intro: assms)

locale submonoid=monoid M "(\<cdot>)" e for N and M and composition (infixl "\<cdot>" 70) and unit ("e") +
                 assumes subset:"N \<subseteq> M"  and 
                         sub_m_closed:"\<lbrakk>a\<in>N;b\<in>N\<rbrakk>\<Longrightarrow>a \<cdot> b\<in>N" and
                         sub_one_closed:"e\<in>N"
begin
lemma sub[intro,simp]:"a\<in>N\<Longrightarrow>a\<in>M"using subset by blast
sublocale sub:monoid N "(\<cdot>)" e by unfold_locales (auto simp:sub_m_closed sub_one_closed)
end 

lemma submonoid_transitive:
  assumes "submonoid K N composition unit" and
          "submonoid N M composition unit" 
 shows "submonoid K M composition unit"
proof-
  interpret K:submonoid K N composition unit 
    by fact
  interpret M:submonoid N M composition unit
    by fact 
  show ?thesis
    by unfold_locales auto
qed

locale transformations=fixes X ::"'a set"
sublocale transformations \<subseteq> monoid "hom X X" "compose X" "id X" 
  by(unfold_locales,auto simp add:hom2 hom3  hom_memD1 hom_memD2 id_compose1,metis hom6)


locale transformation_monoid=transformations X + submonoid M "hom X X" "compose X" "id X" for M and X
begin
lemma transformation_closed[intro,simp]:"\<lbrakk>f\<in>M;x\<in>X\<rbrakk>\<Longrightarrow>f x\<in>X"  using subset by auto
lemma transformation_undefined[intro,simp]:"\<lbrakk>f\<in>M;x\<notin>X\<rbrakk>\<Longrightarrow>f x=undefined"by (meson hom10 sub)
end

context submonoid begin
lemma submonoid_invertible[intro,simp]:"\<lbrakk>sub.invertible u;u\<in>N\<rbrakk>\<Longrightarrow>invertible u" using invertibleI by blast
lemma submonoid_inv_closed[intro,simp]:"\<lbrakk>sub.invertible u;u\<in>N\<rbrakk>\<Longrightarrow>inv u\<in>N" using inv_equality by auto
end 

locale group=monoid G "(\<cdot>)" e for G and composition (infixl "\<cdot>" 70) and unit ("e") +
            assumes invertible[simp, intro]:"u\<in>G\<Longrightarrow>invertible u"

lemma groupI:
  fixes G and composition (infixl "\<cdot>" 70) and unit ("e") 
  assumes m_closed:"\<And>a b. \<lbrakk>a\<in>G;b\<in>G\<rbrakk> \<Longrightarrow> a\<cdot>b\<in>G" and
          one_closed:"e\<in>G" and
         m_assoc:"\<And>a b c. \<lbrakk>a\<in>G;b\<in>G;c\<in>G\<rbrakk>\<Longrightarrow>(a\<cdot>b)\<cdot>c=a\<cdot>(b\<cdot>c)" and
         l_one:"\<And>a. a\<in>G\<Longrightarrow>e\<cdot>a=a" and
         r_one:"\<And>a. a\<in>G\<Longrightarrow>a\<cdot>e=a" and
         l_inv_ex:"\<And>x. x\<in>G\<Longrightarrow>\<exists>y \<in> G. y\<cdot>x=e" 
       shows "group G (\<cdot>) e" 
  apply(rule group.intro)
  apply(rule monoidI)
  apply (simp add: m_closed) 
  apply (simp add: one_closed) 
  apply (simp add: m_assoc) 
  apply (simp add: l_one)
  apply (simp add: r_one)
  apply(auto simp add: group_axioms_def)
  proof- 
    fix x assume x:"x \<in> G" with l_inv_ex obtain y where y: "y \<in> G" and l_inv: "y\<cdot>x=e" by blast  
    from x y have "y\<cdot>(x\<cdot>y)=y\<cdot>e" using l_inv l_one m_assoc r_one by force
    with x y have r_inv: "x\<cdot>y=e"  by (metis l_inv l_inv_ex l_one m_assoc r_one) 
    have m:"monoid G (\<cdot>) e" 
      by (simp add: l_one m_assoc m_closed monoidI one_closed r_one)  
    show "monoid.invertible G (\<cdot>) e x" using monoid.invertibleI[of G composition unit x y] by (simp add: l_inv m r_inv x y)
  qed

context monoid
begin
lemma group_l_invI:
  assumes l_inv_ex:"\<And>x. x\<in>M \<Longrightarrow> \<exists>y \<in> M. y\<cdot>x=e" 
  shows "group M (\<cdot>) e" 
  by(rule groupI,auto intro:  l_inv_ex) 
end

context group
begin

lemma is_group [iff]:"group G (\<cdot>) e" by (rule group_axioms)
lemma is_monoid [iff]:"monoid G (\<cdot>) e" by (rule monoid_axioms)
lemma Units:"Units \<subseteq> G"  by blast
lemma Units_eq[simp]:  "Units=G"  using mem_UnitsI by blast
lemma inv_closed[intro,simp]: "x\<in>G\<Longrightarrow>inv x\<in>G" using Units_inv_closed by simp
lemma l_inv_ex[simp]: "x\<in>G\<Longrightarrow>\<exists>y\<in>G. y\<cdot>x=e" using Units_l_inv_ex by simp
lemma r_inv_ex[simp]: "x\<in>G\<Longrightarrow>\<exists>y\<in>G. x\<cdot>y=e" using Units_r_inv_ex by simp
lemma l_inv[simp]: "x\<in>G\<Longrightarrow>inv x\<cdot>x=e" by simp
lemma inv_eq_1_iff[simp]:"x\<in>G \<Longrightarrow>inv x=e \<longleftrightarrow> x=e" using  l_inv by fastforce
lemma r_inv[simp]: "x\<in>G\<Longrightarrow>x\<cdot>inv x=e" by simp
lemma right_cancel[simp]:"\<lbrakk>x\<in>G;y\<in>G;z\<in>G\<rbrakk> \<Longrightarrow>  (y\<cdot>x=z\<cdot>x)=(y=z)" by (metis inv_closed m_assoc r_inv r_one)
lemma inv_inv[simp]: "x\<in>G\<Longrightarrow>inv (inv x)=x" using Units_inv_inv by simp
lemma inv_inj: "inj_on inv G" using inv_inj_on_Units by simp
lemma inv_mult_group: "\<lbrakk>x\<in>G;y\<in>G\<rbrakk>\<Longrightarrow>inv (x\<cdot>y)=inv y\<cdot>inv x" 
proof- 
  assume G: "x\<in>G""y\<in>G" 
  then have "inv (x\<cdot>y)\<cdot>(x\<cdot>y)=(inv y\<cdot>inv x)\<cdot>(x\<cdot>y)"  
    by (simp add: m_assoc) (simp add: m_assoc [symmetric])
  with G show ?thesis
    by (meson inv_closed m_closed right_cancel)
qed
lemma inv_comm: "\<lbrakk>x\<cdot>y=e;x\<in>G;y\<in>G\<rbrakk>\<Longrightarrow>y\<cdot>x=e" by (rule Units_inv_comm) auto
lemma inv_equality: "\<lbrakk>y\<cdot>x=e;x\<in>G; y\<in>G\<rbrakk>\<Longrightarrow>inv x=y" using inv_comm local.inv_equality by blast
lemma inv_solve_left: "\<lbrakk> a\<in>G; b\<in>G; c\<in>G \<rbrakk> \<Longrightarrow> a=inv b\<cdot>c \<longleftrightarrow> c=b\<cdot>a"  by (metis inv_closed l_inv l_one m_assoc r_inv) 
lemma inv_solve_left': "\<lbrakk> a\<in>G; b\<in>G; c\<in>G \<rbrakk> \<Longrightarrow> inv b\<cdot>c=a \<longleftrightarrow> c=b\<cdot>a"  by (metis inv_solve_left) 
lemma inv_solve_right: "\<lbrakk> a\<in>G; b\<in>G; c\<in>G \<rbrakk> \<Longrightarrow> a=b\<cdot>inv c \<longleftrightarrow> b=a\<cdot>c"  using m_assoc by fastforce 
lemma inv_solve_right': "\<lbrakk>a\<in>G; b\<in>G; c\<in>G\<rbrakk> \<Longrightarrow> b\<cdot>inv c=a \<longleftrightarrow> b=a\<cdot>c" by (auto simp: m_assoc) 
end

locale subgroup_of_monoid=
  submonoid G M "(\<cdot>)" e + sub:group G "(\<cdot>)" e 
  for G and M and composition (infixl "\<cdot>" 70) and unit ("e")
begin
lemma subgroup_of_monoid_inv_equality[simp]:"u\<in>G\<Longrightarrow>inv u=sub.inv u"by (simp add:inv_equality)
lemma subgroup_of_monoid_inv_iff[simp]:"\<lbrakk>invertible x;x\<in>M\<rbrakk>\<Longrightarrow>inv x\<in>G \<longleftrightarrow> x\<in>G" using invertible_inv_inv sub.invertible_inv_closed by fastforce
end


lemma subgroup_of_monoid_transitive[trans]: 
  assumes "subgroup_of_monoid K H composition unit" and
          "subgroup_of_monoid H G composition unit"
 shows "subgroup_of_monoid K G composition unit"
proof-
  interpret K:subgroup_of_monoid K H composition unit 
    by fact
  interpret H:subgroup_of_monoid H G composition unit 
    by fact
  show ?thesis
    by unfold_locales auto
qed


context monoid begin

lemma subgroup_of_monoidI:
  fixes G 
  assumes subset[THEN subsetD, intro]:"G \<subseteq> M"   and 
          [intro]:"e\<in>G"   and 
          [intro]:"\<And>g h. \<lbrakk>g\<in>G;h\<in>G\<rbrakk>\<Longrightarrow>g \<cdot> h\<in>G"  and
          [intro]:"\<And>g. g\<in>G\<Longrightarrow>invertible g"   and
          [intro]:"\<And>g. g\<in>G\<Longrightarrow>inv g\<in>G" 
   shows "subgroup_of_monoid G M (\<cdot>) e"
proof-
  interpret sub:monoid G "(\<cdot>)" e 
    by unfold_locales auto
  show ?thesis 
  proof unfold_locales 
    fix u assume[intro]:"u\<in>G"
    show "sub.invertible u"  
      using invertible_left_inv invertible_right_inv by blast qed auto
qed

interpretation units:subgroup_of_monoid Units M  by (simp add: mem_UnitsD monoid.subgroup_of_monoidI monoid_axioms subsetI)
lemma group_of_Units[intro,simp]:"group Units (\<cdot>) e" by auto 
lemma composition_invertible[simp, intro]: "\<lbrakk>invertible x;invertible y;x\<in>M;y\<in>M\<rbrakk>\<Longrightarrow>invertible (x \<cdot> y)"  using mem_UnitsD mem_UnitsI by blast
lemma unit_invertible: "invertible e"  by fast
lemma invertible_right_inv2:  "\<lbrakk>invertible u;u\<in>M;v\<in>M\<rbrakk>\<Longrightarrow>u \<cdot> (inv u \<cdot> v)=v" by (simp add:m_assoc[THEN sym])
lemma invertible_left_inv2:  "\<lbrakk>invertible u;u\<in>M;v\<in>M\<rbrakk>\<Longrightarrow>inv u \<cdot> (u \<cdot> v)=v" by (simp add:m_assoc[THEN sym])
lemma inv_composition_commute:assumes[simp]:"invertible x" "invertible y" "x\<in>M" "y\<in>M"  shows "inv (x \<cdot> y)=inv y \<cdot> inv x"
proof - have "inv (x \<cdot> y) \<cdot> (x \<cdot> y)=(inv y \<cdot> inv x) \<cdot> (x \<cdot> y)" by (simp add:invertible_left_inv2 m_assoc) then show ?thesis by (simp del:invertible_left_inv)
qed
end 

context transformations begin
lemma invertible_is_bijective: 
  assumes dom:"f\<in>hom X X" 
  shows "invertible f \<longleftrightarrow> bij f X X" 
proof- 
  from dom interpret set_morphism f X X 
    by unfold_locales
  show ?thesis
    by (auto simp add:bij_iff_has_inv invertible_def)
qed
lemma Units_bijective: "Units={f\<in>hom X X. bij f X X}"  unfolding Units_def by (auto simp add:invertible_is_bijective)
lemma Units_bijI[intro,simp]: "f\<in>Units\<Longrightarrow>bij f X X" by (simp add:Units_bijective)
lemma Units_bijD[dest, simp]: "\<lbrakk>f\<in>hom X X;bij f X X\<rbrakk>\<Longrightarrow>f\<in>Units"  unfolding Units_bijective by simp
abbreviation "\<SS> \<equiv> Units"
sublocale symmetric:group "\<SS>" "compose X" "id X"  by (fact group_of_Units)
end
locale transformation_group=transformations X + symmetric:subgroup_of_monoid G \<SS> "compose X" "id X" for G and X
begin
lemma transformation_group_closed[intro,simp]:"\<lbrakk>f\<in>G;x\<in>X\<rbrakk>\<Longrightarrow>f x\<in>X" using bij_betwE by blast 
lemma transformation_group_undefined[intro,simp]:"\<lbrakk>f\<in>G;x\<notin>X\<rbrakk>\<Longrightarrow>f x=undefined" by (metis compose_def symmetric.sub.r_one restrict_apply)
end

locale monoid_isomorphism=set_isomorphism f M M' +source:monoid M "(\<cdot>)" e + target:monoid M' "(\<cdot>')" "e'"
  for f and M and composition (infixl "\<cdot>" 70) and unit ("e") and M' and composition' (infixl "\<cdot>''" 70) and unit' ("e''") +
  assumes commutes_with_composition:"\<lbrakk>x\<in>M;y\<in>M\<rbrakk>\<Longrightarrow>f x \<cdot>' f y=f (x \<cdot> y)" and
          commutes_with_unit:"f e=e'"


definition isomorphic_as_monoids (infixl "\<cong>\<^sub>M" 50)  where
  "\<M> \<cong>\<^sub>M \<M>' \<longleftrightarrow> (let (M, composition, unit)=\<M>;(M', composition', unit')=\<M>' 
                  in  (\<exists>f. monoid_isomorphism f M composition unit M' composition' unit'))"

locale monoid_isomorphism'=
  set_isomorphism f M M' + source:monoid M "(\<cdot>)" e + target:monoid M' "(\<cdot>')" "e'"
  for f and M and composition (infixl "\<cdot>" 70) and unit ("e") and M' and composition' (infixl "\<cdot>''" 70) and unit' ("e''") +
  assumes commutes_with_composition:"\<lbrakk>x\<in>M;y\<in>M\<rbrakk>\<Longrightarrow>f x \<cdot>' f y=f (x \<cdot> y)"

sublocale monoid_isomorphism \<subseteq> monoid_isomorphism' by unfold_locales (simp add:commutes_with_composition)

sublocale monoid_isomorphism' \<subseteq> monoid_isomorphism
proof unfold_locales {
    fix y assume "y\<in>M'"  
    then obtain x where "f x=y" "x\<in>M" 
      by (metis image_iff surjective)  
    then have "y \<cdot>' f e=y" 
      using commutes_with_composition by auto
  }
  then show "f e=e'" 
    by fastforce
qed (simp add:commutes_with_composition)

context monoid_isomorphism
begin
lemma inv_monoid_isomorphism: "monoid_isomorphism (restrict (inv_into M f) M') M' (\<cdot>') e' M (\<cdot>) e"
  using commutes_with_composition commutes_with_unit surjective by unfold_locales auto
end

lemma isomorphic_as_monoids_symmetric: 
"(M, composition, unit) \<cong>\<^sub>M (M', composition', unit')\<Longrightarrow>(M', composition', unit') \<cong>\<^sub>M (M, composition, unit)" 
  by (simp add:isomorphic_as_monoids_def) (meson monoid_isomorphism.inv_monoid_isomorphism)

locale left_translations_of_monoid=monoid begin
definition l_trans  where "l_trans=(\<lambda>a\<in>M. \<lambda>x\<in>M. a \<cdot> x)"
lemma translation_set_morphism[intro,simp]:"a\<in>M\<Longrightarrow>l_trans a\<in>hom M M"  unfolding l_trans_def by (simp add: hom_memI1)
lemma translations_set_morphisms[intro,simp]: "l_trans ` M \<subseteq> hom M M"  by (simp add:image_subsetI)
lemma translation_apply: "\<lbrakk>a\<in>M;b\<in>M\<rbrakk>\<Longrightarrow>l_trans a b=a \<cdot> b"  unfolding l_trans_def by auto
lemma translation_exist: "f\<in>l_trans`M\<Longrightarrow>\<exists>a\<in>M. f=l_trans a"  by auto
lemmas Translations_E[elim]=translation_exist[THEN bexE]
lemma translation_unit_eq[simp]:  "id M=l_trans e"  unfolding l_trans_def by auto
lemma translation_composition_eq[simp]: 
  assumes[simp]:"a\<in>M" "b\<in>M" 
  shows "compose M (l_trans a) (l_trans b)=(l_trans (a \<cdot> b))" 
  unfolding l_trans_def by rule (simp add:m_assoc compose_def)
sublocale transformation:transformations M .
lemma Translations_transformation_monoid: "transformation_monoid (l_trans ` M) M"  by unfold_locales auto
sublocale transformation:transformation_monoid "l_trans ` M" M by (fact Translations_transformation_monoid)
sublocale set_morphism l_trans M "l_trans ` M"  by(unfold_locales, auto simp add:l_trans_def hom_memI1)
lemma translation_isomorphism[intro]:"monoid_isomorphism l_trans M (\<cdot>) e (l_trans ` M) (compose M) (id M)"
proof unfold_locales 
  have "inj_on l_trans M" 
  proof (rule inj_onI)  
    fix a b   
    assume[simp]:"a\<in>M" "b\<in>M" "l_trans a=l_trans b"  
    have "l_trans a e=l_trans b e" 
      by simp 
    then show "a=b" 
      by (simp add:l_trans_def) 
  qed 
  then show "bij l_trans M (l_trans ` M)"  
    by (simp add:inj_on_imp_bij_betw)
qed simp_all

sublocale monoid_isomorphism l_trans M "(\<cdot>)" e "l_trans ` M" "compose M" "id M" ..
end 


context monoid begin
interpretation left_translations_of_monoid ..
lemma cayley_monoid:  
  "\<exists>M' composition' unit'. transformation_monoid M' M \<and> (M, (\<cdot>), e) \<cong>\<^sub>M (M', composition', unit')"  
  by (simp add:isomorphic_as_monoids_def) (fast intro:Translations_transformation_monoid)
end 


locale left_translations_of_group=group begin
sublocale left_translations_of_monoid where M=G ..
lemma translation_invertible[intro,simp]:  assumes[simp]:"a\<in>G"  shows "transformation.sub.invertible (l_trans a)"
proof show "compose G (l_trans a) (l_trans (inv a))=id G" by simp
next show "compose G(l_trans (inv a)) (l_trans a)=id G" by simp
qed auto

lemma translation_bijective[intro,simp]:"a\<in>G\<Longrightarrow>bij (l_trans a) G G"  by (blast intro:transformation.invertible_is_bijective[THEN iffD1])
lemma Translations_transformation_group: "transformation_group (l_trans ` G) G"
proof unfold_locales
  show "(l_trans ` G) \<subseteq> transformation.\<SS>"  
    unfolding transformation.Units_bijective
    by auto
next
  fix f assume f:"f\<in>l_trans ` G" 
  then obtain a where a:"a\<in>G" and eq:"f=l_trans a" 
    .. 
  with translation_invertible 
  show "transformation.sub.invertible f" 
    by simp
qed auto

sublocale transformation:transformation_group "l_trans ` G" G  
  by (fact Translations_transformation_group)

end

context group begin
interpretation left_translations_of_group ..
lemma cayley_group: 
  "\<exists>G' composition' unit'. transformation_group G' G \<and> (G, (\<cdot>), e) \<cong>\<^sub>M (G', composition', unit')"
  by (simp add:isomorphic_as_monoids_def) (fast intro:Translations_transformation_group)
end 

locale right_translations_of_group=group begin
definition r_trans where "r_trans=(\<lambda>a\<in>G. \<lambda>x\<in>G. x \<cdot> a)"
abbreviation "Right_Translations \<equiv> r_trans ` G"
interpretation aux:set_morphism r_trans G Right_Translations by(unfold_locales;auto simp add:r_trans_def)
lemma translation_set_morphism[intro,simp]:  "a\<in>G\<Longrightarrow>(r_trans a)\<in>hom G G"  unfolding r_trans_def by auto
lemma Translation_set_morphisms[intro,simp]:  "Right_Translations \<subseteq> hom G G"  by (simp add:image_subsetI)
lemma translation_apply: "\<lbrakk>a\<in>G;b\<in>G\<rbrakk>\<Longrightarrow>(r_trans a) b=b \<cdot> a" unfolding r_trans_def by auto
lemma translation_exist:  "f\<in>Right_Translations\<Longrightarrow>\<exists>a\<in>G. f=(r_trans a)"  by auto
lemmas Translations_E[elim]=translation_exist[THEN bexE]
lemma translation_unit_eq[simp]:  "id G=(r_trans e)"unfolding r_trans_def by auto
lemma translation_composition_eq[simp]: 
  assumes[simp]:"a\<in>G" "b\<in>G" 
  shows "compose G (r_trans a) (r_trans b)=(r_trans (b\<cdot>a))"
  unfolding r_trans_def
  by rule (simp add:m_assoc compose_def) 

sublocale transformation:transformations G .
lemma Translations_transformation_monoid:  "transformation_monoid Right_Translations G"  by unfold_locales auto
sublocale transformation:transformation_monoid Right_Translations G  by (fact Translations_transformation_monoid)
lemma translation_invertible[intro,simp]:  assumes[simp]:"a\<in>G"  shows "transformation.sub.invertible (r_trans a)"
proof show "compose G (r_trans a) (r_trans (inv a))=id G" by simp
next show "compose G (r_trans (inv a)) (r_trans a)=id G" by simp
qed auto
lemma translation_bijective[intro,simp]: "a\<in>G\<Longrightarrow>bij (r_trans a) G G"  by (blast intro:transformation.invertible_is_bijective[THEN iffD1])
lemma Translations_transformation_group: "transformation_group Right_Translations G"
proof unfold_locales   show "Right_Translations \<subseteq> transformation.\<SS>"   unfolding transformation.Units_bijective by auto
next fix f  assume f:"f\<in>Right_Translations"  then obtain a where a:"a\<in>G" and eq:"f=(r_trans a)" .. with translation_invertible show "transformation.sub.invertible f" by simp
qed auto
sublocale transformation:transformation_group Right_Translations G  by (rule Translations_transformation_group)
lemma translation_inv_eq[simp]:  assumes[simp]:"a\<in>G"  shows "transformation.sub.inv (r_trans a)=(r_trans (inv a))"
proof (rule transformation.sub.inv_equality) show "compose G (r_trans a) (r_trans (inv a))=id G" by simp
next show "compose G (r_trans (inv a)) (r_trans a)=id G" by simp
qed auto

lemma translation_inv_monoid_isomorphism[intro]: "monoid_isomorphism (\<lambda>a\<in>G. transformation.symmetric.inv (r_trans a)) G (\<cdot>) e Right_Translations (compose G) (id G)" (is "monoid_isomorphism ?inv _ _ _ _ _ _")
proof unfold_locales show "?inv\<in>hom G Right_Translations" by (auto simp del:translation_unit_eq)
next note bij_compose[trans] have "bij inv G G"   by (rule bijI[where g=inv]) auto also have "bij r_trans G Right_Translations"   by (rule bijI[where g="\<lambda>f\<in>Right_Translations. f e"]) (auto simp:translation_apply) finally show "bij ?inv G Right_Translations"   by (simp cong:bij_betw_cong add:compose_eq del:translation_unit_eq)
next fix x and y assume[simp]:"x\<in>G" "y\<in>G" show "compose G (?inv x) (?inv y)=(?inv (x \<cdot> y))" by (simp add:inv_composition_commute del:translation_unit_eq)
next show "?inv e=id G" by (simp del:translation_unit_eq) simp
qed

sublocale monoid_isomorphism  "\<lambda>a\<in>G. transformation.symmetric.inv (r_trans a)" G "(\<cdot>)" e Right_Translations "compose G" "id G" by blast
end 


locale commutative_monoid=monoid + assumes commutative:"\<lbrakk>x\<in>M;y\<in>M\<rbrakk>\<Longrightarrow>x \<cdot> y=y \<cdot> x"
locale abelian_group=group + commutative_monoid G "(\<cdot>)" e

context transformation_group begin
definition Orbit_Relation  where "Orbit_Relation={(x, y). x\<in>X \<and> y\<in>X \<and> (\<exists>f\<in>G. y=f x)}"
lemma Orbit_Relation_memI[intro]:  "\<lbrakk>\<exists>f\<in>G. y=f x;x\<in>X\<rbrakk>\<Longrightarrow>(x, y)\<in>Orbit_Relation" unfolding Orbit_Relation_def by auto
lemma Orbit_Relation_memE[elim]:  "\<lbrakk>(x, y)\<in>Orbit_Relation;\<And>f. \<lbrakk>f\<in>G;x\<in>X;y=f x\<rbrakk>\<Longrightarrow>Q\<rbrakk>\<Longrightarrow>Q" unfolding Orbit_Relation_def by auto
sublocale orbit:equivalence X Orbit_Relation
proof (unfold_locales, auto simp:Orbit_Relation_def) fix x  assume x:"x\<in>X" then have id:"x=id X x" by simp with x show "\<exists>f\<in>G. x=f x" by fast fix f assume f:"f\<in>G" with x id have y:"x=compose X (symmetric.inv f) f x" by auto with x f show "\<exists>f'\<in>G. x=f' (f x)"   by (metis compose_eq symmetric.sub.invertible symmetric.submonoid_inv_closed) fix g  assume g:"g\<in>G" with x have "g (f x)=compose X g f x" by (simp add:compose_eq) with f g show "\<exists>h\<in>G. g (f x)=h x" by fast
qed
lemma orbit_equality:  "x\<in>X\<Longrightarrow>orbit.proj x={f x | f. f\<in>G}" by (simp add:orbit.proj_def) (blast intro:orbit.symmetric dest:orbit.symmetric)
end

context monoid_isomorphism
begin
lemma image_subgroup_of_monoid: assumes "subgroup_of_monoid G M (\<cdot>) e" shows "subgroup_of_monoid (f ` G) M' (\<cdot>') e'"
proof-
  interpret subgroup_of_monoid G M "(\<cdot>)" e 
    by fact
  interpret image:monoid "f ` G" "(\<cdot>')" "e'"  
    by unfold_locales (auto simp add:commutes_with_composition commutes_with_unit[symmetric])
  show ?thesis proof (unfold_locales, auto) 
    fix x assume x:"x\<in>G"  
    show "image.invertible (f x)"   
    proof     
      show "f (sub.inv x)\<in>f ` G" 
        using x by simp 
    qed (auto simp:x commutes_with_composition commutes_with_unit)
  qed
qed

end 

locale coset_notation=fixes composition (infixl "\<cdot>" 70)  begin
definition r_coset (infixl "|\<cdot>" 70) where "H |\<cdot> x={h \<cdot> x | h. h\<in>H}"
definition l_coset (infixl "\<cdot>|" 70) where "x \<cdot>| H={x \<cdot> h | h. h\<in>H}"
lemma r_coset_memI[intro]:"h\<in>H\<Longrightarrow>h \<cdot> x\<in>H |\<cdot> x" unfolding r_coset_def by blast
lemma r_coset_memE[elim]:"\<lbrakk>a\<in>H |\<cdot> x;\<And>h. \<lbrakk>h\<in>H;a=h \<cdot> x\<rbrakk>\<Longrightarrow>P\<rbrakk>\<Longrightarrow>P"  unfolding r_coset_def by blast
lemma l_coset_memI[intro]:"h\<in>H\<Longrightarrow>x \<cdot> h\<in>x \<cdot>| H"  unfolding l_coset_def by blast
lemma l_coset_memE[elim]:"\<lbrakk>a\<in>x \<cdot>| H;\<And>h. \<lbrakk>h\<in>H;a=x \<cdot> h\<rbrakk>\<Longrightarrow>P\<rbrakk>\<Longrightarrow>P"  unfolding l_coset_def by blast
end

locale subgroup=subgroup_of_monoid H G "(\<cdot>)" e +coset_notation "(\<cdot>)" + group G "(\<cdot>)" e 
  for H and G and composition (infixl "\<cdot>" 70) and unit ("e")

context group begin
lemma subgroupI:
  fixes H 
  assumes subset:"H \<subseteq> G" and
          m_closed:"\<And>x y. \<lbrakk>x\<in>H;y\<in>H\<rbrakk> \<Longrightarrow> x\<cdot>y\<in>H" and
          one_closed:"e\<in>H" and
          m_inv_closed:"\<And>x. x \<in> H \<Longrightarrow> monoid.inv G (\<cdot>) e x \<in> H"
  shows "subgroup H G (\<cdot>) e"
  apply(rule subgroup.intro)
  apply(rule subgroup_of_monoid.intro)
  apply(rule submonoid.intro)
  apply simp
  unfolding submonoid_axioms_def
  apply (simp add: m_closed one_closed subset)
  apply(rule group.intro)
  apply(rule monoid.intro)
  apply (simp add: m_closed)
  apply (simp add: one_closed)
  using subset apply blast
  using subset apply blast
  using subset apply blast
  unfolding group_axioms_def
proof(auto)
  fix u assume u:"u \<in> H"
  have "monoid H (\<cdot>) e"
    apply(auto intro!:monoidI assms)
    using subset apply blast+ .
  then show "monoid.invertible H (\<cdot>) e u"
    using m_inv_closed monoid.invertible_def subset u by fastforce
qed


lemma subgroupE:
  assumes "subgroup H G (\<cdot>) e"
  shows "H \<subseteq> G"
    and "H \<noteq> {}"
    and "\<And>a. a \<in> H \<Longrightarrow> inv a \<in> H"
    and "\<And>a b. \<lbrakk> a \<in> H; b \<in> H \<rbrakk> \<Longrightarrow> a \<cdot> b \<in> H"
  using assms unfolding subgroup_def[of H G]
  apply (simp add: subgroup_of_monoid_def submonoid_axioms_def submonoid_def)
  apply (metis assms group.is_monoid monoid.carrier_not_empty subgroup.axioms(1) subgroup_of_monoid.axioms(2))
  apply (meson assms group.invertible subgroup.axioms(1) subgroup_of_monoid_def submonoid.submonoid_inv_closed)
  by (meson assms subgroup.axioms(1) subgroup_of_monoid.axioms(1) submonoid.sub_m_closed) 


lemma submonoid_subgroupI:
  assumes "submonoid H G (\<cdot>) e" and "\<And>a. a \<in> H \<Longrightarrow> inv a \<in> H"
  shows "subgroup H G (\<cdot>) e"
  by (metis assms(1) assms(2) subgroupI submonoid.sub_m_closed submonoid.sub_one_closed submonoid.subset)


end

context subgroup
begin
lemma subgroup_is_submonoid:"submonoid H G (\<cdot>) e" using submonoid_axioms by blast 

interpretation left:left_translations_of_group  by (simp add: group_axioms left_translations_of_group_def) 
interpretation right:right_translations_of_group  by (simp add: group_axioms right_translations_of_group_def) 

lemma left_translations_of_subgroup_of_monoid_are_transformation_group[intro]: "transformation_group (left.l_trans ` H) G"
proof-
  have "subgroup_of_monoid (left.l_trans ` H) (left.l_trans ` G) (compose G) (id G)"  
    by (rule left.image_subgroup_of_monoid) unfold_locales
  also have "subgroup_of_monoid (left.l_trans ` G) left.transformation.\<SS> (compose G) (id G)"
    .. 
  finally interpret right_coset:subgroup_of_monoid "left.l_trans ` H" left.transformation.\<SS> "compose G" "id G"
    . 
  show ?thesis
    ..
qed

interpretation transformation_group "left.l_trans ` H" G ..
lemma r_coset_is_orbit:  "x\<in>G\<Longrightarrow>H |\<cdot> x=orbit.proj x" using left.translation_apply by (auto simp:orbit_equality r_coset_def) (metis imageI sub)
lemma r_coset_Union:  "(\<Union>x\<in>G. H |\<cdot> x)=G" by (simp add:r_coset_is_orbit)
lemma r_coset_bij:
  assumes G[simp]:"x\<in>G" "y\<in>G" 
 shows "bij (right.r_trans (inv x \<cdot> y)) (H |\<cdot> x) (H |\<cdot> y)"
proof (rule bij_betw_imageI) show "inj_on (right.r_trans (inv x \<cdot> y)) (H |\<cdot> x)"  by (fastforce intro:inj_onI simp add:r_coset_is_orbit right.translation_apply orbit.block_closed)
next show "right.r_trans (inv x \<cdot> y) ` (H |\<cdot> x)=H |\<cdot> y"   by (force simp add:right.translation_apply m_assoc invertible_right_inv2)
qed

lemma r_cosets_cardinality:  "\<lbrakk>x\<in>G;y\<in>G\<rbrakk>\<Longrightarrow>card (H |\<cdot> x)=card (H |\<cdot> y)"  by (fast intro:bij_betw_same_card r_coset_bij)
lemma r_coset_unit:  "H |\<cdot> e=H"  by (force simp add:r_coset_def)
lemma r_coset_cardinality:  "x\<in>G\<Longrightarrow>card (H |\<cdot> x)=card H"  using r_coset_unit r_cosets_cardinality one_closed by presburger
definition "index=card orbit.quotient_set"

lemma lagrange: "finite G\<Longrightarrow>card G=card H * index" unfolding index_def apply (subst card_partition)     apply (auto simp:finite_UnionD orbit.complete orbit.disjoint) apply (metis r_coset_cardinality r_coset_is_orbit orbit.part_self orbit.element_exists) done

end


context subgroup_of_monoid begin
lemma image_of_inv[intro,simp]: "x\<in>G\<Longrightarrow>x\<in>inv ` G"  by (metis image_eqI sub.invertible sub.invertible_inv_closed sub.invertible_inv_inv subgroup_of_monoid_inv_equality)
end 
context group begin
lemma inv_subgroup_of_monoidI:assumes sub:"subgroup_of_monoid H G (\<cdot>) e" shows "subgroup_of_monoid (inv ` H) G (\<cdot>) e"
proof - from sub interpret subgroup_of_monoid H G "(\<cdot>)" e . interpret inv:monoid "inv ` H" "(\<cdot>)" e   by unfold_locales (auto simp del:subgroup_of_monoid_inv_equality) interpret inv:group "inv ` H" "(\<cdot>)" e   by unfold_locales (force simp del:subgroup_of_monoid_inv_equality) show ?thesis   by unfold_locales (auto simp del:subgroup_of_monoid_inv_equality)
qed
lemma inv_subgroup_of_monoidD:assumes sub:"subgroup_of_monoid (inv ` H) G (\<cdot>) e" and inv:"H \<subseteq> Units" shows "subgroup_of_monoid H G (\<cdot>) e"
proof - from sub have "subgroup_of_monoid (inv ` inv ` H) G (\<cdot>) e" by (rule inv_subgroup_of_monoidI) moreover from inv[THEN subsetD, simplified Units_def] have "inv ` inv ` H=H"   by (simp cong:image_cong add:image_comp) ultimately show ?thesis by simp
qed
end 

context subgroup begin

interpretation right_translations_of_group ..

lemma right_translations_of_subgroup_of_monoid_are_transformation_group[intro]: "transformation_group (r_trans ` H) G"
proof - have "subgroup_of_monoid ((\<lambda>a\<in>G. transformation.symmetric.inv (r_trans a)) ` H) Right_Translations (compose G) (id G)"   by (rule image_subgroup_of_monoid) unfold_locales also have "subgroup_of_monoid Right_Translations transformation.\<SS> (compose G) (id G)" .. finally interpret left_coset:subgroup_of_monoid "r_trans ` H" transformation.\<SS> "compose G" "id G"   by (auto intro:transformation.symmetric.inv_subgroup_of_monoidD cong:image_cong     simp:image_image transformation.symmetric.Units_def simp del:translation_unit_eq) show ?thesis ..
qed

interpretation transformation_group "r_trans ` H" G ..

lemma l_coset_is_orbit: "x\<in>G\<Longrightarrow>x \<cdot>| H=orbit.proj x" using translation_apply by (auto simp:orbit_equality l_coset_def) (metis imageI sub)

end 
locale monoid_congruence=monoid + equivalence where X=M +  assumes cong:"\<lbrakk>(a, a')\<in>R;(b, b')\<in>R\<rbrakk>\<Longrightarrow>(a \<cdot> b, a' \<cdot> b')\<in>R"
begin
lemma proj_cong:  "\<lbrakk>proj a=proj a';proj b=proj b';a\<in>M;a'\<in>M;b\<in>M;b'\<in>M\<rbrakk>\<Longrightarrow>proj (a \<cdot> b)=proj (a' \<cdot> b')"  by (simp add:proj_equivalence cong)
definition quotient_composition (infixl "[\<cdot>]" 70) where "quotient_composition=(\<lambda>t\<in> (M/R). \<lambda>s\<in>(M/R). THE r. \<exists>a\<in>t. \<exists>b\<in>s. r=proj (a \<cdot> b))"
lemma proj_commutes_with_composition:"\<lbrakk>a\<in>M;b\<in>M\<rbrakk>\<Longrightarrow>proj a[\<cdot>] proj b=proj (a \<cdot> b)" by (auto simp:quotient_composition_def intro:proj_cong[OF proj_eq proj_eq] del:equalityI)
lemma quotient_m_closed[intro,simp]: "\<lbrakk>t\<in>M/R;s\<in>M/R\<rbrakk>\<Longrightarrow>t[\<cdot>]s\<in>M/R" by (metis m_closed proj_commutes_with_composition proj_in_quotient_set representant_exists)
sublocale quotient:monoid "M/R" "([\<cdot>])" "proj e" apply(unfold_locales) apply(blast) apply simp using m_assoc proj_commutes_with_composition apply fastforce using proj_commutes_with_composition apply force using proj_commutes_with_composition by fastforce

end

locale group_congruence=group + monoid_congruence where M=G begin

notation quotient_composition (infixl "[\<cdot>]" 70)

lemma proj_right_inv: "a\<in>G\<Longrightarrow>proj a[\<cdot>] proj (inv a)=proj e" by (simp add:proj_commutes_with_composition)
lemma proj_left_inv:  "a\<in>G\<Longrightarrow>proj (inv a)[\<cdot>] proj a=proj e"by (simp add:proj_commutes_with_composition)
lemma proj_invertible:  "a\<in>G\<Longrightarrow>quotient.invertible (proj a)"  by (blast intro!:proj_right_inv proj_left_inv)+
lemma proj_commutes_with_inv:  "a\<in>G\<Longrightarrow>quotient.inv (proj a)=proj (inv a)" by (rule quotient.inv_equality) (auto simp:proj_right_inv proj_left_inv)
sublocale quotient:group "G/R" "([\<cdot>])" "proj e"  by(unfold_locales,metis part_self proj_invertible element_exists)
end 

locale normal_subgroup=subgroup K G "(\<cdot>)" e for K and G and composition (infixl "\<cdot>" 70) and unit ("e") +  assumes normal:"\<lbrakk>g\<in>G;k\<in>K\<rbrakk>\<Longrightarrow>inv g \<cdot> k \<cdot> g\<in>K"

context subgroup begin
lemma Left_equals_Right_coset_implies_normality: assumes[simp]:"\<And>g. g\<in>G\<Longrightarrow>g \<cdot>| H=H |\<cdot> g"  shows "normal_subgroup H G (\<cdot>) e"
proof fix g k assume[simp]:"g\<in>G" "k\<in>H" have "k \<cdot> g\<in>g \<cdot>| H" by auto then obtain k' where "k \<cdot> g=g \<cdot> k'" and "k'\<in>H" by blast then show "inv g \<cdot> k \<cdot> g\<in>H" by (simp add:m_assoc invertible_left_inv2)
qed

end

context group_congruence begin
definition "Normal=proj e"

interpretation subgroup_of_monoid "Normal" G "(\<cdot>)" e unfolding Normal_def
proof (rule subgroup_of_monoidI) fix k1 and k2 assume K:"k1\<in>proj e" "k2\<in>proj e" then have "k1 \<cdot> k2\<in>proj (k1 \<cdot> k2)" by blast also have "\<dots>=proj k1[\<cdot>] proj k2" using K by (auto simp add:proj_commutes_with_composition proj_closed) also have "\<dots>=proj e[\<cdot>] proj e" using K by (metis projD proj_eq one_closed) also have "\<dots>=proj e" by simp finally show "k1 \<cdot> k2\<in>proj e" .
next fix k assume K:"k\<in>proj e" then have "inv k\<in>proj (inv k)" by blast also have "\<dots>=quotient.inv (proj k)" using proj_commutes_with_inv K by blast also have "\<dots>=quotient.inv (proj e)" using part_self K by auto also have "\<dots>=proj e" using quotient.inv_unit by blast finally show "inv k\<in>proj e" .
qed auto

interpretation subgroup "Normal" G "(\<cdot>)" e ..
lemma r_coset_proj_unit: assumes g:"g\<in>G" shows "Normal |\<cdot> g=proj g" unfolding Normal_def
proof auto fix a  \<comment> \<open>ll 6--8\<close> assume a:"a\<in>proj g" from a g have "a \<cdot> inv g\<in>proj (a \<cdot> inv g)" by blast also from a g have "\<dots>=proj a[\<cdot>] proj (inv g)"   by (simp add:proj_commutes_with_composition block_closed) also from a g have "\<dots>=proj g[\<cdot>] quotient.inv (proj g)"   using part_self proj_commutes_with_inv by auto also from g have "\<dots>=proj e" by simp finally show "a\<in>proj e |\<cdot> g"   unfolding r_coset_def   by simp (metis proj_closed a m_assoc g inv_equality invertible invertible_def r_one) 
next fix a  \<comment> \<open>ll 8--9\<close> assume a:"a\<in>proj e |\<cdot> g" then obtain k where eq:"a=k \<cdot> g" and k:"k\<in>proj e" by blast with g have "proj a=proj k[\<cdot>] proj g" using proj_commutes_with_composition by auto also from k have "\<dots>=proj e[\<cdot>] proj g" using part_self by auto also from g have "\<dots>=proj g" by simp finally show "a\<in>proj g" using g eq k m_closed quotient.one_closed by blast
qed

lemma l_coset_proj_unit: assumes g:"g\<in>G" shows "g \<cdot>| Normal=proj g" unfolding Normal_def
proof auto fix a  \<comment> \<open>ll 6--8\<close> assume a:"a\<in>proj g" from a g have "inv g \<cdot> a\<in>proj (inv g \<cdot> a)" by blast also from a g have "\<dots>=proj (inv g)[\<cdot>] proj a"   by (simp add:proj_commutes_with_composition block_closed) also from a g have "\<dots>=quotient.inv (proj g)[\<cdot>] proj g"   using part_self proj_commutes_with_inv by auto also from g have "\<dots>=proj e" by simp finally show "a\<in>g \<cdot>| proj e"   unfolding l_coset_def   by simp (metis proj_closed a m_assoc g inv_equality invertible invertible_def r_one) 
next fix a  \<comment> \<open>ll 8--9, ``the same thing holds''\<close> assume a:"a\<in>g \<cdot>| proj e" then obtain k where eq:"a=g \<cdot> k" and k:"k\<in>proj e" by blast with g have "proj a=proj g[\<cdot>] proj k" using proj_commutes_with_composition by auto also from k have "\<dots>=proj g[\<cdot>] proj e" using part_self by auto also from g have "\<dots>=proj g" by simp finally show "a\<in>proj g" using g eq k m_closed quotient.one_closed by blast
qed

lemma proj_unit_is_normal: "normal_subgroup Normal G (\<cdot>) e"
proof - {   fix g   assume "g\<in>G"   then have "g \<cdot>| Normal=Normal |\<cdot> g" by (simp add:r_coset_proj_unit l_coset_proj_unit) } then show ?thesis by (rule Left_equals_Right_coset_implies_normality)
qed

sublocale normal:normal_subgroup Normal G "(\<cdot>)" e by (fact proj_unit_is_normal)

end
context normal_subgroup begin
lemma Left_equals_Right_coset: "g\<in>G\<Longrightarrow>g \<cdot>| K=K |\<cdot> g"
proof assume[simp]:"g\<in>G" show "K |\<cdot> g \<subseteq> g \<cdot>| K" proof   fix x   assume x:"x\<in>K |\<cdot> g"   then obtain k where "x=k \<cdot> g" and[simp]:"k\<in>K" by (auto simp add:r_coset_def)   then have "x=g \<cdot> (inv g \<cdot> k \<cdot> g)" by (simp add:m_assoc invertible_right_inv2)   also from normal have "\<dots>\<in>g \<cdot>| K" by (auto simp add:l_coset_def)   finally show "x\<in>g \<cdot>| K" . qed
next assume[simp]:"g\<in>G" show "g \<cdot>| K \<subseteq> K |\<cdot> g" proof   fix x   assume x:"x\<in>g \<cdot>| K"   then obtain k where "x=g \<cdot> k" and[simp]:"k\<in>K" by (auto simp add:l_coset_def)   then have "x=(inv (inv g) \<cdot> k \<cdot> inv g) \<cdot> g" by (simp add:m_assoc del:invertible_right_inv)   also from normal[where g="inv g"] have "\<dots>\<in>K |\<cdot> g" by (auto simp add:r_coset_def)   finally show "x\<in>K |\<cdot> g" . qed
qed

definition "Congruence={(a, b). a\<in>G \<and> b\<in>G \<and> inv a \<cdot> b\<in>K}"
interpretation right_translations_of_group ..
interpretation transformation_group "r_trans ` K" G rewrites "Orbit_Relation=Congruence"
proof - interpret transformation_group "r_trans ` K" G .. show "Orbit_Relation=Congruence"   unfolding Orbit_Relation_def Congruence_def   by (force simp:invertible_left_inv2 invertible_right_inv2 translation_apply simp del:restrict_apply)
qed rule


lemma CongruenceI:"\<lbrakk>a=b \<cdot> k;a\<in>G;b\<in>G;k\<in>K\<rbrakk>\<Longrightarrow>(a, b)\<in>Congruence" by (clarsimp simp:Congruence_def m_assoc inv_composition_commute)

lemma CongruenceD:"(a, b)\<in>Congruence\<Longrightarrow>\<exists>k\<in>K. a=b \<cdot> k" by (drule orbit.symmetric) (force simp:Congruence_def invertible_right_inv2)

sublocale group_congruence where R=Congruence rewrites "Normal=K"
proof - show "group_congruence G (\<cdot>) e Congruence" proof unfold_locales   note CongruenceI[intro] CongruenceD[dest]   fix a g b h   assume 1:"(a, g)\<in>Congruence" and 2:"(b, h)\<in>Congruence"   then have G:"a\<in>G" "g\<in>G" "b\<in>G" "h\<in>G" unfolding Congruence_def by clarify+   from 1 obtain k1 where a:"a=g \<cdot> k1" and k1:"k1\<in>K" by blast   from 2 obtain k2 where b:"b=h \<cdot> k2" and k2:"k2\<in>K" by blast   from G Left_equals_Right_coset have "K |\<cdot> h=h \<cdot>| K" by blast   with k1 obtain k3 where c:"k1 \<cdot> h=h \<cdot> k3" and k3:"k3\<in>K"     unfolding l_coset_def r_coset_def by blast   from G k1 k2 a b have "a \<cdot> b=g \<cdot> k1 \<cdot> h \<cdot> k2" by (simp add:m_assoc)   also from G k1 k3 c have "\<dots>=g \<cdot> h \<cdot> k3 \<cdot> k2" by (simp add:m_assoc)   also have "\<dots>=(g \<cdot> h) \<cdot> (k3 \<cdot> k2)" using G k2 k3 by (simp add:m_assoc)   finally show "(a \<cdot> b, g \<cdot> h)\<in>Congruence" using G k2 k3 by blast qed then interpret group_congruence where R=Congruence . show "Normal=K"   unfolding Normal_def orbit.proj_def unfolding Congruence_def   using invertible_inv_inv submonoid_inv_closed by fastforce 
qed

end


context group begin
abbreviation Factor_Group (infixl "'/'/" 75) where "X // K \<equiv> X / (normal_subgroup.Congruence K G (\<cdot>) e)"
end 

context normal_subgroup begin
lemma proj_unit_normal_subgroup:"proj e=K" unfolding proj_def unfolding Congruence_def using invertible_inv_inv submonoid_inv_closed by fastforce
lemma proj_is_l_coset: "g\<in>G\<Longrightarrow>proj g=g \<cdot>| K" using l_coset_proj_unit proj_unit_normal_subgroup by simp
lemma l_cosetE:"\<lbrakk>t\<in>G//K;\<And>a. a\<in>G\<Longrightarrow>P (a \<cdot>| K)\<rbrakk>\<Longrightarrow>P t"  using l_coset_proj_unit by auto
lemma factor_composition[simp]:  "\<lbrakk>g\<in>G;h\<in>G\<rbrakk>\<Longrightarrow>(g \<cdot>| K)[\<cdot>] (h \<cdot>| K)=g \<cdot> h \<cdot>| K"  using proj_commutes_with_composition proj_is_l_coset by auto
lemma factor_unit: "K=e \<cdot>| K"  using proj_is_l_coset proj_unit_normal_subgroup by blast
lemma factor_inv[simp]:  "g\<in>G\<Longrightarrow>quotient.inv (g \<cdot>| K)=(inv g \<cdot>| K)" using proj_commutes_with_inv proj_is_l_coset by auto
end


locale subgroup_of_monoid_of_abelian_group=subgroup H G "(\<cdot>)" e + abelian_group G "(\<cdot>)" e for H and G and composition (infixl "\<cdot>" 70) and unit ("e")
sublocale subgroup_of_monoid_of_abelian_group \<subseteq> normal_subgroup H G "(\<cdot>)" e using commutative invertible_right_inv2 by unfold_locales auto

locale monoid_homomorphism= 
    set_morphism f M M'+ source:monoid M "(\<cdot>)" e + target:monoid M' "(\<cdot>')" "e'"
    for f and M and composition (infixl "\<cdot>" 70) and unit ("e")  and M' and composition' (infixl "\<cdot>''" 70) and unit' ("e''") +
    assumes commutes_with_composition:"\<lbrakk>x\<in>M;y\<in>M\<rbrakk>\<Longrightarrow>f (x \<cdot> y)=f x \<cdot>' f y"   and commutes_with_unit:"f e=e'"
begin

notation source.invertible ("invertible _"[100] 100)
notation source.inv ("inv _"[100] 100)
notation target.invertible ("invertible'' _"[100] 100)
notation target.inv ("inv'' _"[100] 100)

end
locale monoid_epimorphism=monoid_homomorphism + set_epimorphism f M M'
locale monoid_monomorphism=monoid_homomorphism + set_monomorphism f M M'
sublocale monoid_isomorphism \<subseteq> monoid_epimorphism  by unfold_locales (auto simp:commutes_with_composition commutes_with_unit)
sublocale monoid_isomorphism \<subseteq> monoid_monomorphism by unfold_locales (auto simp:commutes_with_composition commutes_with_unit)

context monoid_homomorphism begin
lemma invertible_image_lemma:assumes "invertible a" "a\<in>M" shows "f a \<cdot>' f (inv a)=e'" and "f (inv a) \<cdot>' f a=e'" using assms commutes_with_composition commutes_with_unit source.inv_equality by auto (metis source.invertible_inv_closed source.invertible_left_inv)
lemma invertible_target_invertible[intro,simp]:"\<lbrakk>invertible a;a\<in>M\<rbrakk>\<Longrightarrow>invertible' (f a)" using invertible_image_lemma by blast
lemma invertible_commutes_with_inv:"\<lbrakk>invertible a;a\<in>M\<rbrakk>\<Longrightarrow>f (inv a)=inv' (f a)"using invertible_image_lemma target.inv_equality by fastforce
end 

sublocale monoid_congruence \<subseteq> natural:monoid_homomorphism proj M "(\<cdot>)" e "M / R" "([\<cdot>])" "proj e"  by(unfold_locales, auto simp add:proj_commutes_with_composition)
sublocale monoid_homomorphism \<subseteq> image:submonoid "f ` M" M' "(\<cdot>')" "e'"  by unfold_locales (auto simp:commutes_with_composition[symmetric] commutes_with_unit[symmetric])


locale monoid_homomorphism_fundamental=monoid_homomorphism begin
sublocale fiber_relation f M M' ..
notation Fiber_Relation ("R'(_')")
sublocale monoid_congruence where R="R(f)" using proj_eq by unfold_locales (rule proj_equivalence[THEN iffD1],    auto simp:left_closed right_closed commutes_with_composition Fiber_equality)
notation quotient_composition (infixl "[\<cdot>]" 70)
sublocale induced:monoid_homomorphism induced "M / R(f)" "([\<cdot>])" "proj e" "M'" "(\<cdot>')" "e'" apply unfold_locales   apply (auto simp:commutes_with_unit) apply (fastforce simp:commutes_with_composition commutes_with_unit proj_commutes_with_composition) done

sublocale natural:monoid_epimorphism proj M "(\<cdot>)" e "M / R(f)" "([\<cdot>])" "proj e" ..

sublocale induced:monoid_monomorphism induced "M / R(f)" "([\<cdot>])" "proj e" "M'" "(\<cdot>')" "e'" ..

end 

locale group_homomorphism=
  monoid_homomorphism f G "(\<cdot>)" e G' "(\<cdot>')" "e'"+source:group G "(\<cdot>)" e + target:group G' "(\<cdot>')" "e'"
  for f and G and composition (infixl "\<cdot>" 70) and unit ("e")  and G' and composition' (infixl "\<cdot>''" 70) and unit' ("e''")
begin


sublocale image:subgroup_of_monoid "f ` G" G' "(\<cdot>')" "e'" using invertible_image_lemma by unfold_locales auto


definition "Ker=f -` {e'}\<inter>G"


lemma Ker_equality:"Ker={a | a. a\<in>G \<and> f a=e'}"  unfolding Ker_def by auto


lemma Ker_closed[intro,simp]:"a\<in>Ker\<Longrightarrow>a\<in>G"unfolding Ker_def by simp


lemma Ker_image[intro]: "a\<in>Ker\<Longrightarrow>f a=e'"  unfolding Ker_def by simp


lemma Ker_memI[intro]:  "\<lbrakk>f a=e';a\<in>G\<rbrakk>\<Longrightarrow>a\<in>Ker" unfolding Ker_def by simp

sublocale kernel:normal_subgroup Ker G
proof - interpret kernel:submonoid Ker G   unfolding Ker_def by unfold_locales (auto simp:commutes_with_composition commutes_with_unit) interpret kernel:subgroup_of_monoid Ker G   by unfold_locales (force intro:source.invertible_right_inv simp:Ker_image invertible_commutes_with_inv) show "normal_subgroup Ker G (\<cdot>) e"   apply unfold_locales   unfolding Ker_def   by (auto simp:commutes_with_composition invertible_image_lemma(2))
qed


lemma injective_iff_kernel_unit:  "inj_on f G \<longleftrightarrow> Ker={e}"
proof (rule Not_eq_iff[THEN iffD1, OF iffI]) assume "Ker\<noteq>{e}" then obtain b where b:"b\<in>Ker" "b\<noteq>e" by blast then have "f b=f e" by (simp add:Ker_image) with b show "\<not> inj_on f G"  by (meson inj_onD kernel.sub source.one_closed)
next assume "\<not> inj_on f G" then obtain a b where "a\<noteq>b" and ab:"a\<in>G" "b\<in>G" "f a=f b" by (meson inj_onI) then have "inv a \<cdot> b\<noteq>e" "f (inv a \<cdot> b)=e'"   using ab source.invertible_right_inv2   by force (metis ab commutes_with_composition invertible_image_lemma(2) source.invertible source.invertible_inv_closed) then have "inv a \<cdot> b\<in>Ker" using Ker_memI ab by blast then show "Ker\<noteq>{e}" using \<open>inv a \<cdot> b\<noteq>e\<close> by blast
qed

end

locale group_epimorphism=group_homomorphism + monoid_epimorphism f G "(\<cdot>)" e G' "(\<cdot>')" "e'"

locale normal_subgroup_in_kernel= group_homomorphism + contained:normal_subgroup L G "(\<cdot>)" e for L + assumes subset:"L \<subseteq> Ker"
begin

notation contained.quotient_composition (infixl "[\<cdot>]" 70)
sublocale natural:group_epimorphism contained.proj G "(\<cdot>)" e "G // L" "([\<cdot>])" "contained.proj e" ..

lemma left_coset_equality: assumes eq:"a \<cdot>| L=b \<cdot>| L" and[simp]:"a\<in>G" and b:"b\<in>G" shows "f a=f b"
proof - obtain l where l:"b=a \<cdot> l" "l\<in>L"   by (metis b contained.proj_is_l_coset contained.proj_self eq kernel.l_coset_memE) then have "f a=f a \<cdot>' f l" using Ker_image monoid_homomorphism.commutes_with_composition subset by auto also have "\<dots>=f b" by (simp add:commutes_with_composition l) finally show ?thesis .
qed

definition "induced=(\<lambda>A\<in>G // L. THE b. \<exists>a\<in>G. a \<cdot>| L=A \<and> b=f a)"

lemma induced_closed[intro,simp]: assumes[simp]:"A\<in>G // L" shows "induced A\<in>G'"
proof - obtain a where a:"a\<in>G" "a \<cdot>| L=A" using contained.proj_is_l_coset contained.quotient_set_def assms by auto have "(THE b. \<exists>a\<in>G. a \<cdot>| L=A \<and> b=f a)\<in>G'"   apply (rule theI2)   using a by (auto intro:left_coset_equality) then show ?thesis unfolding induced_def by simp
qed


lemma induced_undefined[intro,simp]:"A\<notin>G // L\<Longrightarrow>induced A=undefined" unfolding induced_def by simp

lemma induced_left_coset_closed[intro,simp]: "a\<in>G\<Longrightarrow>induced (a \<cdot>| L)\<in>G'" using contained.proj_is_l_coset contained.proj_in_quotient_set by auto 

lemma induced_left_coset_equality[simp]: assumes[simp]:"a\<in>G" shows "induced (a \<cdot>| L)=f a"
proof - have "(THE b. \<exists>a'\<in>G. a' \<cdot>| L=a \<cdot>| L \<and> b=f a')=f a"   by (rule the_equality) (auto intro:left_coset_equality) then show ?thesis unfolding induced_def   using contained.proj_is_l_coset contained.proj_in_quotient_set by auto 
qed


lemma induced_l_coset_commutes_with_composition[simp]:"\<lbrakk>a\<in>G;b\<in>G\<rbrakk>\<Longrightarrow>induced ((a \<cdot>| L)[\<cdot>] (b \<cdot>| L))=induced (a \<cdot>| L) \<cdot>' induced (b \<cdot>| L)" by (simp add:commutes_with_composition)

lemma induced_group_homomorphism:"group_homomorphism induced (G // L) ([\<cdot>]) (contained.proj e) G' (\<cdot>') e'" apply unfold_locales   apply (auto elim!:contained.l_cosetE simp:commutes_with_composition commutes_with_unit) using contained.factor_unit induced_left_coset_equality apply (fastforce simp:contained.proj_unit_normal_subgroup) done


sublocale induced:group_homomorphism induced "G // L" "([\<cdot>])" "contained.proj e" G' "(\<cdot>')" "e'" by (fact induced_group_homomorphism)


lemma factorization_lemma:"a\<in>G\<Longrightarrow>compose G induced contained.proj a=f a"  unfolding compose_def by (simp add:contained.proj_is_l_coset)


lemma factorization[simp]:"compose G induced contained.proj=f" by rule (simp add:compose_def contained.proj_is_l_coset set_morphism_undefined)

lemma uniqueness: assumes set_morphism:"h\<in> hom (G // L) G'"   and factorization:"compose G h contained.proj=f" shows "h=induced"
proof fix A show "h A=induced A" proof (cases "A\<in>G // L")   case True   then obtain a where[simp]:"A=contained.proj a" "a\<in>G" by fast   then have "h (contained.proj a)=f a" by (metis compose_eq factorization)   also have "\<dots>=induced (contained.proj a)" by (simp add:contained.proj_is_l_coset)   finally show ?thesis by simp next   case False   then show ?thesis     using assms(1) by auto qed
qed

lemma induced_image:  "induced ` (G // L)=f ` G"  by (metis factorization contained.natural.surjective surj_compose)
interpretation L:normal_subgroup L Ker  by unfold_locales (auto simp:subset, metis kernel.sub kernel.subgroup_of_monoid_inv_equality contained.normal)
lemma induced_kernel:"induced.Ker=Ker / L.Congruence" 
proof - have "induced.Ker={ a \<cdot>| L | a. a\<in>G \<and> a\<in>Ker }"   unfolding induced.Ker_equality   by simp (metis (opaque_lifting) contained.proj_is_l_coset Ker_image Ker_memI       induced_left_coset_equality contained.proj_in_quotient_set contained.representant_exists) also have "\<dots>=Ker / L.Congruence"   using L.proj_is_l_coset L.proj_in_quotient_set   by auto (metis L.proj_is_l_coset L.representant_exists kernel.sub) finally show ?thesis .
qed

lemma induced_inj_on: "inj_on induced (G // L) \<longleftrightarrow> L=Ker" apply (simp add:induced.injective_iff_kernel_unit induced_kernel contained.proj_unit_normal_subgroup) apply rule using L.block_exists apply auto[1] using L.part_self L.proj_unit_normal_subgroup L.quotient.one_closed L.representant_exists apply auto done

end 

locale group_homomorphism_fundamental=group_homomorphism begin
notation kernel.quotient_composition (infixl "[\<cdot>]" 70)
sublocale normal_subgroup_in_kernel where L=Ker by unfold_locales rule

end 
locale group_isomorphism=group_homomorphism + set_isomorphism f G G' begin
sublocale monoid_isomorphism f G "(\<cdot>)" e G' "(\<cdot>')" "e'"  by unfold_locales (auto simp:commutes_with_composition)
lemma inv_group_isomorphism:"group_isomorphism (restrict (inv_into G f) G') G' (\<cdot>') e' G (\<cdot>) e" using commutes_with_composition commutes_with_unit surjective by unfold_locales auto
end 

definition isomorphic_as_groups (infixl "\<cong>\<^sub>G" 50) where "\<G> \<cong>\<^sub>G \<G>' \<longleftrightarrow> (let (G, composition, unit)=\<G>;(G', composition', unit')=\<G>' in (\<exists>f. group_isomorphism f G composition unit G' composition' unit'))"

lemma isomorphic_as_groups_symmetric: "(G, composition, unit) \<cong>\<^sub>G (G', composition', unit')\<Longrightarrow>(G', composition', unit') \<cong>\<^sub>G (G, composition, unit)"  by (simp add:isomorphic_as_groups_def) (meson group_isomorphism.inv_group_isomorphism)
sublocale group_isomorphism \<subseteq> group_epimorphism ..
locale group_epimorphism_fundamental=group_homomorphism_fundamental + group_epimorphism begin
interpretation image:group_homomorphism induced "G // Ker" "([\<cdot>])" "kernel.proj e" "(f ` G)" "(\<cdot>')" "e'" by (simp add:surjective group_homomorphism_fundamental.intro induced_group_homomorphism)
sublocale image:group_isomorphism induced "G // Ker" "([\<cdot>])" "kernel.proj e" "(f ` G)" "(\<cdot>')" "e'"  using induced_group_homomorphism  by unfold_locales (auto simp:bij_betw_def induced_image induced_inj_on induced.commutes_with_composition)
end

context group_homomorphism begin
lemma image_isomorphic_to_factor_group: "\<exists>K composition unit. normal_subgroup K G (\<cdot>) e \<and> (f ` G, (\<cdot>'), e') \<cong>\<^sub>G (G // K, composition, unit)"
proof - interpret image:group_epimorphism_fundamental where G'="f ` G"   by unfold_locales (auto simp:commutes_with_composition) have "group_isomorphism image.induced (G // Ker) ([\<cdot>]) (kernel.proj e) (f ` G) (\<cdot>') e'" .. then have "(f ` G, (\<cdot>'), e') \<cong>\<^sub>G (G // Ker, ([\<cdot>]), kernel.proj e)"   by (simp add:isomorphic_as_groups_def) (meson group_isomorphism.inv_group_isomorphism) moreover have "normal_subgroup Ker G (\<cdot>) e" .. ultimately show ?thesis by blast
qed

end 

context monoid
begin

primrec pow_nat  (infixr "**" 80)where 
 pow_0:"x ** 0=e " 
 | pow_Suc:"x ** Suc n=x \<cdot> (x ** n)"


lemma power_one[simp]:"e ** n=e" 
proof(induct n)   case 0 then show ?case  by simp  
next    case (Suc n)  then show ?case by simp
qed
lemma power_on_right[simp]:"x\<in>M \<Longrightarrow> x ** 1=x" by simp 
lemma power_Suc0_right[simp]: "x\<in>M \<Longrightarrow> x ** Suc 0=x" by simp
lemma pow_closed[simp]:"x\<in>M \<Longrightarrow> x ** n\<in>M"
proof(induct n)   case 0 then show ?case by simp
next  case (Suc n) then obtain "x**Suc n=x \<cdot> x**n" and "x**n\<in>M" by simp then show ?case by (simp add: Suc.prems) 
qed
lemma power_commutes: "x\<in>M \<Longrightarrow> (x**n) \<cdot> x=x \<cdot> (x**n)"
proof(induct n)
case 0 then show ?case by simp next case (Suc n) then show ?case by (simp add: m_assoc)
qed
lemma power_Suc2: "x\<in>M \<Longrightarrow> x**Suc n=x**n \<cdot> x" by (simp add: power_commutes)
lemma power_add: "x\<in>M \<Longrightarrow> x**(m + n)=x**m \<cdot> x**n" proof(induct m) case 0  then show ?case by simp next  case (Suc m)  then show ?case  by (simp add: m_assoc)  qed
lemma power_mult: "x\<in>M \<Longrightarrow> x**(m * n)=(x**m)**n"  by (induct n) (simp_all add: power_add)
definition elem_exponents :: "'a \<Rightarrow> nat set" where "elem_exponents x \<equiv> {n::nat. 0<n \<and> x**n=e}"
definition elem_ord::"'a \<Rightarrow> nat" where "elem_ord x \<equiv> if elem_exponents x \<noteq> {} then (Least (\<lambda>n::nat. n\<in>elem_exponents x))  else 0"
lemma elem_ord_simp1:"elem_ord x \<noteq> 0 \<Longrightarrow> elem_ord x= Least (\<lambda>n::nat. n\<in>(elem_exponents x))"  using elem_ord_def by auto
lemma elem_ord_exp:"x**(elem_ord x)=e"
proof(cases "elem_ord x =0") case True  then show ?thesis by auto
next case False then have "elem_ord x=(Least (\<lambda>n::nat. n\<in>elem_exponents x))"   using elem_ord_simp1 by auto also have "...\<in>(elem_exponents x)" by (metis Collect_empty_eq Collect_mem_eq False LeastI elem_ord_def) then show ?thesis   by (simp add: calculation elem_exponents_def) 
qed

lemma order_divides_exponent:assumes "x\<in>M" "elem_ord x \<noteq> 0" "m\<in>elem_exponents x" shows "(elem_ord x) dvd m"
proof- obtain n where nleast:"n =(Least (\<lambda>k::nat. k\<in>elem_exponents x))" and "n\<in>elem_exponents x"   by (meson LeastI assms)  obtain "x**m=e" and "0 < m" using assms elem_exponents_def by auto then obtain "m\<in>elem_exponents x"   by (simp add: assms) then obtain "n \<le> m"   by (simp add: \<open>(n::nat)=(LEAST n::nat. n\<in>elem_exponents (x::'a))\<close> wellorder_Least_lemma(2)) define q where "q \<equiv> m div n" define r where "r=m mod n" then obtain mf:"m=q * n + r" and "0 \<le> r" and "r < n"   by (metis \<open>(n::nat)=(LEAST n::nat. n\<in>elem_exponents (x::'a))\<close> assms(2) bot_nat_0.extremum bot_nat_0.not_eq_extremum div_mod_decomp elem_ord_def mod_less_divisor q_def) then have "e=x**m"  using \<open>(x::'a)**(m::nat)=(e::'a)\<close> by auto also  have "... =x**(q * n + r)"  by (simp add: \<open>(m::nat)=(q::nat) * (n::nat) + (r::nat)\<close>) also have "...=(x**(q * n)) \<cdot> (x**r) " by (simp add: assms(1) local.power_add) also have "...=(e) \<cdot> (x**r)"   by (metis \<open>(n::nat)=(LEAST n::nat. n\<in>elem_exponents (x::'a))\<close> assms(1) assms(2) elem_ord_def elem_ord_exp local.power_mult local.power_one mult.commute) also have "...=x**r"  by (simp add: assms(1))   finally have "r=0" proof-   assume "e=x**r"   show " r=(0::nat)"   proof(rule ccontr)     assume "r \<noteq> 0" then obtain "0<r" and "r < n"   using \<open>(r::nat) < (n::nat)\<close> by blast     also have rmem:"r\<in>elem_exponents x"       using \<open>(e::'a)=(x::'a)**(r::nat)\<close> calculation(1) elem_exponents_def by fastforce     show False       using not_less_Least[of r "(\<lambda>k. k\<in>elem_exponents x)"] nleast rmem calculation by blast   qed qed then have "m=q * n" by (simp add: mf) also have "...=q * (elem_ord x) "   using assms(2) elem_ord_simp1 nleast by presburger finally  show ?thesis by simp
qed

lemma elem_exp_memD1:"\<lbrakk>x\<in>M; elem_ord x \<noteq> 0; m\<in>elem_exponents x\<rbrakk> \<Longrightarrow> (\<exists>k. m =(elem_ord x) * k )" using order_divides_exponent by blast
lemma elem_exp_memD2:"\<lbrakk>x\<in>M; elem_ord x \<noteq> 0; m\<in>elem_exponents x\<rbrakk> \<Longrightarrow> (\<exists>k. k \<ge>1 \<and> m =(elem_ord x) * k )" by (metis Least_eq_0 One_nat_def elem_exp_memD1 elem_ord_simp1 linorder_not_le nat_0_less_mult_iff not_gr0 not_less_eq_eq) 
lemma elem_exp_memI:"\<lbrakk>x\<in>M; elem_ord x \<noteq> 0;(\<exists>k. k \<ge> 1 \<and> m =(elem_ord x) * k)\<rbrakk> \<Longrightarrow> m\<in>elem_exponents x "
proof- assume xmem:"x\<in>M" and nzo:" elem_ord x \<noteq> 0" and mul1:"\<exists>k. k \<ge> 1 \<and> m =(elem_ord x) * k " then obtain k where geq1:"k \<ge> 1" and mul2:"m =(elem_ord x) * k" by blast have "x**(elem_ord x)=e "  by (simp add: elem_ord_exp) then obtain "(x**(elem_ord x))**k=e"  by simp then obtain "x**m=e"  by (simp add: local.power_mult mul2 xmem) then show "m\<in>elem_exponents x"   using elem_exponents_def mul1 nzo by force
qed
lemma elem_exp_memI2:"\<lbrakk>x\<in>M; elem_ord x \<noteq> 0;m > 0; (elem_ord x dvd m)\<rbrakk> \<Longrightarrow> m\<in>elem_exponents x "  using elem_exp_memI by auto
lemma elem_pow_eq_id:"\<lbrakk>a\<in>M; elem_ord a \<noteq> 0; k>0; m>0\<rbrakk> \<Longrightarrow> (a**k)**m=e \<longleftrightarrow> (elem_ord a) dvd (k * m)"
proof- assume amem:"a\<in>M" and nzo:"elem_ord a \<noteq> 0" and kgeqz:"k > 0" and mgeqz:"m>0" show "(a**k)**m=e \<longleftrightarrow> (elem_ord a) dvd (k * m)" proof   assume "(a**k)**m=e"   then obtain "a**(k * m)=e" using amem local.power_mult by auto   then obtain "(k * m)\<in>elem_exponents a" unfolding elem_exponents_def by (simp add: kgeqz mgeqz)   then show "(elem_ord a) dvd (k * m)"   using amem nzo order_divides_exponent by blast next assume "(elem_ord a) dvd (k * m)" then show "(a**k)**m=e"  by (metis amem dvd_def elem_ord_exp local.power_mult monoid.power_one monoid_axioms) qed
qed

lemma id_exps:"elem_exponents e \<noteq> {}" using elem_exponents_def by auto

lemma elem_ord_id:"elem_ord e=1"  unfolding elem_ord_def apply(simp add:id_exps) apply(rule Least_equality) apply (simp add: elem_exponents_def) by (simp add: elem_exponents_def)  
lemma ord_pow1:"\<lbrakk>a\<in>M; elem_ord a \<noteq> 0; (1::nat) \<le> (k::nat)\<rbrakk> \<Longrightarrow> elem_ord (a**k)=(elem_ord a) div (gcd( elem_ord a) k) "
proof- let ?b="a**k" let ?n="elem_ord a" let ?j="?n div (gcd ?n k)" assume amem:"a\<in>M" and nzo:"elem_ord a \<noteq> 0" and kgeq1:"1 \<le> k"  have B1:"\<And>m. m>0 \<Longrightarrow>  (?b**m =e) \<longleftrightarrow>  ?j dvd m" proof-   fix m::nat assume mgtz:"m>0"   then have "(?b**m =e) \<longleftrightarrow> ?n dvd k*m" using amem elem_pow_eq_id kgeq1 nzo by force   also have "... \<longleftrightarrow> ?j dvd ((k * m) div ((gcd ?n k)))" by simp   also have "... \<longleftrightarrow> ?j dvd m"  by (simp add: div_dvd_iff_mult gcd_mult_distrib_nat mult.commute nzo)   finally  show "(?b**m =e) \<longleftrightarrow>  ?j dvd m"  by blast qed then have B2:"?j\<in>elem_exponents ?b"  by (simp add: div_greater_zero_iff elem_exponents_def nzo) have B3:"\<And>m. m\<in>elem_exponents ?b \<Longrightarrow> ?j dvd m"  using B1 elem_exponents_def by auto then have B4:"\<And>m. m\<in>elem_exponents ?b \<Longrightarrow>  ?j \<le> m" using dvd_imp_le elem_exponents_def by blast have B5:"Least (\<lambda>i::nat. i\<in>elem_exponents ?b)=?j "   unfolding elem_ord_def     apply(rule Least_equality)     using B2 elem_ord_def apply force   using B4 elem_ord_def by force show "elem_ord ?b=?j"  by (metis B2 B5 elem_ord_def empty_iff)
qed

lemma pow_fin_ord:"\<lbrakk>a\<in>M; elem_ord a \<noteq> 0\<rbrakk> \<Longrightarrow> elem_ord (a**(k::nat)) \<noteq> 0 "
proof- assume amem:"a\<in>M" and ford:"elem_ord a \<noteq> 0" let ?b="a**(k::nat)" show "elem_ord ?b \<noteq> 0" proof(cases "k=0")   case True then show ?thesis by (simp add: elem_ord_id)  next   case False then show ?thesis  by (simp add: amem div_greater_zero_iff ford ord_pow1)  qed
qed

lemma ord_pow2:"\<lbrakk>a\<in>M; elem_ord a \<noteq> 0;(k::nat)>0;(d::nat)>0; d dvd (elem_ord a)\<rbrakk> \<Longrightarrow> elem_ord (a**k)=d \<longleftrightarrow> (\<exists>r::nat. r > 0 \<and> gcd r d=1 \<and> k=r * (elem_ord a) div d)"
proof- assume amem:"a\<in>M" and ford:"elem_ord a \<noteq> 0" and knz:"(k::nat)>0" and dnz:"(d::nat)>0" and ddvd:"d dvd (elem_ord a)" let ?b="a**k" let ?n="elem_ord a" let ?m="?n div d" have "elem_ord ?b=d \<longleftrightarrow> d=?n div (gcd ?n k)"  using amem ford knz ord_pow1 by auto also have "... \<longleftrightarrow> (gcd ?n k)=?m"   by (metis ddvd dnz dvd_mult_div_cancel gcd.commute gcd_dvd2 gcd_eq_0_iff gcd_pos_nat knz nonzero_mult_div_cancel_right) also have "... \<longleftrightarrow> gcd (d * ?m) k=?m" by (simp add: ddvd) also have "... \<longleftrightarrow> (\<exists>r::nat. r > 0 \<and> gcd r d=1 \<and> k=r * ?m)" (is "?lhs \<longleftrightarrow> ?rhs") proof   assume ?lhs   then show ?rhs   proof -     have f1: "\<forall>n na. \<not> (n::nat) dvd na \<or> na div n * n=na"       using dvd_div_mult_self by blast     have f2: "gcd (elem_ord a) k=elem_ord a div d"       using \<open>(gcd (elem_ord (a::'a)) (k::nat)=elem_ord a div (d::nat))=(gcd (d * (elem_ord a div d)) k=elem_ord a div d)\<close> \<open>gcd ((d::nat) * (elem_ord (a::'a) div d)) (k::nat)=elem_ord a div d\<close> by blast     then have f3: "elem_ord a div d dvd elem_ord a \<and> elem_ord a div d dvd k \<and> (\<forall>n. \<not> n dvd elem_ord a \<or> \<not> n dvd k \<or> n dvd elem_ord a div d)"       by (metis (no_types) gcd_unique_nat)     have f4: "k \<noteq> 0"       using knz by force     have f5: "\<forall>n na. \<not> (n::nat) dvd na \<or> \<not> 0 < na \<or> n \<le> na"       by force     have f6: "\<forall>n na. \<not> (n::nat) dvd na \<or> n * (na div n)=na"       using dvd_mult_div_cancel by blast     have "Suc 0 \<le> d"       using dnz by presburger     then have f7: "1 \<le> d"       by simp     have f8: "d div d=1"       by (simp add: dnz)     have f9: "d div d dvd elem_ord a div d"       by (simp add: ddvd)     then have f10: "d div d * (elem_ord a div d div (d div d))=elem_ord a div d"       using f6 by blast     have "elem_ord a div d=elem_ord a div d div (d div d)"       using f8 by simp     then show ?thesis       using f10 f9 f8 f7 f6 f5 f4 f3 f2 f1 by (smt (z3) One_nat_def \<open>gcd ((d::nat) * (elem_ord (a::'a) div d)) (k::nat)=elem_ord a div d\<close> amem ddvd div_greater_zero_iff dnz dvd_div_eq_0_iff dvd_refl elem_ord_exp elem_ord_id ford gcd.commute gcd_mult_distrib_nat gcd_nat.absorb_iff2 gcd_pos_nat knz local.power_mult monoid.ord_pow1 monoid_axioms nat_mult_eq_cancel1 nonzero_mult_div_cancel_right)   qed   next   assume ?rhs   then obtain r::nat where "r > 0" and "gcd r d=1" and "k=r * ?m" by metis   then show ?lhs  by (metis gcd.commute gcd_mult_distrib_nat mult.comm_neutral mult.commute) qed finally show "elem_ord ?b =d \<longleftrightarrow>  (\<exists>r::nat. r > 0 \<and> gcd r d=1 \<and> k=r * ?n div d)"   by (simp add: ddvd div_mult_swap) 
qed


lemma commute_pow1:"x\<in>M \<Longrightarrow> y\<in>M \<Longrightarrow>x \<cdot> y=y \<cdot> x \<Longrightarrow> x**(n::nat) \<cdot> y=y \<cdot> x**n"
proof- assume xmem:"x\<in>M" and ymem:"y\<in>M" and comm:"x \<cdot> y=y \<cdot> x " let ?xn="x**n"  show "?xn \<cdot> y=y \<cdot> ?xn"  proof(induct n)  case 0 then show ?case by (simp add: ymem)   next   case (Suc n)  then obtain "x**n \<cdot> y=y \<cdot> x **n"   by simp  let ?n1="Suc n"   have "x**?n1 \<cdot> y=x**n \<cdot> (x \<cdot> y)"   using m_assoc local.power_Suc2 pow_closed xmem ymem by presburger   also have "...=x**n \<cdot> (y \<cdot> x)"   by (simp add: comm)   also have "...=(x**n \<cdot> y) \<cdot> x"  by (simp add: m_assoc xmem ymem)   also have "...=(y \<cdot> x **n) \<cdot> x"    by (simp add: Suc)   also have "...=y \<cdot> x**?n1"  using m_assoc local.power_Suc2 pow_closed xmem ymem by presburger   then show ?case   using calculation by auto  qed
qed    
lemma commute_pow2:"x\<in>M \<Longrightarrow> y\<in>M \<Longrightarrow>x \<cdot> y=y \<cdot> x \<Longrightarrow> x**(n::nat) \<cdot> y**(m::nat)=y**m \<cdot> x**n"
proof- assume xmem:"x\<in>M" and ymem:"y\<in>M" and comm:"x \<cdot> y=y \<cdot> x " let ?xn="x**n" let ?ym="y**m" show "?xn \<cdot> ?ym=?ym \<cdot> ?xn" proof(induct m)  case 0 then show ?case using xmem by auto next case (Suc m)   then show ?case   by (metis comm commute_pow1 pow_closed xmem ymem)   qed
qed

lemma commute_pow3:"x\<in>M \<Longrightarrow> y\<in>M\<Longrightarrow>x \<cdot> y=y \<cdot> x \<Longrightarrow> (x \<cdot> y)**(n::nat)=x**n \<cdot> y**n"
proof- assume xmem:"x\<in>M" and ymem:"y\<in>M" and comm:"x \<cdot> y=y \<cdot> x " let ?a="x**n" let ?b="y**n" let ?c="x \<cdot> y" show "(x \<cdot> y)**n=(x**n) \<cdot> (y**n)" proof(induct n)   case 0  then show ?case by simp next   case (Suc n)   then obtain "(x \<cdot> y) ** n=x ** n \<cdot> y ** n"  by blast   let ?m="Suc n"   have "(x \<cdot> y) ** (Suc n)=(x \<cdot> y)**n \<cdot> (x \<cdot> y)"   using local.power_Suc2 xmem ymem by auto    also have "...=(x ** n \<cdot> y ** n) \<cdot> (x \<cdot> y)"  by (simp add: Suc)   also have "...=x**n \<cdot>( y**n \<cdot> x) \<cdot> y"  by (simp add: m_assoc xmem ymem)    also have "...=x**n \<cdot>(x \<cdot> y**n) \<cdot> y" using comm commute_pow1 xmem ymem by auto   also have "...=x**(Suc n) \<cdot> y** (Suc n)" by (metis m_assoc local.power_Suc2 pow_closed xmem ymem)   finally show ?case by simp qed
qed
lemma commute_invertible:"\<lbrakk>x\<in>M; y\<in>M; invertible x; invertible y; x \<cdot> y=y \<cdot> x\<rbrakk> \<Longrightarrow> inv x \<cdot> inv y=inv y \<cdot> inv x" by (metis inv_composition_commute) 
lemma fin_prod_ord: assumes amem:"a\<in>M" and bmem:"b\<in>M" and commute:"a \<cdot> b=b \<cdot> a" and aford:"elem_ord a \<noteq> 0" and bford:"elem_ord b \<noteq> 0" shows "elem_ord (a \<cdot> b) \<noteq> 0"
proof- let ?m="lcm (elem_ord a) (elem_ord b)" have "(a \<cdot> b)**?m=a**?m \<cdot> b**?m"  using amem bmem commute commute_pow3 by blast also have "...=e"   by (metis amem bmem dvdE dvd_lcm1 dvd_lcm2 elem_ord_exp local.power_mult local.power_one pow_closed r_one) then obtain "?m\<in>elem_exponents (a \<cdot> b)"  using aford bford calculation elem_exponents_def by fastforce then show ?thesis by (metis (no_types, lifting) LeastI_ex elem_exponents_def elem_ord_def empty_iff mem_Collect_eq order_less_irrefl) 
qed

lemma commute_ords: assumes amem:"a\<in>M" and bmem:"b\<in>M" and commute:"a \<cdot> b=b \<cdot> a" and aford:"elem_ord a \<noteq> 0" and bford:"elem_ord b \<noteq> 0" shows "(lcm (elem_ord a) (elem_ord b)) div (gcd (elem_ord a) (elem_ord b)) dvd elem_ord (a \<cdot> b)" and       "elem_ord (a \<cdot> b) dvd (lcm (elem_ord a) (elem_ord b))"
proof- let ?\<alpha>="elem_ord a" let ?\<beta>="elem_ord b"  have B0:"elem_ord (a \<cdot> b) \<noteq> 0" by (simp add: aford amem bford bmem commute fin_prod_ord) have B1:"(a \<cdot> b)**?\<beta>=a ** ?\<beta>"  by (simp add: amem bmem commute commute_pow3 elem_ord_exp)   then have B2:"elem_ord ((a \<cdot> b)**?\<beta>)=elem_ord (a ** ?\<beta>)" by simp also have B3:"...=?\<alpha> div (gcd ?\<alpha> ?\<beta>)" using aford amem bford ord_pow1 by auto also have B4:"elem_ord ((a \<cdot> b)**?\<beta>) dvd (elem_ord (a \<cdot> b))"   by (metis B0 One_nat_def amem bford bmem m_closed dvd_div_mult_self dvd_mult2 dvd_refl gcd_Suc_0 gcd_dvd1 gcd_le1_nat ord_pow1)   then have B5:"?\<alpha> div (gcd ?\<alpha> ?\<beta>) dvd (elem_ord (a \<cdot> b))"   by (simp add: calculation)  have B6:"(a \<cdot> b)**?\<alpha>=b ** ?\<alpha>" by (simp add: amem bmem commute commute_pow3 elem_ord_exp)  then have B7:"elem_ord ((a \<cdot> b)**?\<alpha>)=elem_ord (b ** ?\<alpha>)" by simp have B8:"...=?\<beta> div (gcd ?\<alpha> ?\<beta>)" by (metis One_nat_def Suc_leI aford bford bmem bot_nat_0.not_eq_extremum gcd.commute ord_pow1)  have B9:"elem_ord ((a \<cdot> b)**?\<alpha>) dvd (elem_ord (a \<cdot> b))" by (metis B0 One_nat_def aford amem bmem m_closed dvd_div_mult_self dvd_mult2 dvd_refl gcd_Suc_0 gcd_dvd1 gcd_le1_nat ord_pow1)  then have B10:"?\<beta> div (gcd ?\<alpha> ?\<beta>) dvd (elem_ord (a \<cdot> b))"  by (simp add: B6 B8)  have B11:"gcd (?\<beta> div (gcd ?\<alpha> ?\<beta>)) (?\<alpha> div (gcd ?\<alpha> ?\<beta>))=1" proof -   have "gcd (elem_ord a) (elem_ord b) * 1=gcd (elem_ord a) (elem_ord b) * gcd (elem_ord a div gcd (elem_ord a) (elem_ord b)) (elem_ord b div gcd (elem_ord a) (elem_ord b))"     by (metis (no_types) dvd_mult_div_cancel gcd_dvd1 gcd_dvd2 gcd_mult_distrib_nat mult.right_neutral)   then show ?thesis     by (metis (no_types) aford gcd.commute gcd_eq_0_iff mult_left_cancel) qed have B12:"coprime (?\<alpha> div (gcd ?\<alpha> ?\<beta>)) (?\<beta> div (gcd ?\<alpha> ?\<beta>))"  using aford div_gcd_coprime by blast have B13:"((?\<alpha>*?\<beta>) div ((gcd ?\<alpha> ?\<beta>)*(gcd ?\<alpha> ?\<beta>))) dvd  (elem_ord (a \<cdot> b))"  by (metis B10 B12 B5 div_mult_div_if_dvd divides_mult gcd_dvd1 gcd_dvd2) have B14:"(?\<alpha>*?\<beta>) div ((gcd ?\<alpha> ?\<beta>)*(gcd ?\<alpha> ?\<beta>))=(lcm ?\<alpha> ?\<beta>) div (gcd ?\<alpha> ?\<beta>)"  using div_mult2_eq lcm_nat_def by presburger show "(lcm (elem_ord a) (elem_ord b)) div (gcd (elem_ord a) (elem_ord b)) dvd elem_ord (a \<cdot> b)"   by (metis B13 B14)   show "elem_ord (a \<cdot> b) dvd (lcm (elem_ord a) (elem_ord b))" by (metis B0 B6 B8 aford amem bford bmem bot_nat_0.not_eq_extremum m_closed div_greater_zero_iff div_mult_swap elem_ord_exp elem_pow_eq_id gcd_le2_nat gcd_nat.cobounded2 gcd_pos_nat lcm_nat_def)
qed



definition set_exponents where "set_exponents A \<equiv> {n::nat. 0<n \<and> (\<forall>a. a\<in>A \<longrightarrow> a**n=e)}"

definition pow_int (infixl "^" 75) where "pow_int x (z::int) \<equiv> if z < 0 then inv (x**(nat(-z))) else x**(nat z)"
lemma int_pow_int: "x^(int n)=x ** n" by (simp add: pow_int_def)

lemma pow_nat: assumes "i\<ge>0" shows "x**nat i=x^i"
proof (cases i rule: int_cases) case (nonneg n) then show ?thesis   by (simp add: int_pow_int)
next case (neg n) then show ?thesis   using assms by linarith
qed

lemma int_pow_0[simp]: "x^(0::int)=e" by (metis int_ops(1) monoid.int_pow_int monoid.pow_0 monoid_axioms)
lemma int_pow_def2: "a^z=(if z < 0 then inv (a**(nat(-z))) else a**(nat z))" by (simp add: pow_int_def)
lemma int_pow_one[simp]: "e^(z::int)=e"  by (simp add: int_pow_def2)

end

context group
begin
notation pow_int (infixl "^" 75) 
lemma left_cancellation:"\<lbrakk>a\<in>G; x\<in>G; y\<in>G; a\<cdot>x=a\<cdot>y\<rbrakk> \<Longrightarrow> x=y " by simp
lemma right_cancellation:"\<lbrakk>b\<in>G; x\<in>G; y\<in>G;x\<cdot>b=y\<cdot>b\<rbrakk> \<Longrightarrow> x=y " by simp
lemma double_inv_prod:"\<lbrakk>a\<in>G; b\<in>G\<rbrakk> \<Longrightarrow> inv (a \<cdot> inv b)\<in>G" by fastforce
lemma insert_id1:"\<lbrakk>a\<in>G;b\<in>G;c\<in>G\<rbrakk> \<Longrightarrow> a \<cdot> b=a \<cdot> (c \<cdot> inv c) \<cdot>b "  by fastforce 
lemma insert_id2:"\<lbrakk>a\<in>G;b\<in>G;c\<in>G\<rbrakk> \<Longrightarrow> a \<cdot> b=a \<cdot> (inv c \<cdot> c) \<cdot>b " by fastforce 
lemma remove_id1:"\<lbrakk>a\<in>G;b\<in>G;c\<in>G\<rbrakk> \<Longrightarrow> (a \<cdot> inv c) \<cdot> (c \<cdot> b)=a \<cdot>b "  by (simp add: m_assoc invertible_left_inv2)
lemma remove_id2:"\<lbrakk>a\<in>G;b\<in>G;c\<in>G\<rbrakk> \<Longrightarrow> (a \<cdot> c) \<cdot> (inv c \<cdot> b)=a \<cdot>b "  by (simp add: m_assoc invertible_right_inv2) 
lemma l_inv_simp[simp]:"x\<in>G \<Longrightarrow> inv x \<cdot> x=e"  using invertible_left_inv by blast
lemma inv_id_iff[simp]:"x\<in>G \<Longrightarrow> inv x=e \<longleftrightarrow> x=e" using invertible_inv_inv by fastforce
lemma r_inv_simp[simp]:"x\<in>G \<Longrightarrow> x \<cdot> inv x=e" using invertible_right_inv by blast
lemma r_cancel[simp]:"\<lbrakk>x \<in>G; y \<in>G; z \<in>G\<rbrakk> \<Longrightarrow> y\<cdot>x=z \<cdot> x \<longleftrightarrow> y=z" by auto
lemma l_cancel[simp]:"\<lbrakk>x \<in>G; y \<in>G; z \<in>G\<rbrakk> \<Longrightarrow> x\<cdot>y =x\<cdot>z \<longleftrightarrow> y=z" by auto
lemma double_inv[simp]:"x\<in>G \<Longrightarrow> inv (inv x)=x" by simp
lemma inv_commute:"\<lbrakk>x \<cdot> y =e; x\<in>G ; y\<in>G\<rbrakk> \<Longrightarrow> y \<cdot> x=e"  using inv_unique r_inv_ex by blast   
lemma inv_solve_left1:"\<lbrakk>a\<in>G;b\<in>G;c\<in>G\<rbrakk> \<Longrightarrow> a=inv b \<cdot> c \<longleftrightarrow> c=b \<cdot> a" using invertible_left_inv2 by fastforce
lemma inv_solve_right1:"\<lbrakk> a \<in>G; b \<in>G; c \<in>G\<rbrakk> \<Longrightarrow> a=b \<cdot> inv c \<longleftrightarrow> b=a \<cdot> c" using m_assoc by force 
lemma inv_solve_left2:"\<lbrakk>a\<in>G;b\<in>G;c\<in>G\<rbrakk> \<Longrightarrow> inv b \<cdot> c=a \<longleftrightarrow> c=b \<cdot> a"  using invertible_left_inv2  by force
lemma inv_solve_right2:"\<lbrakk> a \<in>G; b \<in>G; c \<in>G\<rbrakk> \<Longrightarrow>  b \<cdot> inv c=a \<longleftrightarrow> b=a \<cdot> c"  using m_assoc by force
lemma int_pow_closed[intro,simp]:"x\<in>G \<Longrightarrow> pow_int x (i::int)\<in>G" by (simp add: int_pow_def2)
lemma int_pow_1[simp]: "x\<in>G \<Longrightarrow> pow_int x (1::int)=x"  by (metis int_ops(2) int_pow_int power_on_right)
lemma int_pow_neg: "x\<in>G \<Longrightarrow> pow_int x (-i::int)=inv (pow_int x i)" by (simp add: int_pow_def2)
lemma int_pow_neg_int: "x\<in>G \<Longrightarrow>x^(-(int n))=inv (x**n)" by (simp add: int_pow_neg int_pow_int)
lemma nat_pow_inv: assumes "x \<in>G" shows "(inv x)**(i :: nat)=inv (x**i)"
proof (induction i) case 0 thus ?case by simp
next case (Suc i) have "(inv x) ** Suc i=((inv x) ** i) \<cdot> inv x" using assms local.power_Suc2 by blast also have " ...=(inv (x ** i)) \<cdot> inv x"   by (simp add: Suc.IH Suc.prems) also have " ...=inv (x \<cdot> (x ** i))" using assms inv_composition_commute invertible pow_closed by presburger  also have " ...=inv (x ** (Suc i))"   by simp finally show ?case  by blast
qed
lemma nat_pow_mult:  "x \<in>G \<Longrightarrow> x ** (n::nat) \<cdot> x ** m=x ** (n + m)" by (simp add: local.power_add)
lemma int_pow_mult:  assumes A0:"x \<in>G" shows "pow_int x (i + j::int)=(pow_int x i) \<cdot> (pow_int x j)"
proof - have[simp]: "-i - j=-j - i" by simp show ?thesis apply(auto simp add:assms int_pow_def2 inv_solve_left inv_solve_right1 nat_add_distrib[symmetric] power_add)   apply (metis add_uminus_conv_diff assms less_imp_le local.power_add nat_add_distrib neg_0_le_iff_le)   apply (smt (verit, best) assms local.power_add nat_add_distrib)   apply (metis add_minus_cancel assms less_imp_le local.power_add nat_add_distrib neg_0_le_iff_le not_less)   apply (smt (verit) assms local.power_add nat_add_distrib)   apply (metis ab_group_add_class.ab_diff_conv_add_uminus add.assoc add_diff_cancel_left' assms less_imp_le linorder_not_le local.power_add nat_add_distrib neg_0_equal_iff_equal neg_less_iff_less)   by (simp add: assms local.power_add nat_add_distrib)
qed

lemma int_pow_inv: "x \<in>G \<Longrightarrow> pow_int (inv x) (i :: int)=inv (pow_int x i)"  by (metis int_pow_def2 nat_pow_inv)
lemma nat_pow_pow:  "x\<in>G \<Longrightarrow> (x ** n) ** m=x** (n * m::nat)"  by (induct m) (simp, simp add: nat_pow_mult add.commute)
lemma int_pow_pow: assumes "x\<in>G" shows "pow_int (pow_int x (n :: int)) (m :: int)=pow_int x (n * m :: int)"
proof (cases) assume n_ge: "n \<ge> 0" thus ?thesis proof (cases)   assume m_ge: "m \<ge> 0" thus ?thesis     by (metis assms monoid.pow_nat monoid.power_mult monoid_axioms mult_nonneg_nonneg n_ge nat_mult_distrib) next   assume m_lt: "\<not> m \<ge> 0"    with n_ge show ?thesis     apply (simp add: int_pow_def2 mult_less_0_iff)     by (metis assms minus_mult_commute minus_mult_left monoid.power_mult monoid_axioms nat_mult_distrib) qed
next assume n_lt: "\<not> n \<ge> 0" thus ?thesis proof (cases)   assume m_ge: "m \<ge> 0"    have "inv x ** (nat m * nat (- n))=inv x ** nat (- (m * n))"     by (metis (full_types) m_ge mult_minus_right nat_mult_distrib)   with m_ge n_lt show ?thesis     by (simp add: int_pow_def2 mult_less_0_iff assms mult.commute nat_pow_inv nat_pow_pow) next   assume m_lt: "\<not> m \<ge> 0" thus ?thesis     using n_lt by (auto simp: int_pow_def2 mult_less_0_iff assms nat_mult_distrib_neg nat_pow_inv nat_pow_pow) qed
qed

lemma int_pow_diff:  "x\<in>G \<Longrightarrow> pow_int x (n - m :: int)= pow_int x n \<cdot> inv (pow_int x m)" by(simp only: diff_conv_add_uminus int_pow_mult int_pow_neg)
lemma inj_on_multc: "c\<in>G \<Longrightarrow> inj_on (\<lambda>x. x \<cdot> c) G" by(simp add: inj_on_def)
lemma inj_on_cmult: "c \<in>G \<Longrightarrow> inj_on (\<lambda>x. c \<cdot> x) G" by(simp add: inj_on_def)

lemma int_pow_mult_distrib: assumes eq: "x \<cdot> y=y \<cdot> x" and xy: "x \<in>G" "y\<in>G" shows "pow_int (x \<cdot> y) (i::int)=(pow_int x i) \<cdot> (pow_int y i)"
proof (cases i rule: int_cases) case (nonneg n) then show ?thesis   using commute_pow3 eq int_pow_int xy(1) xy(2) by presburger
next case (neg n) then show ?thesis   unfolding neg   apply (simp add: xy int_pow_neg_int del: of_nat_Suc)   by (metis commute_pow3 eq  inv_mult_group pow_Suc pow_closed xy)
qed

lemma pow_eq_div2: fixes m n :: nat assumes x_car: "x\<in>G" assumes pow_eq: "x ** m=x ** n" shows "x ** (m - n)=e"
proof (cases "m < n") case False have "e \<cdot> x ** m=x ** m"  by (simp add: x_car)  also have "\<dots>=x ** (m - n) \<cdot> x **n"  using False by (simp add: nat_pow_mult x_car) also have "\<dots>=x ** (m - n) \<cdot> x ** m"   by (simp add: pow_eq) finally show ?thesis   by (metis pow_closed r_cancel one_closed x_car)  
qed simp

inductive_set group_generated::"'a set \<Rightarrow> 'a set" for A where idm:"e\<in>group_generated A"
 |iso:"a\<in>A \<Longrightarrow> a\<in>group_generated A"
 |inv:"a\<in>A \<Longrightarrow> inv a\<in>group_generated A"
 |opc:"a\<in>group_generated A \<Longrightarrow> b\<in>group_generated A \<Longrightarrow> a\<cdot>b\<in>group_generated A"

lemma group_generate: "a\<in>group_generated (G\<inter>A) \<Longrightarrow> a\<in>G" apply (induction rule: group_generated.induct) apply simp apply simp apply simp by simp 


definition cl_group:: "'a set \<Rightarrow> 'a set"  where "cl_group A=group_generated (G\<inter>A)"

lemma inverse_in_cl: "a\<in>cl_group H \<Longrightarrow> inv a\<in>cl_group H" unfolding cl_group_def
apply(induction rule: group_generated.induct) apply (simp add: group_generated.idm) using group_generated.inv apply force using group_generated.iso apply force by (simp add: group_generate group_generated.opc inv_mult_group)

lemma cl_monoid: "monoid (cl_group H) (\<cdot>) e" by (simp add: monoid.intro m_assoc cl_group_def group_generate group_generated.idm group_generated.opc)
lemma cl_sub: "cl_group H \<subseteq> G" using cl_group_def group_generate by blast 
lemma cl_subgroup_of_monoid: "subgroup_of_monoid (cl_group H) G (\<cdot>) e" using cl_group_def cl_sub group_generate group_generated.idm group_generated.opc inverse_in_cl subgroup_of_monoidI by force
lemma cl_subgroup: "subgroup (cl_group H) G (\<cdot>) e" by (simp add: cl_subgroup_of_monoid subgroup_def) 

lemma cl_group_ub:
  assumes A0:"A \<subseteq> B" and 
          A1:"subgroup_of_monoid B G (\<cdot>) e"   
        shows "cl_group A \<subseteq> B"
proof
  fix x assume x:"x \<in> cl_group A"
  then show "x \<in> B"
  unfolding cl_group_def
  apply(induction rule: group_generated.induct)
  apply (meson A1 subgroup_of_monoid.axioms(1) submonoid.sub_one_closed)
  using A0 apply blast
  apply (metis A0 A1 Int_iff inf.absorb_iff2 is_group subgroup.intro subgroupE(3))
  by (simp add: A1 subgroupE(4) subgroup_def)
qed


lemma cl_group_ub2:
  assumes A0:"A \<subseteq> B" and 
          A1:"subgroup B G (\<cdot>) e"   
        shows "cl_group A \<subseteq> B"
proof
  fix x assume x:"x \<in> cl_group A"
  then show "x \<in> B"
  unfolding cl_group_def
  apply(induction rule: group_generated.induct)
  apply (meson A1 subgroup.subgroup_is_submonoid submonoid.sub_one_closed)
  using A0 apply blast
  using A0 A1 subgroupE(3) apply auto[1]
  by (simp add: A1 subgroupE(4))
qed

lemma cl_group_iso:
    assumes A0:"A \<subseteq> B" 
    shows "cl_group A \<subseteq> cl_group B"
proof 
  fix x assume "x\<in>cl_group A" 
  then show "x\<in>cl_group B" unfolding cl_group_def 
  apply(induction rule: group_generated.induct)
  apply (simp add: group_generated.idm)
  using assms group.group_generated.iso in_mono apply fastforce
  using assms group_generated.inv apply auto[1]
  by (simp add: group_generated.opc)
qed


lemma cl_group_extensive:  
  assumes A0:"A \<subseteq> G" 
  shows "A \<subseteq>cl_group A"
proof 
  fix x assume "x\<in>A" 
  then show "x \<in>cl_group A" 
  unfolding cl_group_def using assms group_generated.iso by auto
qed

lemma cl_group_idempotent:"cl_group A=cl_group (cl_group A)"  by (simp add: cl_group_extensive cl_group_ub2 cl_sub cl_subgroup set_eq_subset) 

lemma cl_group_moore1:"cl_group A \<subseteq> \<Inter>{C. subgroup_of_monoid C G (\<cdot>) e \<and> A \<subseteq> C}"  by (metis (no_types, lifting) CollectD Inf_greatest cl_group_ub)
lemma cl_group_moore1b:"cl_group A \<subseteq> \<Inter>{C. subgroup C G (\<cdot>) e \<and> A \<subseteq> C}"  by (metis (no_types, lifting) Inf_greatest cl_group_ub2 mem_Collect_eq)  

lemma cl_group_moore2:"A \<subseteq> G \<Longrightarrow> cl_group A \<supseteq> \<Inter>{C. subgroup_of_monoid C G (\<cdot>) e \<and> A \<subseteq> C}"  by (simp add: Inter_lower  cl_group_extensive cl_subgroup_of_monoid)
lemma cl_group_moore2b:"A \<subseteq> G \<Longrightarrow> cl_group A \<supseteq> \<Inter>{C. subgroup C G (\<cdot>) e \<and> A \<subseteq> C}"  by (simp add: Inter_lower cl_group_extensive cl_subgroup)

lemma cl_group_moore3:"A \<subseteq> G \<Longrightarrow> cl_group A=\<Inter>{C. subgroup_of_monoid C G (\<cdot>) e \<and> A \<subseteq> C}" by (simp add: cl_group_moore1 cl_group_moore2 subset_antisym) 
lemma cl_group_moore3b:"A \<subseteq> G \<Longrightarrow> cl_group A=\<Inter>{C. subgroup C G (\<cdot>) e \<and> A \<subseteq> C}" by (simp add: cl_group_moore1b cl_group_moore2b subset_antisym) 

lemma subgroup_of_monoid_imp_group: "subgroup_of_monoid H G (\<cdot>) e \<Longrightarrow>  group H (\<cdot>) e"   by (simp add: subgroup_of_monoid_def)
lemma subgroup_imp_group: "subgroup H G (\<cdot>) e \<Longrightarrow>  group H (\<cdot>) e" by (simp add: subgroup_def subgroup_of_monoid_imp_group) 

lemma subgroup_of_monoid_int_pow_closed:
  assumes "subgroup_of_monoid H G (\<cdot>) e" "h\<in>H" 
  shows "h^ (k :: int)\<in>H" 
  by (metis assms group.is_monoid group.subgroup_of_monoid_imp_group int_pow_def2 is_group monoid.pow_closed subgroupE(3) subgroup_def)


lemma subgroup_int_pow_closed:
  assumes "subgroup H G (\<cdot>) e" "h\<in>H" 
  shows "h^ (k :: int)\<in>H"
  by (simp add: assms(1) assms(2) subgroup.axioms(1) subgroup_of_monoid_int_pow_closed) 


lemma generate_pow:
  assumes "a \<in>G"
  shows "cl_group {a}={a^(k :: int) | k. k\<in>UNIV }" (is "?LHS=?RHS")
proof
  show "?RHS \<subseteq> ?LHS" 
  proof 
    fix x assume "x\<in>?RHS" 
    then obtain k::"int" where "x=pow_int a k" by blast 
    then show "x\<in>?LHS"
      by (meson assms cl_group_extensive cl_subgroup_of_monoid empty_subsetI insert_subset subgroup_of_monoid_int_pow_closed) 
  qed
next
  show "?LHS \<subseteq> ?RHS" 
  proof   
    fix h assume "h\<in>cl_group {a}" 
    hence "\<exists>k :: int. h=pow_int a k" 
      unfolding cl_group_def
    proof(induction rule: group_generated.induct) 
      case idm then show ?case  by (metis int_pow_0) 
    next     
      case (iso a)  then show ?case by (metis IntD2 assms int_pow_1 singletonD) 
    next 
      case (inv a) 
      then show ?case by (metis IntD2 assms int_pow_1 int_pow_neg singletonD)   
    next  
      case (opc a b)  
      then show ?case by (metis assms int_pow_mult) 
    qed   
    then show "h\<in>?RHS"   
      by blast 
  qed
qed

lemma subgroup_of_monoidI1: 
  assumes subset: "H \<subseteq> G" and
          non_empty: "H \<noteq> {}" and
          closed: "\<And>a b. \<lbrakk>a\<in>H; b\<in>H\<rbrakk> \<Longrightarrow> a\<cdot>b\<in>H"  and 
          inv_cl: "\<And>a. a\<in>H \<Longrightarrow> inv a\<in>H" 
  shows "subgroup_of_monoid H G (\<cdot>) e" 
  apply(unfold_locales) 
  apply(auto simp add:subset closed inv_cl)
  apply (metis closed ex_in_conv inv_cl non_empty r_inv_simp subset subset_iff)
  using subset apply blast 
  using subset apply blast
  using subset apply blast
proof-
  fix u assume u:"u \<in> H"
  have "monoid H (\<cdot>) e"
   using assms apply(auto intro!:monoid.intro) by (metis r_inv_simp subset_iff)
  then show "monoid.invertible H (\<cdot>) e u"
    by (simp add: closed group.invertible inv_cl monoid.one_closed subgroupI subgroup_imp_group subset u)
qed


lemma subgroupI1: 
  assumes subset: "H \<subseteq> G" and
          non_empty: "H \<noteq> {}" and
          closed: "\<And>a b. \<lbrakk>a\<in>H; b\<in>H\<rbrakk> \<Longrightarrow> a\<cdot>b\<in>H"  and 
          inv_cl: "\<And>a. a\<in>H \<Longrightarrow> inv a\<in>H" 
  shows "subgroup H G (\<cdot>) e"
  by (simp add: closed inv_cl non_empty subgroup.intro subgroup_of_monoidI1 subset) 

lemma subgroup_of_monoidE1: 
  assumes "subgroup_of_monoid H G (\<cdot>) e" 
  shows "H \<subseteq> G" and
        "H \<noteq> {}" and
        "\<And>a. a\<in>H \<Longrightarrow> inv a\<in>H" and 
        "\<And>a b. \<lbrakk>a\<in>H; b\<in>H\<rbrakk> \<Longrightarrow> a \<cdot> b\<in>H"  
  using assms unfolding subgroup_of_monoid_def
     apply (meson submonoid.subset)
    apply (metis assms equals0D subgroup_of_monoid_def submonoid.sub_one_closed) 
   apply (meson assms group.invertible subgroup_of_monoid_def submonoid.submonoid_inv_closed)
  by (meson assms subgroup_of_monoid_def submonoid.sub_m_closed) 

lemma trivial_subgroup_of_monoid:"subgroup_of_monoid {e} G (\<cdot>) e"  using subgroup_of_monoidI1 by force 
lemma trivial_subgroup:"subgroup {e} G (\<cdot>) e"  using subgroupI1 by force 

lemma subgroup_of_monoid_inverse_equality[simp]:
  assumes A0:"subgroup_of_monoid H G (\<cdot>) e" and 
          A1:"x\<in>H" 
   shows "monoid.inv H (\<cdot>) e x= inv x" 
  by (metis A0 assms(2) subgroup_of_monoid.subgroup_of_monoid_inv_equality)

lemma subgroup_inverse_equality[simp]:
  assumes A0:"subgroup H G (\<cdot>) e" and 
          A1:"x\<in>H" 
   shows "monoid.inv H (\<cdot>) e x= inv x"
  by (simp add: A0 A1 subgroup.axioms(1)) 

lemma generate_id: "cl_group {e}={e}" by (meson cl_group_extensive cl_group_ub equalityE subgroup_of_monoidE1(1) subset_antisym trivial_subgroup_of_monoid)  
lemma generate_empty: "cl_group {}={e}" by (metis cl_group_iso cl_subgroup_of_monoid empty_subsetI generate_id group.subgroup_of_monoidE1(2) group_axioms subset_singletonD)

definition exps :: "'a \<Rightarrow> int set" where "exps x \<equiv> {n::int. 0<n \<and> x^n=e}"
lemma exps_eq_elem_exps1:"\<And>n. n\<in>elem_exponents x \<Longrightarrow> (int n)\<in>exps x" unfolding elem_exponents_def exps_def using int_pow_int by auto 
lemma exps_eq_elem_exps2:"\<And>n. (int n)\<in>exps x \<Longrightarrow> n\<in>elem_exponents x" unfolding elem_exponents_def exps_def using int_pow_int by auto 
lemma exps_eq_elem_exps3:"\<And>n. n\<in>exps x \<Longrightarrow> (nat n)\<in>elem_exponents x" unfolding elem_exponents_def exps_def using pow_nat by auto
lemma exps_eq_elem_exps4:"\<And>n. (nat n)\<in>elem_exponents x \<Longrightarrow> n\<in>exps x" unfolding elem_exponents_def exps_def using pow_nat by auto 
lemma exps_eq_elem_exps5:"\<And>n::int. n\<in>exps x \<Longrightarrow> \<exists>m::nat. n=int m \<and> m\<in>elem_exponents x" using exps_eq_elem_exps3 group.exps_def group_axioms by fastforce
lemma exps_eq_elem_exps6:"\<And>n::nat. n\<in>elem_exponents x \<Longrightarrow> \<exists>m::int. n=nat m \<and> m\<in>exps x"  using exps_eq_elem_exps1 by force 
lemma exps_eq_elem_exps7:"exps x={int n|n. n\<in>elem_exponents x}" by(auto intro:exps_eq_elem_exps1 exps_eq_elem_exps5)
lemma exps_eq_elem_exps8:"elem_exponents x={nat n|n. n\<in>exps x}" by(auto intro:exps_eq_elem_exps3 exps_eq_elem_exps6)
lemma elem_exponents_ne1:"elem_exponents x \<noteq> {} \<Longrightarrow> (\<exists>!n. n=Least (\<lambda>k::nat. k\<in>elem_exponents x)) " by auto
lemma elem_exponents_ne2:"elem_exponents x \<noteq> {} \<Longrightarrow> (\<exists>!n. n\<in>elem_exponents x \<and> (\<forall>m. m\<in>elem_exponents x \<longrightarrow> n \<le> m)) " using elem_exponents_ne1 apply(auto)  apply (meson wellorder_Least_lemma(1) wellorder_Least_lemma(2))using le_antisym by presburger
lemma exps_ne1:"exps x \<noteq> {} \<Longrightarrow> (\<exists>!n. n=Least (\<lambda>k::int. k\<in>exps x)) " by auto
lemma exps_ne2:assumes A0:"exps x \<noteq> {}" shows "(\<exists>!n. n\<in>exps x \<and> (\<forall>m. m\<in>exps x \<longrightarrow> n \<le> m)) "
proof- from A0 have "elem_exponents x \<noteq> {}" using exps_eq_elem_exps7 by force  then obtain n where "n\<in>elem_exponents x" and "\<And>m. m\<in>elem_exponents x \<Longrightarrow> n \<le> m" using elem_exponents_ne2[of x] by auto then obtain "int n\<in>exps x" and "\<And>m. m\<in>exps x \<Longrightarrow> int n \<le> m" using exps_eq_elem_exps1 exps_eq_elem_exps5 of_nat_le_iff by blast then show ?thesis by force
qed
lemma exps_ne3:assumes A0:"exps x \<noteq> {}"   shows "Least (\<lambda>k::int. k\<in>exps x)=int (Least (\<lambda>k::nat. k\<in>elem_exponents x))" and  "nat (Least (\<lambda>k::int. k\<in>exps x))=(Least (\<lambda>k::nat. k\<in>elem_exponents x))"
proof- from A0 have "elem_exponents x \<noteq> {}" using exps_eq_elem_exps7 by force  then obtain n where B0:"n\<in>elem_exponents x" and B1:"\<And>m. m\<in>elem_exponents x \<Longrightarrow> n \<le> m" using elem_exponents_ne2[of x] by auto then obtain B2:"n=(Least (\<lambda>k::nat. k\<in>elem_exponents x))"  by (meson LeastI Least_le le_antisym) then obtain "int n\<in>exps x" and "\<And>m. m\<in>exps x \<Longrightarrow> int n \<le> m" using B0 B1 exps_eq_elem_exps1 exps_eq_elem_exps5 of_nat_le_iff by blast then obtain B3:"(int n)=(Least (\<lambda>k::int. k\<in>exps x))"  by (simp add: Least_equality)  then show "Least (\<lambda>k::int. k\<in>exps x)=int (Least (\<lambda>k::nat. k\<in>elem_exponents x))"  by (simp add: B2)  then show "nat (Least (\<lambda>k::int. k\<in>exps x))=(Least (\<lambda>k::nat. k\<in>elem_exponents x))" by auto
qed
lemma exps_ne4:assumes A0:"exps x \<noteq> {} | elem_exponents x \<noteq> {}"                shows "Least (\<lambda>k::int. k\<in>exps x)=int (Least (\<lambda>k::nat. k\<in>elem_exponents x))" and                     "nat (Least (\<lambda>k::int. k\<in>exps x))=(Least (\<lambda>k::nat. k\<in>elem_exponents x))" using assms exps_eq_elem_exps7 exps_ne3(1) apply auto[1] using assms exps_eq_elem_exps7 exps_ne3(2) by force

definition ord::"'a \<Rightarrow> int" where "ord x \<equiv> if exps x \<noteq> {} then (Least (\<lambda>n::int. n\<in>exps x))  else 0"
lemma ord_simp:"exps x \<noteq> {} \<Longrightarrow> ord x = (Least (\<lambda>n::int. n\<in>exps x))" using ord_def by auto
lemma ord_eq_elem_ord1:"ord x=int (elem_ord x)"  using elem_ord_def exps_eq_elem_exps7 exps_ne3(1) ord_def by force 
lemma ord_eq_elem_ord2:"nat (ord x)=(elem_ord x)"  using elem_ord_def exps_eq_elem_exps7 exps_ne3(1) ord_def by force 
lemma ord_exp:"x^(ord x)=e"  by (simp add: elem_ord_exp monoid.int_pow_int ord_eq_elem_ord1) 
abbreviation finord where "finord x \<equiv> ord x \<noteq> 0"
lemma pow_mem:"x\<in>G \<Longrightarrow> x^k\<in>cl_group {x}"   by (meson cl_group_extensive cl_subgroup_of_monoid insert_subset subgroup_of_monoidE1(1) subgroup_of_monoid_int_pow_closed trivial_subgroup_of_monoid)
lemma thebigchungus:"\<lbrakk>x\<in>G;ord x \<noteq> 0;m\<in>exps x\<rbrakk>\<Longrightarrow>(ord x) dvd m" using exps_eq_elem_exps5 ord_eq_elem_ord1 order_divides_exponent by fastforce                        
lemma finord_eq:
  assumes A0:"finord x" and A1:"x\<in>G" 
  shows "cl_group {x}={x^k|k. 0 \<le> k \<and> k < ord x}"
proof- 
  obtain n where B0:"n=ord x" by auto
  then have B1:"n > 0"  using A0 ord_eq_elem_ord1 by auto 
  have "\<And>k. \<lbrakk>0 \<le> k; k < ord x\<rbrakk> \<Longrightarrow> x^k\<in>cl_group {x}" 
    using A1 pow_mem by auto
  then have RL:"\<And>y. y\<in>{x^k|k. 0 \<le> k \<and> k < ord x} \<Longrightarrow> y\<in>cl_group {x}" 
    by blast have B1:"cl_group {x}={x^(k :: int) | k. k\<in>UNIV }" 
  using A1 generate_pow by blast have LR:"\<And>y. y\<in>cl_group {x} \<Longrightarrow> y\<in>{x^k|k. 0 \<le> k \<and> k < ord x}"
  proof-  
    fix y assume A2:"y\<in>cl_group {x}"   
    then obtain k where B2:"y=x^(k :: int)" using B1 by auto  
    define q r where"q \<equiv> k div n" and "r \<equiv> k mod n"  
    then obtain B3:"k=q * n + r" and B4:"0 \<le> r" and B5:"r < n" 
      using A0 B0 ord_eq_elem_ord1 by force  
    then have "y=x ^ k" 
      using B2 by blast 
    also have "... =x^(q*n+r)"  
      using B3 by auto   
    also have "...=x^(q*n) \<cdot> x^r"  
      by (simp add: A1 int_pow_mult)   
    also have "...=(x^n)^q \<cdot> x^r"    
      by (simp add: A1 int_pow_pow mult.commute)  
    also have "...=e^q \<cdot> x^r"  
      using B0 ord_exp by auto       
    also have "...=x ^ r" 
      using A1 by fastforce   
    also have "...\<in>{x^k|k. 0 \<le> k \<and> k < ord x}" 
      using B0 B4 B5 by blast
    finally show "y\<in> {x^k|k. 0 \<le> k \<and> k < ord x}" 
      by blast
  qed 
  from RL LR show ?thesis
    by blast
qed       

lemma big_chungus1:
  assumes A0:"(n::int)>0" 
  shows "bij_betw (\<lambda>i. nat i) {i::int. 0 \<le>i \<and> i<  n} {i::nat. i<nat n}" 
proof-              
  let ?f=" (\<lambda>i. nat i)" let ?A="{i::int. 0 \<le>i \<and> i<  n}" let ?B="{i::nat. i<nat n}" 
  have B0:"inj_on ?f ?A"  
    by (simp add: eq_nat_nat_iff inj_on_def)      
  have B1:"?f`?A \<subseteq> ?B" by force            
  have B2:"?B \<subseteq> ?f `?A"   
  proof  
    fix b assume A1:"b\<in>?B"  
    then obtain "0 \<le> int b" and "int b < n" 
      by simp               
    then obtain "int b\<in>?A"  
      by auto                                      
    then obtain "?f (int b)\<in>?f`?A" 
      by blast      
    then show "b\<in>?f`?A"  
      by auto                           
  qed                  
  then show ?thesis  
    using B0 B1 bij_betw_def by blast    
qed

lemma big_chungus2:
  assumes A0:"(n::int)>0" 
  shows "card {i::int. 0 \<le>i \<and> i<  n}=card {i::nat. i<nat n}" 
  using assms big_chungus1 bij_betw_same_card by blast   

lemma big_chungus3:
  assumes A0:"(n::int)>0" 
  shows "card {k|k. 0 \<le> k \<and> k < nat n}=card {k|k. 0 \<le> k \<and> k < n}" 
  using assms big_chungus1 bij_betw_same_card by fastforce

definition cyclic_group where "cyclic_group C \<equiv> (\<exists>x\<in>G. cl_group {x}=C)"
lemma cyclic_group_eq: 
  assumes A0:"C\<subseteq>G" 
  shows "cyclic_group C \<longleftrightarrow> (\<exists>g\<in>G. C= { pow_int g (k :: int) | k. k\<in>UNIV })"   
  using cyclic_group_def generate_pow by auto

lemma cylic_subgroup_of_monoid_pow: 
  assumes A0:"x\<in>G" 
  shows "cl_group {x}=cl_group {inv x}"
proof-
  have "cl_group {x}={ pow_int x (k :: int) | k. k\<in>UNIV }" 
    by (simp add: assms generate_pow)
  also have "...={ pow_int x (-(k :: int)) | k. k\<in>UNIV }" 
    by (metis UNIV_I add.inverse_inverse)
  also have "...={pow_int (inv x) (k :: int)|k. k\<in>UNIV}"
    using assms int_pow_inv int_pow_neg by presburger 
  also have "...=cl_group {inv x}" 
    using assms generate_pow invertible invertible_inv_closed by presburger
  finally show ?thesis 
    by auto
qed


end

locale cyclic_group=group G "(\<cdot>)" e for G and f (infixl "\<cdot>" 70) and e+ assumes cyclic:"\<exists>g\<in>G. cl_group {g}=G"
begin
lemma cyclic_subgroup_of_monoid:
  assumes A0:"cyclic_group G" and A1:"subgroup_of_monoid H G (\<cdot>) e" 
  shows "cyclic_group H"
proof- 
  obtain g where A2:"g\<in>G" and A3:"G=cl_group {g}"
    using A0 cyclic_group_def by auto 
  have B0:"H \<subseteq> G"  
    by (simp add: A1 subgroup_of_monoidE1(1))  
  show ?thesis proof(cases "H={e}") 
    case True then show ?thesis
      using generate_id local.cyclic_group_def by blast
  next 
    case False  
    define M where "M \<equiv> {n::nat. n >0 \<and> monoid.pow_nat f e g n\<in>H}"  
    have B0:"M \<noteq> {}" 
    proof- 
      obtain h where A4:"h\<in>H" and A4b:"h \<noteq> e" 
        by (metis A1 False insertI1 subgroup_of_monoidE1(2) subsetI subset_singleton_iff) 
      obtain A5:"inv h\<in>H" and A6:"h\<in>G"   
        using A1 A4 B0 subgroup_of_monoidE1(3) by auto 
      obtain k::"int" where A7:"h=monoid.pow_int G f e g k" 
        using A2 A3 A6 generate_pow by fastforce
      show ?thesis
      proof(cases "k < 0")
        case True 
        then have "inv h=monoid.pow_int G f e g (-k)"
          using A2 A7 int_pow_neg by presburger     
        also have "...\<in>H" 
          using A5 calculation by auto
        then have "nat (-k)\<in>M" 
          unfolding M_def using True int_pow_def2 by force
        then show ?thesis by auto
      next      
        case False      
        then obtain A7:"nat k\<in>M"
          unfolding M_def using A4 A7 int_pow_def2 A4b by force
        then show ?thesis
          by auto 
      qed 
    qed  
    define n where "n \<equiv> Least (\<lambda>n::nat. n\<in>M)" 
    define h where "h \<equiv> pow_nat g n"  
    have B3:"h\<in>G"  
      by (simp add: A2 h_def)  
    have B5:"n > 0"
      unfolding n_def M_def using B0 
      by (metis (no_types, lifting) LeastI M_def ex_in_conv mem_Collect_eq) 
    have B1:"h\<in>H" 
      unfolding h_def n_def M_def using B0 by (metis (mono_tags, lifting) Collect_empty_eq LeastI M_def mem_Collect_eq) 
    have B2:"cl_group {h} \<subseteq> H" 
      by (simp add: A1 B1 cl_group_ub) 
    have B4:"H \<subseteq> cl_group {h}"  
    proof   
      fix x assume A8:"x\<in>H"  
      then obtain A9:"x\<in>G" 
        using A1 subgroup_of_monoidE1(1) by fastforce 
      then obtain k::"int" where A10:"x=pow_int g k" 
        using A2 A3 generate_pow by fastforce
      show "x\<in>cl_group {h}"  
      proof(cases "k > 0") 
        case True   
        define m where "m \<equiv> nat k"  
        define q where "q \<equiv> m div n" 
        define r where "r \<equiv> m mod n"   
        then obtain B6:"m=n * q + r" and B6b:"0 \<le> r" and B6c:"r < n"  
          by (metis (no_types, lifting) B0 CollectD LeastI_ex M_def bot_nat_0.extremum ex_in_conv mod_less_divisor mult_div_mod_eq n_def q_def r_def)
        have "x=pow_int g k"  by (simp add: A10)
        also have "...=pow_nat g m" 
          using True int_pow_def2 m_def by auto
        also have "...=pow_nat g (n * q + r)" 
          by (simp add: B6)    
        also have "...=pow_nat g (n * q) \<cdot> (pow_nat g r)"
          by (simp add: A2 nat_pow_mult) 
        finally have B7:"x=pow_nat (pow_nat g n) q \<cdot> (pow_nat g r)"
          using A2 nat_pow_pow by auto     
        then obtain B8:"pow_int (pow_nat g n) (-(int q)) \<cdot> x=(pow_nat g r)" 
          by (metis A2 A9 group.int_pow_neg group_axioms int_pow_closed int_pow_int inv_solve_left)
        then have "inv (pow_nat (pow_nat g n) q) \<cdot> x=(pow_nat g r)" 
          by (simp add: A2 int_pow_neg_int)     
        also have "...\<in>H" 
          by (metis A1 A8 B1 B8 group.subgroup_of_monoidE1(4) group.subgroup_of_monoid_int_pow_closed group_axioms h_def) 
        then have B9:"r=0" 
           using M_def not_less_Least B6 B6b B6c  using bot_nat_0.not_eq_extremum n_def by blast 
        then have "n dvd m" 
          by (simp add: mod_eq_0_iff_dvd r_def)
        then have "x\<in>cl_group {h}"
          by (metis A9 B3 B8 B9 h_def int_pow_closed int_pow_neg inv_inv local.inv_equality pow_0 pow_mem) 
        then show ?thesis by auto   
      next     
        case False       
        have B9:"(-k) \<ge> 0"  
          using False by auto   
        define m where "m \<equiv> nat (-k)" 
        define q where "q \<equiv> m div n"  
        define r where "r \<equiv> m mod n"  
        then obtain B6:"m=n * q + r" and B6b:"0 \<le> r" and B6c:"r < n"
          by (simp add: B5 q_def)  
        have "inv x=pow_int g (-k)" using A10 A2 int_pow_neg by presburger
        also have "...=pow_nat g m" 
          using B9 m_def pow_nat by presburger   
        also have "...=pow_nat g (n * q + r)" 
          by (simp add: B6)     
        also have "...=pow_nat g (n * q) \<cdot> (pow_nat g r)" 
          by (simp add: A2 nat_pow_mult)   
        finally have B7:"(inv x)=pow_nat (pow_nat g n) q \<cdot> (pow_nat g r)" 
          using A2 local.power_mult by presburger  
        then obtain B8:"pow_int (pow_nat g n) (-(int q)) \<cdot> (inv x)=(pow_nat g r)"
          by (simp add: A2 int_pow_int int_pow_neg invertible_left_inv2) 
        then have "inv (pow_nat (pow_nat g n) q) \<cdot> (inv x)=(pow_nat g r)" 
          by (simp add: A2 int_pow_neg_int)   
        also have "...\<in>H" 
          by (metis A1 A8 B1 B8 group.subgroup_of_monoidE1(3) group_axioms h_def subgroup_of_monoidE1(4) subgroup_of_monoid_int_pow_closed) 
        then have B9:"r=0" 
          unfolding n_def using B6 B6b B6c not_less_Least  using M_def linorder_cases n_def by blast
        then have "n dvd m"  by (simp add: mod_eq_0_iff_dvd r_def)   
        then have "inv x\<in>cl_group {h}"
          by (metis B3 B7 B9 h_def int_pow_diff int_pow_int inv_unit pow_0 pow_mem)
        then obtain "x\<in>cl_group {h}" using A10 A2 inverse_in_cl by fastforce 
        then show ?thesis by auto 
      qed  
    qed  
  then show ?thesis
    using B2 B3 local.cyclic_group_def
    by blast qed
qed

end


context group
begin

definition rconj where "rconj g x \<equiv> x \<cdot> g \<cdot> inv x"
definition conjugacy_class where "conjugacy_class g \<equiv> {x \<cdot> g \<cdot> inv x|x. x\<in>G}"

lemma rconj_pow:assumes A0:"g\<in>G" and A1:"x\<in>G" shows "(rconj g x)** n=x \<cdot> g **n \<cdot> inv x"
proof(induct n) case 0 then show ?case using A1 by auto
next case (Suc n) then show ?case unfolding rconj_def using A0 A1 group.remove_id1 group_axioms monoid.m_assoc monoid_axioms by fastforce  
qed

lemma rconj_pow_int:assumes A0:"g\<in>G" and A1:"x\<in>G" shows "(rconj g x)^ n=x \<cdot> g ^n \<cdot> inv x"
proof(cases "n<0") case True then have "(rconj g x)^n=inv ((rconj g x)**(nat(-n)))"    by (meson int_pow_def2) also have "...=inv (x \<cdot> g**(nat(-n)) \<cdot> inv x)"  using A0 A1 rconj_pow by presburger also have "...= x \<cdot> inv (g**(nat(-n))) \<cdot> inv x"  by (simp add: A0 A1 m_assoc inv_mult_group) also have "...=x \<cdot> g^n \<cdot> inv x" using True int_pow_def2 by presburger finally show ?thesis  by blast 
next case False then show ?thesis   using A0 A1 int_pow_def2 rconj_pow by presburger 
qed

lemma conj_class_ord_lt: assumes A0:"g\<in>G" and A1:"h\<in>conjugacy_class g" shows "\<And>n. g^n=e \<Longrightarrow> h^n=e" and "\<And>n. h^n=e \<Longrightarrow> g^n=e" and       "\<And>n. g**n=e \<Longrightarrow> h**n=e" and "\<And>n. h**n=e \<Longrightarrow> g**n=e"
proof- obtain x where A2:"x\<in>G" and A3:"h=x \<cdot> g \<cdot> inv x" using A1 conjugacy_class_def by auto have B0:"h=rconj g x"  by (simp add: A3 rconj_def) show B1:"\<And>n. g^n=e \<Longrightarrow> h^n=e"  by (simp add: A0 A2 B0 rconj_pow_int)   show B2:"\<And>n. h^n=e \<Longrightarrow> g^n=e" proof-   fix n assume A4:"h^n=e" then obtain " x \<cdot> g ^n \<cdot> inv x=e" by (simp add: A0 A2 B0 rconj_pow_int)    then obtain "inv x \<cdot> x \<cdot> g^n \<cdot> inv x \<cdot> x=inv x \<cdot>e \<cdot> x" by (metis A0 A2 m_assoc m_closed int_pow_closed invertible monoid.invertible_inv_closed monoid_axioms)    then show "g^n=e"  by (simp add: A0 A2 m_assoc)  qed show B3:"\<And>n. g**n=e \<Longrightarrow> h**n=e"    by (metis B1 int_pow_int)   show B4: "\<And>n. h**n=e \<Longrightarrow> g**n=e"   by (metis B2 int_pow_int) 
qed

lemma conj_class_ord: assumes A0:"g\<in>G" and A1:"h\<in>conjugacy_class g" shows "elem_ord g=elem_ord h"
proof- have B0:"elem_exponents g \<subseteq> elem_exponents h"  unfolding elem_exponents_def   using A0 A1 conj_class_ord_lt(3) by force  also have B1:"elem_exponents h \<subseteq> elem_exponents g" unfolding elem_exponents_def using A0 A1 conj_class_ord_lt(4) by blast finally show ?thesis  using elem_ord_def by auto
qed
(*converse is false viz. abelian groups*)


end

context group begin

lemma top_subgroup_of_monoid: "subgroup_of_monoid G G (\<cdot>) e"  by (auto intro:subgroup_of_monoidI) 
lemma top_subgroup:"subgroup G G (\<cdot>) e" by (auto intro:subgroupI)

definition elem_commutator ("C'[_,_']")  where "C[a,b] \<equiv> a \<cdot> b \<cdot> inv a \<cdot> inv b"

lemma commutesI1:"\<lbrakk>a\<in>G; b\<in>G; C[a,b]=e\<rbrakk> \<Longrightarrow> a\<cdot>b=b\<cdot>a" unfolding elem_commutator_def using group.inv_solve_right1 group_axioms local.inv_equality by fastforce 
lemma commutesI2:"\<lbrakk>a\<in>G; b\<in>G; e=C[a,b]\<rbrakk> \<Longrightarrow> a\<cdot>b=b\<cdot>a" by (metis commutesI1) 
lemma commutesD1:"\<lbrakk>a\<in>G; b\<in>G; a\<cdot>b=b\<cdot>a\<rbrakk> \<Longrightarrow>C[a,b]=e" unfolding elem_commutator_def by (simp add: m_assoc)
lemma commutesD2:"\<lbrakk>a\<in>G; b\<in>G; a\<cdot>b=b\<cdot>a\<rbrakk> \<Longrightarrow>e=C[a,b]" unfolding elem_commutator_def by (simp add: m_assoc)  

lemma commutes_iff1:"\<lbrakk>a\<in>G; b\<in>G\<rbrakk> \<Longrightarrow> a\<cdot>b=b\<cdot>a \<longleftrightarrow> C[a,b]=e"  using commutesD1 commutesI1 by blast
lemma commutes_iff2:"\<lbrakk>a\<in>G; b\<in>G\<rbrakk> \<Longrightarrow> a\<cdot>b=b\<cdot>a \<longleftrightarrow> e=C[a,b]"  using commutesD2 commutesI2 by blast

lemma commutes_inv:"\<lbrakk>a\<in>G; b\<in>G\<rbrakk> \<Longrightarrow> C[b,a]=inv C[a,b]" unfolding elem_commutator_def using inv_closed inv_inv inv_mult_group m_assoc m_closed by presburger  


definition derived where "derived A \<equiv> cl_group  {C[a,b]|a b. a\<in>A \<and> b\<in>A}"


lemma commutators_sub1: assumes "K \<subseteq> H" "subgroup_of_monoid H G (\<cdot>) e" shows "{C[a,b]|a b. a\<in>K \<and> b\<in>K} \<subseteq> H"  unfolding elem_commutator_def using assms subgroup_of_monoidE1 by (auto simp add: subset_iff)
lemma commutators_sub2:"K \<subseteq> H \<Longrightarrow> subgroup H G (\<cdot>) e \<Longrightarrow>{C[a,b]|a b. a\<in>K \<and> b\<in>K} \<subseteq> H"   by (simp add: commutators_sub1 subgroup.axioms(1))

lemma derived_sub1: assumes "K \<subseteq> H" "subgroup_of_monoid H G (\<cdot>) e" shows "derived K \<subseteq> H" unfolding derived_def by(rule cl_group_ub, auto simp add: assms commutators_sub1)
lemma derived_sub2:"K \<subseteq> H \<Longrightarrow> subgroup H G (\<cdot>) e \<Longrightarrow>derived K \<subseteq> H" by (simp add: derived_sub1 subgroup.axioms(1))  

lemma commutators_sub3: "H \<subseteq> G \<Longrightarrow> {C[a,b]|a b. a\<in>H \<and> b\<in>H} \<subseteq> G"  unfolding elem_commutator_def by(blast)
lemma derived_sub3:"H \<subseteq> G \<Longrightarrow> derived H \<subseteq> G"  using  top_subgroup_of_monoid  derived_sub1 by auto

lemma exp_of_derived_sub: assumes "H \<subseteq> G" shows "(derived ^^ n) H \<subseteq> G" using assms derived_sub3 by (induct n) (auto)
lemma derived_is_subgroup_of_monoid:"H \<subseteq> G \<Longrightarrow> subgroup_of_monoid (derived H) G (\<cdot>) e"  unfolding derived_def using cl_subgroup_of_monoid by blast 
lemma derived_is_subgroup:"H \<subseteq> G \<Longrightarrow> subgroup (derived H) G (\<cdot>) e" unfolding derived_def using cl_subgroup by blast 


end

context group_homomorphism
begin
lemma id_to_id:"f e = e'" 
  by auto

lemma inv_to_inv:
  assumes A0:"g \<in> G"
  shows "f (source.inv g) = target.inv (f g)" 
  using assms invertible_commutes_with_inv by blast


lemma pos_pow_to_pow:
  assumes A0:"g \<in> G"
  shows " f (source.pow_int g (int n)) = target.pow_int (f g) (int n)"
proof(induct n)
  case 0
  then show ?case
    by (simp add: id_to_id) 
next
  case (Suc n)
  then show ?case
    by (metis assms commutes_with_composition source.int_pow_closed source.int_pow_int source.pow_Suc target.int_pow_int target.pow_Suc) 
qed

lemma pow_to_pow:
  assumes A0:"g \<in> G"
  shows " f (source.pow_int g  n) = target.pow_int (f g)  n"
proof(induct n)
  case (nonneg n)
  then show ?case
    using assms pos_pow_to_pow by blast 
next
  case (neg n)
  then show ?case
  proof-
    have "f (source.pow_int g (- int (Suc n))) = f (source.inv (source.pow_int g (int (Suc n))))"
      using assms source.int_pow_neg by presburger
    also have "... = target.inv (f (source.pow_int g (int (Suc n))))"
      using assms inv_to_inv by blast
    also have "... =   target.inv (target.pow_int (f g) (int (Suc n)))"
      using assms pos_pow_to_pow by presburger
    also have "... =  target.pow_int (f g) (- int (Suc n))"
      using assms set_morphism_closed target.int_pow_neg by presburger
    finally show ?thesis 
      by auto
  qed
qed


lemma kernel_conj_closed:
  assumes A0:"g \<in> G" and A1:"h \<in> Ker"
  shows "g \<cdot> h \<cdot> source.inv g \<in> Ker"
proof-
  obtain B0:"f h = e'"  
    by (simp add: A1 Ker_image) 
  have "f (g \<cdot> h \<cdot> source.inv g) = (f g) \<cdot>' (f h) \<cdot>' (f (source.inv g))"
    using A0 A1 Ker_closed commutes_with_composition source.inv_closed source.m_closed by presburger
  also have "... = (f g) \<cdot>' e' \<cdot>' (target.inv (f g))"
    using A0 B0 inv_to_inv by presburger
  also have "... = e'"
    using A0 set_morphism_closed target.r_inv_simp target.r_one by presburger
  finally show ?thesis
    using A0 A1 Ker_closed Ker_memI by blast
qed

lemma ker_sub:"subgroup (Ker) G (\<cdot>) e"  using kernel.subgroup_axioms by blast
lemma ker_norm:"normal_subgroup Ker G (\<cdot>) e" by (simp add: kernel.proj_unit_is_normal)

end

context group
begin
definition rcoset where "rcoset H a \<equiv> (\<Union>h\<in>H. {h \<cdot> a})"
definition lcoset where "lcoset a H \<equiv> (\<Union>h\<in>H. {a \<cdot> h})"
definition rcosets where "rcosets H \<equiv> (\<Union>g \<in> G. {rcoset H g})"
definition lcosets where "lcosets H \<equiv> (\<Union>g \<in> G. {lcoset g H})"
definition setprod where "setprod H K \<equiv> (\<Union>h\<in>H. \<Union>k\<in>K. {h\<cdot>k})"
definition setinv where "setinv H \<equiv> (\<Union>h\<in>H. {inv h})"

lemma lcset:"lcoset a H = setprod {a} H" unfolding lcoset_def setprod_def by simp
lemma rcset:"rcoset H a = setprod H {a}" unfolding rcoset_def setprod_def by simp

end

context subgroup
begin

lemma rcne:
  assumes A0:"t \<in> rcosets H" 
  shows "t \<noteq> {}"
proof-
  obtain g where "g \<in> G" and "t = rcoset H g" and "e \<in> H"
    using A0 unfolding rcosets_def by blast
  then have "e \<cdot> g \<in> t"
    unfolding rcoset_def by blast
  then show ?thesis
    by auto
qed


lemma lcne:
  assumes A0:"t \<in> lcosets H" 
  shows "t \<noteq> {}"
proof-
  obtain g where "g \<in> G" and "t = lcoset g H" and "e \<in> H"
    using A0 unfolding lcosets_def by blast
  then have "g \<cdot> e \<in> t"
    unfolding lcoset_def by blast
  then show ?thesis
    by auto
qed

     



end

end

 


