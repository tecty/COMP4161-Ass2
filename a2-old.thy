theory a2
imports Main
begin

section "Part 1"

datatype condition =
  Above nat nat | Joinable nat nat

inductive_set connection :: "condition set \<Rightarrow> condition set"
  for A :: "condition set" where
  con_refl:
    "Above a a \<in> connection A"
| con_in:
    "\<phi> \<in> A \<Longrightarrow> \<phi> \<in> connection A"
| con_mirror:
    "Joinable a b \<in> connection A
     \<Longrightarrow> Joinable b a \<in> connection A"
| con_trans:
    "\<lbrakk>Above a b \<in> connection A;
      Above b c \<in> connection A\<rbrakk>
     \<Longrightarrow> Above a c \<in> connection A"
| con_join:
    "\<lbrakk>Above a b \<in> connection A;
      Above c b \<in> connection A\<rbrakk>
     \<Longrightarrow> Joinable a c \<in> connection A"
| con_ext_join:
    "\<lbrakk>Above a b \<in> connection A;
      Joinable b c \<in> connection A\<rbrakk>
     \<Longrightarrow> Joinable a c \<in> connection A"

print_theorems

primrec is_refl :: "_" where
  "is_refl(Above a b) = (a = b)"
| "is_refl(Joinable a b) = (a = b)"

section "Question 1 (a)"


(*4 is router1 5 is router2*)
definition example_network where
"example_network = {
Above 1 4 , Above 2 4, Above 2 5 , Above 3 5
}"  (* TODO *)

lemma "Joinable 1 2 \<in> connection example_network"
  apply (unfold example_network_def)
  apply (rule_tac b=4 in con_join)
   apply (rule con_in)
   apply (blast)
  apply (simp add:con_in)
  done 

subsection "Questions 1 (b)-(j)"

(* 1-b *)
lemma connection_monotonic:
  assumes "\<phi> \<in> connection A"
  shows   "\<phi> \<in> connection(A \<union> B)"
  using assms
  apply (induct rule:connection.induct)
       apply (auto intro:connection.intros)
  done

lemma connection_mono : 
  "connection (connection A) \<subseteq> connection A"
  apply (safe)
  apply (erule connection.induct)
  apply (simp_all add: connection.intros)
  done

(* 1-c *)
lemma connection_idem:
  shows "connection(connection A) = connection A"
  apply (rule equalityI)
  apply (simp add:  connection_mono)
  apply (auto intro:connection.intros)
  done

(* 1-d *)
lemma connection_decompose:
  assumes "\<phi> \<in> connection(A \<union> B)"
  shows   "\<exists>C D. C \<subseteq> connection A \<and>
                 D \<subseteq> connection B \<and>
                 \<phi> \<in> connection(C \<union> D)"
  using assms
  apply -
  apply (simp add: connection.induct)
  apply (auto intro:connection.intros)
  done

(* 1-e *)
lemma connection_nil:
  assumes "\<phi> \<in> connection {}"
  shows "is_refl \<phi>"
  (* TODO *)
  using assms
  apply (induct \<phi>)
   apply (simp_all)
  done

(* 1-f *)
lemma con_is_refl:
  assumes "is_refl \<phi>"
  shows "\<phi> \<in> connection A"
  (* TODO *)
  using assms 
  apply - 
  apply (induct)
   apply (simp_all add: connection.inducts)
  apply (auto intro:connection.intros)
  done 
  

(* 1-g *)
lemma refl_wont_loss: "is_refl x \<Longrightarrow> x \<in> connection A"
  apply induct 
  apply (auto intro: connection_nil con_is_refl)
  done

lemma connection_filter_refl:
  assumes "\<phi> \<in> connection A"
  shows "\<phi> \<in> connection(A - {\<phi>. is_refl \<phi>})"
  using assms 
  using refl_wont_loss
  apply induct
  apply (simp_all add:connection.intros)
  by (metis DiffI connection.con_in mem_Collect_eq)
  

(* 1-h *)
lemma not_refl_wont_derive_nil:
  "\<And>a b . a \<noteq> b \<Longrightarrow> Above a b \<notin> connection {} "
  apply safe
  using connection.inducts
  using connection_nil 
  using is_refl.simps(1) by blast


lemma not_refl_wont_derive_no_reason:
  "\<lbrakk>a \<noteq> b; Above a b \<notin> A; Above a c \<in> A \<and> Above c b \<in> A \<rbrakk> \<Longrightarrow> Above a b \<in> connection A"
  using connection.con_in connection.con_trans 
  by blast

lemma no_above_from_join_lemma_gen:
  "\<forall> x \<in> A. x = Above c c \<Longrightarrow> Above a b \<in> connection A \<Longrightarrow> a = b"
  using connection_idem connection_monotonic not_refl_wont_derive_nil refl_wont_loss 
  using le_iff_sup subsetI
  by (metis is_refl.simps(1))

lemma refl_derive_no_reson_2:
  "\<And>a b. Above a b \<notin> A \<Longrightarrow> Above a a \<in> connection A \<and> Above b b \<in> connection A"
  using connection.intros
  by blast

lemma 
  "\<And>a b c. \<lbrakk>a \<noteq> b; a \<noteq> c; Above a c \<notin> connection A ; Above c b \<notin> connection A\<rbrakk> \<Longrightarrow> Above a b \<notin> connection A"
  apply (case_tac "c = b")
   apply simp 
  oops 

lemma must_be_above_or_joinable:
  " x \<in> A \<Longrightarrow>\<exists> a b. x = Joinable a b \<or> x = Above a b"
  using condition.exhaust by blast

lemma no_joinable_from_join_lemma_gen:
  "\<forall> x \<in> A. x = Joinable c d \<Longrightarrow> Above a b \<in> connection A \<Longrightarrow> a = b"
  using connection.intros 
  using connection.inducts 
  sorry 



lemma have_not_have_able_only_joinable:
 " x \<in> A\<Longrightarrow> \<lbrakk>\<And>a b. Above a b \<notin> A\<rbrakk> \<Longrightarrow>  x = Joinable c d" 

  sorry


lemma no_above_from_join_lemma:
  assumes "Above a b \<in> connection A"
  and "\<And>a b. Above a b \<notin> A" 
  shows "a = b"
  using assms
  using no_joinable_from_join_lemma_gen
  using have_not_have_able_only_joinable
  by meson
 

(* 1-i *)
lemma "\<lbrakk> x \<in> C \<union> D ;C \<subseteq> A ; D \<subseteq> B \<rbrakk> \<Longrightarrow> x \<in> A \<union> B"
  by blast

lemma connections_idem_simp: "x \<in> connection (connection C) \<Longrightarrow> x \<in> connection C"
  using connection_idem
  by blast

lemma connection_subset_simp: "x \<in> connection A \<Longrightarrow> A \<subseteq> B \<Longrightarrow> x \<in> connection B"
  by (metis connection_monotonic le_iff_sup)

lemma connection_subset_con_simp: "x \<in> connection A \<Longrightarrow> A \<subseteq> connection B \<Longrightarrow> x \<in> connection B"
  using connections_idem_simp connection_subset_simp 
  by blast

lemma connection_union_subset: 
  "\<lbrakk>A\<subseteq>C; B\<subseteq>D \<rbrakk> \<Longrightarrow> connection(A\<union> B) \<subseteq> connection (C\<union> D)"
  by (meson Un_mono connection_subset_simp subset_eq)

lemma connection_union_simp:
  "connection(connection A \<union> connection B) = connection(A \<union> B)"
  apply safe
  using connection_union_subset connection_subset_con_simp 
  apply (metis (no_types, lifting) sup.bounded_iff sup.idem sup_ge2)
  using connection_decompose connection_union_subset by blast

lemma connection_compose:
  assumes "\<phi> \<in> connection(C \<union> D)"
  and     "C \<subseteq> connection A"
  and     "D \<subseteq> connection B"
  shows   "\<phi> \<in> connection(A \<union> B)"
  using assms
  using connection_union_subset connection_subset_con_simp connection_union_simp
  by (smt connection_idem)
  
(* 1-j *)
lemma connection_compositional:
  assumes "connection A = connection B"
  shows   "connection(A \<union> C) = connection(B \<union> C)"
  using assms 
  using connection_compose
  by (metis connection_union_simp)   
  

section "Part 2"

datatype process =
  Cond condition
  | Par process process
  | Input nat process
  | Output nat process
  | Nil

datatype action =
  LInput nat | LOutput nat | LTau

primrec frame :: "process \<Rightarrow> condition set" where
  "frame Nil = {}"
| "frame(Cond \<phi>) = {\<phi>}"
| "frame(Par P Q) = frame P \<union> frame Q"
| "frame(Input \<phi> P) = {}"
| "frame(Output \<phi> P) = {}"


inductive semantics :: "condition set \<Rightarrow> process \<Rightarrow> action \<Rightarrow> process \<Rightarrow> bool"
  where
  semantics_input:
     "semantics A (Input n P) (LInput n) P"
| semantics_output:
    "semantics A (Output n P) (LOutput n) P"
| semantics_par_l:
    "semantics (A \<union> frame Q) P \<alpha> P'
     \<Longrightarrow> semantics A (Par P Q) \<alpha> (Par P' Q)"
| semantics_par_r:
    "semantics (A \<union> frame P) Q \<alpha> Q'
     \<Longrightarrow> semantics A (Par P Q) \<alpha> (Par P Q')"
| semantics_com_l:
    "\<lbrakk>semantics (A \<union> frame Q) P (LOutput n) P';
      semantics (A \<union> frame P) Q (LInput m) Q';
      Joinable n m \<in> connection(A \<union> frame P \<union> frame Q)\<rbrakk>
     \<Longrightarrow> semantics A (Par P Q) LTau (Par P' Q')"
| semantics_com_r:
    "\<lbrakk>semantics (A \<union> frame Q) P (LInput n) P';
      semantics (A \<union> frame P) Q (LOutput m) Q';
      Joinable n m \<in> connection(A \<union> frame P \<union> frame Q)\<rbrakk>
     \<Longrightarrow> semantics A (Par P Q) LTau (Par P' Q')"

inductive_cases
  par: "semantics A (Par P Q) x R" and
  nil: "semantics A Nil x R" and
  cond: "semantics A (Cond cond) x R"

subsection "Questions 2 (a)-(c)"

(* 2-a *)
lemma semantics_monotonic:
  assumes "semantics A P \<alpha> Q"
  shows "semantics (A \<union> B) P \<alpha> Q"
  using assms 
  apply induct 
       apply (simp_all add:semantics.intros sup_assoc sup_commute  sup_left_commute)
   apply (smt Un_assoc connection_monotonic inf_sup_aci(5) semantics_com_l)
  apply (smt Un_commute connection_monotonic semantics_com_r sup_assoc)
  done 
 
(* 2-b *)
lemma semantics_empty_env:
  assumes "semantics A P \<alpha> Q"
  shows "\<exists>\<beta> Q'. semantics {} P \<beta> Q'"
  (* TODO *)
  
  apply (rule_tac exI)+
  using assms
  apply induct
  

  oops

(* 2-c *)
lemma semantics_swap_frame:
  assumes "semantics A P \<alpha> Q"
  and "connection A = connection B"
  shows "semantics B P \<alpha> Q"
  using assms 
  apply - 
  apply induct 
  oops

section "Part 3"

definition stuck :: "process \<Rightarrow> bool"
where
  "stuck P \<equiv> \<forall>\<alpha> P'. semantics {} P \<alpha> P' \<longrightarrow> False"

primrec list_trans :: "_" where
  "list_trans A P [] Q = (P = Q)"
| "list_trans A P (\<alpha>#tr) Q =
    (\<exists>R. semantics A P \<alpha> R \<and> list_trans A R tr Q)"

definition traces_of :: "process \<Rightarrow> action list set"
  where "traces_of P = {tr | tr. \<exists>Q. list_trans {} P tr Q \<and> stuck Q}"

definition trace_eq :: "process \<Rightarrow> process \<Rightarrow> bool"
  where "trace_eq P Q = (traces_of P = traces_of Q)"

subsection "Question 3 (a)"

lemma trace_eq_refl:
  shows "trace_eq P P"
  (* TODO *)
  oops

lemma trace_eq_sym:
  assumes "trace_eq P Q"
    shows "trace_eq Q P"
  (* TODO *)
  oops

lemma trace_eq_trans:
  assumes "trace_eq P Q"
      and "trace_eq Q R"
    shows "trace_eq P R"
  (* TODO *)
  oops

subsection "Question 3 (b)"

lemma trace_eq_stuck:
  assumes "stuck P"
      and "stuck Q"
    shows "trace_eq P Q"
  (* TODO *)
  oops

subsection "Question 3 (c)"

lemma traces_of_monotonic:
  assumes "stuck R"
  shows "traces_of P \<subseteq> traces_of (Par P R)"
  (* TODO *)
  oops

subsection "Question 3 (d)"

text \<open>Feel free to give this answer in free-text comments,
      or as Isabelle definitions. \<close>

subsection "Question 3 (e)"

lemma traces_of_not_antimonotonic:
  assumes "\<And>P R. stuck R \<Longrightarrow> traces_of (Par P R) \<subseteq> traces_of P"
  shows "False"
  (* TODO *)
  oops

subsection "Question 3 (f)"

lemma semantics_par_assoc1:
  assumes "semantics A (Par P (Par Q S)) \<alpha> R"
  shows "\<exists>P' Q' S'.
           R = Par P' (Par Q' S') \<and>
           semantics A (Par (Par P Q) S) \<alpha> (Par (Par P' Q') S')"
  (* TODO *)
  oops

text \<open>
  This similar lemma will be needed later.
  You may use it without proof. \<close>
lemma semantics_par_assoc2:
  "semantics A (Par (Par P Q) S) \<alpha> R \<Longrightarrow>
  \<exists> P' Q' S'. R = Par (Par P' Q') S' \<and> semantics A (Par P (Par Q S)) \<alpha> (Par P' (Par Q' S'))"
  sorry

subsection "Question 3 (g)"

lemma list_trans_par_assoc:
  "list_trans A (Par (Par P Q) S) tr (Par (Par P' Q') S') =
       list_trans A (Par P (Par Q S)) tr (Par P' (Par Q' S'))"
  (* TODO *)
  oops

subsection "Question 3 (h)"

lemma stuck_par:
  "stuck(Par P Q) = (stuck P \<and> stuck Q)"
  (* TODO *)
  oops

subsection "Question 3 (i)"

lemma trace_eq_par_assoc:
  shows "trace_eq (Par (Par P Q) S) (Par P (Par Q S))"
  (* TODO *)
  oops

subsection "Question 3 (j)"

lemma trace_eq_nil_par:
  shows "trace_eq P (Par P Nil)"
  (* TODO *)
  oops

subsection "Question 3 (k)"

lemma trace_eq_par_comm:
  shows "trace_eq (Par P Q) (Par Q P)"
  (* TODO *)
  oops

end