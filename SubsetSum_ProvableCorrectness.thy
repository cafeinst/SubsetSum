theory SubsetSum_ProvableCorrectness
  imports SubsetSum_CookLevin
begin

section \<open>Provable correctness \(\Longrightarrow\) LR-read\<close>

text \<open>
This theory formalizes a *proof-carrying* notion of solver correctness.
A machine counts as "provably correct" only if it comes with a derivation
establishing (i) semantic correctness for SUBSET-SUM and (ii) the LR-read
information-flow interface facts needed to import the abstract lower bound.

The main theorem then states: provably-correct solver \(\Longrightarrow\) LR_Read_TM.
\<close>

subsection \<open>A proof-carrying solver package\<close>

text \<open>
We package "provably correct" as a single predicate.
It takes the same parameters as the LR_Read_TM locale:
  - a Cook--Levin machine M with start state q0,
  - an encoding enc,
  - concrete observables steps_TM, seenL_TM, seenR_TM,
and requires that:
  1) M is a well-formed Cook--Levin TM with k_tapes tapes and start q0,
  2) M decides subset-sum correctly (halts+accepts iff mathematical predicate),
  3) the LR-read coverage property holds (for distinct-subset-sums instances),
  4) the LR-read cost lower bound holds (steps at least |seenL|+|seenR|).

This is the minimal "route 1" formalization: correctness-proof obligations
imply the LR-read interface.
\<close>

definition steps_TM_CL :: "machine => (int list => int => bool list) => int list => int => nat"
where
  "steps_TM_CL M enc as s = steps_CL M (enc as s)"

definition read0_TM_CL :: "machine => (int list => int => bool list) => int list => int => nat set"
where
  "read0_TM_CL M enc as s = read0_CL M (enc as s)"

definition seenL_from_reads ::
  "(int list => int => nat => nat => int) =>
   machine => (int list => int => bool list) =>
   int list => int => nat => int set"
where
  "seenL_from_reads candL_of_pos M enc as s k =
     candL_of_pos as s k ` (read0_TM_CL M enc as s)"

definition seenR_from_reads ::
  "(int list => int => nat => nat => int) =>
   machine => (int list => int => bool list) =>
   int list => int => nat => int set"
where
  "seenR_from_reads candR_of_pos M enc as s k =
     candR_of_pos as s k ` (read0_TM_CL M enc as s)"

definition readL_from_reads ::
  "(nat => bool) =>
   machine => (int list => int => bool list) =>
   int list => int => nat set"
where
  "readL_from_reads isL M enc as s =
     {i \<in> read0_TM_CL M enc as s. isL i}"

definition readR_from_reads ::
  "(nat => bool) =>
   machine => (int list => int => bool list) =>
   int list => int => nat set"
where
  "readR_from_reads isL M enc as s =
     {i \<in> read0_TM_CL M enc as s. \<not> isL i}"

definition seenL_from_reads' ::
  "(int list => int => nat => nat => int) =>
   (nat => bool) =>
   machine => (int list => int => bool list) =>
   int list => int => nat => int set"
where
  "seenL_from_reads' candL_of_pos isL M enc as s k =
     candL_of_pos as s k ` (readL_from_reads isL M enc as s)"

definition seenR_from_reads' ::
  "(int list => int => nat => nat => int) =>
   (nat => bool) =>
   machine => (int list => int => bool list) =>
   int list => int => nat => int set"
where
  "seenR_from_reads' candR_of_pos isL M enc as s k =
     candR_of_pos as s k ` (readR_from_reads isL M enc as s)"

lemma finite_read0_CL[simp]: "finite (read0_CL M x)"
  using read0_CL_subset_indices
  by (rule finite_subset) simp

lemma finite_read0_TM_CL[simp]: "finite (read0_TM_CL M enc as s)"
  unfolding read0_TM_CL_def by simp

lemma card_readL_plus_readR_le_read0:
  "card (readL_from_reads isL M enc as s) + card (readR_from_reads isL M enc as s)
   \<le> card (read0_TM_CL M enc as s)"
proof -
  have disj:
    "readL_from_reads isL M enc as s \<inter> readR_from_reads isL M enc as s = {}"
    unfolding readL_from_reads_def readR_from_reads_def by auto
  have union:
    "readL_from_reads isL M enc as s \<union> readR_from_reads isL M enc as s
     = read0_TM_CL M enc as s"
    unfolding readL_from_reads_def readR_from_reads_def by auto
  have fin0: "finite (read0_TM_CL M enc as s)" by simp
  have finL: "finite (readL_from_reads isL M enc as s)"
    unfolding readL_from_reads_def using fin0 by auto
  have finR: "finite (readR_from_reads isL M enc as s)"
    unfolding readR_from_reads_def using fin0 by auto

  have "card (readL_from_reads isL M enc as s) + card (readR_from_reads isL M enc as s)
        = card (readL_from_reads isL M enc as s \<union> readR_from_reads isL M enc as s)"
    using finL finR disj by (simp add: card_Un_disjoint)
  also have "... = card (read0_TM_CL M enc as s)"
    by (simp add: union)
  finally show ?thesis by simp
qed

lemma card_image_le_card:
  assumes "finite S"
  shows "card (f ` S) \<le> card S"
  using assms by (simp add: card_image_le)

lemma seen_from_reads_cost:
  assumes fin: "finite (read0_TM_CL M enc as s)"
  shows
    "card (seenL_from_reads candL_of_pos M enc as s k)
     \<le> card (read0_TM_CL M enc as s)"
    "card (seenR_from_reads candR_of_pos M enc as s k)
     \<le> card (read0_TM_CL M enc as s)"
  unfolding seenL_from_reads_def seenR_from_reads_def
  using card_image_le_card[OF fin] by auto

definition pos0_at ::
  "machine => bool list => nat => nat" where
  "pos0_at M x t = nat (head0_CL (conf_CL M x t))"

lemma read0_CL_subset_positions_over_time:
  "read0_CL M x
   \<subseteq> pos0_at M x ` {t. t < steps_CL M x}"
proof
  fix h assume "h \<in> read0_CL M x"
  then obtain t hh where
    hh: "h = nat hh" and
    cfg: "hh = head0_CL (conf_CL M x t)" and
    lt: "t < steps_CL M x"
    unfolding read0_CL_def head0_CL_def
    by (auto simp: Let_def)
  have "h = pos0_at M x t"
    unfolding pos0_at_def using hh cfg by simp
  moreover have "t \<in> {t. t < steps_CL M x}"
    using lt by simp
  ultimately show "h \<in> pos0_at M x ` {t. t < steps_CL M x}"
    by blast
qed

lemma finite_time_set:
  "finite {t::nat. t < T}"
  by (simp add: finite_less_ub)

lemma card_read0_le_steps:
  "card (read0_CL M x) \<le> steps_CL M x"
proof -
  have sub:
    "read0_CL M x \<subseteq> pos0_at M x ` {..< steps_CL M x}"
  proof
    fix h assume "h \<in> read0_CL M x"
    then obtain t hh where
      hh: "h = nat hh" and
      cfg: "hh = head0_CL (conf_CL M x t)" and
      lt: "t < steps_CL M x"
      unfolding read0_CL_def head0_CL_def
      by (auto simp: Let_def)
    have "h = pos0_at M x t"
      unfolding pos0_at_def using hh cfg by simp
    moreover have "t \<in> {..< steps_CL M x}"
      using lt by simp
    ultimately show "h \<in> pos0_at M x ` {..< steps_CL M x}"
      by blast
  qed

  have fin_img: "finite (pos0_at M x ` {..< steps_CL M x})"
    by simp

  have mono:
    "card (read0_CL M x) \<le> card (pos0_at M x ` {..< steps_CL M x})"
    by (rule card_mono[OF fin_img sub])

  have img_le:
    "card (pos0_at M x ` {..< steps_CL M x})
     \<le> card ({..< steps_CL M x} :: nat set)"
    by (rule card_image_le) simp

  show ?thesis
    using mono img_le
    by simp
qed

theorem derived_LR_cost:
  "card (seenL_from_reads' candL_of_pos isL M enc as s k)
   + card (seenR_from_reads' candR_of_pos isL M enc as s k)
   \<le> steps_TM_CL M enc as s"
proof -
  have finL: "finite (readL_from_reads isL M enc as s)"
    unfolding readL_from_reads_def by simp
  have finR: "finite (readR_from_reads isL M enc as s)"
    unfolding readR_from_reads_def by simp

  have imgL:
    "card (seenL_from_reads' candL_of_pos isL M enc as s k)
     \<le> card (readL_from_reads isL M enc as s)"
    unfolding seenL_from_reads'_def
    using card_image_le[OF finL] .

  have imgR:
    "card (seenR_from_reads' candR_of_pos isL M enc as s k)
     \<le> card (readR_from_reads isL M enc as s)"
    unfolding seenR_from_reads'_def
    using card_image_le[OF finR] .

  have lr_le0:
    "card (readL_from_reads isL M enc as s) + card (readR_from_reads isL M enc as s)
     \<le> card (read0_TM_CL M enc as s)"
    by (rule card_readL_plus_readR_le_read0)

  have step0:
    "card (read0_TM_CL M enc as s) \<le> steps_TM_CL M enc as s"
    unfolding read0_TM_CL_def steps_TM_CL_def
    using card_read0_le_steps by simp

  have "card (seenL_from_reads' candL_of_pos isL M enc as s k)
        + card (seenR_from_reads' candR_of_pos isL M enc as s k)
        \<le> card (readL_from_reads isL M enc as s)
          + card (readR_from_reads isL M enc as s)"
    using imgL imgR by linarith
  also have "... \<le> card (read0_TM_CL M enc as s)"
    using lr_le0 by linarith
  also have "... \<le> steps_TM_CL M enc as s"
    using step0 by linarith
  finally show ?thesis .
qed

definition provably_correct_SS_solver_basic ::
  "machine \<Rightarrow> nat \<Rightarrow> (int list \<Rightarrow> int \<Rightarrow> bool list) \<Rightarrow> bool"
where
  "provably_correct_SS_solver_basic M q0 enc \<longleftrightarrow>
     turing_machine k_tapes q0 M
   \<and> (\<forall>as s. accepts_CL_halt M (enc as s) \<longleftrightarrow> subset_sum_true as s)"

theorem basic_correctness_imp_derived_LR_cost:
  assumes PC: "provably_correct_SS_solver_basic M q0 enc"
  shows
    "card (seenL_from_reads' candL_of_pos isL M enc as s k)
     + card (seenR_from_reads' candR_of_pos isL M enc as s k)
     \<le> steps_TM_CL M enc as s"
  using derived_LR_cost .

lemma provably_correct_basic_imp_CL_SubsetSum_Solver:
  assumes PC: "provably_correct_SS_solver_basic M q0 enc"
  shows "CL_SubsetSum_Solver M q0 enc"
proof -
  have TM: "turing_machine k_tapes q0 M"
    using PC unfolding provably_correct_SS_solver_basic_def by blast
  have SOLVES: "\<And>as s. accepts_CL_halt M (enc as s) \<longleftrightarrow> subset_sum_true as s"
    using PC unfolding provably_correct_SS_solver_basic_def by blast
  show ?thesis
    by (unfold_locales) (use TM SOLVES in auto)
qed

definition provably_correct_SS_solver_strong ::
  "machine \<Rightarrow> nat \<Rightarrow> (int list \<Rightarrow> int \<Rightarrow> bool list)
   \<Rightarrow> (int list \<Rightarrow> int \<Rightarrow> nat)
   \<Rightarrow> (int list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> int set)
   \<Rightarrow> (int list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> int set)
   \<Rightarrow> bool"
where
  "provably_correct_SS_solver_strong M q0 enc steps_TM seenL_TM seenR_TM \<longleftrightarrow>
     provably_correct_SS_solver_basic M q0 enc
   \<and> (\<forall>as s. steps_TM as s = steps_CL M (enc as s))
   \<and> (\<forall>as s. distinct_subset_sums as \<longrightarrow>
          (\<exists>k\<le>length as.
             seenL_TM as s k = LHS (e_k as s k) (length as)
           \<and> seenR_TM as s k = RHS (e_k as s k) (length as)))
   \<and> (\<forall>as s k. k \<le> length as \<longrightarrow>
          steps_TM as s \<ge> card (seenL_TM as s k) + card (seenR_TM as s k))"

subsection \<open>Main theorem: provable correctness implies LR-read\<close>

theorem provably_correct_imp_LR_Read_TM_Derived:
  fixes M :: machine and q0 :: nat
    and enc :: "int list \<Rightarrow> int \<Rightarrow> bool list"
    and isL :: "nat \<Rightarrow> bool"
    and candL_of_pos :: "int list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int"
    and candR_of_pos :: "int list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int"
  assumes PC: "provably_correct_SS_solver_basic M q0 enc"
  assumes COV:
    "\<And>as s. distinct_subset_sums as \<Longrightarrow>
       \<exists>k\<le>length as.
         (candL_of_pos as s k ` {i \<in> read0_CL M (enc as s). isL i})
           = LHS (e_k as s k) (length as) \<and>
         (candR_of_pos as s k ` {i \<in> read0_CL M (enc as s). \<not> isL i})
           = RHS (e_k as s k) (length as)"
  shows "LR_Read_TM_Derived M q0 enc isL candL_of_pos candR_of_pos"
proof -
  have TM: "turing_machine k_tapes q0 M"
    using PC unfolding provably_correct_SS_solver_basic_def by blast

  have SOLVES: "\<And>as s. accepts_CL_halt M (enc as s) \<longleftrightarrow> subset_sum_true as s"
    using PC unfolding provably_correct_SS_solver_basic_def by blast

  show ?thesis
  proof (unfold_locales)
    show "turing_machine k_tapes q0 M" by (rule TM)
    show "\<And>as s. accepts_CL_halt M (enc as s) \<longleftrightarrow> subset_sum_true as s"
      by (rule SOLVES)
    show "\<And>as s. distinct_subset_sums as \<Longrightarrow>
       \<exists>k\<le>length as.
         (candL_of_pos as s k ` {i \<in> read0_CL M (enc as s). isL i})
           = LHS (e_k as s k) (length as) \<and>
         (candR_of_pos as s k ` {i \<in> read0_CL M (enc as s). \<not> isL i})
           = RHS (e_k as s k) (length as)"
      by (rule COV)
  qed
qed

subsection \<open>How you use this\<close>

text \<open>
If you can prove `provably_correct_SS_solver M q0 enc steps_TM seenL_TM seenR_TM`
for your chosen M/enc/observables, then Isabelle immediately gives you
`LR_Read_TM M q0 enc steps_TM seenL_TM seenR_TM` via the theorem above,
and you can inherit the \(\sqrt{2^n}\) lower bound using the machinery
already in SubsetSum_CookLevin.
\<close>

end
