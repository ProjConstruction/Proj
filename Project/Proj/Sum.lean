import Project.Proj.Opens

/-
--A_(∑ a_k) (Potion ring)

  def sum_potion:  (a_1, … , a_n ∈ Graded Ring ) relevant of same degree i : A_0-algebra :=

        (∑ _{k=1}^n a_k).PotionRing

   --a_k':= a_k / (a_1+...+a_n) (element in A_(∑ a_k) )

  def s_elem:  (a_1, … , a_n ) relevant of degree i ,  (k ∈ {1...n})  : elem ∈ sum_potion (a_1...a_n) :=

         a_k / (a_1+...+a_n)

  --(A_(∑ a_k))_{a_k'}= A_(a_k(∑ a_k)) (localization of potion ring isom potion of subtile product)

  lemma sum_lemm :  (a_1, … , a_n ) relevant of degree i (k ∈ {1...n}):

    (Localization sum_potion (a_1...a_n) s_elem k )

           ≅_[A_0] (a_k (∑ _{k=1}^n a_k)).PotionPotionRing  := by

           Exact Magic of potion

           sorry

  -- Spec( (A_(∑ a_k))_{a_k'}) → open immersion → Spec(A_(a_k))

  lemma sum_lemm_open  (a_1, … , a_n ) relevant of degree i (k ∈ 1...n): ∃ open immersion

    Spec( (Localization sum_potion (a_1...a_n) sum_elem k ) ) →

           ( (a_k)).PotionSch over Spec(A_0) := by

           apply sum_lemm and Potion( bc ) ⊆ Potion (c)

           sorry

   --Spec(A_(∑ a_k)) ---> open immersion ---> Union Spec(A_(a_k)) (Potion schemes)

  lemma sum_open : (a_1, … , a_n ) relevant of degree i :

           ∃(∑ _{k=1}^n a_k).PotionSch → ∪ _k (a_k).PotionSch open immersion over Spec(A_0) :=  by

            Have Eq= s_elem  1 +...+s_elem  k +... +s_elem  n =1  in sum_potion (a_1, … , a_n )

            Put D(a_k'):= Spec ((Localization sum_potion (a_1...a_n) s_elem k ) )

                                           (a basic open of Spec(sum_potion))

            Apply PrimeSpectrum.iSup_basicOpen_eq_top_iff to get

                   Union k=1...n D(a_k') = Spec(sum_potion)

            Have open immersion D(a_k') → ( (a_k)).PotionSch over Spec(A_0)

              --by sum_lemm_open

            Have open immersion  Union k=1...n D(a_k') → Union_k=1..n  ( ( a_k)).PotionSch over Spec(A_0)

               -- by union/gluing

            Have open immersion  Spec(sum_potion)  → Union ( ( a_k)).PotionSch over Spec(A_0)

                 -- by Apply PrimeSpectrum.iSup_basicOpen_eq_top_iff to get

                   --BigUnion k=1...n D(a_k') = Spec(sum_potion)

            sorry

-/
