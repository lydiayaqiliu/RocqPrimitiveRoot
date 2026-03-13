1. Motivation and Overview
This project was inspired by a YouTube video (https://www.youtube.com/watch?v=8NWwwvM5Kpo) which claims that the "ugliest" or most patternless music can be constructed using the Costas array, leveraging the fact that 3 is a primitive root modulo 89. With 88 piano keys and 88 positions, the construction maps interval i to key 3^i mod 89, producing a sequence in which no two note pairs share the same interval-and-pitch-difference combination.
The project formally verifies the following claims in the Coq proof assistant:
•	3 is a primitive root mod 89.
•	The mapping i -> g^i mod p yields a Costas array when g is a primitive root mod p.
•	The musical score produced by (i, 3^i mod 89) for i = 1 to 88 is patternless in the formal Costas sense: no two distinct pairs of positions share the same difference vector.

2. Key Definitions
2.1 Primality and Coprimality
A computational reflection approach is used to verify primality. The function for_all f n checks whether a boolean predicate f holds for all integers in [1, n), enabling decidable prime checking via the function is_prime:
Definition is_prime (p:Z) :=   (1 <? p) && for_all (fun k => Z.gcd k p =? 1) p.
Soundness is established by the theorem is_prime_correct, which converts a boolean true result into Coq's mathematical prime predicate from Znumtheory. The example p89 then applies this to prove prime 89 by reflexivity.
2.2 Primitive Root
A primitive root g modulo a prime p is defined as follows: g is coprime to p, and for every a in [1, p), there exists some exponent i in (0, p-1] such that g^i mod p = a. This matches the standard mathematical definition of a generator of the multiplicative group (Z/pZ)*.
Definition primitive_root (g p : Z) : Prop :=   prime p /\   coprime g p /\   forall a : Z, 1 <= a < p -> coprime a p ->   exists i : Z, 0 < i <= p-1 /\ ((g ^ i) mod p) = a.
2.3 Costas Array
A function f : Z -> Z on [1, n] forms a Costas array if all difference vectors are distinct. Formally:
Definition costas (f : Z -> Z) (n : Z) : Prop :=   forall i j k l,   0 < i /\ i < j /\ j <= n ->   0 < k /\ k < l /\ l <= n ->   j - i = l - k ->   f j - f i = f l - f k ->   i = k /\ j = l.
That is, if two pairs of positions have the same positional gap (j - i = l - k) and the same function-value gap (f(j) - f(i) = f(l) - f(k)), the pairs must be identical. This captures the musical "patternlessness" property.

3. Project Structure
The project is organized across three Coq source files:
3.1 CostasConstruction.v
The main file. Contains:
•	Primality checking infrastructure (for_all, is_prime, is_prime_correct).
•	Primitive root definition and computational verification via check_primitive_root.
•	The key theorem primitive_root_gives_costas, proving that any primitive root mod p induces a Costas array.
•	The final example patternless_music : costas (fun i => 3^i mod 89) 88, which is the main result.
3.2 PrimitiveRootInjective.v
Proves the injectivity of the primitive root map g^i mod p using a group-order argument. The key steps are:
•	If g^m = g^k mod p, factor out to get g^(m-k) = 1 mod p.
•	Using the order of g being exactly p-1 (order_eq_pminus1), deduce (p-1) | (m-k).
•	Since 0 <= m-k < p-1, the only valid multiple of p-1 in range is 0, so m = k.
The theorem order_eq_pminus1 and its connection to primitive_root (via primitive_root_order_eq) are admitted, as their proof would require substantial group-theoretic infrastructure (orbit-stabilizer, Lagrange's theorem, etc.).
3.3 InjectiveAlt.v (Incomplete)
An alternative approach to proving injectivity via finite maps and pigeonhole. The pigeonhole lemma pigeonhole_nat is fully proved by induction, but the connection to the primitive root surjectivity argument is not completed. This file is included as a saved work-in-progress and is not part of the final proof chain.

4. Core Proofs
4.1 Verifying 3 is a Primitive Root mod 89
The proof is completed entirely by computation. check_primitive_root runs find_exp for every candidate value a in [1, 89), returning true if an exponent can be found for each. Soundness of this check (check_primitive_root_correct) is formally proved, and the example three_is_a_primitive_root_mod_89 reduces to reflexivity.
4.2 Primitive Root Gives Costas
The main theorem primitive_root_gives_costas is proved as follows. Suppose j - i = l - k and g^j - g^i = g^l - g^k (mod p). Factor both sides:
g^i * (g^(j-i) - 1) = g^k * (g^(j-i) - 1)  (mod p)
Since g^(j-i) is not 1 mod p (because 0 < j-i < p-1 and primitive_root_pow_ne_one applies), the factor (g^(j-i) - 1) is nonzero mod p. The lemma mod_cancel then cancels this factor, yielding g^i = g^k mod p. By injectivity (primitive_root_injective), i = k, and then j = l follows from j - i = l - k.
4.3 Order Divides
The lemma order_divides is a key component of the injectivity proof in PrimitiveRootInjective.v. It establishes that if g^r = 1 mod p and g has order p-1, then (p-1) divides r:
Lemma order_divides :   forall g p r : Z,   primitive_root g p ->   order_eq_pminus1 g p ->   r > 0 ->   g ^ r mod p = 1 ->   ((p - 1) | r)%Z.
The proof proceeds by Euclidean division: write r = (p-1)*q + s where 0 <= s < p-1. Then:
•	Expand g^r = g^((p-1)*q + s) = (g^(p-1))^q * g^s.
•	Since g^(p-1) = 1 mod p (from order_eq_pminus1), the term (g^(p-1))^q reduces to 1 mod p.
•	Therefore g^s = 1 mod p.
•	By the minimality condition in order_eq_pminus1 (no smaller positive exponent yields 1), and since 0 <= s < p-1, we must have s = 0.
•	With s = 0, r = (p-1)*q, so (p-1) | r.
Two supporting lemmas are used: Euclidean_division_mod (that the remainder s from Z.div_eucl satisfies s = s mod (p-1), i.e., is already reduced) and Euclidean_division_pos (that the quotient q is non-negative). Both are proved rigorously from Z.mod_pos_bound and Z.div_pos in the standard library.
4.4 Injectivity of the Primitive Root Map
The theorem primitive_root_injective establishes that if g^m = g^k mod p with 0 <= m, k < p-1, then m = k. This is the final piece needed to close the Costas proof, and it is fully proved in PrimitiveRootInjective.v via the auxiliary lemma primitive_root_injective_aux.
The auxiliary lemma handles the case k < m and derives a contradiction. The argument is:
•	Factor: g^m = g^(m-k) * g^k, so g^(m-k) * g^k = g^k mod p.
•	Cancel g^k (which is coprime to p via coprime_pow) using mod_cancel, giving g^(m-k) = 1 mod p.
•	Apply order_divides: since g^(m-k) = 1 mod p and r = m-k > 0, conclude (p-1) | (m-k).
•	But 0 < m-k < p-1, so the only multiple of p-1 in this range is impossible — contradiction.
The full theorem then dispatches by trichotomy on k vs m, applying the auxiliary lemma symmetrically for both k < m and k > m cases, with the k = m case trivially closing the goal.
It is worth noting a gap in the proof chain: order_divides depends on order_eq_pminus1, and the connection primitive_root_order_eq — that any primitive root has order exactly p-1 — is admitted. Its proof would require constructing the multiplicative group (Z/pZ)*, showing g generates it, and appealing to a cardinality or Lagrange argument. This infrastructure is non-trivial to build from scratch in Coq and is left as the main open gap in the formalization.

5. External Tools and Resources
The following external tools and resources were used or cited in this project:
5.1 Coq Standard Library
The project depends on several modules from the Coq standard library:
•	Coq.ZArith.ZArith and Coq.ZArith.Zdiv: Integer arithmetic and division.
•	Coq.ZArith.Znumtheory: Number-theoretic definitions including prime, rel_prime, Zgcd_is_gcd, Gauss, and related lemmas.
•	Lia: The linear integer arithmetic tactic used extensively throughout.
•	Recdef: For the Function keyword used in the recursive for_all definition with measure.
•	Bool: For andb_true_iff and boolean reasoning.
5.2 Online References
The following online resources informed the design of the project:
•	YouTube: https://www.youtube.com/watch?v=8NWwwvM5Kpo - The original inspiration for the project, claiming that primitive roots mod 89 can produce maximally patternless music.
•	Stack Overflow: https://stackoverflow.com/questions/49282773/how-to-prove-that-a-number-is-prime-using-znumtheory-in-coq - Inspired the computational reflection approach to primality checking using for_all and Z.gcd.
5.3 Admitted Results
One result was admitted (axiomatically assumed) rather than fully proved, as their complete verification would require substantial additional infrastructure:
•	primitive_root_order_eq (in PrimitiveRootInjective.v): That a primitive root g has multiplicative order exactly p-1 in (Z/pZ)*. The handwavy justification given is that g generates the full group by definition, whose cardinality is p-1.
5.4 Writeup Tools
This write up used LLM to check for grammer & increased readability.

6. Final Result
The top-level theorem of the project is:
Example patternless_music : costas (fun i => 3^i mod 89) 88. Proof.   apply primitive_root_gives_costas.   - apply p89.   - apply three_is_a_primitive_root_mod_89. Qed.
This states that the function mapping each position i to the piano key 3^i mod 89 is a Costas array on 88 positions, formally verifying the claim that the resulting musical score is patternless in the difference-vector sense. The proof reduces to two previously verified facts: that 89 is prime, and that 3 is a primitive root mod 89.

7. Summary
This project demonstrates that formal proof assistants can be used to verify non-trivial mathematical claims arising from recreational mathematics and music theory. The core mathematical insight - that primitive root maps yield Costas arrays - is captured cleanly in a three-line paper proof that expands naturally into a fully formal Coq development. The main gap is the group-order argument required for injectivity, which is verified in a separate file modulo the admitted order theorem.
