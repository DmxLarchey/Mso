
(* multisets as provided in Isabelle, with original ordering *)
theory mso imports Wfss Multiset begin

consts
  mset_of :: "'a list => 'a multiset"
  msol :: "('a * 'a) set => ('a list * 'a list) set"
  smsol :: "('a * 'a) set => ('a list * 'a list) set"
  (* strict multiset order, using Baader & Nipkow, Lemma 2.5.6 *)
  smso :: "('a * 'a) set => ('a multiset * 'a multiset) set"

primrec
  Nil : "mset_of [] = {#}"
  Cons : "mset_of (x # xs) = mset_of xs + {#x#}"

inductive "smso r"
  intros 
    singleI : "ALL n. n :# N --> (n, m) : r ==> (N, {#m#}) : smso r"
    plusI : "(N, M) : smso r ==> (N + X, M + X) : smso r"
    addI : "(N, M) : smso r ==> (X, Y) : smso r ==> (N + X, M + Y) : smso r"
  (*
    I : "M ~= N ==> ALL n. n :# N - M --> (EX m. m :# M - N & (n, m) : r) ==>
      (N, M) : smso r"
      *)

defs
  (* shouldn't need ^+ in following, but would need to prove
    "ALL x. (x, y) : mult1 (r^+) --> (x, y) : (mult1 r)^+"
    *)
  msol_def : "msol r == inv_image (mult (r^+)) mset_of"
  smsol_def : "smsol r == inv_image (smso r) mset_of"

end

