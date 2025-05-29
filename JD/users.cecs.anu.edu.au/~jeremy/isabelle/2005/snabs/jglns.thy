
(* theory for the results in 
  Jean Goubault-Larrecq.  Well-founded recursive relations. (CSL'2001),
  section 5, but without substitution,
  conditions on page 492 are
  Property 2 "ALL dt. red_props_jglhf isub btri rho cuto dt"
    (thus, a fortiori, "red_props_jglh isub btri rho cuto")
  (iv)o "gjgl isub 
  (xv) "jgl15 btri (isub Un trio) (wfp (rho Un trio))"
  *)

theory jglns imports rewr begin 

consts
  jgl14 ::
    "'a relation => 'a relation => 'a relation => 'a relation => bool"
  jgl14f :: 
    "'a relation => 'a relation => 'a relation => 'a relation => 'a => bool"
  jgl15 :: "'a relation => 'a relation => 'a set => bool"
  jgl15f :: "'a relation => 'a relation => 'a set => 'a => bool"
  jgl13f :: "'a relation => 'a relation => 'a relation => 'a => bool"

defs

  jgl15f_def : "jgl15f btri sub sn == %dt.
    (ALL v. (v, dt) : sub --> v : sn) --> 
    (ALL u. (u, dt) : btri --> u : sn)"

(* not used  
  jgl15_def : "jgl15 btri sub sn == ALL dt. jgl15f btri sub sn dt"
  *)

  jgl14f_def : "jgl14f cuto trio isub rho == %s.
    ALL t u.  (t, s) : cuto --> (u, t) : trio -->
      (u, t) : isub | (t, s) : (isub Un trio) O rho^*"

(* jgl paper has, in (xiii), (u, s) : isub Un trio *)
  jgl13f_def : "jgl13f isub trio rho == %s. s : wfp rho |
    (ALL u. (u, s) : trio --> u : wfp rho | (u, s) : isub O rho^*)"

end
