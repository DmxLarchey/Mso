
theory jgls imports jglns begin 

consts
  jgl13sf :: "['a relation, 'a relation, 'a relation, 'a relation, 'a] => bool"
  jgl4sf :: "['a relation,'a relation,'a relation,'a relation,'a relation] =>
    'a => bool"

defs
  jgl13sf_def : "jgl13sf sig isub trio rho == %s. ALL t. (t, s) : sig --> 
    t : wfp rho |
    (ALL u. (u, t) : isub Un trio --> 
      u : wfp rho | (u, s) : (isub O sig) O rho^*)"

  jgl4sf_def : "jgl4sf sig isub trio cuto rho == %s. 
    (ALL v. (v, s) : isub O sig --> v : wfp rho) -->
    (ALL t. (t, s) : sig --> t : bars cuto (gindy (isub Un trio) (wfp rho)))"
  
end

