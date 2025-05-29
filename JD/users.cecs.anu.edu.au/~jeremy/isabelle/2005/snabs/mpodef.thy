
theory mpodef imports cpodef mso begin

consts (* single step and transitive versions *)
  mpo :: "('a * 'a) set => 'a rule set"
  mpo_ruleredn :: "'a :: symbwf rule set"
  mpo_cutorder :: "'a :: symbwf rule set"

(* note that mult r is transitive even if r is not,
  but that mult1 is not transitive even if r is;
  Dershowitz's bag-ordering is in between, it is transitive iff r is *)

inductive "mpo r"
  intros (* note order *)
    msoI : "(mset_of ts, mset_of ss) : smso (mpo r) ==>
      (Node f ts, Node f ss) : mpo r"
    fgI : "(g, f) : r ==> 
        ALL t: set ts. (t, Node f ss) : mpo r ==> 
	(Node g ts, Node f ss) : mpo r"
    subtI : "si : set ss ==> (si, Node f ss) : mpo r"
    esubtI : "si : set ss ==> (t, si) : mpo r ==> (t, Node f ss) : mpo r"
  monos smso_mono

consts
  mpocl :: "('a * 'a) set => 'a rule set"

inductive "mpocl r"
  intros
    I : "(ts, ss) : smsol (fwf (ctxt (mpo r))) ==>
      (Node f ts, Node f ss) : mpocl r"

defs
  mpordef : "mpo_ruleredn == mpo symborder"
  mpocdef : "mpo_cutorder == cpocfg symborder Un mpocl symborder"

end 


