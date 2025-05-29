

(* abstract version general path ordering, see
  Nachum Dershowitz & Charles Hoot.  Natural Termination.
  Genet & Gnaedig, CAAP, LNCS 1214, 1997 *)

theory gpodef imports rewr begin

consts 
  gpoc :: "('a relation) => ('a relation)"

consts 
  gpo :: "'a relation => ('a relation => 'a relation) => 'a relation"
  gpo2 :: "'a relation => ('a relation => 'a relation) => 'a relation"

(* vtl generalises the immediate subterm relation *)
inductive "gpo vtl crel" "gpo2 vtl crel"
  intros (* note order *)
    cI : "(t, s) : crel gpot ==> gpot <= gpo vtl crel ==>
      ALL t'. (t', t) : vtl --> (t', s) : gpo vtl crel ==> 
      (t, s) : gpo2 vtl crel"
    gpo2I : "(t, s) : gpo2 vtl crel ==> (t, s) : gpo vtl crel"
    subtI : "(si, s) : vtl ==> (si, s) : gpo vtl crel"
    esubtI : "(si, s) : vtl ==> (t, si) : gpo vtl crel ==> 
      (t, s) : gpo vtl crel"
  monos ctns_mono

(* key property of gpoc *)
consts
  gpoc_props :: "('a * 'a) set => (('a * 'a) set => ('a * 'a) set) => bool"
  wf_gpoc_fwf :: "('a * 'a) set => (('a * 'a) set => ('a * 'a) set) => bool"

defs
  wf_gpoc_fwf_def : "wf_gpoc_fwf vtl crel == 
    ALL r dt dt'.  (ALL x. (x, dt) : vtl --> x : wfp r) --> 
      (dt', dt) : crel r --> (dt', dt) : crel (fwf r)"

  gpoc_props_def : "gpoc_props vtl crel == 
    mono crel & wf_der crel & wf_gpoc_fwf vtl crel" 

end 



