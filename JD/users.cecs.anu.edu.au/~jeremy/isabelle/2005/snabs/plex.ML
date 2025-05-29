
structure plex = struct val thy = theory "plex" end ;
use_legacy_bindings plex.thy ;

(* now to show the link between this and the lexicographic ordering *)

val _ = qed_goal_spec_mp "lex_tree" plex.thy 
  "(l1 :: symb list, l2) : lex symborder --> \
    \ (hd (trees l1), hd (trees l2)) : ctxt plex_ruleredn"
  (fn _ => [ (rtac impI 1), (etac lex.induct 1), 
    (rtac ron.red_nuI 1), (etac lex.elim 1), Auto_tac, 
    (rewtac plexrdef), (rtac ron.red_cutI 1),
    (etac plc2.I 1), (simp_tac (esimps [depths_trees]) 1)]) ;

val _ = qed_goal "wf_lex_symb" plex.thy 
  "wf (lex (symborder :: (symb * symb) set))"
  (fn _ => [ (rtac wf_subset 1), (rtac wf_inv_image 1), (rtac plexwf 1), 
    (clarsimp_tac (cesimps [inv_image_def]) 1), (etac lex_tree 1) ]) ;

