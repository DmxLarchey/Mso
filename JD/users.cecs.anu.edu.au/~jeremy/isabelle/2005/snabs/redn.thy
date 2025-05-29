
theory redn imports clcon 

begin 

consts
  (* properties used in incremental proofs *)
  cut1_propa :: "'a rtree relation => 'a rtree relation => bool"
  cut1_prop :: "'a rtree relation => bool"
  cut1_gip_propa :: "'a rtree relation => 'a rtree relation => bool"
  cut1_gip_prop :: "'a rtree relation => bool"
  cut1_dvk_prop :: "'a rtree relation => bool"

defs
  (* properties used in incremental proofs *)
  cut1_propa_def : 
    "cut1_propa c1 any == c1 O nured any <= (nured any)^* O c1"
  cut1_prop_def' : "cut1_prop c1 == ALL any. (cut1_propa c1 any)"
  cut1_gip_propa_def : 
    "cut1_gip_propa c1 any == gip_cond c1 (nured any)"
  cut1_gip_prop_def : 
    "cut1_gip_prop c1 == ALL any. gip_cond c1 (nured any)"
  cut1_dvk_prop_def : 
    "cut1_dvk_prop c1 == ALL any. dvk_cond c1 (nured any)"

end 

